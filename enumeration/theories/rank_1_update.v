Require Import PArray Uint63.
From Bignums Require Import BigQ.
From mathcomp Require Import all_ssreflect all_algebra.
From Polyhedra Require Import extra_misc inner_product vector_order.
Require Import graph extra_array extra_int array_set rat_bigQ diameter img_graph refinement enum_algo.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import Order.Theory.
Import GRing.Theory Num.Theory.

(* ---------------------------------------------------------------------------- *)

Local Notation int63 := Uint63.int.

(* ---------------------------------------------------------------------------- *)

Module Rank1Certif.

Definition scal_col (x : array (array bigQ)) (i : int63) (a : bigQ):=
  x.[i <-
  IFold.ifold (fun k c=> c.[k <- (a * c.[k])%bigQ])
  (length x.[i]) x.[i]].

Definition lin_col
  (x : array (array bigQ)) (i j : int63) (ai aj : bigQ):=
  x.[i <-
    IFold.ifold (fun k c=> c.[k <- (ai * c.[k] + aj * x.[j].[k])%bigQ])
    (length x.[i]) x.[i]].

Definition col0
  (x : array (array bigQ)) (i : int63):=
  x.[i <- IFold.ifold (fun k c=> c.[k <- 0%bigQ]) (length x.[i]) x.[i]].

Definition deep_copy {T : Type} (M : array (array T)):=
  PArrayUtils.mk_fun (fun i=> copy M.[i]) (length M) (default M).

(* ------------------------------------------------------------------ *)
Definition sat_pert (Ax : (array bigQ)) (m : int63) (cmp : array comparison):=
  IFold.ifold (fun i cmp=>
    if cmp.[i] is Eq then
      if (i =? m)%uint63 then cmp.[i <- (Ax.[i] ?= -1)%bigQ] else cmp.[i <- (Ax.[i] ?= 0)%bigQ]
    else cmp
  ) (length cmp) cmp.

Definition cmp_vect (u : array bigQ) (v : array bigQ):=
  PArrayUtils.mk_fun (fun i=> (u.[i] ?= v.[i])%bigQ) (length u)%uint63 Eq.

Definition sat_cmp (Ax : array (array bigQ)) (b : array bigQ) :=
  IFold.ifoldx (fun i cmp=>
    sat_pert Ax.[i] (Uint63.pred i) cmp
  ) 1%uint63 (length Ax) (cmp_vect Ax.[0] b).

Definition sat_lex (Ax : array (array bigQ)) (q : bigZ) (b : array bigQ) (I : array int63):=
  let: Ax :=
    PArrayUtils.map (PArrayUtils.map (fun x => (x / (BigQ.Qz q))%bigQ)) Ax
  in
  let cmp := sat_cmp Ax b in
  (IFold.ifold (fun i '(test,k)=>
    if test then
      if (i =? I.[k])%uint63 then
        if cmp.[i] is Eq then (true,Uint63.succ k) else (false,k)
      else
        if cmp.[i] is Lt then (false, k) else (true, k)
    else (test,k)
    ) (length cmp) (true, 0%uint63)).1.

(*sat_lex Ax b I verifies that AX >=lex b and (AX)_I == b_I*)

(* ------------------------------------------------------------------ *)

Definition divQZ (x : bigQ) (q : bigZ) :=
  match x with
  | BigQ.Qz x =>
      let '(y, r) := BigZ.div_eucl x q in
      if (r =? 0)%bigZ then
        BigQ.Qz y
      else
        BigQ.Qq ((BigZ.sgn q) * x)%bigZ (BigZ.to_N q)
  | BigQ.Qq x d =>
      let '(y, r) := BigZ.div_eucl x q in
      if (r =? 0)%bigZ then
        BigQ.Qq y d
      else
        BigQ.Qq ((BigZ.sgn q) * x)%bigZ (d * BigZ.to_N q)%bigN
  end.

Definition get_num (x : bigQ) :=
  match x with
  | BigQ.Qz x => x
  | BigQ.Qq x _ => x
  end.

Definition update
  (b : array bigQ)
  (I : array Uint63.int) (r s : Uint63.int)
  (M : array (array bigQ)) (q : bigZ) :=
  let M' := PArrayUtils.mk_fun (fun _ => make (length M.[0]) 0%bigQ) (length M) (default M) in
  let Is := I.[s] in
  let Ms := M.[Uint63.succ Is] in
  let Mrs := Ms.[r] in
  let M0r := M.[0].[r] in
  let M'0 :=
    PArrayUtils.mk_fun
      (fun k => divQZ (M.[0].[k] * Mrs + ((BigQ.Qz q) * b.[r] - M0r) * Ms.[k])%bigQ q)
      (length M.[0]) (default M.[0]) in
  let M' := M'.[0 <- M'0] in
  let M' := IFold.ifold (fun k M'=>
    if (k =? s)%uint63 then M' else
    let Ik := I.[k] in
    let M'Ik :=
      PArrayUtils.mk_fun
        (fun l => divQZ (M.[Uint63.succ Ik].[l] * Mrs - M.[Uint63.succ Is].[l] * M.[Uint63.succ Ik].[r])%bigQ q)
        (length M.[Uint63.succ Ik]) 0%bigQ in
    let M' := M'.[Uint63.succ Ik <- M'Ik] in
    M') (length I) M' in
  let M'r := PArrayUtils.mk_fun (fun l => (-Ms.[l])%bigQ) (length Ms) 0%bigQ in
  let M' := M'.[Uint63.succ r <- M'r] in
  (M', get_num Mrs).

Definition explore
  (b : array bigQ)
  (certif_bases : array (array int63))
  (certif_pred : array (int63 * (int63 * int63)))
  (main : array (option ((array (array bigQ)) * bigZ)))
  (order : array int63) (steps : int63):=
  IFold.ifold
    (fun i main=>
       let (idx,rs) := certif_pred.[order.[i]] in
       let (r,s) := rs in
       let I := certif_bases.[idx] in
       if main.[idx] is Some (M, q) then
         let '(M', q') := update b I r s M q in
         if sat_lex M' q' b certif_bases.[order.[i]] then main.[order.[i] <- Some (M', q')] else main
       else main) steps main.

Definition initial
  (A : array (array bigQ)) (b : array bigQ)
  (certif_bases : array (array int63))
  (idx : int63) (x : array bigQ) (inv : array (array bigQ)) (q : bigZ) :=
  let I := certif_bases.[idx] in
  let M := PArrayUtils.mk_fun (fun _ => make (length A) 0%bigQ) (Uint63.succ (length A)) (make (length A) 0%bigQ) in
  let M := M.[0 <- BigQUtils.bigQ_mul_mx_col A x] in
  let M :=
    IFold.ifold (fun i M=>
                   let M := M.[Uint63.succ I.[i] <- BigQUtils.bigQ_scal_arr (-1)%bigQ (BigQUtils.bigQ_mul_mx_col A inv.[i])] in M)
      (length I) M
  in
  (M, q).

Definition initial_main
  (A : array (array bigQ)) (b : array bigQ)
  (certif_bases : array (array int63))
  (idx : int63) (x : array bigQ) (inv : array (array bigQ)) q :=
  let main := make (length certif_bases) None in
  let '(M, q) := initial A b certif_bases idx x inv q in
  if sat_lex M q b (certif_bases.[idx]) then main.[idx <- Some (M, q)] else main.

Definition explore_from_initial
  A b certif_bases certif_pred idx x inv q order steps:=
  explore b certif_bases certif_pred (initial_main A b certif_bases idx x inv q) order steps.

Definition vertex_certif
  (A : array (array bigQ)) (b : array bigQ)
  (certif_bases : array (array int63))
  (certif_pred : array (int63 * (int63 * int63)))
  (idx : int63) (x : array bigQ) (inv : array (array bigQ)) q
  (order : array int63) steps:=
  PArrayUtils.all isSome (explore_from_initial A b certif_bases certif_pred idx x inv q order steps).


(*
Definition update
  (b : array bigQ)
  (I : array Uint63.int) (r s : Uint63.int)
  (x : array bigQ) (B M : array (array bigQ)):=
  let '(B',M') :=
    (PArrayUtils.mk_fun (fun _ => make (length B.[0]) 0%bigQ) (length B) (default B),
     PArrayUtils.mk_fun (fun _ => make (length M.[0]) 0%bigQ) (length M) (default M)) in
  let Is := I.[s] in
  let Ms := M.[Uint63.succ Is] in
  let Mrs := Ms.[r] in
  let Bs := B.[Is] in
  let M0r := M.[0].[r] in
  let x' := PArrayUtils.mk_fun
             (fun k => BigQ.red (x.[k] + ((M0r - b.[r])/Mrs) * Bs.[k])%bigQ) (length x) (default x) in
  let M'0 := PArrayUtils.mk_fun (fun k => BigQ.red (M.[0].[k] + ((b.[r] - M0r)/Mrs) * Ms.[k])%bigQ) (length M.[0]) (default M.[0]) in
  let M' := M'.[0 <- M'0] in
  let (B', M') := IFold.ifold (fun k '(B',M')=>
    if (k =? s)%uint63 then (B',M') else
    let Ik := I.[k] in
    let B'Ik := PArrayUtils.mk_fun (fun l => BigQ.red (B.[Ik].[l] - B.[Is].[l] * M.[Uint63.succ Ik].[r] / Mrs)%bigQ) (length B.[Ik]) 0%bigQ in
    let M'Ik := PArrayUtils.mk_fun (fun l => BigQ.red (M.[Uint63.succ Ik].[l] - M.[Uint63.succ Is].[l] * M.[Uint63.succ Ik].[r] / Mrs)%bigQ) (length M.[Uint63.succ Ik]) 0%bigQ in
    let B' := B'.[Ik <- B'Ik] in
    let M' := M'.[Uint63.succ Ik <- M'Ik] in
    (B', M')) (length I) (B',M') in
  let B'r := PArrayUtils.mk_fun (fun l => BigQ.red (-Bs.[l] / Mrs)%bigQ) (length Bs) 0%bigQ in
  let M'r := PArrayUtils.mk_fun (fun l => BigQ.red (-Ms.[l] / Mrs)%bigQ) (length Ms) 0%bigQ in
  let B' := B'.[r <- B'r] in
  let M' := M'.[Uint63.succ r <- M'r] in
  (x', B', M').

Definition explore
  (b : array bigQ)
  (certif_bases : array (array int63))
  (certif_pred : array (int63 * (int63 * int63)))
  (main : array (option (array bigQ * array (array bigQ) * array (array bigQ))))
  (order : array int63) (steps : int63):=
  IFold.ifold
    (fun i main=>
       let (idx,rs) := certif_pred.[order.[i]] in
       let (r,s) := rs in
       let I := certif_bases.[idx] in
       if main.[idx] is Some (x, B, M) then
         let '(x',B',M'):= update b I r s x B M in
         if sat_lex M' b certif_bases.[order.[i]] then main.[order.[i] <- Some(x', B', M')] else main
       else main) steps main.

Definition initial
  (A : array (array bigQ)) (b : array bigQ)
  (certif_bases : array (array int63))
  (idx : int63) (x : array bigQ) (inv : array (array bigQ)):=
  let I := certif_bases.[idx] in
  let M := PArrayUtils.mk_fun (fun _ => make (length A) 0%bigQ) (Uint63.succ (length A)) (make (length A) 0%bigQ) in
  let B := PArrayUtils.mk_fun (fun _ => make (length A) 0%bigQ) (length A) (make (length A) 0%bigQ) in
  let M := M.[0 <- BigQUtils.bigQ_mul_mx_col A x] in
  IFold.ifold (fun i '(B,M)=>
    let B := B.[I.[i] <- inv.[i]] in
    let M := M.[Uint63.succ I.[i] <- BigQUtils.bigQ_scal_arr (-1)%bigQ (BigQUtils.bigQ_mul_mx_col A inv.[i])] in (B,M))
  (length I) (B,M).

Definition initial_main
  (A : array (array bigQ)) (b : array bigQ)
  (certif_bases : array (array int63))
  (idx : int63) (x : array bigQ) (inv : array (array bigQ)):=
  let main := make (length certif_bases) None in
  let (B,M) := initial A b certif_bases idx x inv in
  if sat_lex M b (certif_bases.[idx]) then main.[idx <- Some (x,B,M)] else main.

Definition explore_from_initial
  A b certif_bases certif_pred idx x inv order steps:=
  explore b certif_bases certif_pred (initial_main A b certif_bases idx x inv) order steps.


Definition make_basic_point (x : array bigQ) (B : array (array bigQ)):=
  let X := make (Uint63.succ (length B)) (make (length x) 0%bigQ) in
  let X := X.[0 <- copy x] in
  IFold.ifold
    (fun i acc=>
       let Bi := B.[i] in
       let x := PArrayUtils.mk_fun (fun k => BigQ.red (-Bi.[k])%bigQ) (length Bi) 0%bigQ in
       acc.[Uint63.succ i <- x])
    (length B) X.

Definition array_to_test (main : array (option (array bigQ * array (array bigQ) * array (array bigQ))))
  (certif_bases : array (array int63)) (order : array int63) (steps : int63) :=
  let res := make steps None in
  IFold.ifold (fun i acc=>
  if main.[order.[i]] is Some (x, B, _) then
    acc.[i <- Some (certif_bases.[order.[i]], make_basic_point x B)]
  else acc
  ) steps res.

Definition check_basic_point (A : array (array bigQ)) (b : array bigQ) (arr : array (option (array int63 * array (array bigQ)))):=
  let Po := (A,b) in
  PArrayUtils.all (fun x =>
                     if x is Some p then
                       (LCA.sat_Po Po p.2) && (LCA.mask_eq Po p.1 p.2)
                     else
                       false) arr.
*)
End Rank1Certif.

Module R1 := Rank1Certif.

(* ---------------------------------------------------------------------------- *)
