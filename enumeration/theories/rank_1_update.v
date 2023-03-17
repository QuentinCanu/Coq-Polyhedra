Require Import PArray Uint63.
From Bignums Require Import BigQ.
From mathcomp Require Import all_ssreflect all_algebra.
From Polyhedra Require Import extra_misc inner_product vector_order.
Require Import graph extra_array extra_int array_set rat_bigQ diameter img_graph refinement.

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

Definition swap
  {T : Type}
  (x : array (array T)) (i j : int63):=
  let temp := copy x.[j] in
  x.[i <- temp].[j <- x.[i]].

Definition test := make 4 (make 1 0%bigQ).
Definition test2 := test.[1 <- (make 2 1%bigQ)].
Definition test3 := test.[2 <- (make 3 2%bigQ)].
Definition test_final := Eval vm_compute in swap test3 1 2.
Print test_final.

(* ------------------------------------------------------------------ *)
Definition sat_pert (Ax : (array bigQ)) (m : int63) (cmp : array comparison):=
  IFold.ifold (fun i cmp=>
    if cmp.[i] is Eq then 
      if (i =? m)%uint63 then cmp.[i <- (Ax.[i] ?= -1)%bigQ] else cmp.[i <- (Ax.[i] ?= 0)%bigQ]
    else cmp
  ) (length cmp) cmp.

Definition cmp_vect (u v : array bigQ):=
  PArrayUtils.mk_fun (fun i=> (u.[i] ?= v.[i])%bigQ) (length u)%uint63 Eq.

Definition sat_cmp (Ax : array (array bigQ)) (b : array bigQ) :=
  IFold.ifoldx (fun i cmp=>
    sat_pert Ax.[i] (Uint63.pred i) cmp
  ) 1%uint63 (length Ax) (cmp_vect Ax.[0] b).

Definition sat_lex (Ax : array (array bigQ)) (b : array bigQ) (I : array int63):=
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

Definition update 
  (b : array bigQ)
  (I : array int63) (r s : int63)
  (x : array bigQ) (B M : array (array bigQ)):=
  (* let M' := make (length M) (make (length M.[0]) 0%bigQ) in
  let B' := make (length B) (make (length B.[0]) 0%bigQ) in *)
  let Is := I.[s] in
  let Ms := M.[Uint63.succ Is] in
  let Mrs := Ms.[r] in
  let Bs := B.[Is] in
  let x' := BigQUtils.bigQ_add_arr x (BigQUtils.bigQ_scal_arr ((M.[0%uint63].[r] - b.[r])/Mrs)%bigQ Bs) in
  let M := M.[0 <- BigQUtils.bigQ_add_arr M.[0] (BigQUtils.bigQ_scal_arr ((b.[r] - M.[0%uint63].[r])/Mrs)%bigQ Ms)] in
  let (B, M) := IFold.ifold (fun k '(B',M')=>
    if (k =? s)%uint63 then (B',M') else
    let Ik := I.[k] in
    let B' := lin_col B' Ik Is 1%bigQ (- M'.[Uint63.succ Ik].[r]/Mrs)%bigQ in
    let M' := lin_col M' (Uint63.succ Ik) (Uint63.succ Is) 1%bigQ (-M'.[Uint63.succ Ik].[r]/Mrs)%bigQ in
    (B',M')
    ) (length I) (B,M) in
    let B := scal_col B.[r <- B.[Is]] r (-1/Mrs)%bigQ in
    let M := scal_col M.[Uint63.succ r <- M.[Uint63.succ Is]] (Uint63.succ r) (-1/Mrs) in
    let B := col0 B Is in let M := col0 M (Uint63.succ Is) in
  (x', B, M).

Definition explore 
  (b : array bigQ)
  (certif_bases : array (array int63))
  (certif_pred : array (int63 * (int63 * int63)))
  (main : array (option (array bigQ * array (array bigQ) * array (array bigQ))))
  (order : array int63):=
  PArrayUtils.fold (fun i main=>
    let (idx,rs) := certif_pred.[i] in
    let (r,s) := rs in
    let I := certif_bases.[idx] in
    if main.[idx] is Some (x, B, M) then
    let '(x',B',M'):= update b I r s x B M in
    if sat_lex M' b certif_bases.[i] then main.[i <- Some(x',B',M')] else main
    else main
  ) order main.

Definition initial
  (A : array (array bigQ)) (b : array bigQ)
  (certif_bases : array (array int63))
  (idx : int63) (x : array bigQ) (inv : array (array bigQ)):=
  let I := certif_bases.[idx] in
  let M := make (Uint63.succ (length A)) (make (length A) 0%bigQ) in
  let B := make (length A) (make (length A) 0%bigQ) in
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
  A b certif_bases certif_pred idx x inv order:=
  explore b certif_bases certif_pred (initial_main A b certif_bases idx x inv) order.

Definition vertex_certif 
  (A : array (array bigQ)) (b : array bigQ)
  (certif_bases : array (array int63))
  (certif_pred : array (int63 * (int63 * int63)))
  (idx : int63) (x : array bigQ) (inv : array (array bigQ))
  (order : array int63):=
  PArrayUtils.all isSome (explore_from_initial A b certif_bases certif_pred idx x inv order).

End Rank1Certif.

Module R1 := Rank1Certif.

(* ---------------------------------------------------------------------------- *)