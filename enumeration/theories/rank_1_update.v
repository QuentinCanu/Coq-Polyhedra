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

Section Defs.

Definition explored_bases := array (option (array (array bigQ) * bigQ)).
Definition basis := (array Uint63.int).

End Defs.

Local Notation int63 := Uint63.int.

(* ---------------------------------------------------------------------------- *)

Module Rank1Certif.

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

Definition sign (x : int63):= if Uint63.is_even x then 1%bigQ else (-1)%bigQ.

Definition update 
  (b : array bigQ)
  (I : array int63) (r s : int63)
  (M B : array (array bigQ)) (x : array bigQ):=
  let M' := make (length M) (make (length M.[0]) 0%bigQ) in
  let B' := make (length B) (make (length B.[0]) 0%bigQ) in
  let Ms := M.[Uint63.succ I.[s]] in
  let Mrs := Ms.[r] in
  let Bs := B.[I.[s]] in
  let Brs := Bs.[r] in
  let x' := BigQUtils.bigQ_add_arr x (BigQUtils.bigQ_scal_norm_arr ((b.[r] - M.[0%uint63].[r])/Mrs)%bigQ Bs) in
  let M' := M'.[0 <- BigQUtils.bigQ_add_arr M.[0] (BigQUtils.bigQ_scal_norm_arr (b.[r] - M.[0%uint63].[r]/Mrs)%bigQ Ms)] in
  let B' := B'.[r <- BigQUtils.bigQ_scal_norm_arr (1/Mrs) Bs] in
  let M' := M'.[r <- BigQUtils.bigQ_scal_norm_arr (1/Mrs) Ms] in
  let: (B', M') := IFold.ifold (fun k '(B',M')=>
    if (I.[k] =? s)%uint63 then (B',M') else
    let B'k := BigQUtils.bigQ_add_arr (BigQUtils.bigQ_scal_arr Mrs B.[k]) (BigQUtils.bigQ_scal_arr M.[Uint63.succ I.[k]].[r] Bs) in
    let B' := B'.[I.[k] <- BigQUtils.bigQ_scal_norm_arr (1/Mrs)%bigQ B'k] in
    let M'k := BigQUtils.bigQ_add_arr (BigQUtils.bigQ_scal_arr Mrs M.[Uint63.succ k]) (BigQUtils.bigQ_scal_arr M.[Uint63.succ I.[k]].[r] Ms) in
    let M' := M'.[Uint63.succ I.[k] <- BigQUtils.bigQ_scal_norm_arr (1/Mrs)%bigQ M'k] in
    (B',M')
    ) (length I) (B',M') in
  (x', B', M').





End Rank1Certif.

(* ---------------------------------------------------------------------------- *)