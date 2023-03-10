Require Import PArray Uint63.
From mathcomp Require Import all_ssreflect all_algebra.
From Bignums Require Import BigQ.
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

Definition cmp_pert (line : array bigQ) (m : int63):=
  IFold.ifoldx (fun i cmp =>
    if cmp is Eq then 
      if (i =? m)%uint63 then (line.[i] ?= -1)%bigQ else (line.[i] ?= 0)%bigQ
    else cmp) 1 (length line) Eq.

Definition geqlex_line (line : array bigQ) (b : bigQ) (m : int63):=
  let: s := (line.[0] ?= b)%bigQ in
  if s is Eq then cmp_pert line m else s.

Definition sat_lex (Ax : array (array bigQ)) (b : array bigQ) (I : basis):=
  (IFold.ifold 
    (fun i '(j,sat)=> if sat then
        let: cmp := geqlex_line Ax.[i] b.[i] i in
        match cmp with
          |Lt => (j,false)
          |Gt => (j, ~~ (j =? I.[i])%uint63)
          |Eq => (Uint63.succ j, (j =? I.[i])%uint63)
        end
      else (j,sat)
    ) (length b) (0%uint63,true)).2.

(*sat_lex verifies that AX >=lex b and A_IX == b_I*)

Definition sign (x : int63):= if Uint63.is_even x then 1%bigQ else (-1)%bigQ.

Definition update (A : array (array bigQ)) (b : array bigQ)
  P (q : bigQ) I s r xJ:=
  let: P' := make (length P) (make (length P.[0%int63]) 0%bigQ) in
  let: sI := I.[s] in
  let: Prs := P.[sI].[r] in
  let: q' := ((sign(Uint63.sub I.[s] r)) * Prs)%bigQ in
  let: P' := P'.[0 <- bigQ_scal_arr q' (bigQ_mul_mx_col A xJ)] in
  let: P' := P'.[r <- P.[sI]] in
  let P' := IFold.ifold (fun k P' => if (k =? sI)%uint63 then P' else
    let P' := P'.[I.[k] <- bigQ_add_arr (bigQ_scal_arr P.[I.[k]].[r] P.[sI]) (bigQ_scal_arr (- P.[sI].[r])%bigQ P.[I.[k]])] in
    P'.[I.[k] <- bigQ_scal_arr (1/q)%bigQ P'.[I.[k]]]
    ) (length I) P' in
  (P', q').

End Rank1Certif.

(* ---------------------------------------------------------------------------- *)