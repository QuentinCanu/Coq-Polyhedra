(* ------ *) Require Import Uint63 PArray.
From Bignums Require Import BigNumPrelude.
From Bignums Require (*  *) BigN.BigN BigZ.BigZ BigQ.BigQ.

(* -------------------------------------------------------------------- *)
Local Open Scope array_scope.

Delimit Scope bigN_scope with bigN.
Delimit Scope bigZ_scope with bigZ.
Delimit Scope bigQ_scope with bigQ.

Local Notation "p # q" :=
  (BigQ.BigQ.Qq p%bigZ q%bigN) (at level 55, no associativity)
  : bigQ_scope.

Local Open Scope bigQ_scope.

Require Import extra_int extra_array rat_bigQ rank_1_update.
From mathcomp Require Import all_ssreflect.

Definition A := [|
  [|1;1|0|];
  [|1;-1|0|];
  [|(-1);1|0|];
  [|(-1);-1|0|]
  |[|0|0|]|]%bigQ.

Definition b := make 4 (-1)%bigQ.

Definition certif_bases := [|
  [|0;1|0|];
  [|0;2|0|];
  [|1;3|0|];
  [|2;3|0|]
|[|0|0|]|]%uint63.

Definition idx := 0%uint63.
Definition x := [|(-1);0|0|]%bigQ.
Definition inv := [|
  [|(1#2);(1#2)|0|];
  [|(1#2);(-1#2)|0|]
|[|0|0|]|]%bigQ.

(* Definition test:=
  let I := certif_bases.[idx] in
  let M := make (Uint63.succ (length A)) (make (length A) 0%bigQ) in
  let B := make (length A) (make (length A) 0%bigQ) in
  let M := M.[0 <- BigQUtils.bigQ_mul_mx_col A x] in
  let '(B,M) := IFold.ifold (fun i '(B,M)=>
    let B := B.[I.[i] <- inv.[i]] in
    let M := M.[Uint63.succ I.[i] <- BigQUtils.bigQ_scal_arr (-1)%bigQ (BigQUtils.bigQ_mul_mx_col A inv.[i])] in
    (B,M)
  ) (length I) (B,M) in M. *)

(* Definition init := Eval compute in R1.initial A b certif_bases idx x inv.

Definition triplet := match init.[0] with |Some (x,B,M)=> (x,B,M) |None => (x, A, A) end.
Definition x0 := Eval compute in triplet.1.1.
Definition B0 := Eval compute in triplet.1.2.
Definition M0 := Eval compute in triplet.2.

Definition I := Eval compute in certif_bases.[idx].
Definition r := 2%uint63.
Definition s := 1%uint63.

Definition test := Eval compute in R1.update b I r s x0 B0 M0.

Compute test. *)

Definition certif_pred :=[|
  (0,0,0);
  (0,2,1);
  (0,3,0);
  (2,2,0)
  |(0,0,0)|]%uint63.

Definition order := [|1;2;3|0|]%uint63.

Compute R1.vertex_certif A b certif_bases certif_pred idx x inv order.

(* Definition test := Eval compute in R1.explore b certif_bases certif_pred (R1.initial A b certif_bases idx x inv) order.
Definition triplet := match test.[2] with |Some X => X |None=> (x,A,A) end.
Definition x2 := Eval compute in triplet.1.1.
Definition B2 := Eval compute in triplet.1.2.
Definition M2 := Eval compute in triplet.2.


Print test.
Definition res:= R1.update b certif_bases.[2] 2 0 x2 B2 M2.
Compute res. *)

