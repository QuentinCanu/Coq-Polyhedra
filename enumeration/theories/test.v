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

Module Cross2.

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

Definition certif_pred :=[|
  (0,0,0);
  (0,2,1);
  (0,3,0);
  (2,2,0)
  |(0,0,0)|]%uint63.

Definition order := [|1;2;3|0|]%uint63.

Compute R1.vertex_certif A b certif_bases certif_pred idx x inv order.
End Cross2.

Module Cube3.

Definition A := [|
  [|1;0;0|0|];
  [|0;1;0|0|];
  [|0;0;1|0|];
  [|(-1);0;0|0|];
  [|0;(-1);0|0|];
  [|0;0;(-1)|0|]
|[|0|0|]|]%bigQ.

Definition b := make 6%uint63 (-1)%bigQ.

Definition certif_bases := [|
  [|0;1;2|0|];
  [|0;1;5|0|];
  [|0;2;4|0|];
  [|0;4;5|0|];
  [|1;2;3|0|];
  [|1;3;5|0|];
  [|2;3;4|0|];
  [|3;4;5|0|]
|[|0|0|]|]%uint63.

Definition idx := 0%uint63.
Definition x := [|(-1);(-1);(-1)|0|]%bigQ.
Definition inv := [|
  [|1;0;0|0|];
  [|0;1;0|0|];
  [|0;0;1|0|]
|[|0|0|]|]%bigQ.

Definition certif_pred :=[|
(0,0,0);
(0,5,2);
(3,2,2);
(1,4,1);
(6,1,2);
(4,5,1);
(2,3,0);
(5,4,0)
|(0,0,0)|]%uint63.

Definition order := [|1;3;2;6;4;5;7|0|]%uint63.

Compute R1.explore_from_initial A b certif_bases certif_pred idx x inv order.
Compute R1.vertex_certif A b certif_bases certif_pred idx x inv order.


End Cube3.

(* Definition test := Eval compute in R1.explore b certif_bases certif_pred (R1.initial A b certif_bases idx x inv) order.
Definition triplet := match test.[2] with |Some X => X |None=> (x,A,A) end.
Definition x2 := Eval compute in triplet.1.1.
Definition B2 := Eval compute in triplet.1.2.
Definition M2 := Eval compute in triplet.2.


Print test.
Definition res:= R1.update b certif_bases.[2] 2 0 x2 B2 M2.
Compute res. *)

