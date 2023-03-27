(* ------ *) Require Import Uint63 PArray.
From Bignums Require Import BigNumPrelude.
From Bignums Require Import BigQ.

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
Definition x := [|(-2);0|0|]%bigQ.
Definition inv := [|
  [|1;1|0|];
  [|1;-1|0|]
|[|0|0|]|]%bigQ.
Definition q := 2%bigZ.

Definition certif_pred :=[|
  (0,(0,0));
  (0,(2,1));
  (0,(3,0));
  (2,(2,0))
  |(0,(0,0))|]%uint63.

Definition order := [|1;2;3|0|]%uint63.
Definition steps := length order.

Time Definition main := Eval vm_compute in R1.explore_from_initial A b certif_bases certif_pred idx x inv q order steps.
Print main.

Time Definition arr := Eval vm_compute in R1.array_to_test main certif_bases order steps.
Eval vm_compute in arr.
Time Compute R1.bench_old A arr.
Time Compute R1.bench_old2 A b arr.
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
Definition q := 1%bigZ.

Definition certif_pred :=[|
(0,(0,0));
(0,(5,2));
(3,(2,2));
(1,(4,1));
(6,(1,2));
(4,(5,1));
(2,(3,0));
(5,(4,0))
|(0,(0,0))|]%uint63.

Definition order := [|1;3;2;6;4;5;7|0|]%uint63.
Definition steps := length order.

Definition test := Eval vm_compute in R1.vertex_certif A b certif_bases certif_pred idx x inv q order steps.
Print test.

End Cube3.

(* From Coq Require Import ExtrOCamlInt63 ExtrOCamlPArray ExtrOcamlBasic Extraction.

Extraction Language OCaml.
Set Extraction Optimize.
Set Extraction AutoInline.
Set Extraction AccessOpaque.

Extract    Constant PArray.array "'a" => "Parray.t".
Extraction Inline   PArray.array.

Extract Constant PArray.make    => "Parray.make".
Extract Constant PArray.get     => "Parray.get".
Extract Constant PArray.default => "Parray.default".
Extract Constant PArray.set     => "Parray.set".
Extract Constant PArray.length  => "Parray.length".
Extract Constant PArray.copy    => "Parray.copy".

Extract Inlined Constant negb => "not".
Extract Inlined Constant fst  => "fst".
Extract Inlined Constant snd  => "snd".

Extraction "cube" Cube3.test. *)
