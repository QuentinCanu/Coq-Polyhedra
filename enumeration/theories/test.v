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
Definition x := [|2;0|0|]%bigQ.
Definition inv := [|
  [| -1; -1|0|];
  [| -1; 1|0|]
|[|0|0|]|]%bigQ.
Definition q := (-2)%bigZ.

Definition certif_pred :=[|
  (0,(0,0));
  (0,(2,1));
  (0,(3,0));
  (2,(2,0))
  |(0,(0,0))|]%uint63.

Definition order := [|1;2;3|0|]%uint63.
Definition steps := length order.

Time Compute (R1.explore_from_initial A b certif_bases certif_pred idx x inv q order steps).[1].


(* Time Definition init := Eval vm_compute in R1.initial A b certif_bases idx x inv q.
Time Definition init_main := Eval vm_compute in R1.initial_main A b certif_bases idx x inv q.
Time Compute let (idx,rs) := certif_pred.[order.[0]] in
let (r,s) := rs in
let I := certif_bases.[idx] in
if init_main.[idx] is Some (x, B, M, q) then
  let '(x', B', M', q') := R1.update b I r s x B M q in
  if R1.sat_lex M' q' b certif_bases.[order.[0]] then init_main.[order.[0] <- Some (x', B', M', q')] else init_main
else init_main. *)
(* Let x' := Eval vm_compute in main.1.1.1.
Let B' := Eval vm_compute in main.1.1.2.
Let M' := Eval vm_compute in main.1.2.
Let q' := Eval vm_compute in main.2. *)

(* Compute R1.update b certif_bases.[0] 2 1 x' B' M' q'. *)


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

Definition det := R1.get_num 1%bigQ.

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
