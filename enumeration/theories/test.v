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

(* Module Cross2.

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
  (0,(0,0));
  (0,(2,1));
  (0,(3,0));
  (2,(2,0))
  |(0,(0,0))|]%uint63.

Definition order := [|1;2;3|0|]%uint63.
Definition steps := length order.

(* Definition main := Eval vm_compute in R1.explore_from_initial A b certif_bases certif_pred idx x inv order steps.
Definition arr := Eval vm_compute in R1.array_to_test main certif_bases.
Compute R1.bench_old A arr.
Compute R1.bench_old2 A b arr. *)
End Cross2. *)

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

Definition test := Eval vm_compute in R1.vertex_certif A b certif_bases certif_pred idx x inv order steps.

Definition update
  (b : array BigQ.bigQ)
  (I : array Uint63.int) (r s : Uint63.int)
  (x : array BigQ.bigQ) (B M : array (array BigQ.bigQ)):=
  let '(B',M') :=
    (PArrayUtils.mk_fun (fun _ => make (length B.[0]) 0%bigQ) (length B) (default B),
     PArrayUtils.mk_fun (fun _ => make (length M.[0]) 0%bigQ) (length M) (default M)) in
  let Is := I.[s] in
  let Ms := M.[Uint63.succ Is] in
  let Mrs := Ms.[r] in
  let Bs := B.[Is] in
  let M0r := M.[0].[r] in
  let x' := PArrayUtils.mk_fun (fun k => x.[k] + ((M0r - b.[r])/Mrs) * Bs.[k])%bigQ (length x) (default x) in
  let M'0 := PArrayUtils.mk_fun (fun k => (M.[0].[k] + ((b.[r] - M0r)/Mrs) * Ms.[k])%bigQ) (length M.[0]) (default M.[0]) in
  let M' := M'.[0 <- M'0] in
  let (B', M') := IFold.ifold (fun k '(B',M')=>
    if (k =? s)%uint63 then (B',M') else
    let Ik := I.[k] in
    let B'Ik := PArrayUtils.mk_fun (fun l => B.[Ik].[l] - B.[Is].[l] * M.[Uint63.succ Ik].[r] / Mrs)%bigQ (length B.[Ik]) 0%bigQ in
    let M'Ik := PArrayUtils.mk_fun (fun l => M.[Uint63.succ Ik].[l] - M.[Uint63.succ Is].[l] * M.[Uint63.succ Ik].[r] / Mrs)%bigQ (length M.[Uint63.succ Ik]) 0%bigQ in
    let B' := B'.[Ik <- B'Ik] in
    let M' := M'.[Uint63.succ Ik <- M'Ik] in
    (B', M')) (length I) (B',M') in
  let B'r := PArrayUtils.mk_fun (fun l => -Bs.[l] / Mrs)%bigQ (length Bs) 0%bigQ in
  let M'r := PArrayUtils.mk_fun (fun l => -Ms.[l] / Mrs)%bigQ (length Ms) 0%bigQ in
  let B' := B'.[r <- B'r] in
  let M' := M'.[Uint63.succ r <- M'r] in
  (x', B', M').


Definition test_func i (main : array (option (array BigQ.bigQ * array (array BigQ.bigQ) * array (array BigQ.bigQ)))) :=
let (idx,rs) := certif_pred.[order.[i]] in
let (r,s) := rs in
let I := certif_bases.[idx] in
if main.[idx] is Some (x, B, M) then
let '(x',B',M'):= update b I r s x B M in
if R1.sat_lex M' b certif_bases.[order.[i]] then main.[order.[i] <- Some(x', B', M')] else main
else main.

Definition main := Eval vm_compute in R1.initial_main A b certif_bases idx x inv.

Eval vm_compute in test_func 0%uint63 main.



(* Definition idx' := Eval vm_compute in certif_pred.[order.[0]].1.
Definition r := Eval vm_compute in certif_pred.[order.[0]].2.1.
Definition s := Eval vm_compute in certif_pred.[order.[0]].2.2.
Definition I := Eval vm_compute in certif_bases.[idx']. *)
(* Eval vm_compute in let (idx,rs) := certif_pred.[order.[0]] in
let (r,s) := rs in
let I := certif_bases.[idx] in
if main.[idx] is Some (x, B, M) then
let '(x',B',M') := (copy x, R1.deep_copy B, R1.deep_copy M) in
let Is := I.[s] in
let Ms := M'.[Uint63.succ Is] in
let Mrs := Ms.[r] in
let Bs := B'.[Is] in
let x := IFold.ifold
  (fun k c=> c.[k <- (BigQ.BigQ.add c.[k] (BigQ.BigQ.mul (BigQ.BigQ.div (BigQ.BigQ.sub M'.[0].[r] b.[r]) Mrs) Bs.[k]))%bigQ]) (length x) x in
let M' := M'.[0 <- IFold.ifold (fun k c=>
  c.[k <- (c.[k] (* + ((b.[r] - M'.[0].[r])/Mrs) * Ms.[k])%bigQ *))])
(length M'.[0]) M'.[0]] in
    let Ik := I.[0] in
    let B' := R1.lin_col B' Ik Is 1%bigQ (BigQ.BigQ.div (BigQ.BigQ.opp M'.[Uint63.succ Ik].[r]) Mrs)%bigQ in
    let M' := R1.lin_col M' (Uint63.succ Ik) (Uint63.succ Is) 1%bigQ (BigQ.BigQ.div (BigQ.BigQ.opp M'.[Uint63.succ Ik].[r]) Mrs)%bigQ in
    Some (B',M')
else None. *)

(* Definition test_func i (main : array (option (array BigQ.bigQ * array (array BigQ.bigQ) * array (array BigQ.bigQ)))) :=
let (idx,rs) := certif_pred.[order.[i]] in
let (r,s) := rs in
let I := certif_bases.[idx] in
if main.[idx] is Some (x, B, M) then
let '(x',B',M') := (copy x, R1.deep_copy B, R1.deep_copy M) in
let '(x'',B'',M''):= R1.update b I r s x' B' M' in
if R1.sat_lex M'' b certif_bases.[order.[i]] then main.[order.[i] <- Some(x'', B'', M'')] else main
else main.
Eval vm_compute in test_func 0%uint63 main. *)

(* Definition test := Eval vm_compute in R1.vertex_certif A b certif_bases certif_pred idx x inv order steps. *)

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
