(* --------------------------------------------------------------------
 * Copyright (c) - 2017--2020 - Xavier Allamigeon <xavier.allamigeon at inria.fr>
 * Copyright (c) - 2017--2020 - Ricardo D. Katz <katz@cifasis-conicet.gov.ar>
 * Copyright (c) - 2019--2020 - Pierre-Yves Strub <pierre-yves@strub.nu>
 *
 * Distributed under the terms of the CeCILL-B-V1 license
 * -------------------------------------------------------------------- *)

(* -------------------------------------------------------------------- *)
Require Import Recdef.
From mathcomp Require Import all_ssreflect ssrnum ssralg zmodp matrix mxalgebra vector finmap.
Require Import extra_misc inner_product extra_matrix xorder vector_order row_submx xvector.
Require Import hpolyhedron polyhedron barycenter poly_base.

Import Order.Theory.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Local Open Scope ring_scope.
Local Open Scope poly_scope.
Import GRing.Theory Num.Theory.

(* Goal :

On suppose qu'on est à la base admissible I, et on considère i \in I.

Pour tout j \notin I, on note
- c_ij := A_j * (col i A_I^{-1}) <- c_{ij} := '[j.1, d] pour j \in base `\` I, où
d est tel que affine << I \` i >> = [line d & _] et '[i.1, d] = 1
- r_j := A_j x^I - b_j (qui ne dépend pas de i)

Proposition
Soit I une base admissible, i \in I, et j \notin I. Alors J = I - i + j est une base admissible ssi les conditions suivantes sont satisfaites :
* c_ij != 0
* r_j > 0 ==> j \in arg max_(k notin I | c_ik < 0) (r_k / c_ik).

*)

Section PBasis.
Context {R : realFieldType} {n : nat} {base : base_t[R,n]}.
Context (P : {poly base}).
Hypothesis Pprop0 : P `>` [poly0].

Implicit Type (I : {fsubset base}).

Lemma span_polyEq (I J : base_t) :
  (<<I>> = <<J>>)%VS -> 'P^=(base; I) = 'P^=(base; J).
Proof.
by rewrite !polyEq_affine => ->.
Qed.

Lemma basis_polyEq (I J : base_t) :
  basis_of <<I>>%VS J -> 'P^=(base; I) = 'P^=(base; J).
Proof.
by move/span_basis/span_polyEq.
Qed.

Definition is_pbasis I :=
   [&& (#|` I | == n)%N, (dim (affine <<I>>%VS) == 1)%N & (affine <<I>>%VS `<=` P)].

(*Definition is_pbasis I :=
  [&& (#|` I | == n)%N, (\dim <<I>> == n)%N & ([poly0] `<` 'P^=(base; I) `<=` P)].*)

Lemma card_pbasis I :
  is_pbasis I -> #|` I | = n.
Proof.
by case/and3P => /eqP.
Qed.

(*Definition point_of_pbasis I := ppick (affine <<I>>%VS).
Lemma point_of_pbasisP I :
  is_pbasis I -> affine <<I>>%VS = [pt (point_of_pbasis I)].*)


Lemma pbasis_proper0 I :
  is_pbasis I -> affine <<I>> `>` [poly0]. (*affine <<I>>%VS `>` .*)
Proof.
by case/and3P => _ /eqP dimI _; rewrite dimN0 dimI.
Qed.

Lemma pbasis_feasible I :
  is_pbasis I -> affine <<I>> `<=` P.
Proof.
by case/and3P.
Qed.

Lemma dim_affine_pbasis I :
  is_pbasis I -> (dim (affine <<I>>) = 1)%N.
Proof.
by case/and3P => _ /eqP.
Qed.

Lemma pbasis_active I :
  is_pbasis I -> 'P^=(base; I) = affine <<I>>.
Proof.
move => pbasisI; rewrite polyEq_affine; apply/polyIidPr.
apply/(poly_subset_trans (pbasis_feasible _)) => //.
exact: poly_base_subset.
Qed.

(*Lemma span_pbasis I :
  is_pbasis I -> (<< I >> = << {eq 'P^=(base; I)%:poly_base} >>)%VS.
Proof.
Admitted.*)

Lemma pbasis_vertex I :
  is_pbasis I -> exists2 x, x \in vertex_set P & affine <<I>> = [pt x].
Proof.
move => pbasis_I.
case/eqP/dim1P: (dim_affine_pbasis pbasis_I) => x ptPbaseI.
move : (pbasis_feasible pbasis_I).
rewrite ptPbaseI; move => ptx_subset_P; exists x => //.
rewrite in_vertex_setP -ptPbaseI face_setE.
- by rewrite ptPbaseI.
- by rewrite -pbasis_active // pvalP.
Qed.

Lemma vertexP (x : 'cV_n) :
  x \in vertex_set P ->
        exists Q : {poly base}, [/\ [pt x] = Q, dim Q = 1%N & (Q `<=` P)].
Proof.
case/imfsetP => Q /=; rewrite inE => /andP [].
case/face_setP => {}Q ? _ /eqP ? ->.
by exists Q; split; rewrite -?dim1_pt_ppick.
Qed.

Lemma vertex_pbasis x :
  x \in vertex_set P -> exists2 I, is_pbasis I & [pt x] = affine <<I>>%VS.
Proof.
case/vertexP => Q [-> dimQ_eq1 Q_sub_P].
have Q_prop0: Q `>` [poly0] by rewrite dimN0 dimQ_eq1.
have dim_eqQ: (\dim <<{eq Q}>> = n)%N.
- apply/anti_leq/andP; split; rewrite ?dim_span_active //.
  move: dimQ_eq1; rewrite dimN0_eq // => /succn_inj/eqP.
  by rewrite subn_eq0.
case: (ebasisP0 {eq Q}) => I I_sub I_basis.
have I_sub_base: (I `<=` base)%fset. (* TODO: missing canonical in fsubset *)
- by apply/(fsubset_trans I_sub)/fsubset_subP.
have I_pbasis : is_pbasis (I%:fsub).
- apply/and3P; split => /=.
  + by rewrite (card_basis I_basis) dim_eqQ.
  + by rewrite (span_basis I_basis) -hullN0_eq // -dim_hull dimQ_eq1.
  + by rewrite (span_basis I_basis) -hullN0_eq //
  (dim1_pt_ppick dimQ_eq1) hull_pt -dim1_pt_ppick.
exists (I%:fsub) => //.
rewrite -pbasis_active // (span_polyEq (span_basis I_basis)).
by rewrite [Q in LHS]repr_active //=.
Qed.

Definition adj_basis I I' := #|` (I `&` I') |%fset = n.-1.
Definition adj_vertex x x' := (x != x') && ([segm x & x'] \in face_set P).

Lemma adj_vertex_prebasis x x':
  adj_vertex x x' -> exists J,
    [/\ 'P^=(base; J) = [segm x & x'], (\dim <<J>>)%N = n.-1 & free J].
Proof.
rewrite /adj_vertex => /andP [x_neq_x'].
case/face_setP => Q Q_sub_P Q_eq.
have Q_prop0: Q `>` [poly0] by rewrite -Q_eq segm_prop0.
case: (ebasisP0 {eq Q})=> J J_sub J_basis.
exists J; split.
- by rewrite [Q]repr_active //= (basis_polyEq J_basis).
- have dimQ2: (dim Q) = 2%N by rewrite -Q_eq dim_segm x_neq_x'.
move: (span_basis J_basis) => ->.
rewrite (dimN0_eq Q_prop0) in dimQ2. move/eq_add_S: dimQ2 => dimQeq.
rewrite -subn1 -dimQeq subKn => //.
by apply ltnW; rewrite -subn_gt0 dimQeq.
- by move/basis_free: J_basis.
Qed.

Lemma adj_vertex_basis x x' :
  adj_vertex x x' -> exists I, exists I',
      [/\ is_pbasis I, is_pbasis I',
       'P^=(base; I) = [pt x], 'P^=(base; I') = [pt x'] & adj_basis I I'].
Proof.
move=> adj_x_x'.
case : (adj_vertex_prebasis adj_x_x') => J [] segm_J dim_J free_J.
move: (adj_x_x'); rewrite /adj_vertex; case/andP => x_neq_x' segm_face.
have: [pt x] \in face_set P /\ [pt x'] \in face_set P.
- split; move/face_setS: segm_face; rewrite face_set_segm;
  move/fsubsetP => H.
  + by apply: (H [pt x]); rewrite !inE eq_refl orbT.
  + by apply: (H [pt x']); rewrite !inE eq_refl orbT.
case; case/face_setP => Qx Qxsub Qxpt; case/face_setP => Qx' Qx'sub Qx'pt.
case/face_setP: segm_face => S Ssub Ssegm.
have: ({eq S} `<=` {eq Qx})%fset /\ ({eq S} `<=` {eq Qx'})%fset.
by rewrite !activeS // -Ssegm -?Qxpt -?Qx'pt pt_subset ?in_segml ?in_segmr.
case => eq_sub_eq_x eq_sub_eq_x'.
have J_sub_eqS: (J `<=` {eq S})%fset.
Admitted.




(* Proof sketch:
 * start from x x' satisfying adj_vertex x x'
 * extract J from adj_vertex_prebasis
 * Then we have x \in 'P^=(base; J), so that
 * J \subset {eq 'P^=(base; J)} \subset {eq [pt x]%:poly_base} (see activeS)
 * apply ebasisP to complete J into a basis I of <<{eq [pt x]%:poly_base}>> containing J
 * since dim <<{eq [pt x]%:poly_base}>> = n, then I is J + one element,
 * apply the same proof to x', which provided I' such that #|` I `&` I'| = n.-1
 *)


Lemma foo' x (I : {fsubset base}) :
  x \in P -> [pt x] = affine <<I>>%VS -> #|` I| = n -> is_pbasis I.
Proof.
move => x_in_P pt_eq cardI.
apply/and3P; split; rewrite -?pt_eq.
- by apply/eqP.
- by rewrite dim_pt.
- by rewrite pt_subset.
Qed.

(*move => H; case: (adj_vertex_prebasis H) => J; case => PbaseJ cardJ.
case/andP: H => x_neq_x' /face_setP [] Q Q_sub_P Qeq.
have x_vtx: x \in vertex_set Q.
- by rewrite -Qeq vertex_set_segm in_fset2 eq_refl.
rewrite in_vertex_setP in x_vtx.
case/face_setP: x_vtx => Qx Qx_sub_Q ptx_eq.
have x'_vtx: x' \in vertex_set Q.
- by rewrite -Qeq vertex_set_segm in_fset2 eq_refl orbT.
rewrite in_vertex_setP in x'_vtx.
case/face_setP: x'_vtx => Qx' Qx'_sub_Q ptx'_eq.*)

(*move/vertex_set_face/fsetP; rewrite vertex_set_segm /eq_mem.
Search _ Imfset.imfset.*)


(*Lemma dim_pbasisD1 I i :
  is_pbasis I -> (i \in (I : {fset _}))
  -> dim (affine << (I `\ i)%fset >>%VS) = 2%N.
Proof.
move => I_pbasis i_in_I /=.
Admitted.*)

Lemma dim_pbasisD1' I i :
  is_pbasis I -> i \in (I : {fset _}) ->
    exists d, (affine << (I `\ i)%fset >> == [line d & (ppick 'P^=(base; I))]) && ('[i.1, d] == 1).
Admitted.

Definition dir I i (H : is_pbasis I) (H' : i \in (I : {fset _})) :=
  xchoose (dim_pbasisD1' H H').

Definition c I i (H : is_pbasis I) (H' : i \in (I : {fset _})) (j : lrel[R]_n) :=
  '[j.1, dir H H'].

Definition r I (j : lrel[R]_n) :=
  '[j.1, ppick (affine << I >>%VS)] - j.2.

End PBasis.
