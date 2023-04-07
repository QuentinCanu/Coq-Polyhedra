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
Local Definition matrix := array (array bigQ).
Local Definition vector := array bigQ.
Local Definition basis := array int63.

(* ---------------------------------------------------------------------------- *)

Module Rank1Certif.

Definition cmp_vect (u : array bigQ) (v : array bigQ):=
  PArrayUtils.mk_fun (fun i=> (u.[i] ?= v.[i])%bigQ) (length u)%uint63 Eq.

(* if ((M.[Ik].[l] - M'.[Ik].[l]) * Mrs ?= M.[Is].[l] * M.[Ik].[r])%bigQ is Eq then true else false) *)

Definition memory_update (memory : array (array (array (option bigQ))))
(k i j :int63) (v : bigQ) : (array (array (array (option bigQ)))):=
  memory.[k <- memory.[k].[j <- memory.[k].[j].[i <- Some v]]].

Fixpoint eval
  (fuel : nat)
  (certif_bases : array basis)
  certif_pred
  (certif_updates : array matrix)
  (kJ : int63) (i j : int63)
  (memory : array (array (array (option bigQ)))):=
  if fuel is n.+1 then
    if memory.[kJ].[j].[i] is Some value then (Some value,memory) else
    let J := certif_bases.[kJ] in
    let '(kI, rs) := certif_pred.[kJ] in let '(r,s) := rs in let I := certif_bases.[kI] in
    let '(Mrs, memory) := eval n certif_bases certif_pred certif_updates kI r I.[s] memory in
    if Mrs is Some mrs then
      if (j =? r)%uint63 then
        let (Mis,memory) := eval n certif_bases certif_pred certif_updates kI i I.[s] memory in
        if Mis is Some mis then
          let m'ir := certif_updates.[kJ].[r].[i] in
          if (mrs * m'ir ?= - mis)%bigQ is Eq then 
            (Some m'ir, memory_update memory kJ i r m'ir)
          else
            (None,memory)
        else
        (None,memory)
      else
        let '(Mij,memory) := eval n certif_bases certif_pred certif_updates kI i j memory in
        if Mij is Some mij then
          let '(Mis,memory) := eval n certif_bases certif_pred certif_updates kI i I.[s] memory in
          if Mis is Some mis then
            let '(Mrj,memory) := eval n certif_bases certif_pred certif_updates kI r j memory in
            if Mrj is Some mrj then
              let m'ij := certif_updates.[kJ].[j].[i] in
              if ((mij - m'ij) * mrs ?= mis * mrj)%bigQ is Eq then
                (Some m'ij, memory_update memory kJ i j m'ij)
              else (None,memory)
            else (None,memory)
          else (None,memory) 
        else (None,memory)
    else (None, memory)
  else (None, memory).

Definition lazy_sat_pert
  (certif_bases : array basis)
  certif_pred
  certif_updates
  (idx_base : int63)
  memory
  (pt k : int63) (sat_vect : array comparison):=
  let I := certif_bases.[idx_base] in
  IFold.ifold (fun i '(acc,memory)=>
    let cmp := acc.[i] in
    if cmp is Eq then
      if (I.[pt] =? k)%uint63 then
        let (Value,memory) := eval Uint63.size certif_bases certif_pred certif_updates idx_base i I.[pt] memory in
        if Value is Some value then
          (acc.[i <- if (i =? k)%uint63 then (-1 ?= value)%bigQ else (0 ?= value)%bigQ],memory)
        else (acc.[i <- Lt],memory)
      else (acc.[i <- if (i =? k)%uint63 then Gt else Eq], memory)
    else (acc,memory)
  ) (length sat_vect) (sat_vect,memory).


Definition lazy_sat (A : matrix) (b x : vector) (I : basis)
  memory:=
  let sat_vect := (cmp_vect (BigQUtils.bigQ_mul_mx_col A x) b) in
  let lex_vect := IFold.ifold (fun i acc =>
    lazy_sat_pert i
  ) (length A) sat_vect in
  IFold.ifold (fun i '(continue,k)=>
    if ~~ continue then (continue,k) else
      if (i =? I.[k])%uint63 then
        if cmp.[i] is Eq then (true,Uint63.succ k) else (false,k)
      else
        if cmp.[i] is Lt then (false, k) else (true, k) 
  ) (length lex_vect) (true,0%uint63).


Definition lazy_vertex_certif 
  (A : matrix) (b : vector)
  (certif_vtx : array vector)
  (certif_bases : array basis)
  (certif_pred : array (int63 * (int63 * int63)))
  (certif_updates : array matrix)
  (idx : int63) (order : array int63) (steps : int63):=
  (IFold.ifold (fun i '(continue, memory)=>
    if ~~ continue then (continue, memory) else
      let kJ := order.[i] in
      let J := certif_bases.[kJ] in
      let '(kI, rs) := certif_pred.[kJ] in let '(r,s) := rs in
      let M := certif_updates.[kI] in
      let x := certif_vtx.[kJ] in
      lazy_sat 
  ) (initial_todo) steps).1.

(* ------------------------------------------------------------------ *)
Definition sat_pert (Ax : (array bigQ)) (m : int63) (cmp : array comparison):=
  IFold.ifold (fun i cmp=>
    if cmp.[i] is Eq then
      if (i =? m)%uint63 then cmp.[i <- (Ax.[i] ?= -1)%bigQ] else cmp.[i <- (Ax.[i] ?= 0)%bigQ]
    else cmp
  ) (length cmp) cmp.

Definition cmp_vect (u : array bigQ) (v : array bigQ):=
  PArrayUtils.mk_fun (fun i=> (u.[i] ?= v.[i])%bigQ) (length u)%uint63 Eq.

Definition sat_cmp (Ax : array bigQ) (b : array bigQ)
  (M : array (array bigQ)):=
  IFold.ifold (fun i cmp=>
    sat_pert M.[i] i cmp) (length M) 
  (cmp_vect Ax b).

Definition sat_lex (A : array (array bigQ)) (b : array bigQ)
  (I : array int63) (x : array bigQ) (M : array (array bigQ)):=
  let Ax := BigQUtils.bigQ_mul_mx_col A x in
  let cmp := sat_cmp Ax b M in
  (IFold.ifold (fun i '(test,k)=>
    if test then
      if (i =? I.[k])%uint63 then
        if cmp.[i] is Eq then (true,Uint63.succ k) else (false,k)
      else
        if cmp.[i] is Lt then (false, k) else (true, k)
    else (test,k)
    ) (length cmp) (true, 0%uint63)).1.

(*sat_lex Ax b I verifies that AX >=lex b and (AX)_I == b_I*)

Definition all_sat_lex A b certif_bases certif_vtx certif_updates
  order steps :=
  IFold.iall (fun i=>
    let idx := order.[i] in 
    let I := certif_bases.[idx] in
    let x := certif_vtx.[idx] in
    let M := certif_updates.[idx] in
    sat_lex A b I x M) steps.

(* ------------------------------------------------------------------ *)

Definition check_update
  (I : array Uint63.int) (r s : Uint63.int)
  (M M' : array (array BigQ.bigQ)) :=
  let Is := I.[s] in
  let Ms := M.[Is] in
  let Mrs := Ms.[r] in
  let q1 := IFold.iall (fun l=>
    if (Mrs * M'.[r].[l] ?= -Ms.[l])%bigQ is Eq then true else false)
    (length M'.[r]) in
  q1 && IFold.iall (fun k =>
    if (k =? s)%uint63 then true else
    let Ik := I.[k] in
    IFold.iall (fun l=>
      if ((M.[Ik].[l] - M'.[Ik].[l]) * Mrs ?= M.[Is].[l] * M.[Ik].[r])%bigQ is Eq then true else false) 
    (length M.[Ik])) (length I).

Definition look_all_updates
  (certif_bases : array (array int63))
  (certif_pred : array (int63 * (int63 * int63)))
  (certif_updates : array ((array (array bigQ))))
  (idx : int63) (order : array int63) (steps : int63) :=
  let res :=
  IFold.ifold (fun i acc=>
    let M' := certif_updates.[order.[i]] in
    let (idx,rs) := certif_pred.[order.[i]] in
    let (r,s) := rs in
    let I := certif_bases.[idx] in
    let M := certif_updates.[idx] in 
      acc.[i <- check_update I r s M M']) 
    steps (make steps false)
  in res.
  (* in let res := res.[idx <- true] in res. *)

Definition check_all_updates
  (certif_bases : array (array int63))
  (certif_pred : array (int63 * (int63 * int63)))
  (certif_updates : array ((array (array bigQ))))
  (idx : int63) (order : array int63) (steps : int63):=
  PArrayUtils.all id (look_all_updates certif_bases certif_pred certif_updates idx order steps).


(* ------------------------------------------------------------------ *)

Definition vertex_certif A b certif_bases certif_vtx certif_pred certif_updates idx order steps :=
  all_sat_lex A b certif_bases certif_vtx certif_updates order steps &&
  check_all_updates certif_bases certif_pred certif_updates idx order steps.

End Rank1Certif.

Module R1 := Rank1Certif.

(* ---------------------------------------------------------------------------- *)

Module CertifPredVerif.



Definition adjacent (I J : array int63) (r s : int63):=
  (IFold.ifold (fun i '(kI,kJ,c)=>
    if c then
      if (kI <? length I)%uint63 then
        if (kJ <? length J)%uint63 then
          if (I.[kI] =? J.[kJ])%uint63 then
            ((Uint63.succ kI),(Uint63.succ kJ),c)
          else
            if (kI =? s)%uint63 then
              ((Uint63.succ kI), kJ, c)
            else
              if (J.[kJ] =? r)%uint63 then
                (kI, (Uint63.succ kJ), c)
              else (kI, kJ, false)
        else
          if (kI =? s)%uint63 then
            ((Uint63.succ kI), kJ, c)
          else (kI, kJ, false)
      else
        if (kJ <? length J)%uint63 then
          if (J.[kJ] =? r)%uint63 then
            (kI, (Uint63.succ kJ), c)
          else (kI,kJ,false)
        else (kI,kJ,true)
    else (kI,kJ,c))
  (length I + length J)%uint63 (0%uint63,0%uint63,true)).2.

Definition certif_pred_correct certif_bases certif_pred :=
  IFold.iall (fun i =>
    let J := certif_bases.[i] in
    let '(idx, rs) := certif_pred.[i] in
    let '(r,s) := rs in
    let I := certif_bases.[idx] in
    adjacent I J r s) (length certif_bases).

End CertifPredVerif.
