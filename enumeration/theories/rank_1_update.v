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
  let col := memory.[k].[j].[i <- Some v] in
  let M := memory.[k].[j <- col] in
  memory.[k <- M].

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
        let '(Mis,memory) := eval n certif_bases certif_pred certif_updates kI i I.[s] memory in
        if Mis is Some mis then
          let m'ir := certif_updates.[kJ].[r].[i] (*(-mis / mrs)%bigQ *) in
          if (mrs * m'ir ?= -mis)%bigQ is Eq then
            (Some m'ir, memory_update memory kJ i r m'ir)
          else (None,memory)
        else (None,memory)
      else
        let '(Mij,memory) := eval n certif_bases certif_pred certif_updates kI i j memory in
        if Mij is Some mij then
          let '(Mis,memory) := eval n certif_bases certif_pred certif_updates kI i I.[s] memory in
          if Mis is Some mis then
            let '(Mrj,memory) := eval n certif_bases certif_pred certif_updates kI r j memory in
            if Mrj is Some mrj then
              let m'ij := certif_updates.[kJ].[j].[i] (*(mij - mis * mrj / mrs)%bigQ*)  in
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
  (k : int63) (sat_vect : array comparison):=
  let I := certif_bases.[idx_base] in
  let '(_, res, memory) := IFold.ifold
    (fun i '(j, acc, memory)=>
       if (I.[j] =? i)%uint63 then
         ((j+1)%uint63, acc, memory) (* no-op when i is a line in the basis *)
       else
         if acc.[i] is Eq then
           let '(value, memory) := eval Uint63.size certif_bases certif_pred certif_updates idx_base i I.[k] memory in
           if value is Some v then
             (j, acc.[i <- (v ?= 0)%bigQ], memory)
           else
             (j, acc.[i <- Lt], memory) (* HACK here, to be fixed *)
         else
           (j, acc, memory) (* no-op since we only need to break inequality ties *)
    ) (length sat_vect) (0%uint63, sat_vect, memory)
  in
  (res, memory).

Definition lazy_check_basis (A : matrix) (b : vector)
  (certif_bases : array basis)
  (certif_pred : array (int63 * (int63 * int63)))
  certif_updates
  (certif_vtx : array vector)
  (idx_base : int63)
  memory :=
  let I := certif_bases.[idx_base] in
  let '(I0, (r, s)) := certif_pred.[idx_base] in
  let '(Mrs, memory) :=
    eval Uint63.size certif_bases certif_pred certif_updates I0 r (certif_bases.[I0]).[s] memory in
  if Mrs is Some Mrs then
    if (Mrs ?= 0)%bigQ is Eq then (Some false, memory)
    else
      (* (Some true, memory) *)
      let x := certif_vtx.[idx_base] in
      let sat_vect := (cmp_vect (BigQUtils.bigQ_mul_mx_col A x) b) in
      let '(_, sat_lex, memory) :=
        IFold.ifold
          (fun i '(j, acc, memory) =>
             if (I.[j] =? i)%uint63 then
               let '(acc, memory) :=
                 lazy_sat_pert certif_bases certif_pred certif_updates idx_base memory j acc
               in
               ((j+1)%uint63, acc, memory)
             else
               (j, acc.[i <- Gt], memory)) (length A) (0%uint63, sat_vect, memory)
      in
      let '(_, res) :=
        IFold.ifold
          (fun i '(j, res) =>
             if res then
               if (i =? I.[j])%uint63 then
                 if sat_lex.[i] is Eq then ((j+1)%uint63, res)
                 else (j, false)
               else
                 if sat_lex.[i] is Gt then (j, res)
                 else (j, false)
             else
               (j, false)) (length sat_lex) (0%uint63, true)
      in
      (Some res, memory)
  else
    (None, memory).

Definition build_initial_memory (certif_bases : array basis) certif_updates m N idx :=
  let mem := PArrayUtils.mk_fun (fun _ => PArrayUtils.mk_fun (fun _ => make m None) m (make m None)) N (make m (make m None)) in
  let I := certif_bases.[idx] in
  IFold.ifold (fun i mem =>
                 IFold.ifold (fun j mem =>
                                memory_update mem idx i I.[j] certif_updates.[idx].[I.[j]].[i])
                   (length I) mem) m mem.

Definition lazy_check_all_bases
  (A : matrix) (b : vector)
  (certif_bases : array basis)
  (certif_pred : array (int63 * (int63 * int63)))
  certif_updates
  (certif_vtx : array vector)
  (idx : int63) (order : array int63) (steps : int63) :=
  let memory := build_initial_memory certif_bases certif_updates (length A) (length certif_bases) idx in
  let res := IFold.ifold
              (fun i '(acc, memory) =>
                 match acc with
                 | None => (acc, memory)
                 | Some false => (acc, memory)
                 | _ =>
                     lazy_check_basis A b certif_bases certif_pred certif_updates certif_vtx order.[i] memory
                 end) steps (Some true, memory)
  in
  res.

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
