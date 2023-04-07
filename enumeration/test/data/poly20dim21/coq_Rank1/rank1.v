Require Import Uint63 PArray.
From mathcomp Require Import all_ssreflect.
From PolyhedraHirsch Require Import extra_int rank_1_update.
From POLY20DIM21_DATA Require Import A b bases idx order pred updates vtx steps.

(* Time Eval vm_compute in *)
(*   (R1.lazy_check_all_bases  A b bases pred updates *)
(*      vtx idx order steps).1. *)

Definition count {T : Type} (f : T -> int) (l : array T) :=
  IFold.ifold (fun i res => (res + f l.[i])%uint63) (length l) (0%uint63).

Time Eval vm_compute in
(*  count (count (count (fun x => if x is Some _ then 1%uint63 else 0%uint63)))*)
    (R1.lazy_check_all_bases  A b bases pred updates
       vtx idx order steps).1.


(*Time (*Definition main :=*) Eval vm_compute in R1.explore_from_initial
                                            A b bases pred idx x_I inv det order steps.
*)
(*Time Definition res := Eval vm_compute in R1.num_profile (R1.explore_from_initial
  A b bases pred idx x_I inv det order steps) order steps.*)
