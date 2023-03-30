Require Import PArray Uint63.
From mathcomp Require Import all_ssreflect.
From PolyhedraHirsch Require Import rank_1_update.
From POLY20DIM21_DATA Require Import A b bases idx inv order pred x_I steps det.

Definition det := R1.get_num det.
(*Time Definition main := Eval vm_compute in R1.explore_from_initial
                                       A b bases pred idx x_I inv det order steps.*)
Time Eval vm_compute in R1.check_all_updates bases pred (R1.explore_from_initial
                                       A b bases pred idx x_I inv det order steps) order steps.
(*Time Compute R1.vertex_certif A b bases pred idx x_I inv det order steps.*)
