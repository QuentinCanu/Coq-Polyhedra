From mathcomp Require Import all_ssreflect.
Require Import PArray Uint63.
From PolyhedraHirsch Require Import rank_1_update extra_array.
From POLY20DIM21_DATA Require Import A b bases idx inv order pred x_I steps.

Eval vm_compute in PArrayUtils.mk_fun (fun i => order.[i]) steps (default order).
Time Definition main := Eval vm_compute in R1.explore_from_initial A b bases pred idx x_I inv order steps.
Definition test := Eval vm_compute in R1.array_to_test main bases order steps.
(*Time Definition bench1 := Eval vm_compute in R1.bench_old A test.*)
Time Eval vm_compute in R1.bench_old2 A b test.
