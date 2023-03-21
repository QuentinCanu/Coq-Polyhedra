From mathcomp Require Import all_ssreflect.
From PolyhedraHirsch Require Import rank_1_update.
From __DATA__ Require Import A b bases idx inv order pred x_I steps.

Time Definition main := Eval vm_compute in R1.explore_from_initial A b bases pred idx x_I inv order steps.
Time Definition test := Eval vm_compute in R1.array_to_test main bases.
Time Definition bench1 := Eval vm_compute in R1.bench_old A test.
Time Definition bench2 := Eval vm_compute in R1.bench_old2 A b test.