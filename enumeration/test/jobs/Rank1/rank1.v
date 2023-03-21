From mathcomp Require Import all_ssreflect.
From PolyhedraHirsch Require Import rank_1_update.
From __DATA__ Require Import A b bases idx inv order pred x_I.

Time Definition main := Eval vm_compute in R1.explore_from_initial A b bases pred idx x_I inv order.
Time Definition test := Eval vm_compute in R1.bench_old A main.