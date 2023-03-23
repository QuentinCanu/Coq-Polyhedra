From mathcomp Require Import all_ssreflect.
Require Import PArray Uint63.
From Bignums Require Import BigQ.
From PolyhedraHirsch Require Import rank_1_update extra_array extra_int.
From POLY20DIM21_DATA Require Import A b bases idx inv order pred x_I steps.
Require Import rank1.

(*Definition test := Eval vm_compute in R1.array_to_test main bases order steps.
(*Time Definition bench1 := Eval vm_compute in R1.bench_old A test.*)
Time Eval vm_compute in R1.check_basic_point A b test.
*)
