From mathcomp Require Import all_ssreflect.
Require Import PArray Uint63.
From Bignums Require Import BigQ.
From PolyhedraHirsch Require Import rank_1_update extra_array extra_int.
From POLY20DIM21_DATA Require Import A b bases idx inv order pred x_I steps.

Time Definition main := Eval vm_compute in R1.explore_from_initial A b bases pred idx x_I inv order steps.
Eval vm_compute in IFold.ifold (fun i acc => acc && (isSome main.[order.[i]])) steps true.
