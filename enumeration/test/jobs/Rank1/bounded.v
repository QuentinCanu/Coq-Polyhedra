Require Import String.
From mathcomp Require Import all_ssreflect.
From PolyhedraHirsch Require Import rank_1_update.
From __DATA__ Require Import A b bound_pos bound_neg.

Time Eval vm_compute in ("bounded"%string, OC.bounded A b bound_pos bound_neg).
