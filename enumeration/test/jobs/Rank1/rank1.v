From mathcomp Require Import all_ssreflect.
From PolyhedraHirsch Require Import rank_1_update.
From __DATA__ Require Import A b bases pred init heap idx steps.

Time Eval vm_compute in
  (R1.lazy_check_all_bases A b bases pred init heap idx steps).1.1.
