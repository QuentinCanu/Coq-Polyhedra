From mathcomp Require Import all_ssreflect.
From PolyhedraHirsch Require Import rank_1_update.
From POLY20DIM21_DATA Require Import A b bases vtx pred updates idx order steps.

Time Eval vm_compute in
  (R1.lazy_check_all_bases  A b bases pred updates vtx idx order steps).1.
