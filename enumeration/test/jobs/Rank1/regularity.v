Require Import String.
From mathcomp Require Import all_ssreflect.
From PolyhedraHirsch Require Import rank_1_update.
From __DATA__ Require Import A graph_lex.

Time Eval vm_compute in ("regularity"%string,OC.regularity A graph_lex).
