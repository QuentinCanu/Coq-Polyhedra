Require Import String.
From mathcomp Require Import all_ssreflect.
From PolyhedraHirsch Require Import rank_1_update.
From __DATA__ Require Import A graph_lex bases.

Time Eval vm_compute in ("adjacency"%string, OC.adjacency A graph_lex bases).
