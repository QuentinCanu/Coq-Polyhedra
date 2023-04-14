Require Import String.
From mathcomp Require Import all_ssreflect.
From PolyhedraHirsch Require Import rank_1_update.
From __DATA__ Require Import morph morph_inv edge_inv graph_lex graph_vtx.

Time Eval vm_compute in ("img_graph"%string, OC.img_graph morph morph_inv edge_inv graph_lex graph_vtx).
