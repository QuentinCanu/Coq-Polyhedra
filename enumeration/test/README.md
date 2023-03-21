# Process to generate rank 1 update example

Assuming you are in test/, you are supposed to find polytopes lrs files in data/{polytope}. Then, run the following commands

```console
scripts/new_lrs2json.py polytope
scripts/new_json2bin.py polytope
scripts/bin2coq.py polytope
scripts/coqjobs.py polytope Rank1 vm_compute
dune clean
dune build --verbose data/polytope/coq_Rank1
```

In case you want to only work on a subset of the bases (the k first), you have to modify the file `data/polytope/coq/steps.v` into

```coq
Require Import Uint63.

Defintion steps := k%uint63.
```

