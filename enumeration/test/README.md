# Process to generate rank 1 update example

Assuming you are in test/, you are supposed to find polytopes lrs files in data/{polytope}. Then, run the following commands

```console
scripts/new_lrs2json.py polytope
scripts/new_json2bin.py polytope
scripts/bin2coq.py polytope
scripts/coqjobs.py polytope Rank1 vm_compute
dune build --verbose data/polytope/coq_Rank1
```

