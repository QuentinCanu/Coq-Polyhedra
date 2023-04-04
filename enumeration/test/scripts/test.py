#! /usr/bin/env python3

import json, os, math

with open(os.path.join(os.getcwd(), "data", "poly20dim21", f'poly20dim21.json')) as stream:
  contents = json.load(stream)

pred = contents["pred"]
pred_vect = contents["pred_vect"]
bases = contents["bases"]

lengths = [math.inf for _ in pred]
lengths[0] = 0
for i in range(1,len(pred)):
    idx = i
    count = 0
    while idx != 0:
        idx = pred[idx][0]
        count += 1
    lengths[i] = count
print("max length = ", max(lengths))

mean = 0
count = 0
maxn = -math.inf
for idx,mat in enumerate(pred_vect):
  base = bases[idx]
  for col in mat:
    for i in range(len(col)):
        if i not in base:
          l = len(col[i])
          mean += l
          count += 1
          if l > maxn:
            maxn = l
print("mean = ", mean/count, "; max = ", maxn)