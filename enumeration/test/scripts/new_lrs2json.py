#! /usr/bin/env python3

import json, os
import fractions as fc
import argparse as argp
from prerequisite import core

import sympy as sym
from sympy.polys.domains  import QQ
from sympy.polys.matrices import DomainMatrix

# Common functions
# -------------------------------------------------------------------
def bigq(x):
    return str(x)

# Extract polyhedron information from lrs files
# -------------------------------------------------------------------
def get_polyhedron_from_lrs(name):
    input = core.resource(name,"lrs",f"{name}.ine")
    with open(input, 'r') as stream:
        mx = [x.strip() for x in stream]
        mx = [x.split() for x in mx[mx.index('begin')+2:mx.index('end')]]
        Po = [list(map(fc.Fraction, xs)) for xs in mx]

    Po = [([x for x in line[1:]], -line[0]) for line in Po]
    Po = [(list(map(bigq, p1)), bigq(p2)) for p1,p2 in Po]
    A,b = zip(*Po)
    return A, b

def get_bases_from_lrs(name):
    input = core.resource(name,"lrs",f"{name}.ext")
    with open(input, 'r') as stream:
        mx = [x.strip() for x in stream]
        mx = [x.split() for x in mx[mx.index('begin')+2:mx.index('end')]]
        mx = [x[x.index('facets')+1:x.index('det=')-1] for x in mx if x[0]!="1"]
        bases = [list(map((lambda x : int(x) - 1), x)) for x in mx]
    return sorted(bases)

# Compute the initial basing point from which we compute our vertex certification
# -------------------------------------------------------------------
def to_gmp_matrix(m):
    M = sym.Matrix(m)
    c = M.shape
    M0 = [[QQ(M[i,j].p, M[i,j].q) for j in range(c[1])] for i in range(c[0])]
    res = DomainMatrix(M0, c, QQ)
    return res

def list_of_gmp_matrix(PM):
    PM = PM.to_Matrix()
    (p,q)=PM.shape
    res = []
    for j in range(q):
        res.append([bigq(fc.Fraction(PM[k,j].p, PM[k,j].q)) for k in range(p)])
    return res

def get_initial_basing_point(A,b,base):
    A_I = [A[i] for i in base]
    b_I = [b[i] for i in base]
    gmp_A_I, gmp_b_I = to_gmp_matrix(A_I), to_gmp_matrix(b_I)
    x_I = gmp_A_I.lu_solve(gmp_b_I)
    inv = gmp_A_I.inv()
    return (list_of_gmp_matrix(x_I)[0], list_of_gmp_matrix(inv))

# Construct the graph of lex feasible bases + order of construction
# -------------------------------------------------------------------
def get_lex_graph(bases,m, n):
    bases_dic = {frozenset(base) : i for (i,base) in enumerate(bases)}
    graph = [set() for _ in range(len(bases))]
    order = []
    pred = [(0,0,0) for _ in range(len(bases))]
    visited = {i : False for i in bases_dic.keys()}
    visited[frozenset(bases[0])] = True
    queue = [0]
    pointer = 0
    while True:
        if pointer >= len(queue):
            break
        idx_base = queue[pointer]
        order.append(idx_base)
        reg = len(graph[idx_base])
        if reg < n:
            base = bases[idx_base]
            base_set = set(base)
            for s in range(len(bases[idx_base])):
                for r in range(m):
                    if r not in base_set:
                        nei_set = frozenset(base_set - {base[s]} | {r})
                        if nei_set in bases_dic:
                            idx_nei = bases_dic[nei_set]
                            graph[idx_base].add(idx_nei)
                            if not visited[nei_set]:
                                visited[nei_set] = True
                                queue.append(idx_nei)
                                pred[idx_nei] = (idx_base,r,s)
        pointer += 1
    return [sorted(elt) for elt in graph], order[1:], pred


# Main function, write a json file with one certificate per entry
# -------------------------------------------------------------------
def optparser():
    parser = argp.ArgumentParser(description='Extract json data from polyhedron data')
    parser.add_argument('name', help="the name of the polyhedron to be extracted")
    return parser

# -------------------------------------------------------------------
def main():
    args   = optparser().parse_args()
    name   = args.name

    # Compute everything
    A,b = get_polyhedron_from_lrs(name)
    bases = get_bases_from_lrs(name)
    idx = 0
    x_I, inv = (get_initial_basing_point(A,b,bases[idx]))
    m,n = len(A), len(A[0])
    graph_lex, order, pred = get_lex_graph(bases,m,n)
    # Store in a dictionnary

    tgtjson = {}
    tgtjson['A'] = A
    tgtjson['b'] = b
    tgtjson['bases'] = bases
    tgtjson['idx'] = idx
    tgtjson['x_I'] = x_I
    tgtjson['inv'] = inv
    tgtjson['order'] = order
    tgtjson['steps'] = len(order)
    tgtjson['pred'] = pred
    tgtdir = core.resource(name)
    
    with open(os.path.join(tgtdir, f"{name}.json"), "w") as stream:
        json.dump(tgtjson,stream, indent=2)

# -------------------------------------------------------------------
if __name__ == '__main__':
    main()