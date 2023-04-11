#! /usr/bin/env python3

import json, os
import fractions as fc
import argparse as argp
import math, fractions, random as rd
import networkx as nx
from prerequisite import farkas as fk
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
        mx = [(x[x.index('facets')+1:x.index('det=')-1], x[x.index('det=')+1]) if x[0]!="1" else x[1:] for x in mx]
        couples = [(mx[i], mx[i+1]) for i in range(0,len(mx),2)]
        couples = [(((list(map((lambda x : int(x) - 1), b))), d) ,v) for (b,d),v in couples]
        bas2vtx = {frozenset(b) : v for ((b,_),v) in couples}
        bas2det = {frozenset(b) : d for ((b,d),_) in couples}
    return sorted([b for (b,_),_ in couples]), bas2vtx, bas2det

#rewrite A and b to be integer matrices
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

def poly_scale(A,b):
    gmp_A, gmp_b = to_gmp_matrix(A), to_gmp_matrix(b)
    ca, cb = gmp_A.shape, gmp_b.shape
    scale = [None for _ in range(ca[0])]
    for i in range(ca[0]):
        mult, div = gmp_b[i,0].element.denominator, gmp_b[i,0].element.numerator
        for j in range(ca[1]):
            mult = QQ.lcm(mult, gmp_A[i,j].element.denominator)
            div = QQ.gcd(div, gmp_A[i,j].element.numerator)
        scale[i] = (mult/div)
    A, b = gmp_A.to_Matrix(), gmp_b.to_Matrix()
    res_A, res_b = [], []
    for i in range(ca[0]):
        aux_A = []
        for j in range(ca[1]):
            aux_A.append(bigq(fc.Fraction(scale[i] * A[i,j])))
        res_A.append(aux_A)
        res_b.append(bigq(fc.Fraction(scale[i] *  b[i,0])))
    return res_A, res_b

# Compute the initial basing point from which we compute our vertex certification
# -------------------------------------------------------------------

# def get_idx(bases, bas2det):
#     min = math.inf
#     idx = 0
#     for i in range(len(bases)):
#         bas = bases[i]
#         det = fc.Fraction(bas2det[frozenset(bas)])
#         if det < min:
#             min = det
#             idx = i
#     return idx

# Construct the graph of lex feasible bases
# -------------------------------------------------------------------

def get_lex_graph(m,n,bases):
    graph = [set() for _ in bases]
    bases_dic = {frozenset(elt) : i for i,elt in enumerate(bases)}
    reg = [0 for _ in bases]
    for kI,I in enumerate(bases):
        I_set = set(I)
        s = 0
        while reg[kI] < n:
            Is = I[s]
            for r in range(m):
                if r not in I_set:
                    J = I_set - {Is} | {r}
                    if frozenset(J) in bases_dic:
                        kJ = bases_dic[frozenset(J)]
                        if kJ not in graph[kI]:
                            graph[kI].add(kJ)
                            graph[kJ].add(kI)
                            reg[kI]+=1
                            reg[kJ]+=1
                            break
            s += 1
    return [sorted(elt) for elt in graph]
        
# Visit the graph in order to construct the values required by the algorithm in the correct order
# -------------------------------------------------------------------

def get_entering_leaving(I,J):
    I_set, J_set = set(I), set(J)
    IJ = I_set & J_set
    s,r = (I_set - IJ).pop(), (J_set - IJ).pop()
    return (r, I.index(s))

def get_initial_basing_point(A,b,bases,idx):
    base = bases[idx]
    A_I = [A[i] for i in base]
    gmp_A_I = to_gmp_matrix(A_I)
    inv = gmp_A_I.inv()
    gmp_A = to_gmp_matrix(A)
    M = - gmp_A * inv
    b_I = [b[i] for i in base]
    init = [[None for _ in range(len(A))] for _ in range(len(A)+1)]
    init[0] = [(((gmp_A * inv * to_gmp_matrix(b_I)) - to_gmp_matrix(b))[i,0]).element for i in range(len(A))]
    for j in range(len(base)):
        init[base[j]+1] = [M[i,j].element for i in range(len(A))]
    return init

def get_pred(bases,graph_lex,idx):
    G = nx.Graph({i:edges for i,edges in enumerate(graph_lex)})
    pred = [None for _ in graph_lex]
    pred[idx] = (idx,0,0)
    order = []
    for u,v in nx.bfs_edges(G,idx):
        order.append(v)
        I,J = bases[u], bases[v]
        r,s = get_entering_leaving(I,J)
        pred[v] = (u,r,s)
    return pred, order


def get_heap(A,b,bases,idx,order,pred):
    m = len(A)
    memory=[[[None for _ in range(m)] for _ in range(m+1)] for _ in bases]
    memory[idx]=get_initial_basing_point(A,b,bases,idx)
    heap = []
    def eval(kJ,p,q):
        if (val := memory[kJ][q][p]) is not None:
            return val
        kI,r,s = pred[kJ]
        I = bases[kI]
        Mrs = eval(kI,r,I[s]+1)
        new_val = None
        if q == 1+r:
            Msp = eval(kI,p,I[s]+1)
            new_val = - Msp/Mrs
        else:
            Mpq = eval(kI,p,q)
            Mrq = eval(kI,r,q)
            Mps = eval(kI,p,I[s]+1)
            new_val = (Mrs * Mpq - Mrq * Mps) / Mrs
        memory[kJ][q][p] = new_val
        heap.append(new_val)
        return new_val

    for kJ in order:
        J = set(bases[kJ])
        (kI,r,s) = pred[kJ]
        I = bases[kI]
        Mrs = eval(kI,r,I[s]+1)
        sat_vect = [None for _ in A]
        for p in range(len(A)):
            val = eval(kJ,p,0)
            sat_vect[p] = 1 if val > 0 else 0
        for q in range(len(A)):
            if q not in J:
                sat_vect[q] = 1
            else:
                for p in range(len(sat_vect)):
                    if sat_vect[p] == 0:
                        val = eval(kJ,p,1+q)
                        sat_vect[p] = 1 if val > 0 else 0
    return heap
        



        




 

# def format_updates(updates):
#     res = []
#     for M in updates:
#         Mf = [['0'] if col is None else list_of_gmp_matrix(col)[0] for col in M]
#         res.append(Mf)
#     return res

# def get_lex_graph(A,b,bases,idx):
#     updates = get_initial_basing_point(A,b,bases,idx)
#     m, n = len(A), len(A[0])
#     bases_dic = {frozenset(base) : i for (i,base) in enumerate(bases)}
#     graph = [set() for _ in bases]
#     order = []
#     pred = [(0,0,0) for _ in bases]
#     visited = {i : False for i in bases_dic.keys()}
#     visited[frozenset(bases[idx])] = True
#     queue = [idx]
#     pointer = 0
#     gmp_b = to_gmp_matrix(b)
#     while True:
#         if pointer >= len(queue):
#             break
#         idx_base = queue[pointer]
#         order.append(idx_base)
#         reg = len(graph[idx_base])
#         if reg < n:
#             base = bases[idx_base]
#             M = updates[idx_base]
#             base_set = set(base)
#             for s in range(len(bases[idx_base])):
#                 for r in range(m):
#                     if r not in base_set:
#                         nei_set = frozenset(base_set - {base[s]} | {r})
#                         if nei_set in bases_dic:
#                             idx_nei = bases_dic[nei_set]
#                             graph[idx_base].add(idx_nei)
#                             if not visited[nei_set]:
#                                 visited[nei_set] = True
#                                 queue.append(idx_nei)
#                                 pred[idx_nei] = (idx_base,r,s)
#                                 updates[idx_nei] = update(gmp_b,M,base,r,s)
#         pointer += 1
#     return [sorted(elt) for elt in graph], order[1:], pred, format_updates(updates)

# Construct the graph of vertices + certificates related to the image graph
# -------------------------------------------------------------------
def get_unsrt_vtx(bases,bas2vtx):
    vtx_list = [None for _ in bases]
    for i in range(len(bases)):
        bas = bases[i]
        vtx = bas2vtx[frozenset(bas)]
        vtx_list[i] = vtx
    return vtx_list

def get_vtx(bas2vtx):
    vtx_list = [i for i in bas2vtx.values()]
    vtx_list = sorted(set([tuple(map((lambda x : fractions.Fraction(x)), l)) for l in vtx_list]))
    return [list(map(str,elt)) for elt in vtx_list]

def get_morph(bases, vtx, bas2vtx):
    morph, morph_inv = [None for _ in bases], [None for _ in vtx]
    aux = {tuple(vtx[i]) : i for i in range(len(vtx))}
    for i in range(len(bases)):
        bas = bases[i]
        v = bas2vtx[frozenset(bas)]
        j = aux[tuple(v)]
        morph[i] = j
        morph_inv[j] = i
    return morph, morph_inv

def get_graph_vtx(graph_lex, morf, length_vtx):
    graph = [[] for i in range(length_vtx)]
    for i in range(len(graph_lex)):
        tgt_i = morf[i]
        for j in graph_lex[i]:
            tgt_j = morf[j]
            if tgt_i != tgt_j and tgt_j not in graph[tgt_i]:
                graph[tgt_i].append(tgt_j)
    return [sorted(x) for x in graph]

def get_edge_inv(G_lex, G_simpl, morf):
    edge_inv = [[None for j in range(len(G_simpl[i]))] for i in range(len(G_simpl))]
    for i in range(len(G_lex)):
        for j in range(len(G_lex[i])):
            nei = G_lex[i][j]
            if morf[i] != morf[nei]:
                j_ = next(i for i,v in enumerate(G_simpl[morf[i]]) if v == morf[nei])
                edge_inv[morf[i]][j_] = (i,nei)
    return edge_inv

# Get final certificates (Farkas, dim_full)
# -------------------------------------------------------------------
def get_farkas_cert(A, m, n):
    A = to_gmp_matrix(A).transpose()
    cert_pos, cert_neg = [], []
    for k in range(n):
        cert_pos.append(list(map(bigq,fk.farkas_gen(A, n, m, k))))
        cert_neg.append(list(map(bigq,fk.farkas_gen(-A, n, m, k))))
    return cert_pos, cert_neg

def get_dim_full(vtx, n):
    while True:
        map_lbl = rd.sample(range(len(vtx)), n+1)
        map_lbl.sort()
        M = sym.Matrix([list(map(fc.Fraction, vtx[i])) for i in list(map_lbl)[1:]])
        N = sym.Matrix([list(map(fc.Fraction, vtx[map_lbl[0]])) for _ in range(n)])
        Q = M - N
        Q_gmp = to_gmp_matrix(Q)
        Q_det = Q_gmp.det()
        if Q_det != 0:
            Q_inv = Q.gmp_inv()
            Q_res = list_of_gmp_matrix(Q_inv)
            return list(map_lbl)[0], list(map_lbl)[:1], Q_res


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
    A,b = poly_scale(A,b)
    bases, bas2vtx, bas2det = get_bases_from_lrs(name)
    idx = 0
    graph_lex = get_lex_graph(len(A), len(A[0]), bases)
    pred, order = get_pred(bases, graph_lex, idx)
    heap = get_heap(A,b,bases,idx,order,pred)
    # steps = len(order)
    # vtx = get_unsrt_vtx(bases, bas2vtx)
    # morph, morph_inv = get_morph(bases,vtx,bas2vtx)
    # graph_vtx = get_graph_vtx(graph_lex,morph,len(vtx))
    # edge_inv = get_edge_inv(graph_lex,graph_vtx,morph)
    # farkas_cert_pos, farkas_cert_neg = get_farkas_cert(A,m,n)


    # Store in a dictionnary

    # tgtjson = {}
    # tgtjson['A'] = A
    # tgtjson['b'] = b
    # tgtjson['bases'] = bases
    # tgtjson['vtx'] = vtx
    # tgtjson['pred'] = pred
    # tgtjson['updates'] = updates
    # tgtjson['idx'] = idx
    # tgtjson['order'] = order
    # tgtjson['steps'] = steps
    # tgtdir = core.resource(name)

    # with open(os.path.join(tgtdir, f"{name}.json"), "w") as stream:
    #     json.dump(tgtjson,stream, indent=2)

# -------------------------------------------------------------------
if __name__ == '__main__':
    main()
