"""Certificado ártico (max,+) de LARGO ACOTADO para el SRS de C_k (ver carry_srs.py).
Interpretación homogénea: cada letra a -> matriz d×d con entradas en {-oo} ∪ [-B, B]; [w] = producto max-plus.
Condiciones: para cada regla l -> r, [l] >= [r] entrada por entrada (débil); M_a[0][0] >= 0 para toda letra y
M_0[0][0], M_1[0][0] >= 1. Entonces [▷w◁][0][0] >= #bits(w) y no crece en ninguna derivación: largo acotado.
Uso: python3 scripts/carry_srs_arctic.py K d B
"""
import sys, z3
from carry_srs import rules
K, d, B = (int(x) for x in sys.argv[1:4]); k = None if K < 0 else K
R = rules(k)
syms = sorted({s for l, r in R for s in l + r})
NEG = -10**6
fin = {a: [[z3.Bool(f"f{a}{i}{j}") for j in range(d)] for i in range(d)] for a in syms}
val = {a: [[z3.Int(f"x{a}{i}{j}") for j in range(d)] for i in range(d)] for a in syms}
s = z3.Solver(); s.set("timeout", 900000)
for a in syms:
    for i in range(d):
        for j in range(d):
            s.add(z3.Implies(fin[a][i][j], z3.And(val[a][i][j] >= -B, val[a][i][j] <= B)))
    s.add(fin[a][0][0], val[a][0][0] >= 0)
s.add(val["0"][0][0] >= 1, val["1"][0][0] >= 1)
def mat(a): return [[(fin[a][i][j], val[a][i][j]) for j in range(d)] for i in range(d)]
def mul(A, Bm):
    C = []
    for i in range(d):
        row = []
        for j in range(d):
            terms = [(z3.And(A[i][t][0], Bm[t][j][0]), A[i][t][1] + Bm[t][j][1]) for t in range(d)]
            f = z3.Or([c for c, _ in terms])
            v = z3.IntVal(NEG)
            for c, e in terms:
                v = z3.If(z3.And(c, e > v), e, v)
            row.append((f, v))
        C.append(row)
    return C
def prod(w):
    M = mat(w[0])
    for a in w[1:]: M = mul(M, mat(a))
    return M
for l, r in R:
    L, Rm = prod(l), prod(r)
    for i in range(d):
        for j in range(d):
            # r finito => l finito y l >= r
            s.add(z3.Implies(Rm[i][j][0], z3.And(L[i][j][0], L[i][j][1] >= Rm[i][j][1])))
res = s.check()
name = "Collatz" if k is None else f"C_{k}"
print(f"{name} ártico d={d} B={B}: {res}", flush=True)
if res == z3.sat:
    m = s.model()
    for a in syms:
        print(f"  [{a}]", [[(m.eval(val[a][i][j]) if z3.is_true(m.eval(fin[a][i][j])) else '-oo') for j in range(d)] for i in range(d)])
