"""Certificado ártico de LARGO ACOTADO para el SRS de C_k (ver carry_srs.py), codificado a SAT (CaDiCaL).

Cada letra a -> matriz d×d sobre ℕ ∪ {-oo} con entradas <= B. Codificación de orden: x se representa por
literales g[t] <=> (x >= t), t = 0..B (g[0] = "finito"). Productos max-plus por Tseitin con equivalencias.
Condiciones (como en carry_srs_arctic.py): [l] >= [r] entrada por entrada para cada regla; M_a[0][0] >= 0 para
toda letra; M_0[0][0] >= 1 y M_1[0][0] >= 1. Implica [▷w◁]_00 >= #bits(w), y que no crece en ninguna derivación.
Uso: python3 scripts/carry_srs_sat.py K d B      (K = -1: Collatz exacto)
"""
import sys
import time
from pysat.formula import IDPool
from pysat.solvers import Solver
from carry_srs import rules


class Enc:
    def __init__(self):
        self.pool = IDPool()
        self.cl = []
        self.TRUE = self.new()
        self.cl.append([self.TRUE])

    def new(self):
        return self.pool.id(("aux", len(self.pool.obj2id)))

    def AND(self, a, b):
        if a == -self.TRUE or b == -self.TRUE:
            return -self.TRUE
        if a == self.TRUE:
            return b
        if b == self.TRUE:
            return a
        v = self.new()
        self.cl += [[-v, a], [-v, b], [v, -a, -b]]
        return v

    def OR(self, lits):
        lits = [x for x in lits if x != -self.TRUE]
        if not lits:
            return -self.TRUE
        if self.TRUE in lits:
            return self.TRUE
        if len(lits) == 1:
            return lits[0]
        v = self.new()
        self.cl.append([-v] + lits)
        for x in lits:
            self.cl.append([v, -x])
        return v


def main(K, d, B, jfreeze=0, verbose=True):
    k = None if K < 0 else K
    R = rules(k, jfreeze)
    syms = sorted({s for l, r in R for s in l + r})
    E = Enc()
    F = -E.TRUE
    # letras: g[a][i][j][t], t = 0..B
    G = {}
    for a in syms:
        G[a] = [[[E.pool.id((a, i, j, t)) for t in range(B + 1)] for j in range(d)] for i in range(d)]
        for i in range(d):
            for j in range(d):
                for t in range(B):
                    E.cl.append([-G[a][i][j][t + 1], G[a][i][j][t]])
        E.cl.append([G[a][0][0][0]])
    E.cl.append([G["0"][0][0][1]])
    E.cl.append([G["1"][0][0][1]])

    def lit(v, t):  # v: lista g[0..T]; (v >= t)
        if t < 0:
            return v[0]  # x >= negativo <=> finito (valores >= 0)
        return v[t] if t < len(v) else F

    def add(x, y):  # suma max-plus de dos valores (finito si ambos finitos)
        T = len(x) + len(y) - 1
        out = []
        for t in range(T):
            terms = []
            for i in range(0, t + 1):
                a, b = lit(x, i), lit(y, t - i)
                if a != F and b != F:
                    terms.append(E.AND(a, b))
            out.append(E.OR(terms))
        return out

    def vmax(vals):
        T = max(len(v) for v in vals)
        return [E.OR([lit(v, t) for v in vals]) for t in range(T)]

    def mul(A, Bm):
        return [[vmax([add(A[i][kk], Bm[kk][j]) for kk in range(d)]) for j in range(d)] for i in range(d)]

    cache = {}

    def prod(w):
        w = tuple(w)
        if w in cache:
            return cache[w]
        M = G[w[0]] if len(w) == 1 else mul(prod(w[:-1]), G[w[-1]])
        cache[w] = M
        return M

    for l, r in R:
        Lm, Rm = prod(l), prod(r)
        for i in range(d):
            for j in range(d):
                lv, rv = Lm[i][j], Rm[i][j]
                for t in range(len(rv)):
                    E.cl.append([-rv[t], lit(lv, t)])
    t0 = time.time()
    with Solver(name="cadical153", bootstrap_with=E.cl) as S:
        ok = S.solve()
        model = set(x for x in S.get_model() if x > 0) if ok else None
    name = "Collatz" if k is None else f"C_{k}"
    if verbose:
        print(f"{name} ártico SAT d={d} B={B} congelados<2^{jfreeze}: {'SAT' if ok else 'UNSAT'}  "
              f"({E.pool.top} vars, {len(E.cl)} cláusulas, {time.time() - t0:.1f}s)", flush=True)
    if ok:
        def val(a, i, j):
            g = [G[a][i][j][t] in model for t in range(B + 1)]
            return "-oo" if not g[0] else str(sum(g) - 1)
        for a in syms:
            print(f"  [{a}]", [[val(a, i, j) for j in range(d)] for i in range(d)])
    return ok


if __name__ == "__main__":
    K, d, B = (int(x) for x in sys.argv[1:4])
    j = int(sys.argv[4]) if len(sys.argv) > 4 else 0
    main(K, d, B, j)
