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


def main(K, d, B, jfreeze=0, verbose=True, sym=False, cube=None, solver="cadical153", neg=0):
    """sym: rompe la simetría de permutar los estados 1..d-1 (simultáneamente en todas las letras): exige
    M_0[0][1] ≥ M_0[0][2] ≥ … ≥ M_0[0][d-1]. Es válido porque P·M·Pᵀ (P permutación que fija el estado 0)
    conserva productos max-plus, el orden entrada por entrada y las entradas [0][0].
    cube: dict {letra: valor exacto de M_letra[0][0]} para dividir el problema en casos (cube and conquer).
    neg: ártico "bajo cero" (Koprowski–Waldmann): las entradas van de -neg a B (o -oo). Las entradas [0][0] siguen
    siendo >= 0 (y >= 1 para los bits), así que [▷w◁]_00 >= #bits igual; el orden entrada por entrada se conserva
    por productos max-plus con enteros cualesquiera, así que el certificado sigue siendo correcto. neg = 0 es el
    caso original. Internamente cada valor es (literales de y, off) con x = y - off."""
    k = None if K < 0 else K
    R = rules(k, jfreeze)
    syms = sorted({s for l, r in R for s in l + r})
    E = Enc()
    F = -E.TRUE
    # letras: g[a][i][j][t], t = 0..B
    G = {}
    for a in syms:
        G[a] = [[[E.pool.id((a, i, j, t)) for t in range(B + neg + 1)] for j in range(d)] for i in range(d)]
        for i in range(d):
            for j in range(d):
                for t in range(B + neg):
                    E.cl.append([-G[a][i][j][t + 1], G[a][i][j][t]])
        E.cl.append([G[a][0][0][neg]])
    E.cl.append([G["0"][0][0][neg + 1]])
    E.cl.append([G["1"][0][0][neg + 1]])
    if sym:
        # Orden lexicográfico de los estados 1..d-1 según su firma (M_a[0][i], M_a[i][0]) para todas las letras a:
        # firma(i) ≥_lex firma(i+1). Válido por el mismo argumento de permutación (toda solución tiene una
        # permutación de estados que ordena las firmas).
        def sig(i):
            return [G[a][0][i] for a in syms] + [G[a][i][0] for a in syms]
        for i in range(1, d - 1):
            x, y = sig(i), sig(i + 1)
            eq = E.TRUE  # "iguales hasta acá"
            for xc, yc in zip(x, y):
                for t in range(B + neg + 1):  # eq -> (xc >= yc)
                    E.cl.append([-eq, -yc[t], xc[t]])
                same = E.new()  # same <-> (xc == yc)
                for t in range(B + neg + 1):
                    E.cl += [[-same, -xc[t], yc[t]], [-same, xc[t], -yc[t]]]
                diffs = []
                for t in range(B + neg + 1):
                    dt = E.new()  # dt <-> (xc[t] xor yc[t])
                    E.cl += [[-dt, xc[t], yc[t]], [-dt, -xc[t], -yc[t]], [dt, -xc[t], yc[t]], [dt, xc[t], -yc[t]]]
                    diffs.append(dt)
                E.cl.append([same] + diffs)
                eq = E.AND(eq, same)
    assumptions = []
    if cube:
        for a, v in cube.items():  # M_a[0][0] = v exactamente
            assumptions.append(G[a][0][0][v + neg])
            if v < B:
                assumptions.append(-G[a][0][0][v + neg + 1])

    def lit(v, t):  # v: lista g[0..T]; (v >= t)
        if t < 0:
            return v[0]  # x >= negativo <=> finito (valores >= 0)
        return v[t] if t < len(v) else F

    def add(x, y):  # suma max-plus de dos valores (finito si ambos finitos); valores = (lits, off)
        (xl, xo), (yl, yo) = x, y
        T = len(xl) + len(yl) - 1
        out = []
        for t in range(T):
            terms = []
            for i in range(0, t + 1):
                a, b = lit(xl, i), lit(yl, t - i)
                if a != F and b != F:
                    terms.append(E.AND(a, b))
            out.append(E.OR(terms))
        return (out, xo + yo)

    def vmax(vals):
        O = max(o for _, o in vals)
        T = max(len(v) + O - o for v, o in vals)
        return ([E.OR([lit(v, t - (O - o)) if t - (O - o) >= 0 else v[0] for v, o in vals]) for t in range(T)], O)

    def mul(A, Bm):
        return [[vmax([add(A[i][kk], Bm[kk][j]) for kk in range(d)]) for j in range(d)] for i in range(d)]

    Gv = {a: [[(G[a][i][j], neg) for j in range(d)] for i in range(d)] for a in syms}
    cache = {}

    def prod(w):
        w = tuple(w)
        if w in cache:
            return cache[w]
        M = Gv[w[0]] if len(w) == 1 else mul(prod(w[:-1]), Gv[w[-1]])
        cache[w] = M
        return M

    for l, r in R:
        Lm, Rm = prod(l), prod(r)
        for i in range(d):
            for j in range(d):
                (lv, lo), (rv, ro) = Lm[i][j], Rm[i][j]
                for t in range(len(rv)):  # y_r >= t  =>  y_l >= t - ro + lo
                    E.cl.append([-rv[t], lit(lv, t - ro + lo)])
    t0 = time.time()
    with Solver(name=solver, bootstrap_with=E.cl) as S:
        ok = S.solve(assumptions=assumptions)
        model = set(x for x in S.get_model() if x > 0) if ok else None
    name = "Collatz" if k is None else f"C_{k}"
    if verbose:
        extra = (" sim" if sym else "") + (f" cubo={cube}" if cube else "") + (f" [{solver}]" if solver != "cadical153" else "") + (f" bajo-cero={neg}" if neg else "")
        print(f"{name} ártico SAT d={d} B={B} congelados<2^{jfreeze}{extra}: {'SAT' if ok else 'UNSAT'}  "
              f"({E.pool.top} vars, {len(E.cl)} cláusulas, {time.time() - t0:.1f}s)", flush=True)
    if ok:
        def val(a, i, j):
            g = [G[a][i][j][t] in model for t in range(B + neg + 1)]
            return "-oo" if not g[0] else str(sum(g) - 1 - neg)
        for a in syms:
            print(f"  [{a}]", [[val(a, i, j) for j in range(d)] for i in range(d)])
        M = {a: [[None if val(a, i, j) == "-oo" else int(val(a, i, j)) for j in range(d)] for i in range(d)] for a in syms}
        assert check(M, R, d), "el modelo NO pasa el chequeo independiente"
        if verbose:
            print("  chequeo independiente (aritmética max-plus explícita): OK", flush=True)
    return ok


def check(M, R, d):
    """Chequeo independiente de un certificado: [l] >= [r] entrada por entrada para cada regla (max-plus con
    enteros, None = -oo), M_a[0][0] >= 0 para toda letra y M_0[0][0], M_1[0][0] >= 1."""
    def mm(A, B):
        C = [[None] * d for _ in range(d)]
        for i in range(d):
            for j in range(d):
                for k in range(d):
                    if A[i][k] is not None and B[k][j] is not None:
                        v = A[i][k] + B[k][j]
                        C[i][j] = v if C[i][j] is None else max(C[i][j], v)
        return C

    def pw(w):
        P = M[w[0]]
        for a in w[1:]:
            P = mm(P, M[a])
        return P
    ge = lambda x, y: y is None or (x is not None and x >= y)
    for l, r in R:
        L, Rm = pw(l), pw(r)
        if not all(ge(L[i][j], Rm[i][j]) for i in range(d) for j in range(d)):
            return False
    if any(M[a][0][0] is None or M[a][0][0] < 0 for a in M):
        return False
    return M["0"][0][0] >= 1 and M["1"][0][0] >= 1


if __name__ == "__main__":
    K, d, B = (int(x) for x in sys.argv[1:4])
    j = int(sys.argv[4]) if len(sys.argv) > 4 else 0
    main(K, d, B, j)
