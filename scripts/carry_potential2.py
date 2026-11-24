"""Potencial con términos de borde para C_k (y Collatz exacto):

V(n) = L(n) + sum_i f(ventanas de w bits) + g(n mod 2^b) + h(b bits de arriba de n)
f >= 0, f(0..0) = 0; g, h libres (tablas finitas, así que V >= L - cte).
Se pide V(C(n)) <= V(n) para n impar con L(n) >= L0, y V(n/2) <= V(n) para n par.
Si es factible: toda órbita tiene largo acotado (no hay divergencia).
Uso: python3 scripts/carry_potential2.py K W B L0    (K = -1: Collatz exacto)
"""
import sys
import numpy as np
from scipy.optimize import linprog
from scipy.sparse import coo_matrix
from carry_potential import carry_step

def build(k, w, b, L0):
    assert b <= w - 2 and L0 >= b + 2
    mask = (1 << (w - 1)) - 1
    init_cs = (1, 1) if k != 0 else (0, 0)
    start, sink = ("start",), ("sink",)
    nf = 1 << w; G0 = nf; H0 = nf + (1 << b)   # offsets de variables g, h
    edges = []
    def push(h, x):
        win = h | (x << (w - 1)); return win, (win >> 1) & mask
    first = (0, 0, init_cs, 0, 0)
    seen = {first}; stack = [first]; edges.append((start, first, {}, 0.0))
    while stack:
        st = stack.pop(); hn, ho, cs, cnt, last = st
        prev = (hn >> (w - 2)) & 1
        for x in (0, 1):
            if cnt == 0 and x == 0: continue
            o, ncs = carry_step(x, prev, cs, k)
            nwin, nhn = push(hn, x); owin, nho = push(ho, o)
            coef = {}
            coef[nwin] = coef.get(nwin, 0) - 1; coef[owin] = coef.get(owin, 0) + 1
            if cnt == b:  # recién leídos n_0..n_b y out_0..out_b: término de abajo
                nb = (nhn >> (w - 1 - b)) & ((1 << b) - 1)        # n_0..n_{b-1}
                ob = ((nho >> (w - 1 - (b + 1))) >> 1) & ((1 << b) - 1)  # out_1..out_b = C(n) mod 2^b
                coef[G0 + nb] = coef.get(G0 + nb, 0) - 1; coef[G0 + ob] = coef.get(G0 + ob, 0) + 1
            nst = (nhn, nho, ncs, min(cnt + 1, L0), x)
            edges.append((st, nst, coef, 0.0))
            if nst not in seen: seen.add(nst); stack.append(nst)
        if last == 1 and cnt >= L0:
            coef = {}; const = 0.0
            topn = [(hn >> (w - 2 - i)) & 1 for i in range(b)]          # n_{L-1}, n_{L-2}, ...
            outs = [(ho >> i) & 1 for i in range(w - 1)]                 # out_{L-w+1..L-1} (i=0 más viejo)
            h_n, h_o, c_s, pb = hn, ho, cs, 1
            flush = []
            for j in range(w + 3):
                o, c_s = carry_step(0, pb, c_s, k); flush.append(o)
                if j == 1 and o == 1: const += 1.0
                nwin, h_n = push(h_n, 0); owin, h_o = push(h_o, o)
                coef[nwin] = coef.get(nwin, 0) - 1; coef[owin] = coef.get(owin, 0) + 1
                pb = 0
            assert c_s[0] == 0
            full = outs + flush[:2]            # out_{L-w+1} .. out_{L+1}
            while full and full[-1] == 0: full.pop()
            topc = list(reversed(full))[:b]    # bits de arriba de out (= de C(n))
            tn = int("".join(map(str, topn)), 2); tc = int("".join(map(str, topc)), 2)
            coef[H0 + tn] = coef.get(H0 + tn, 0) - 1; coef[H0 + tc] = coef.get(H0 + tc, 0) + 1
            edges.append((st, sink, coef, const))
    return [start, sink] + sorted(seen, key=repr), edges, nf, G0, H0

def solve(k, w, b, L0, slack=False):
    states, edges, nf, G0, H0 = build(k, w, b, L0)
    idx = {s: i for i, s in enumerate(states)}
    P0 = H0 + (1 << b); nS = len(states); T = P0 + nS; nv = T + 1
    R, C, Vv, rhs = [], [], [], []; r = 0
    def row(items, bound):
        nonlocal r
        for c_, v_ in items: R.append(r); C.append(c_); Vv.append(v_)
        rhs.append(bound); r += 1
    for (u, v, coef, const) in edges:
        row([(c_, v_) for c_, v_ in coef.items() if v_] + [(P0 + idx[u], 1.0), (P0 + idx[v], -1.0)], -const)
    row([(P0 + idx[("sink",)], 1.0), (T, -1.0)], 0.0)
    # pasos pares: g((x>>1) | beta<<(b-1)) - g(x) <= 1, x par
    for x in range(0, 1 << b, 2):
        for beta in (0, 1):
            y = (x >> 1) | (beta << (b - 1))
            if y != x: row([(G0 + y, 1.0), (G0 + x, -1.0)], 1.0)
    A = coo_matrix((Vv, (R, C)), shape=(r, nv)).tocsr()
    bnd = [(0, None)] * nf + [(None, None)] * ((1 << b) * 2) + [(None, None)] * nS + [(0, None) if slack else (0, 0)]
    bnd[0] = (0, 0); bnd[P0 + idx[("start",)]] = (0, 0)
    c = np.zeros(nv); c[T] = 1.0; c[:nf] = 1e-6
    return linprog(c, A_ub=A, b_ub=np.array(rhs), bounds=bnd, method="highs"), nS, len(edges)

if __name__ == "__main__":
    K, W, B, L0 = map(int, sys.argv[1:5])
    res, nS, nE = solve(None if K < 0 else K, W, B, L0, slack=True)
    name = "Collatz" if K < 0 else f"C_{K}"
    print(f"{name} w={W} b={B} L0={L0} estados={nS}: status={res.status}  subida mínima t* = {res.x[-1] if res.status == 0 else None}")
