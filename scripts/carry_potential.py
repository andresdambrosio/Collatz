"""Busca una función potencial local para C_k (Collatz con acarreos de vida <= k) por programación lineal.

V(n) = L(n) + sum_i f(n_i .. n_{i+w-1})   (suma sobre todas las ventanas de w bits, con ceros alrededor;
                                            f(0...0) = 0, f >= 0, así que V(n) >= L(n))
Paso par: V(n/2) = V(n) - 1 (la suma es invariante por traslación).
Paso impar: se pide V(C_k(n)) <= V(n) para todo n impar con L(n) >= L0.
Si existe tal f, toda órbita tiene largo acotado: C_k no tiene órbitas divergentes.

La condición "para todo n" es "el camino más largo de un autómata ponderado es <= 0", y eso se escribe
con potenciales de nodos (pi(v) >= pi(u) + peso(e)): un LP en (f, pi).
El autómata lee n desde el bit menos significativo y lleva: los últimos w-1 bits de n, los últimos w-1 bits
de out = n + 2n + 1 (acarreos truncados), el estado del acarreo y un contador hasta L0.

Uso: python3 scripts/carry_potential.py K W L0     (K = -1 para Collatz exacto, sin truncar)
"""
import sys
import numpy as np
from scipy.optimize import linprog
from scipy.sparse import coo_matrix


def carry_step(x, y, cs, k):
    """cs = (carry, edad). Devuelve (bit de salida, nuevo cs)."""
    c, age = cs
    s = x + y + c
    o = s & 1
    if x + y == 2:
        nc = (1, 1)
    elif s >= 2:
        nc = (1, age + 1)
    else:
        nc = (0, 0)
    if k is None:
        nc = (nc[0], min(nc[1], 1))
    elif k == 0 or (nc[0] and nc[1] > k):
        nc = (0, 0)
    return o, nc


def build(k, w, L0):
    """Aristas (u, v, coef_f: dict ventana->coef, constante). Estados: tuplas hashables."""
    mask = (1 << (w - 1)) - 1
    init_cs = (1, 1) if k != 0 else (0, 0)  # el +1 inicial; con k = 0 se descarta
    start = ("start",)
    sink = ("sink",)
    edges = []
    # estado: (hn, ho, cs, cnt, last)   hn/ho: últimos w-1 bits como entero (bit más nuevo = bit alto)
    def push(h, b):  # ventana completa = (h con w-1 bits viejos) + b nuevo
        win = (h >> 0) | (b << (w - 1))
        return win, (win >> 1) & mask
    first = (0, 0, init_cs, 0, 0)
    stack = [first]
    seen = {first}
    edges.append((start, first, {}, 0.0))
    while stack:
        st = stack.pop()
        hn, ho, cs, cnt, last = st
        prev = (hn >> (w - 2)) & 1 if w >= 2 else 0
        for b in (0, 1):
            if cnt == 0 and b == 0:
                continue  # n impar
            o, ncs = carry_step(b, prev, cs, k)
            nwin, nhn = push(hn, b)
            owin, nho = push(ho, o)
            coef = {}
            coef[nwin] = coef.get(nwin, 0) - 1
            coef[owin] = coef.get(owin, 0) + 1
            nst = (nhn, nho, ncs, min(cnt + 1, L0), b)
            edges.append((st, nst, coef, 0.0))
            if nst not in seen:
                seen.add(nst)
                stack.append(nst)
        # fin del número: último bit leído = 1 y L >= L0 -> vaciar con ceros
        if last == 1 and cnt >= L0:
            coef = {}
            const = 0.0
            h_n, h_o, c_s = hn, ho, cs
            prev_b = 1
            for j in range(w + 3):
                o, c_s = carry_step(0, prev_b, c_s, k)
                if j == 1 and o == 1:
                    const += 1.0  # out tiene largo L+2: C(n) ganó un bit
                nwin, h_n = push(h_n, 0)
                owin, h_o = push(h_o, o)
                coef[nwin] = coef.get(nwin, 0) - 1
                coef[owin] = coef.get(owin, 0) + 1
                prev_b = 0
            assert c_s[0] == 0
            edges.append((st, sink, coef, const))
    states = [start, sink] + sorted(seen, key=repr)
    return states, edges


def solve(k, w, L0, verbose=True):
    states, edges = build(k, w, L0)
    idx = {s: i for i, s in enumerate(states)}
    nf = 1 << w
    nS = len(states)
    nv = nf + nS  # variables: f[0..nf-1], pi[states]
    rows, cols, vals, rhs = [], [], [], []
    r = 0
    # pi(u) + peso(e) - pi(v) <= 0,  peso = sum coef*f + const
    for (u, v, coef, const) in edges:
        for win, c in coef.items():
            if c != 0:
                rows.append(r); cols.append(win); vals.append(c)
        rows.append(r); cols.append(nf + idx[u]); vals.append(1.0)
        rows.append(r); cols.append(nf + idx[v]); vals.append(-1.0)
        rhs.append(-const)
        r += 1
    A = coo_matrix((vals, (rows, cols)), shape=(r, nv)).tocsr()
    bounds = [(0, None)] * nf + [(None, None)] * nS
    bounds[0] = (0, 0)  # f(0...0) = 0
    bounds[nf + idx[("start",)]] = (0, 0)
    bounds[nf + idx[("sink",)]] = (None, 0)
    c = np.zeros(nv); c[:nf] = 1.0  # f lo más chica posible
    res = linprog(c, A_ub=A, b_ub=np.array(rhs), bounds=bounds, method="highs")
    if verbose:
        name = "Collatz exacto" if k is None else f"C_{k}"
        print(f"{name:15s} w={w} L0={L0}  estados={nS} aristas={len(edges)}  ->  {res.status} {'FACTIBLE' if res.status == 0 else 'INFACTIBLE' if res.status == 2 else res.message}")
    return res, states, edges


if __name__ == "__main__":
    K = int(sys.argv[1]); W = int(sys.argv[2]); L0 = int(sys.argv[3])
    res, states, edges = solve(None if K < 0 else K, W, L0)
    if res.status == 0:
        nf = 1 << W
        f = res.x[:nf]
        print("f no nulas:", {format(i, f"0{W}b")[::-1]: round(v, 4) for i, v in enumerate(f) if v > 1e-9})
