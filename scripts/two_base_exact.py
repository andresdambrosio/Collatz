"""Ronda 10, test exacto: potencial que lee el número en base 2 y en base 3 a la vez (mapa clásico).

V(n) = lam2*L2(n) + lam3*L3(n) + sum f2(ventanas del binario) + sum f3(ventanas del ternario)

Ventanas de ancho w sobre la escritura rellenada con ceros a ambos lados; f >= 0 y f(0...0) = 0, así que
V >= lam2*L2 + lam3*L3 >= log2(n) - cte con la normalización lam2 + lam3*log_3(2) = 1.

Condiciones, para todo n "grande" (L2 >= L0 en binario; L3 >= L0t en ternario, que cubre lo anterior):
  par   n -> n/2  :  binario = corrimiento (ventanas iguales, L2 baja 1); ternario = transductor de división
                     exacta por 2 (desde la cifra menos significativa, acarreo en {0,1}).    Pide dV <= -eps.
  impar n -> 3n+1 :  binario = transductor n + 2n + 1; ternario = agregar la cifra 1 al final (sólo cambian
                     las ventanas del borde, que dependen de las últimas w3-1 cifras t).        Pide dV <= 0.
En el paso impar se toma el peor t para cada escritura binaria (t y el binario como independientes). Eso sólo
agrega restricciones: si el LP es factible con eps > 0, V es un certificado válido para todo n grande
(V >= 0 baja sin cota) y toda órbita cae debajo del umbral.

"Para todo n" = camino más largo <= 0 en cada autómata: potenciales de nodos (LP exacto, sin muestras).

Uso: python3 scripts/two_base_exact.py W2 W3 L0      (W3 = 0: sólo binario, control)
"""
import sys, math
import numpy as np
from scipy.optimize import linprog
from scipy.sparse import coo_matrix


class LP:
    def __init__(self):
        self.var = {}
        self.rows = []  # (coef dict, rhs): sum coef*x <= rhs

    def v(self, name):
        if name not in self.var:
            self.var[name] = len(self.var)
        return self.var[name]

    def le(self, coef, rhs=0.0):
        self.rows.append((coef, rhs))


def addc(d, k, c):
    d[k] = d.get(k, 0.0) + c


def path_constraints(lp, tag, edges):
    """edges: (u, v, coef) con coef un dict variable->coeficiente; pide pi(v) >= pi(u) + peso."""
    for (u, v, coef) in edges:
        c = dict(coef)
        addc(c, ('pi', tag, u), 1.0)
        addc(c, ('pi', tag, v), -1.0)
        lp.le(c, 0.0)


def win_key(base, digits_msb_first):
    if all(d == 0 for d in digits_msb_first):
        return None
    return ('f%d' % base, tuple(digits_msb_first))


def binary_odd(w, L0):
    """Autómata de n -> 3n+1 en binario, leyendo desde el bit menos significativo.
    Estado: (hist_in, hist_out, carry, cnt). hist = últimos w-1 dígitos (el más nuevo al final)."""
    edges = []
    start, sink = 'start', 'sink'
    first = ((0,) * (w - 1), (0,) * (w - 1), 1, 0)
    edges.append((start, first, {}))
    stack, seen = [first], {first}

    def step(st, b):
        hin, hout, c, cnt = st
        prev = hin[-1]
        s = b + prev + c
        o, nc = s & 1, s >> 1
        coef = {}
        kin = win_key(2, (b,) + tuple(reversed(hin)))
        kout = win_key(2, (o,) + tuple(reversed(hout)))
        if kin: addc(coef, kin, -1.0)
        if kout: addc(coef, kout, 1.0)
        return (hin[1:] + (b,), hout[1:] + (o,), nc, min(cnt + 1, L0)), coef, o

    while stack:
        st = stack.pop()
        hin, hout, c, cnt = st
        for b in (0, 1):
            if cnt == 0 and b == 0:
                continue  # n impar
            nst, coef, _ = step(st, b)
            edges.append((st, nst, coef))
            if nst not in seen:
                seen.add(nst); stack.append(nst)
        if hin[-1] == 1 and cnt >= L0:  # fin: el último bit leído es el más significativo
            coef = {}
            s2 = st
            outs = []
            for j in range(w + 2):
                s2, cf, o = step(s2, 0)
                for k_, val in cf.items():
                    addc(coef, k_, val)
                outs.append(o)
            assert s2[2] == 0
            dL2 = 2 if outs[1] == 1 else 1  # 3n+1 tiene L+1 o L+2 bits
            addc(coef, 'lam2', dL2)
            addc(coef, 'lam3', 1.0)  # el ternario gana una cifra
            addc(coef, 'M3', 1.0)    # peor cambio de ventanas ternarias del borde
            edges.append((st, sink, coef))
    return edges


def ternary_append_one(w3):
    """Para cada t (últimas w3-1 cifras ternarias, más significativa primero): cambio de ventanas al agregar '1'."""
    out = []
    if w3 == 0:
        return out
    import itertools
    for t in itertools.product(range(3), repeat=w3 - 1):
        coef = {}
        for i in range(w3 - 1):
            old = t[i:] + (0,) * (i + 1)
            new = t[i:] + (1,) + (0,) * i
            ko, kn = win_key(3, old), win_key(3, new)
            if ko: addc(coef, ko, -1.0)
            if kn: addc(coef, kn, 1.0)
        addc(coef, win_key(3, (1,) + (0,) * (w3 - 1)), 1.0)
        out.append(coef)
    return out


def ternary_even(w, L0t):
    """Autómata de n -> n/2 en ternario (n par), desde la cifra menos significativa.
    2*m_i + c_i = n_i + 3*c_{i+1}.  Estado: (hist_in, hist_out, carry, cnt, último m)."""
    edges = []
    start, sink = 'start', 'sink'
    first = ((0,) * (w - 1), (0,) * (w - 1), 0, 0, 0)
    edges.append((start, first, {}))
    stack, seen = [first], {first}
    while stack:
        st = stack.pop()
        hin, hout, c, cnt, lastm = st
        for d in (0, 1, 2):
            nc = (d + c) % 2
            m = (d + 3 * nc - c) // 2
            assert 2 * m + c == d + 3 * nc and 0 <= m <= 2
            coef = {}
            kin = win_key(3, (d,) + tuple(reversed(hin)))
            kout = win_key(3, (m,) + tuple(reversed(hout)))
            if kin: addc(coef, kin, -1.0)
            if kout: addc(coef, kout, 1.0)
            nst = (hin[1:] + (d,), hout[1:] + (m,), nc, min(cnt + 1, L0t), m)
            edges.append((st, nst, coef))
            if nst not in seen:
                seen.add(nst); stack.append(nst)
        # fin: la última cifra leída es la más significativa (no nula), acarreo final 0 (n par)
        if hin[-1] != 0 and c == 0 and cnt >= L0t:
            coef = {}
            h_in, h_out = hin, hout
            for j in range(w - 1):  # vaciar las ventanas con ceros
                kin = win_key(3, (0,) + tuple(reversed(h_in)))
                kout = win_key(3, (0,) + tuple(reversed(h_out)))
                if kin: addc(coef, kin, -1.0)
                if kout: addc(coef, kout, 1.0)
                h_in, h_out = h_in[1:] + (0,), h_out[1:] + (0,)
            dL3 = -1 if lastm == 0 else 0
            addc(coef, 'lam3', dL3)
            addc(coef, 'lam2', -1.0)  # el binario pierde un bit
            addc(coef, 'eps', 1.0)    # pide dV <= -eps
            edges.append((st, sink, coef))
    return edges


def ternary_odd_S(w, L0t):
    """n impar -> (3n+1)/2 en ternario: se lee m = 3n+1 (primera cifra = 1) y se emite m/2.
    Peso = ventanas(m/2) - ventanas(n) = [ventanas(m/2) - ventanas(m)] + [ventanas(m) - ventanas(n)];
    el segundo término es el borde de agregar '1' (depende de las cifras 1..w-1 de m) y se suma al leer la cifra w-1."""
    bnd = {}
    import itertools
    ts = list(itertools.product(range(3), repeat=w - 1))
    for t, coef in zip(ts, ternary_append_one(w)):
        bnd[t] = coef
    edges = []
    start, sink = 'start', 'sink'
    first = ((0,) * (w - 1), (0,) * (w - 1), 0, 0, 0)
    edges.append((start, first, {}))
    stack, seen = [first], {first}
    while stack:
        st = stack.pop()
        hin, hout, c, cnt, lastm = st
        for d in (0, 1, 2):
            if cnt == 0 and d != 1:
                continue  # m = 3n+1 termina en 1
            nc = (d + c) % 2
            m = (d + 3 * nc - c) // 2
            coef = {}
            kin = win_key(3, (d,) + tuple(reversed(hin)))
            kout = win_key(3, (m,) + tuple(reversed(hout)))
            if kin: addc(coef, kin, -1.0)
            if kout: addc(coef, kout, 1.0)
            nh = hin[1:] + (d,)
            if cnt + 1 == w:  # ya se leyeron las cifras 0..w-1: t = cifras 1..w-1 de m (la más significativa primero)
                for k_, val in bnd[tuple(reversed(nh))].items():
                    addc(coef, k_, val)
            nst = (nh, hout[1:] + (m,), nc, min(cnt + 1, max(L0t, w)), m)
            edges.append((st, nst, coef))
            if nst not in seen:
                seen.add(nst); stack.append(nst)
        if hin[-1] != 0 and c == 0 and cnt >= max(L0t, w):
            coef = {}
            h_in, h_out = hin, hout
            for j in range(w - 1):
                kin = win_key(3, (0,) + tuple(reversed(h_in)))
                kout = win_key(3, (0,) + tuple(reversed(h_out)))
                if kin: addc(coef, kin, -1.0)
                if kout: addc(coef, kout, 1.0)
                h_in, h_out = h_in[1:] + (0,), h_out[1:] + (0,)
            # largo: L3(m) = L3(n) + 1; L3(m/2) = L3(m) - [última cifra de m/2 = 0]
            addc(coef, 'lam3', 1.0 + (-1 if lastm == 0 else 0))
            addc(coef, 'Mt', -1.0)  # Mt >= peso del camino
            edges.append((st, sink, coef))
    return edges


def binary_odd_S(w, L0):
    """n impar -> (3n+1)/2 en binario: el transductor de 3n+1 y un corrimiento (ventanas iguales, un bit menos)."""
    edges = binary_odd(w, L0)
    out = []
    for (u, v, coef) in edges:
        if v == 'sink':
            c = {k: x for k, x in coef.items() if k not in ('lam3', 'M3')}
            addc(c, 'lam2', -1.0)
            addc(c, 'Mb', -1.0)
            out.append((u, v, c))
        else:
            out.append((u, v, coef))
    return out


def solve_S(w2, w3, L0):
    L0t = max(1, math.floor((L0 - 1) * math.log(2) / math.log(3)))
    lp = LP()
    eb = binary_odd_S(w2, L0)
    path_constraints(lp, 'b', eb)
    import os
    deficit = os.environ.get('DEFICIT') == '1'
    if not deficit:
        lp.le({'Mb': 1.0, 'Mt': 1.0}, 0.0)  # impar: Mb + Mt <= 0
    lp.deficit = deficit
    et, eo = [], []
    if w3 == 0:
        lp.le({'lam3': 1.0}, 0.0); lp.le({'Mt': 1.0}, 0.0); lp.le({'Mt': -1.0}, 0.0)
        lp.le({'lam2': -1.0, 'eps': 1.0}, 0.0)
        tags = ('b',)
    else:
        eo = ternary_odd_S(w3, L0t)
        path_constraints(lp, 'o', eo)
        et = ternary_even(w3, L0t)
        path_constraints(lp, 't', et)
        tags = ('b', 'o', 't')
    for tag in tags:
        lp.le({('pi', tag, 'start'): 1.0}, 0.0); lp.le({('pi', tag, 'start'): -1.0}, 0.0)
        lp.le({('pi', tag, 'sink'): 1.0}, 0.0)
    r = math.log(2) / math.log(3)
    lp.le({'lam2': 1.0, 'lam3': r}, 1.0); lp.le({'lam2': -1.0, 'lam3': -r}, -1.0)
    return finish(lp, f"[S] w2={w2} w3={w3} L0={L0} (L0t={L0t}) aristas bin={len(eb)} ter_impar={len(eo)} ter_par={len(et)}")


def finish(lp, header):
    for name in ('lam2', 'lam3', 'eps', 'M3', 'Mb', 'Mt'):
        lp.v(name)
    for coef, _ in lp.rows:
        for k in coef:
            lp.v(k)
    nv = len(lp.var)
    rows, cols, vals, rhs = [], [], [], []
    for i, (coef, b) in enumerate(lp.rows):
        for k, c in coef.items():
            if c != 0:
                rows.append(i); cols.append(lp.var[k]); vals.append(c)
        rhs.append(b)
    A = coo_matrix((vals, (rows, cols)), shape=(len(lp.rows), nv)).tocsr()
    bounds = []
    for k in sorted(lp.var, key=lp.var.get):
        if isinstance(k, tuple) and k[0] in ('f2', 'f3'):
            bounds.append((0, 100))
        elif k in ('lam2', 'lam3'):
            bounds.append((0, None))
        elif k == 'eps':
            bounds.append((None, 1.0))
        else:
            bounds.append((None, None))
    c = np.zeros(nv); c[lp.var['eps']] = -1.0
    if getattr(lp, 'deficit', False):
        # déficit: mínimo K = Mb + Mt con eps >= 0.01 fijo
        c = np.zeros(nv); c[lp.var['Mb']] = 1.0; c[lp.var['Mt']] = 1.0
        bounds[lp.var['eps']] = (0.01, 0.01)
    res = linprog(c, A_ub=A, b_ub=np.array(rhs), bounds=bounds, method='highs')
    print(header + f"  vars={nv} filas={len(lp.rows)}")
    if getattr(lp, 'deficit', False) and res.status == 0:
        x = res.x
        print(f"  DEFICIT K* = Mb + Mt = {res.fun:.6f}  (Mb={x[lp.var['Mb']]:.4f}, Mt={x[lp.var['Mt']]:.4f}, "
              f"lam2={x[lp.var['lam2']]:.4f}, lam3={x[lp.var['lam3']]:.4f})  -> {'hay potencial' if res.fun <= 1e-9 else 'no hay potencial'}")
        return res, lp
    if res.status != 0:
        print("  estado:", res.status, "INFACTIBLE" if res.status == 2 else res.message)
        return None
    x = res.x
    eps = x[lp.var['eps']]
    print(f"  eps* = {eps:.6f}   lam2={x[lp.var['lam2']]:.4f} lam3={x[lp.var['lam3']]:.4f}"
          f"   -> {'CERTIFICADO (eps > 0)' if eps > 1e-9 else 'no hay potencial de este tipo'}")
    return res, lp


def solve(w2, w3, L0):
    L0t = max(1, math.floor((L0 - 1) * math.log(2) / math.log(3)))
    lp = LP()
    eb = binary_odd(w2, L0)
    path_constraints(lp, 'b', eb)
    for coef in ternary_append_one(w3):  # M3 >= cambio de borde, para todo t
        c = dict(coef); addc(c, 'M3', -1.0); lp.le(c, 0.0)
    if w3 == 0:
        lp.le({'lam3': 1.0}, 0.0)
        lp.le({'M3': 1.0}, 0.0); lp.le({'M3': -1.0}, 0.0)
        # paso par en binario solo: dV = -lam2 <= -eps
        lp.le({'lam2': -1.0, 'eps': 1.0}, 0.0)
        et = []
    else:
        et = ternary_even(w3, L0t)
        path_constraints(lp, 't', et)
    for tag in ('b', 't'):
        if tag == 't' and w3 == 0:
            continue
        lp.le({('pi', tag, 'start'): 1.0}, 0.0); lp.le({('pi', tag, 'start'): -1.0}, 0.0)
        lp.le({('pi', tag, 'sink'): 1.0}, 0.0)
    # normalización lam2 + lam3*log_3 2 = 1
    r = math.log(2) / math.log(3)
    lp.le({'lam2': 1.0, 'lam3': r}, 1.0); lp.le({'lam2': -1.0, 'lam3': -r}, -1.0)
    for name in ('lam2', 'lam3', 'eps', 'M3'):
        lp.v(name)
    for coef, _ in lp.rows:
        for k in coef:
            lp.v(k)
    nv = len(lp.var)
    rows, cols, vals, rhs = [], [], [], []
    for i, (coef, b) in enumerate(lp.rows):
        for k, c in coef.items():
            if c != 0:
                rows.append(i); cols.append(lp.var[k]); vals.append(c)
        rhs.append(b)
    A = coo_matrix((vals, (rows, cols)), shape=(len(lp.rows), nv)).tocsr()
    bounds = []
    for k in sorted(lp.var, key=lp.var.get):
        if isinstance(k, tuple) and k[0] in ('f2', 'f3'):
            bounds.append((0, 100))
        elif k in ('lam2', 'lam3'):
            bounds.append((0, None))
        elif k == 'eps':
            bounds.append((None, 1.0))
        else:
            bounds.append((None, None))
    c = np.zeros(nv); c[lp.var['eps']] = -1.0
    res = linprog(c, A_ub=A, b_ub=np.array(rhs), bounds=bounds, method='highs')
    print(f"w2={w2} w3={w3} L0={L0} (L0t={L0t})  aristas bin={len(eb)} ter={len(et)}  vars={nv} filas={len(lp.rows)}")
    if res.status != 0:
        print("  estado:", res.status, res.message)
        return None
    x = res.x
    eps = x[lp.var['eps']]
    print(f"  eps* = {eps:.6f}   lam2={x[lp.var['lam2']]:.4f} lam3={x[lp.var['lam3']]:.4f} M3={x[lp.var['M3']]:.4f}"
          f"   -> {'CERTIFICADO (eps > 0)' if eps > 1e-9 else 'no hay potencial de este tipo'}")
    return res, lp


if __name__ == '__main__':
    W2, W3, L0 = map(int, sys.argv[1:4])
    if len(sys.argv) > 4 and sys.argv[4] == 'S':
        solve_S(W2, W3, L0)
    else:
        solve(W2, W3, L0)
