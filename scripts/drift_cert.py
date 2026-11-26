#!/usr/bin/env python3
"""Certificados enteros de "clase forzada" para Collatz (versión entera del Teorema A de rStation collatz_32).

Mapa C(n) = n/2 (par), 3n+1 (impar). Un conjunto A ⊆ ℤ/2^m es *forzado* si toda órbita que no llega a 1
visita algún n con n mod 2^m ∈ A. Grafo de residuos G_g(A): nodos u ∈ [0, 2^g) con u mod 2^m ∉ A;
u impar → 3u+1 mod 2^g; u par → u/2 y u/2 + 2^(g-1). Se borran aristas a no-nodos.

Certificado (todo entero/racional exacto, chequeable en Lean):
  * lvl : nodo → ℕ, no creciente a lo largo de toda arista;
  * cada nivel es de tipo 'pot' (potencial) o 'pin':
      - 'pot': Φ : nodo → ℤ con, en toda arista interna al nivel,
               a + Φ(v) − Φ(u) ≤ −1 (u impar),  −M + Φ(v) − Φ(u) ≤ −1 (u par),
               donde 2^a > 3^M (a, M globales). Además X0 con (3·X0+1)^M ≤ 2^a·X0^M.
      - 'pin': p : nodo → ℚ con, en toda arista interna, p(v) = 3p(u)+1 (u impar), p(v) = p(u)/2 (u par),
               y ningún p(u) es entero positivo fuera de {1, 2, 4}.
  * todo n < X0 llega a 1.

Uso: python3 scripts/drift_cert.py m g r1,r2,...   (ej.: 4 6 9,15)
"""
import sys
from fractions import Fraction
from math import ceil, log2


def graph(m, A, g):
    N = 1 << g
    nodes = [u for u in range(N) if (u % (1 << m)) not in A]
    S = set(nodes)
    adj = {}
    for u in nodes:
        if u % 2:
            outs = [(3 * u + 1) % N]
        else:
            outs = [u // 2, u // 2 + N // 2]
        adj[u] = [v for v in outs if v in S]
    return nodes, adj


def sccs(nodes, adj):
    # Tarjan iterativo; devuelve SCCs en orden topológico inverso (sumideros primero)
    index, low, onst, st, out = {}, {}, set(), [], []
    counter = [0]
    for s in nodes:
        if s in index:
            continue
        work = [(s, 0)]
        index[s] = low[s] = counter[0]; counter[0] += 1; st.append(s); onst.add(s)
        while work:
            u, i = work[-1]
            if i < len(adj[u]):
                work[-1] = (u, i + 1)
                v = adj[u][i]
                if v not in index:
                    index[v] = low[v] = counter[0]; counter[0] += 1; st.append(v); onst.add(v)
                    work.append((v, 0))
                elif v in onst:
                    low[u] = min(low[u], index[v])
            else:
                work.pop()
                if work:
                    low[work[-1][0]] = min(low[work[-1][0]], low[u])
                if low[u] == index[u]:
                    comp = []
                    while True:
                        w = st.pop(); onst.discard(w); comp.append(w)
                        if w == u:
                            break
                    out.append(comp)
    return out  # sumideros primero


def pin_labels(comp, adj):
    """Etiquetas racionales consistentes en un SCC con un solo ciclo, o None."""
    cs = set(comp)
    internal = {u: [v for v in adj[u] if v in cs] for u in comp}
    if any(len(internal[u]) != 1 for u in comp):
        return None
    # recorrer el ciclo desde comp[0]: x ↦ a x + b compuesto
    u0 = comp[0]
    a, b = Fraction(1), Fraction(0)
    u = u0
    seq = []
    while True:
        seq.append(u)
        if u % 2:
            a, b = 3 * a, 3 * b + 1
        else:
            a, b = a / 2, b / 2
        u = internal[u][0]
        if u == u0:
            break
    if len(seq) != len(comp):
        return None
    p0 = b / (1 - a)
    p = {u0: p0}
    x = p0
    for u in seq[:-1]:
        x = 3 * x + 1 if u % 2 else x / 2
        p[internal[u][0]] = x
    return p


def potential(comp, adj, a, M):
    """Φ entero con a+Φ(v)−Φ(u) ≤ −1 (impar), −M+Φ(v)−Φ(u) ≤ −1 (par) en aristas internas; o None."""
    cs = set(comp)
    edges = [(u, v, (a if u % 2 else -M) + 1) for u in comp for v in adj[u] if v in cs]
    # Φ(v) ≤ Φ(u) − w : caminos más cortos con pesos −w (Bellman–Ford); ciclo negativo ⇒ no existe
    dist = {u: 0 for u in comp}
    for _ in range(len(comp) + 1):
        changed = False
        for u, v, w in edges:
            if dist[u] - w < dist[v]:
                dist[v] = dist[u] - w
                changed = True
        if not changed:
            return dist
    return None


def certify(m, A, g, a, M):
    nodes, adj = graph(m, A, g)
    comps = sccs(nodes, adj)
    lvl, kind, Phi, pin = {}, {}, {}, {}
    for i, comp in enumerate(comps):
        for u in comp:
            lvl[u] = i
        cs = set(comp)
        has_edge = any(v in cs for u in comp for v in adj[u])
        if not has_edge:
            kind[i] = 'pot'
            for u in comp:
                Phi[u] = 0
            continue
        p = pin_labels(comp, adj)
        if p is not None:
            bad = [x for x in p.values() if x.denominator == 1 and x > 0 and x not in (1, 2, 4)]
            if bad:
                return None, f'pin entero positivo {bad}'
            kind[i] = 'pin'
            pin.update(p)
            continue
        ph = potential(comp, adj, a, M)
        if ph is None:
            return None, f'SCC no simple sin potencial (tamaño {len(comp)})'
        kind[i] = 'pot'
        Phi.update(ph)
    # chequeo de niveles no crecientes
    assert all(lvl[v] <= lvl[u] for u in nodes for v in adj[u])
    # X0 mínimo con (3X0+1)^M ≤ 2^a X0^M
    X0 = 1
    while (3 * X0 + 1) ** M > 2 ** a * X0 ** M:
        X0 += 1
    return dict(nodes=len(nodes), levels=len(comps), kinds=kind, X0=X0, Phi=Phi, pin=pin, lvl=lvl), 'ok'


def best(m, A, g):
    # convergentes de log2 3 por arriba: a/M
    cands, rec = [], 10.0
    for M in range(1, 700):
        a = 1
        while 2 ** a <= 3 ** M:
            a += 1
        gap = a / M - log2(3)
        if gap < rec:
            rec = gap
            cands.append((a, M))
    for a, M in cands:
        assert 2 ** a > 3 ** M
        c, msg = certify(m, A, g, a, M)
        if c:
            return (a, M), c, msg
        last = msg
    return None, None, last



def bt(vals, fmt):
    """Árbol `BT` de Lean: se baja por los bits de u (LSB primero); subárboles constantes = hoja."""
    if all(v == vals[0] for v in vals):
        return f'.leaf {fmt(vals[0])}'
    return f'.node ({bt(vals[0::2], fmt)}) ({bt(vals[1::2], fmt)})'


def lean_cert(name, pairs, g):
    """Certificado en sintaxis Lean. `pairs`: la clase, como lista de (k, r) con x ≡ r (mod 2^k)."""
    from math import lcm
    N = 1 << g
    A = {u for u in range(N) if any(u % (1 << k) == r for k, r in pairs)}
    aM, c, msg = best(g, A, g)
    assert c is not None, msg
    a, M = aM
    phi_min = min(c['Phi'].values(), default=0)
    phi = [c['Phi'].get(u, phi_min) - phi_min for u in range(N)]
    D = 1
    for p in c['pin'].values():
        D = lcm(D, p.denominator)
    P = [int(c['pin'][u] * D) if u in c['pin'] else 0 for u in range(N)]
    lvl = [c['lvl'].get(u, 0) for u in range(N)]
    pinF = [c['kinds'][c['lvl'][u]] == 'pin' if u in c['lvl'] else False for u in range(N)]
    js = lambda xs: '[' + ', '.join(f'({k}, {r})' for k, r in xs) + ']'
    ints = lambda v: f'({v})' if v < 0 else str(v)
    return (f'set_option maxRecDepth 100000 in\ndef {name} : Cert where\n  g := {g}\n  A := {js(pairs)}\n  a := {a}\n  M := {M}\n'
            f'  X0 := {c["X0"]}\n  D := {D}\n'
            f'  lvl := {bt(lvl, str)}\n  pinF := {bt(pinF, lambda b: "true" if b else "false")}\n'
            f'  phi := {bt(phi, str)}\n  pin := {bt(P, ints)}\n'), (a, M, c)


def bc_pairs(g):
    """Bc_g de collatz_32: 7 mod 8 o los residuos del ciclo de −5 módulo 2^g."""
    N = 1 << g
    return [(3, 7)] + [(g, (-x) % N) for x in (5, 14, 7, 20, 10)]


CASES = [  # (nombre, pares, g, etiqueta)
    *[(f'mod4_{r}', [(2, r)], 2, 'YAH') for r in range(4)],
    *[(f'mod8_{"_".join(map(str, R))}', [(3, x) for x in R], 3, 'YAH')
      for R in ([2], [3], [4], [6], [1, 5], [1, 7])],
    ('mod16_6', [(4, 6)], 4, 'c32'), ('mod16_12', [(4, 12)], 4, 'c32'),
    ('mod16_9_15', [(4, 9), (4, 15)], 6, 'c32b'), ('mod16_11_15', [(4, 11), (4, 15)], 6, 'c32b'),
    ('mod32_27_28', [(5, 27), (5, 28)], 6, 'c32b'),
    *[(f'mod32_{"_".join(map(str, R))}', [(5, x) for x in R], 5, 'c32b')
      for R in ([1, 27, 30], [7, 25, 30], [7, 27, 30], [9, 27, 30], [18, 19, 31], [18, 23, 31],
                [18, 29, 31], [19, 22, 31], [22, 29, 31])],
    ('Bc13', bc_pairs(13), 13, 'c32bc'),
]

HEADER = """import Collatz.Forced

/-!
# Certificados concretos de clases forzadas (generado por `scripts/drift_cert.py --lean`; no editar)

Cada teorema dice: toda órbita de Collatz que no llega a `1` pasa por la clase indicada.
* `YAH`: clases probadas por Yolcu, Aaronson y Heule (2023), re-verificadas aquí con otro método.
* `{6}`, `{12}` mod 16: rStation collatz_32 (derivables de YAH).
* `c32b`: la "base" de clases que collatz_32 reporta como no derivables de YAH por su test de clausura
  (fourier_wren, rStation, 2026; no arbitrado).
* `Bc13`: 7 mod 8 o un residuo del ciclo de −5 módulo 2^13 (collatz_32, Teorema F). Con `g ≥ 14` esta
  familia ya no tiene certificado (lo prueba el mismo paper; nuestro certificador también falla).
-/

namespace Collatz

namespace Forced

open Cert
"""


def statement(pairs):
    mods = sorted({k for k, _ in pairs})
    parts = []
    for k in mods:
        rs = [r for kk, r in pairs if kk == k]
        if len(rs) == 1:
            parts.append(f'collatz^[t] n % {2 ** k} = {rs[0]}')
        else:
            parts.append(f'collatz^[t] n % {2 ** k} ∈ ({rs} : List ℕ)')
    return ' ∨ '.join(parts)


def gen_lean(path):
    out = [HEADER]
    for nm, pairs, g, tag in CASES:
        txt, (a, M, c) = lean_cert('cert_' + nm, pairs, g)
        out.append(txt)
        alts = ' | '.join(['rfl'] * len(pairs))
        js = '[' + ', '.join(f'({k}, {r})' for k, r in pairs) + ']'
        out.append(f"""set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
/-- Toda órbita que no llega a `1` pasa por la clase ({tag}). -/
theorem forced_{nm} (n : ℕ) (hn : 0 < n) (h : ¬ ReachesOne n) :
    ∃ t, {statement(pairs)} := by
  obtain ⟨t, p, hp, hx⟩ := (cert_{nm}).forced (by decide +kernel) n hn h
  refine ⟨t, ?_⟩
  have hA : (cert_{nm}).A = {js} := rfl
  rw [hA] at hp
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with {alts} <;> simp at hx <;> simp [hx]
""")
    out.append('end Forced\n\nend Collatz\n')
    open(path, 'w').write('\n'.join(out))

if __name__ == '__main__':
    if sys.argv[1] == '--lean':
        gen_lean(sys.argv[2] if len(sys.argv) > 2 else 'Collatz/Forced/Certs.lean')
        sys.exit(0)
    m, g = int(sys.argv[1]), int(sys.argv[2])
    A = {int(x) for x in sys.argv[3].split(',')}
    aM, c, msg = best(m, A, g)
    if c is None:
        print(f'm={m} g={g} A={sorted(A)}: SIN certificado ({msg})')
    else:
        npin = sum(1 for k in c['kinds'].values() if k == 'pin')
        print(f'm={m} g={g} A={sorted(A)}: OK a/M={aM[0]}/{aM[1]} nodos={c["nodes"]} niveles={c["levels"]} '
              f'pin-niveles={npin} X0={c["X0"]} maxΦ={max(map(abs, c["Phi"].values()), default=0)} '
              f'pins={sorted(set(c["pin"].values()))[:6]}')

