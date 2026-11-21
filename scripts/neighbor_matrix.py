"""¿La orientación débil de 𝒯 por una interpretación matricial natural (forma EWZ) obliga a
orientar también la regla vecina t◁ → e◁ (e = 1: 3x−1, e = 0: 3x−3)?
Busca con z3 un contraejemplo: interpretación afín [a](x) = M_a x + v_a sobre ℕ^d, entradas en
[0, B], M_a[0][0] ≥ 1, que oriente débilmente las 11 reglas (entrada a entrada) pero NO la vecina.
Uso: python3 scripts/neighbor_matrix.py d B e"""
import sys, z3
d, B, e = (int(x) for x in sys.argv[1:4])
syms = ['f', 't', '0', '1', '2', '<', '>']
M = {a: [[z3.Int(f'M{a}_{i}{j}') for j in range(d)] for i in range(d)] for a in syms}
v = {a: [z3.Int(f'v{a}_{i}') for i in range(d)] for a in syms}
s = z3.Solver()
for a in syms:
    s.add(M[a][0][0] >= 1)
    for i in range(d):
        s.add(v[a][i] >= 0, v[a][i] <= B)
        for j in range(d): s.add(M[a][i][j] >= 0, M[a][i][j] <= B)
def interp(w):  # [w] = [w0] ∘ [w1] ∘ ...
    Mw = [[1 if i == j else 0 for j in range(d)] for i in range(d)]; vw = [0] * d
    for a in w:  # composición: (Mw, vw) ∘ (M_a, v_a) = (Mw M_a, Mw v_a + vw)
        vw = [sum(Mw[i][k] * v[a][k] for k in range(d)) + vw[i] for i in range(d)]
        Mw = [[sum(Mw[i][k] * M[a][k][j] for k in range(d)) for j in range(d)] for i in range(d)]
    return Mw, vw
def geq(l, r):
    (Ml, vl), (Mr, vr) = interp(l), interp(r)
    return z3.And([Ml[i][j] >= Mr[i][j] for i in range(d) for j in range(d)] +
                  [vl[i] >= vr[i] for i in range(d)])
T = [('f>', '>'), ('t>', '2>'), ('f0', '0f'), ('f1', '0t'), ('f2', '1f'), ('t0', '1t'), ('t1', '2f'),
     ('t2', '2t'), ('<0', '<t'), ('<1', '<ff'), ('<2', '<ft')]
for l, r in T: s.add(geq(l, r))
s.add(z3.Not(geq('t>', f'{e}>')))
r = s.check()
print(f"d={d} B={B} e={e}: {r}")
if r == z3.sat:
    m = s.model()
    for a in syms:
        print(a, [[m[M[a][i][j]] for j in range(d)] for i in range(d)], [m[v[a][i]] for i in range(d)])
