"""Busca interpretaciones matriciales naturales (EWZ, d×d, entradas ≤ B, M[0][0] ≥ 1) del sistema 𝒯
etiquetado semánticamente por el valor mod m (ver labelled_neighbors.py) que orienten débilmente todas
las reglas etiquetadas y estrictamente al menos una. Zantema: 𝒯 termina ⇔ 𝒯_m termina (modelo, no
cuasi-modelo), así que eliminar una regla etiquetada es un paso genuino de terminación relativa.
Convención: la palabra se lee de izquierda a derecha; [s₁…sₙ](x) = [sₙ](…[s₁](x)) (el primero es el más interno).
Uso: python3 scripts/labelled_search.py m d B"""
import sys, z3
m, d, B = (int(x) for x in sys.argv[1:4])
RULES = [('f>', '>'), ('t>', '2>'), ('f0', '0f'), ('f1', '0t'), ('f2', '1f'), ('t0', '1t'), ('t1', '2f'),
         ('t2', '2t'), ('<0', '<t'), ('<1', '<ff'), ('<2', '<ft')]
act = {'f': lambda x: 2 * x, 't': lambda x: 2 * x + 1, '0': lambda x: 3 * x, '1': lambda x: 3 * x + 1,
       '2': lambda x: 3 * x + 2, '<': lambda x: 1, '>': lambda x: 0}
def label(word, x):
    out = []
    for ch in word:
        out.append(ch if ch in '<>' else f'{ch}{x % m}')
        x = act[ch](x) % m
    return out, x
lrules = set()
for l, r in RULES:
    for x in range(m):
        L, xl = label(l, x); R, xr = label(r, x)
        assert xl == xr or l.endswith('>'), (l, r, x)
        lrules.add((tuple(L), tuple(R)))
lrules = sorted(lrules)
syms = sorted({s for L, R in lrules for s in L + R})
M = {a: [[z3.Int(f'M{a}_{i}{j}') for j in range(d)] for i in range(d)] for a in syms}
v = {a: [z3.Int(f'v{a}_{i}') for i in range(d)] for a in syms}
s = z3.Solver(); s.set('timeout', 600000)
for a in syms:
    s.add(M[a][0][0] >= 1)
    s.add([z3.And(0 <= x, x <= B) for row in M[a] for x in row] + [z3.And(0 <= x, x <= B) for x in v[a]])
def interp(w):  # composición con el primer símbolo más interno: [w] = [w_n] ∘ … ∘ [w_1]
    Mw = [[1 if i == j else 0 for j in range(d)] for i in range(d)]; vw = [0] * d
    for a in w:   # nuevo = [a] ∘ actual : M_a·Mw, M_a·vw + v_a
        vw = [sum(M[a][i][k] * vw[k] for k in range(d)) + v[a][i] for i in range(d)]
        Mw = [[sum(M[a][i][k] * Mw[k][j] for k in range(d)) for j in range(d)] for i in range(d)]
    return Mw, vw
strict = []
for L, R in lrules:
    (Ml, vl), (Mr, vr) = interp(L), interp(R)
    s.add([Ml[i][j] >= Mr[i][j] for i in range(d) for j in range(d)] + [vl[i] >= vr[i] for i in range(d)])
    strict.append(vl[0] > vr[0])
s.add(z3.Or(strict))
res = s.check()
print(f"m={m} d={d} B={B}: {len(lrules)} reglas etiquetadas, {len(syms)} símbolos -> {res}", flush=True)
if res == z3.sat:
    mod = s.model()
    for (L, R), st in zip(lrules, strict):
        if z3.is_true(mod.eval(st)): print("   ESTRICTA:", ' '.join(L), '->', ' '.join(R))
