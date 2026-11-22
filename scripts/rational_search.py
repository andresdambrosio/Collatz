"""Búsqueda de interpretaciones matriciales RACIONALES (forma EWZ) que eliminen una regla de 𝒯.
Fuera del alcance de la barrera de Nashida (que cubre matrices naturales y árticas).
Entradas de la forma k/D con k ∈ [0, B]. Cada símbolo es la matriz aumentada (numeradores)
  A_a = [[K_a, V_a], [0, D]]   (valor real: A_a / D)
y una palabra de largo p tiene numerador ∏ A y denominador D^p. Orden EWZ sobre ℚ^d con δ = 1/D^p_max:
  débil  l → r : (M_l, v_l) ≥ (M_r, v_r) entrada a entrada;
  estricto     : además v_l[0] > v_r[0]   (sobre ℚ, con finitas reglas, alcanza con > : hay δ > 0 común).
Monotonía: M_a[0][0] ≥ 1  ⇔  K_a[0][0] ≥ D.
Uso: python3 scripts/rational_search.py d D B [regla ...]   (reglas: f>, t>, f0, ..., <2; 'sep1', 'sep0')"""
import sys, z3
d, D, B = (int(x) for x in sys.argv[1:4])
which = sys.argv[4:] or ['sep1', 'sep0', 'f>', 't>', 'f0', 'f1', 'f2', 't0', 't1', 't2', '<0', '<1', '<2']
syms = ['f', 't', '0', '1', '2', '<', '>']
T = [('f>', '>'), ('t>', '2>'), ('f0', '0f'), ('f1', '0t'), ('f2', '1f'), ('t0', '1t'), ('t1', '2f'),
     ('t2', '2t'), ('<0', '<t'), ('<1', '<ff'), ('<2', '<ft')]
n = d + 1

def build():
    s = z3.Solver(); s.set('timeout', int(sys.argv[0] and 300000))
    K = {a: [[z3.Int(f'K{a}{i}{j}') for j in range(d)] for i in range(d)] for a in syms}
    V = {a: [z3.Int(f'V{a}{i}') for i in range(d)] for a in syms}
    for a in syms:
        s.add(K[a][0][0] >= D)
        s.add([z3.And(0 <= x, x <= B) for row in K[a] for x in row] + [z3.And(0 <= x, x <= B) for x in V[a]])
    A = {a: [K[a][i] + [V[a][i]] for i in range(d)] + [[0] * d + [D]] for a in syms}
    def num(w):
        P = [[1 if i == j else 0 for j in range(n)] for i in range(n)]
        for a in w:
            P = [[z3.simplify(z3.Sum([P[i][k] * A[a][k][j] for k in range(n)])) if any(
                not (isinstance(P[i][k], int) and P[i][k] == 0) for k in range(n)) else 0
                for j in range(n)] for i in range(n)]
        return P
    def rel(l, r, strict):
        Pl, Pr = num(l), num(r)
        sl, sr = D ** (len(r)), D ** (len(l))   # Pl/D^|l| ≥ Pr/D^|r|  ⇔  Pl·D^|r| ≥ Pr·D^|l|
        c = [Pl[i][j] * sl >= Pr[i][j] * sr for i in range(d) for j in range(n)]
        if strict: c.append(Pl[0][d] * sl > Pr[0][d] * sr)
        return z3.And(c)
    for l, r in T: s.add(rel(l, r, False))
    return s, rel, K, V

for q in which:
    s, rel, K, V = build()
    if q.startswith('sep'):
        s.add(z3.Not(rel('t>', q[3] + '>', False)))
    else:
        l, r = dict(T)[q] and (q, dict(T)[q])
        s.add(rel(l, r, True))
    res = s.check()
    print(f"d={d} D={D} B={B} {q}: {res}", flush=True)
    if res == z3.sat:
        m = s.model()
        for a in syms:
            print('   ', a, [[f"{m.eval(K[a][i][j])}/{D}" for j in range(d)] for i in range(d)],
                  [f"{m.eval(V[a][i])}/{D}" for i in range(d)], flush=True)
