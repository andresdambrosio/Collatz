"""Filtro de clases de certificados con los vecinos de 𝒯 (ver Ideas/vecinos_de_T.md).
Para una clase de interpretaciones monótonas (correcta para terminación relativa), pregunta a z3:
  sep e : ¿orienta débilmente 𝒯 pero NO la regla vecina t◁ → e◁?   (si unsat: clase descartada)
  rm  ρ : ¿orienta débilmente 𝒯 y estrictamente ρ?                  (si sat: elimina ρ de 𝒯)
Clases:
  rat d   : matrices EWZ sobre ℚ≥0, [a]x = M x + v, M[0][0] ≥ 1; estricto = (≥ entrada a entrada) y
            v_l[0] ≥ v_r[0] + 1 (orden x >_δ y ⇔ x₀ ≥ y₀ + δ, xᵢ ≥ yᵢ; δ = 1 por homogeneidad).
  poly k  : una variable, [a](x) = Σ_{i≤k} c_i x^i sobre ℕ, coeficientes en [0, B], c_1 + … + c_k ≥ 1
            (estrictamente monótona); débil = coeficiente a coeficiente; estricto = además constante +1.
Uso: python3 scripts/neighbor_classes.py rat 2 | poly 2 [B]"""
import sys, z3
cls, par = sys.argv[1], int(sys.argv[2])
B = int(sys.argv[3]) if len(sys.argv) > 3 else 3
syms = ['f', 't', '0', '1', '2', '<', '>']
T = [('f>', '>'), ('t>', '2>'), ('f0', '0f'), ('f1', '0t'), ('f2', '1f'), ('t0', '1t'), ('t1', '2f'),
     ('t2', '2t'), ('<0', '<t'), ('<1', '<ff'), ('<2', '<ft')]

def setup():
    s = z3.Solver(); s.set('timeout', 120000)
    if cls == 'rat':
        d = par
        M = {a: [[z3.Real(f'M{a}{i}{j}') for j in range(d)] for i in range(d)] for a in syms}
        v = {a: [z3.Real(f'v{a}{i}') for i in range(d)] for a in syms}
        for a in syms:
            s.add(M[a][0][0] >= 1)
            s.add([x >= 0 for row in M[a] for x in row] + [x >= 0 for x in v[a]])
        def interp(w):
            Mw = [[1 if i == j else 0 for j in range(d)] for i in range(d)]; vw = [0] * d
            for a in w:
                vw = [sum(Mw[i][k] * v[a][k] for k in range(d)) + vw[i] for i in range(d)]
                Mw = [[sum(Mw[i][k] * M[a][k][j] for k in range(d)) for j in range(d)] for i in range(d)]
            return Mw, vw
        def rel(l, r, strict):
            (Ml, vl), (Mr, vr) = interp(l), interp(r)
            c = [Ml[i][j] >= Mr[i][j] for i in range(d) for j in range(d)] + [vl[i] >= vr[i] for i in range(d)]
            if strict: c.append(vl[0] >= vr[0] + 1)
            return z3.And(c)
        show = lambda m: {a: ([[m.eval(x) for x in row] for row in M[a]], [m.eval(x) for x in v[a]]) for a in syms}
    else:
        k = par
        C = {a: [z3.Int(f'c{a}{i}') for i in range(k + 1)] for a in syms}
        for a in syms:
            s.add([0 <= x for x in C[a]] + [x <= B for x in C[a]] + [z3.Sum(C[a][1:]) >= 1])
        def compose(p, q):  # p ∘ q, polinomios como listas de coeficientes
            out = [0]; powq = [1]
            for i, c in enumerate(p):
                if i > 0:
                    new = [0] * (len(powq) + len(q) - 1)
                    for x, a_ in enumerate(powq):
                        for y, b_ in enumerate(q): new[x + y] = new[x + y] + a_ * b_
                    powq = new
                term = [c * x for x in powq]
                out = [ (out[i2] if i2 < len(out) else 0) + (term[i2] if i2 < len(term) else 0)
                        for i2 in range(max(len(out), len(term)))]
            return out
        def interp(w):
            p = [0, 1]
            for a in w: p = compose(p, C[a])
            return p
        def rel(l, r, strict):
            pl, pr = interp(l), interp(r)
            n = max(len(pl), len(pr)); pl += [0] * (n - len(pl)); pr += [0] * (n - len(pr))
            c = [pl[i] >= pr[i] for i in range(n)]
            if strict: c.append(pl[0] >= pr[0] + 1)
            return z3.And(c)
        show = lambda m: {a: [m.eval(x) for x in C[a]] for a in syms}
    for l, r in T: s.add(rel(l, r, False))
    return s, rel, show

for e in (1, 0):
    s, rel, show = setup()
    s.add(z3.Not(rel('t>', f'{e}>', False)))
    print(f"{cls} {par}: sep e={e}: {s.check()}", flush=True)
for l, r in T:
    s, rel, show = setup()
    s.add(rel(l, r, True))
    res = s.check()
    print(f"{cls} {par}: rm {l}->{r}: {res}", flush=True)
    if res == z3.sat: print("   ", show(s.model()))
