"""C_k (Collatz con acarreos de vida <= k) como sistema de reescritura de palabras, y búsqueda de un certificado
matricial de LARGO ACOTADO (no de terminación: C_k tiene ciclos espurios).

Palabra: ▷ n_{L-1} … n_0 ◁ (bit más significativo a la izquierda). Una cabeza H[p,c] (p = bit anterior,
c = estado del acarreo) recorre el número hacia la izquierda calculando (n + 2n + 1)/2 con acarreos truncados.
  par:     0◁ → ◁
  impar:   1◁ → H[1,c0]◁          (el bit 0 de la salida es 0 y se descarta: la división por 2)
  mover:   x H[p,c] → H[x,c'] o   (o, c') = carry_step(x, p, c)
  arriba:  ▷ H[p,c] → ▷ o_{L+1} o_L  (sin ceros a la izquierda)

Certificado: interpretación afín monótona sobre ℕ^d (EWZ: M[0][0] >= 1, entradas en [0, B]) que oriente
DÉBILMENTE todas las reglas (ℓ >= r) y con v_0[0] >= 1, v_1[0] >= 1. Entonces [▷w◁]_0 >= #bits(w) y no crece
en ninguna derivación: toda derivación tiene largo acotado, así que C_k no tiene órbitas divergentes.
(No lo cubre la barrera de Nashida, que es sobre orientación estricta.)

Uso: python3 scripts/carry_srs.py K d B     (K = -1: Collatz exacto)
"""
import sys
import z3
from carry_potential import carry_step


def heads(k):
    cs = [(0, 0), (1, 1)] + ([(1, a) for a in range(2, k + 1)] if k else [])
    if k == 0:
        cs = [(0, 0)]
    return [(p, c) for p in (0, 1) for c in cs]


def H(p, c):
    return f"H{p}{c[0]}{c[1]}"


def rules(k, j=0):
    """j > 0: la cabeza cuenta los bits que cruzó (hasta j) y en el extremo izquierdo sólo actúa si cruzó >= j:
    los números con menos de j bits quedan congelados (eso elimina sus ciclos y no afecta la conclusión)."""
    R = [(("0", "◁"), ("◁",))]
    _, c0 = carry_step(1, 0, (1, 1) if k != 0 else (0, 0), k)
    cnts = list(range(1, j + 1)) if j else [None]
    def Hc(p, c, n):
        return H(p, c) + ("" if n is None else f"_{n}")
    R.append((("1", "◁"), (Hc(1, c0, cnts[0]), "◁")))
    for (p, c) in heads(k):
      for n in cnts:
        n2 = None if n is None else min(n + 1, j)
        for x in (0, 1):
            o, c2 = carry_step(x, p, c, k)
            R.append(((str(x), Hc(p, c, n)), (Hc(x, c2, n2), str(o))))
        if n is not None and n < j:
            continue
        oL, c1 = carry_step(0, p, c, k)
        oL1, c2 = carry_step(0, 0, c1, k)
        assert c2[0] == 0
        out = [str(oL1), str(oL)]
        while out and out[0] == "0":
            out.pop(0)
        R.append((("▷", Hc(p, c, n)), tuple(["▷"] + out)))
    return R


def simulate(n, k, R):
    """Estrategia canónica: aplicar la única regla posible (la cabeza, o el extremo derecho si no hay cabeza)."""
    w = ["▷"] + list(bin(n)[2:]) + ["◁"]
    steps = 0
    while True:
        hpos = [i for i, s in enumerate(w) if s.startswith("H")]
        applied = False
        for (l, r) in R:
            L = len(l)
            rng = [hpos[0] - 1] if hpos else [len(w) - 2]
            for i in rng:
                if tuple(w[i:i + L]) == l:
                    w = w[:i] + list(r) + w[i + L:]
                    applied = True
                    break
            if applied:
                break
        assert applied
        if not any(s.startswith("H") for s in w):
            return int("".join(w[1:-1]) or "0", 2)


def search(k, d, B, R):
    syms = sorted({s for l, r in R for s in l + r})
    M = {a: [[z3.Int(f"M{a}_{i}{j}") for j in range(d)] for i in range(d)] for a in syms}
    v = {a: [z3.Int(f"v{a}_{i}") for i in range(d)] for a in syms}
    s = z3.Solver()
    s.set("timeout", 600000)
    for a in syms:
        s.add(M[a][0][0] >= 1)
        s.add([z3.And(0 <= x, x <= B) for row in M[a] for x in row] + [z3.And(0 <= x, x <= B) for x in v[a]])
    s.add(v["0"][0] >= 1, v["1"][0] >= 1)

    def interp(w):
        Mw = [[1 if i == j else 0 for j in range(d)] for i in range(d)]
        vw = [0] * d
        for a in w:
            vw = [sum(M[a][i][kk] * vw[kk] for kk in range(d)) + v[a][i] for i in range(d)]
            Mw = [[sum(M[a][i][kk] * Mw[kk][j] for kk in range(d)) for j in range(d)] for i in range(d)]
        return Mw, vw

    for l, r in R:
        (Ml, vl), (Mr, vr) = interp(l), interp(r)
        s.add([Ml[i][j] >= Mr[i][j] for i in range(d) for j in range(d)] + [vl[i] >= vr[i] for i in range(d)])
    res = s.check()
    return res, (s.model() if res == z3.sat else None), M, v, syms


if __name__ == "__main__":
    K, d, B = (int(x) for x in sys.argv[1:4])
    k = None if K < 0 else K
    R = rules(k)
    from carry_trunc import step as cstep
    for n in range(1, 3000):
        if n % 2 == 1:
            assert simulate(n, k, R) == cstep(n, k), n
    name = "Collatz" if k is None else f"C_{k}"
    res, mod, M, v, syms = search(k, d, B, R)
    print(f"{name}: {len(R)} reglas, simulación OK; certificado de largo acotado d={d} B={B}: {res}", flush=True)
    if mod is not None:
        for a in syms:
            print(f"  [{a}] M={[[mod.eval(x) for x in row] for row in M[a]]} v={[mod.eval(x) for x in v[a]]}")
