"""Ronda 11 (potenciales no locales), parte 2: rasgos de "cola" (distancia 2-ádica a ciclos negativos).

Syracuse S(n) = (3n+1)/2^v sobre impares. Potenciales probadas (en bits):
  V1 = log2 n + c * t1(n),                 t1 = v2(n+1)  (largo de la tira final de unos = profundidad en -1)
  V2 = V1 + c5 * D5(n),                    D5 = max_{x in {-5,-7}} v2(n - x)        (ciclo de -5)
  V3 = V2 + c17 * D17(n),                  D17 = max_{x en el ciclo de -17} v2(n - x) (7 impares, 11 divisiones)
Falla en n  <=>  V(S n) > V(n) - eps.

1. Medida exacta de fallas de V1 en el modelo de Haar (t1 geométrica; si t1 = 1, v >= 2 y la cola nueva t'
   son independientes) contra conteo directo sobre enteros grandes al azar.
2. Tasa de fallas de V1, V2, V3 sobre enteros grandes (conteo directo) y desglose.
3. Sombras de un ciclo racional NO entero de deriva positiva (palabra de valuaciones (1,1,2): 27/16 > 1):
   enteros positivos que crecen durante muchos pasos sin acercarse a -1, -5 ni -17; V3 sube linealmente.

Uso: python3 scripts/nl_tail_features.py [muestras] [semilla]
"""
import sys, math, random
from fractions import Fraction

L3 = math.log2(3)


def v2(m):
    return (m & -m).bit_length() - 1


def syr(n):
    m = 3 * n + 1
    v = v2(m)
    return m >> v, v


def cycle_odd(x0):
    """Puntos impares del ciclo negativo de Syracuse que pasa por x0."""
    pts, x = [], x0
    while True:
        pts.append(x)
        m = 3 * x + 1
        x = m >> v2(m)
        if x == x0:
            return pts


C5 = cycle_odd(-5)
C17 = cycle_odd(-17)


def depth(n, pts):
    return max(v2(n - x) for x in pts)


def feats(n):
    return v2(n + 1), depth(n, C5), depth(n, C17)


def Vfun(n, c, c5, c17):
    t1, d5, d17 = feats(n)
    return math.log2(n) + c * t1 + c5 * d5 + c17 * d17


def predicted_fail_V1(c, eps):
    """Medida de Haar (sobre impares) de las fallas de V1 = log2 n + c t1 (n grande)."""
    tot = 0.5 if c < (L3 - 1) + eps else 0.0  # t1 >= 2: dV = log2(3/2) - c
    for j in range(2, 80):          # t1 = 1, v = j
        pj = 2.0 ** -(j - 1)
        for s in range(1, 200):     # t' = s
            if L3 - j + c * (s - 1) > -eps:
                tot += 0.5 * pj * 2.0 ** -s
    return tot


def main():
    nsamp = int(sys.argv[1]) if len(sys.argv) > 1 else 200000
    rng = random.Random(int(sys.argv[2]) if len(sys.argv) > 2 else 3)
    eps = 0.01
    print("ciclo -5:", C5, " ciclo -17:", C17)
    bits = 120
    sample = [(rng.getrandbits(bits) | (1 << bits) | 1) for _ in range(nsamp)]

    print("\n== 1. V1 = log2 n + c t1: medida exacta (Haar) vs conteo directo (n ~ 2^%d, %d muestras) ==" % (bits, nsamp))
    for c in (0.5, L3 - 1 + eps + 1e-3, 0.7, 1.0, 2.0):
        pred = predicted_fail_V1(c, eps)
        fails = 0
        for n in sample:
            m, _ = syr(n)
            if Vfun(m, c, 0, 0) > Vfun(n, c, 0, 0) - eps:
                fails += 1
        print("  c=%.4f  predicha=%.5f  medida=%.5f" % (c, pred, fails / nsamp))

    c = L3 - 1 + eps + 1e-3
    print("\n  Desglose de fallas de V1 (c=%.4f) por (v, t'): " % c)
    br = {}
    for n in sample:
        m, v = syr(n)
        if Vfun(m, c, 0, 0) > Vfun(n, c, 0, 0) - eps:
            key = (v2(n + 1), v, v2(m + 1))
            br[key] = br.get(key, 0) + 1
    for key, cnt in sorted(br.items(), key=lambda kv: -kv[1])[:10]:
        print("    t1=%d v=%d t'=%d : %.5f" % (key[0], key[1], key[2], cnt / nsamp))

    # pesos que pagan exactamente la sombra de cada ciclo: crecimiento por bit de profundidad perdido
    g5 = (2 * L3 - 3) / 3 + eps
    g17 = (7 * L3 - 11) / 11 + eps
    print("\n== 2. Agregar profundidades en los ciclos -5 (c5=%.4f) y -17 (c17=%.4f) ==" % (g5, g17))
    for name, (cc, c5, c17) in [("V1", (c, 0, 0)), ("V2", (c, g5, 0)), ("V3", (c, g5, g17))]:
        fails = 0
        for n in sample:
            m, _ = syr(n)
            if Vfun(m, cc, c5, c17) > Vfun(n, cc, c5, c17) - eps:
                fails += 1
        print("  %s: fallas %.5f" % (name, fails / nsamp))

    # sombras de -5 y -17: ¿las paga V3?
    print("\n  Sombras de los ciclos negativos (n = x + 2^K t, K = 600): dV total en K/2 pasos para V1 y V3")
    for x in (-1, -5, -17):
        K = 600
        n = x + (1 << K) * (rng.getrandbits(40) | 1)
        traj = [n]
        for _ in range(K // 2 // (1 if x == -1 else 2)):
            traj.append(syr(traj[-1])[0])
        for name, pars in [("V1", (c, 0, 0)), ("V3", (c, g5, g17))]:
            dV = Vfun(traj[-1], *pars) - Vfun(traj[0], *pars)
            nf = sum(1 for a, b in zip(traj, traj[1:]) if Vfun(b, *pars) > Vfun(a, *pars) - eps)
            print("    x=%4d %s: pasos=%d  dV=%+.2f  log2 crece %+.1f  pasos con falla=%d" % (
                x, name, len(traj) - 1, dV, math.log2(traj[-1]) - math.log2(traj[0]), nf))

    print("\n== 3. Sombra de un ciclo racional no entero de deriva positiva ==")
    # palabra de valuaciones w = (1,1,2): S^3(x) = (27 x + c)/16; punto fijo x = c/(16-27)
    for word in [(1, 1, 2), (1, 1, 1, 2), (1, 2, 1, 1, 2)]:
        # composición afín exacta
        a, b = Fraction(1), Fraction(0)
        for v in word:
            a, b = a * 3 / 2 ** v, (b * 3 + 1) / 2 ** v
        x = b / (1 - a)   # punto fijo racional (2-ádico, denominador impar)
        p, D = len(word), sum(word)
        q = x.denominator
        # x mod 2^K como entero positivo: num * inv(den) mod 2^K
        K = 900
        r = (x.numerator * pow(q, -1, 1 << K)) % (1 << K)
        n = r + (1 << K) * 5
        assert n % 2 == 1
        steps = (K // D - 2) * p
        traj, vs = [n], []
        for _ in range(steps):
            m, v = syr(traj[-1]); traj.append(m); vs.append(v)
        ok = all(vs[i] == word[i % p] for i in range(steps))
        pars = (c, g5, g17)
        dV = Vfun(traj[-1], *pars) - Vfun(traj[0], *pars)
        nf = sum(1 for a_, b_ in zip(traj, traj[1:]) if Vfun(b_, *pars) > Vfun(a_, *pars) - eps)
        maxfeat = max(max(feats(y)) for y in traj)
        print("  palabra %s: x = %s, 3^%d/2^%d = %.3f; sigue la palabra: %s; pasos=%d; log2 crece %+.1f;"
              " V3 dV=%+.1f; pasos con falla=%d/%d; rasgo máx en la órbita=%d" % (
                  word, x, p, D, 3 ** p / 2 ** D, ok, steps, math.log2(traj[-1]) - math.log2(traj[0]),
                  dV, nf, steps, maxfeat))


if __name__ == '__main__':
    main()
