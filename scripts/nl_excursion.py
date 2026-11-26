"""Ronda 11 (potenciales no locales), parte 3: el ingrediente mínimo = el funcional de excursión G_eps.

Syracuse S, v_i = valuaciones de la órbita de n. Paseo con margen eps (en bits):
    W_0 = 0,   W_{j+1} = W_j + log2 3 - v_j + eps.
    G_eps(n) = sup_j W_j(n)   (= max(0, W_1(n) + G_eps(S n)))
Recíproco de Lyapunov: V = log2 n + G_eps cumple V(Sn) - V(n) <= -eps + log2(1 + 1/(3n)) en todo n donde G sea
finito, y TODA potencial log2 n + g con g >= 0 que baje eps por paso cumple g >= G_eps - O(sum 1/S^i n).
Truncaciones con mirada de d pasos: V_d = log2 n + max_{j<=d} W_j. Falla en n (dV > -eps/2) <=> la órbita bate su récord
exactamente en el paso d+1 (W_{d+1} > max_{j<=d} W_j), salvo el término 1/(3n).

1. Medida de fallas de V_d (Monte Carlo con v_i geométricas iid, que es la ley exacta de Haar) vs conteo directo
   sobre enteros grandes al azar.
2. G_eps exacto para impares n < X (la órbita llega a 1, verificado): máximo de G, del índice de la excursión J(n),
   comparación con el tiempo de parada, y control: V = log2 n + G baja en cada paso.

Uso: python3 scripts/nl_excursion.py [X] [eps]
"""
import sys, math, random
import numpy as np

L3 = math.log2(3)


def v2(m):
    return (m & -m).bit_length() - 1


def syr(n):
    m = 3 * n + 1
    v = v2(m)
    return m >> v, v


def Vd_fail_direct(n, d, eps):
    """Falla de V_d en n, calculada directamente con la órbita entera."""
    def Md(x):
        W, best = 0.0, 0.0
        for _ in range(d):
            x, v = syr(x)
            W += L3 - v + eps
            best = max(best, W)
        return best
    m, _ = syr(n)
    return (math.log2(m) + Md(m)) > (math.log2(n) + Md(n)) - eps / 2  # empates: dV = -eps + log2(1+1/(3n))


def part1(eps, rng):
    print("== 1. Fallas de V_d = log2 n + max_{j<=d} W_j (eps=%.2f) ==" % eps)
    nrng = np.random.default_rng(5)
    S = 400_000
    ds = [0, 1, 2, 4, 8, 16, 32, 64]
    v = nrng.geometric(0.5, size=(S, max(ds) + 2)).astype(np.float64)
    W = np.cumsum(L3 - v + eps, axis=1)
    W = np.concatenate([np.zeros((S, 1)), W], axis=1)
    runmax = np.maximum.accumulate(W, axis=1)
    sample = [rng.getrandbits(400) | (1 << 400) | 1 for _ in range(20000)]
    for d in ds:
        mc = float(np.mean(W[:, d + 1] > runmax[:, d] - 1e-12))
        dl = sum(Vd_fail_direct(n, d, eps) for n in sample) / len(sample) if d <= 32 else float('nan')
        print("  d=%2d  Haar (MC, %d) = %.5f   enteros ~2^400 (20000) = %.5f" % (d, S, mc, dl))
    print("  Siempre > 0: n = 2^K t - 1 con K > d+1 bate récord en cada paso (sombra de -1).")


def part2(X, eps):
    print("\n== 2. G_eps exacto para impares n < %d (eps=%.2f) ==" % (X, eps))
    G = {1: 0.0}
    J = {1: 0}
    for n0 in range(3, X, 2):
        path = []
        x = n0
        while x not in G:
            m, v = syr(x)
            path.append((x, v))
            x = m
        for (y, v) in reversed(path):
            m, _ = syr(y)
            w = L3 - v + eps + G[m]
            if w > 0:
                G[y], J[y] = w, 1 + J[m]
            else:
                G[y], J[y] = 0.0, 0
    # control de descenso: V = log2 n + G
    worst = -1e9
    for n in range(3, X, 2):
        m, _ = syr(n)
        dV = (math.log2(m) + G[m]) - (math.log2(n) + G[n])
        worst = max(worst, dV + eps - math.log2(1 + 1 / (3 * n)))
    print("  control: max_n [dV + eps - log2(1+1/(3n))] = %.2e  (debe ser <= 0)" % worst)
    odds = range(3, X, 2)
    Gs = np.array([G[n] for n in odds]); Js = np.array([J[n] for n in odds])
    i = int(np.argmax(Gs)); j = int(np.argmax(Js))
    print("  G max = %.2f bits en n=%d;  J max = %d pasos en n=%d (log2 n = %.1f)" % (
        Gs[i], 3 + 2 * i, Js[j], 3 + 2 * j, math.log2(3 + 2 * j)))
    print("  fracción con G = 0 (baja ya en el primer paso con margen): %.4f" % float(np.mean(Gs == 0)))
    for q in (0.5, 0.9, 0.99, 0.999, 1.0):
        print("  cuantil %.3f de J: %d" % (q, int(np.quantile(Js, q))))
    # comparación con el tiempo de parada sigma(n) (pasos de Syracuse hasta bajar de n)
    sig = []
    for n in range(3, min(X, 200001), 2):
        x, s = n, 0
        while x >= n:
            x, _ = syr(x); s += 1
        sig.append(s)
    sig = np.array(sig); Jsub = Js[:len(sig)]
    print("  n < 2e5: corr(J, sigma) = %.3f; J <= sigma en %.4f de los casos; max sigma = %d" % (
        float(np.corrcoef(Jsub, sig)[0, 1]), float(np.mean(Jsub <= sig)), int(sig.max())))


def main():
    X = int(sys.argv[1]) if len(sys.argv) > 1 else 1_000_000
    eps = float(sys.argv[2]) if len(sys.argv) > 2 else 0.05
    rng = random.Random(11)
    part1(eps, rng)
    part2(X, eps)


if __name__ == '__main__':
    main()
