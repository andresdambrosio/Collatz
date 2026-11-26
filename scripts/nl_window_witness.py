"""Ronda 11 (potenciales no locales), parte 1: descenso por BLOQUES con potenciales de ventanas.

V(n) = lam * L(n) + sum_{i=0}^{L-k} f(w_i(n)),   w_i = bits i..i+k-1 (desde la cifra menos significativa),
S = Syracuse (3n+1)/2^v sobre impares. Pregunta: ¿puede valer V(S^{j+B} n) <= V(S^j n) - eps (bloques de B pasos)?

Argumento (ver Ideas/potenciales_no_locales.md):
  f1   = f(1^k)                       (ventana de la tira de unos, ciclo de -1)
  F(z) = promedio de f por bit sobre la expansión 2-ádica periódica de z
  fbar = 2^-k sum_w f(w)              (promedio uniforme), mu = lam + fbar (crecimiento de V en números típicos)
  (a) Familia "sección media": n = 2^{K+M} + c 2^K + (2^K - 1), c+1 = (-3^{-N}) mod 2^M.  En N pasos la sección
      media (patrón de -3^{-N}) se vuelve una tira de unos: dV = M (f1 - F(-3^{-N})) + O_N(1).
  (b) Familia "sombra de -1": n = 2^K t - 1 con t al azar: dV sobre K pasos = K (0.585 lam + 1.585 fbar - f1) + O(sqrt K).
  F(-3^{-N}) -> fbar (2 es raíz primitiva mod 3^N), así que si (a) no da testigo, f1 <= fbar + o(1), y entonces
  (b) da crecimiento ~ 0.585 * mu * K > 0.
El script construye testigos explícitos y busca, por cálculo DIRECTO de V, un bloque de B pasos con
V(S^{j+B} n) > V(S^j n) - eps. También valida la equidistribución y la predicción de dV.

Uso: python3 scripts/nl_window_witness.py [n_pruebas] [semilla]
"""
import sys, math, random
import numpy as np

LOG23 = math.log2(3)


def bits_lsb(n):
    s = bin(n)[2:]
    return np.frombuffer(s[::-1].encode(), dtype=np.uint8) - 48


def V(n, lam, f, k):
    b = bits_lsb(n).astype(np.int64)
    L = len(b)
    if L < k:
        return lam * L
    idx = np.zeros(L - k + 1, dtype=np.int64)
    for j in range(k):
        idx |= b[j:L - k + 1 + j] << j
    return lam * L + float(f[idx].sum())


def syr(n):
    m = 3 * n + 1
    return m >> ((m & -m).bit_length() - 1)


def period_block(N):
    """Bloque periódico (p bits, LSB primero) de la expansión 2-ádica de -3^{-N}."""
    p = 2 * 3 ** (N - 1)
    Q = (2 ** p - 1) // 3 ** N
    return Q, p


def F_of_block(Q, p, f, k):
    b = bits_lsb(Q).astype(np.int64)
    b = np.concatenate([b, np.zeros(p - len(b), dtype=np.int64)])
    bb = np.tile(b, k // p + 2)
    idx = np.zeros(p, dtype=np.int64)
    for j in range(k):
        idx |= bb[j:p + j] << j
    return float(f[idx].mean()), np.bincount(idx, minlength=2 ** k) / p


def find_block(traj_V, B, eps):
    for j in range(0, len(traj_V) - B):
        if traj_V[j + B] > traj_V[j] - eps:
            return j, traj_V[j + B] - traj_V[j]
    return None


def witness(lam, f, k, B, eps, rng, Nmax=9, verbose=False):
    f1 = float(f[2 ** k - 1])
    fbar = float(f.mean())
    mu = lam + fbar
    # (a) sección media
    for N in range(1, Nmax + 1):
        Q, p = period_block(N)
        FN, _ = F_of_block(Q, p, f, k)
        if f1 - FN > 1e-9:
            steps = N + B
            M = int(math.ceil((40.0 + 4 * steps * (abs(lam) + np.abs(f).max() * k + 2) + eps * steps) / (f1 - FN))) + 8 * p
            M = min(M, 400000)
            K = steps + k + 4
            c1 = sum(Q << (p * i) for i in range(M // p + 1)) % (2 ** M)
            assert (c1 * 3 ** N + 1) % (2 ** M) == 0
            n = (1 << (K + M)) + ((c1 - 1) << K) + ((1 << K) - 1)
            traj = [n]
            for _ in range(steps):
                traj.append(syr(traj[-1]))
            Vs = [V(x, lam, f, k) for x in traj]
            pred = M * (f1 - FN)
            fb = find_block(Vs, B, eps)
            if fb is not None:
                return dict(kind='media', N=N, M=M, dV=Vs[N] - Vs[0], pred=pred, block=fb, bits=n.bit_length())
    if mu <= 0:
        return dict(kind='mu<=0 (V no crece con n: no es certificado)', mu=mu)
    # (b) sombra de -1
    K = int(max(2000, 60.0 / (0.3 * mu))) if mu > 0 else 2000
    K = min(K, 6000)
    t = rng.getrandbits(K) | (1 << K)
    n = (t << K) - 1
    traj = [n]
    for _ in range(K - 1):
        traj.append(syr(traj[-1]))
    Vs = [V(x, lam, f, k) for x in traj[::1]]
    pred = (K - 1) * ((LOG23 - 1) * lam + LOG23 * fbar - f1)
    fb = find_block(Vs, B, eps)
    if fb is not None:
        return dict(kind='sombra', K=K, dV=Vs[-1] - Vs[0], pred=pred, block=fb, bits=n.bit_length())
    return dict(kind='SIN TESTIGO', f1=f1, fbar=fbar, mu=mu, dV=Vs[-1] - Vs[0], pred=pred)


def check_equidistribution():
    print("== Equidistribución de ventanas en -3^{-N} (desvío máximo de frecuencia, relativo a 2^-k) ==")
    for N in range(2, 10):
        Q, p = period_block(N)
        row = []
        for k in (3, 5, 8):
            _, freq = F_of_block(Q, p, np.zeros(2 ** k), k)
            row.append("k=%d: %.3f" % (k, np.abs(freq * 2 ** k - 1).max()))
        print("  N=%d periodo=%6d  " % (N, p) + "  ".join(row))


def check_shadow_formula(rng):
    bad = 0
    for _ in range(300):
        K = rng.randint(5, 80)
        t = rng.getrandbits(rng.randint(1, 60)) + 1
        n = (t << K) - 1
        x = n
        for j in range(K):
            if x != 3 ** j * (t << (K - j)) - 1:
                bad += 1
            x = syr(x)
    print("== Fórmula de la sombra S^j(2^K t - 1) = 3^j 2^{K-j} t - 1: %d discrepancias en 300 casos ==" % bad)


def main():
    ntests = int(sys.argv[1]) if len(sys.argv) > 1 else 60
    rng = random.Random(int(sys.argv[2]) if len(sys.argv) > 2 else 1)
    nrng = np.random.default_rng(rng.getrandbits(32))
    check_equidistribution()
    check_shadow_formula(rng)
    print("== Testigos para potenciales de ventanas (B = largo del bloque, eps = 0.01) ==")
    stats = {}
    cases = []
    for i in range(ntests):
        k = rng.choice([3, 4, 5, 6, 8])
        lam = rng.uniform(0, 1)
        kind = i % 4
        if kind == 0:      # f >= 0 al azar
            f = nrng.uniform(0, 1, 2 ** k)
        elif kind == 1:    # con signo
            f = nrng.uniform(-0.5, 1, 2 ** k)
        elif kind == 2:    # paga la sombra de -1: tira de unos carísima
            f = nrng.uniform(0, 0.2, 2 ** k); f[2 ** k - 1] = rng.uniform(1, 5)
        else:              # paga -1 y además los patrones cercanos a unos (muchos unos)
            f = np.array([max(0.0, (bin(w).count('1') - k + 2)) * rng.uniform(0.5, 3) for w in range(2 ** k)])
        B = rng.choice([1, 2, 5, 20, 100])
        cases.append((lam, f, k, B, kind))
    for (lam, f, k, B, kind) in cases:
        r = witness(lam, f, k, B, 0.01, rng)
        stats[r['kind']] = stats.get(r['kind'], 0) + 1
        extra = {kk: (round(v, 2) if isinstance(v, float) else v) for kk, v in r.items() if kk != 'kind'}
        print("  tipo f=%d k=%d B=%3d lam=%.2f f1=%.2f fbar=%.2f -> %s %s" % (
            kind, k, B, lam, f[2 ** k - 1], f.mean(), r['kind'], extra))
    print("Resumen:", stats)


if __name__ == '__main__':
    main()
