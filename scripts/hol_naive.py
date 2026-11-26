# Extensión entera "ingenua" (sin corrección de criticidad), ronda 11 del laboratorio:
#   g(z) = z/2 + ((q-1) z + r)/2 * (1 - cos πz)/2,   g(n) = T(n),   g'(n) = 1/2 (n par), q/2 (n impar).
# Con esta extensión la derivada a lo largo de una órbita entera es  ∏ T'(n_i) = q^{#impares} / 2^{#pasos},
# así que la deriva log(3/4) y el signo aparecen en los multiplicadores. Experimentos:
#   N1  multiplicadores de los ciclos conocidos (3x+1 positivos y negativos; 5x+1) y la identidad
#       mult = ∏_{n_i impar} 1/(1 + r/(q n_i))  (=> ciclos positivos atractores, negativos repulsores);
#   N2  derivada a lo largo de órbitas enteras: |(g^k)'(n)| vs |T^k(n)|/|n| (iguales salvo un producto convergente);
#   N3  obstrucción a la clase de Eremenko–Lyubich: |n g'(n)/g(n)| acotado en los pares => g ∉ B
#       (Lema 6.1 de EL92 en la versión de Sixsmith, arXiv:1709.09095); valores críticos reales no acotados;
#   N4  separación: punto fijo/2-periódico repulsor (en J) en cada intervalo (n, n+1).
# Uso: python3 scripts/hol_naive.py      (segundos, memoria despreciable)
from fractions import Fraction
from mpmath import mp, mpf, pi, cos, sin, fabs, log

mp.dps = 50


def T(n, q, r=1):
    return n // 2 if n % 2 == 0 else (q * n + r) // 2


def g(z, q, r=1):
    return z / 2 + ((q - 1) * z + r) / 2 * (1 - cos(pi * z)) / 2


def dg(z, q, r=1):
    return mpf(1) / 2 + (q - 1) * (1 - cos(pi * z)) / 4 + ((q - 1) * z + r) * pi * sin(pi * z) / 4


def cycle_from(n, q, maxlen=10000):
    seen = {}
    x = n
    for i in range(maxlen):
        if x in seen:
            start = seen[x]
            c = [x]
            y = T(x, q)
            while y != x:
                c.append(y)
                y = T(y, q)
            return c
        seen[x] = i
        x = T(x, q)
    return None


def N1():
    print("N1 multiplicadores de ciclos de g (exactos, racionales):")
    for q, seeds in ((3, [1, -1, -5, -17]), (5, [1, 13, 17, -1, -3])):
        for s in seeds:
            c = cycle_from(s, q)
            if c is None:
                print(f"   q={q} semilla {s}: sin ciclo en 10^4 pasos")
                continue
            mult = Fraction(1)
            ident = Fraction(1)
            for x in c:
                mult *= Fraction(1, 2) if x % 2 == 0 else Fraction(q, 2)
                if x % 2:
                    ident *= 1 / (1 + Fraction(1, q * x))
            tipo = "atractor" if abs(mult) < 1 else "repulsor"
            print(f"   q={q} ciclo de largo {len(c):>2} por {min(c, key=abs):>4}: mult = {mult} = {float(mult):.5f} "
                  f"({tipo}); identidad ∏1/(1+1/(q n_i)) = {ident == mult}")


def N2(q, n, steps):
    x = n
    logd = 0.0
    for k in range(1, steps + 1):
        logd += float(log(mpf(q) / 2)) if x % 2 else float(log(mpf(1) / 2))
        x = T(x, q)
    print(f"N2 q={q} n={n}: tras {steps} pasos  log|(g^k)'(n)| = {logd:9.3f},  log(|T^k(n)|/|n|) = "
          f"{float(log(mpf(abs(x)) / abs(n))):9.3f},  exponente de Lyapunov ≈ {logd/steps:+.4f} "
          f"(½log(3/4) = {float(log(mpf(3)/4))/2:+.4f}, ½log(5/4) = {float(log(mpf(5)/4))/2:+.4f})")


def N3(q):
    vals = [fabs(n * dg(mpf(n), q) / g(mpf(n), q)) for n in range(2, 2001, 2)]
    # valores críticos reales: ceros de g' en (m, m+1) por cambio de signo
    crit = []
    for m in range(0, 400):
        xs = [m + mpf(i) / 50 for i in range(51)]
        v = [dg(x, q) for x in xs]
        for i in range(50):
            if v[i] * v[i + 1] < 0:
                a, b = xs[i], xs[i + 1]
                for _ in range(60):
                    c = (a + b) / 2
                    if dg(a, q) * dg(c, q) <= 0:
                        b = c
                    else:
                        a = c
                crit.append(g((a + b) / 2, q))
    print(f"N3 q={q}: max_(n par <= 2000) |n g'(n)/g(n)| = {mp.nstr(max(vals), 4)} (acotado ⇒ g ∉ clase B); "
          f"{len(crit)} puntos críticos reales en [0,400], |valor crítico| máx = {mp.nstr(max(fabs(c) for c in crit), 5)}")


def N4(q, lo=-40, hi=40, grid=300):
    found = 0
    for n in range(lo, hi):
        got = False
        for p in (1, 2):
            def F(x):
                y = x
                for _ in range(p):
                    y = g(y, q)
                return y - x
            xs = [n + mpf(i + 1) / (grid + 2) for i in range(grid)]
            vals = [F(x) for x in xs]
            for i in range(grid - 1):
                if vals[i] * vals[i + 1] < 0:
                    a, b = xs[i], xs[i + 1]
                    for _ in range(80):
                        c = (a + b) / 2
                        if F(a) * F(c) <= 0:
                            b = c
                        else:
                            a = c
                    x = (a + b) / 2
                    mult = mpf(1)
                    y = x
                    for _ in range(p):
                        mult *= dg(y, q)
                        y = g(y, q)
                    if fabs(mult) > 1:
                        got = True
                        break
            if got:
                break
        found += got
    print(f"N4 q={q}: intervalos (n,n+1), {lo} <= n < {hi}, con periódico real repulsor de período <= 2: {found}/{hi-lo}")


if __name__ == "__main__":
    N1()
    for q, n, s in ((3, 27, 200), (3, 871, 300), (5, 7, 200), (5, 7, 1000), (3, -17, 300)):
        N2(q, n, s)
    for q in (3, 5):
        N3(q)
        N4(q)
