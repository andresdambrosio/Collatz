# Dinámica holomorfa de la extensión entera de Letherman–Schleicher–Wood (1999), ronda 11 del laboratorio.
#
# Para el mapa "qx+r" acelerado  T(n) = n/2 (n par), (q n + r)/2 (n impar)  definimos la extensión entera
#   f(z) = z/2 + ((q-1) z + r)/2 * (1 - cos πz)/2 + (α + β cos πz) sin πz,
#   α = (q-1)/(4π), β = -(q+1)/(4π),
# que cumple f(n) = T(n) y f'(n) = 0 para todo entero n (q = 3, r = 1 es la f_0 de LSW según la reseña
# de Lagarias, math/0309224, entrada 115). Con q = 5 es la extensión análoga de 5x+1.
#
# Experimentos:
#   E1  interpolación y criticidad en |n| <= N (3x+1 y 5x+1);
#   E2  constante de superatracción EXPLÍCITA: |f(m+w) - T(m)| <= (K1|m| + K0)|w|^2 para |w| <= ρ,
#       con K1, K0 calculados por principio del máximo sobre |w| = ρ; de ahí el radio de un disco alrededor
#       de cada entero que queda en el conjunto de Fatou (para 3x+1, 5x+1 y negativos por igual);
#   E3  ancho real medido de la zona que sigue a la órbita entera, comparado con la cota de E2;
#   E4  separación: puntos periódicos repulsores (en J) en cada intervalo (n, n+1);
#   E5  el modelo clásico de dominio errante con órbita de puntos críticos: z + sin z + 2π (Baker 1984).
#
# Uso: python3 scripts/hol_lsw.py [N]     (N por defecto 200; corre en < 1 minuto, memoria despreciable)
import sys
from mpmath import mp, mpf, mpc, pi, cos, sin, exp, fabs

mp.dps = 60
N = int(sys.argv[1]) if len(sys.argv) > 1 else 200


def T(n, q, r=1):
    return n // 2 if n % 2 == 0 else (q * n + r) // 2


def coeffs(q):
    return (q - 1) / (4 * pi), -(q + 1) / (4 * pi)


def f(z, q, r=1):
    a, b = coeffs(q)
    return z / 2 + ((q - 1) * z + r) / 2 * (1 - cos(pi * z)) / 2 + (a + b * cos(pi * z)) * sin(pi * z)


def df(z, q, r=1):
    a, b = coeffs(q)
    c, s = cos(pi * z), sin(pi * z)
    return (mpf(1) / 2 + (q - 1) / 2 * (1 - c) / 2 + ((q - 1) * z + r) / 2 * pi * s / 2
            - b * pi * s * s + (a + b * c) * pi * c)


def E1(q):
    err = max(fabs(f(mpf(n), q) - T(n, q)) for n in range(-N, N + 1))
    der = max(fabs(df(mpf(n), q)) for n in range(-N, N + 1))
    print(f"E1 q={q}: max|f(n)-T(n)| = {mp.nstr(err, 3)}, max|f'(n)| = {mp.nstr(der, 3)}  (|n| <= {N})")


def E2(q, rho=mpf("0.2"), npts=720):
    """f(m+w) - T(m) = m * P_c(w) + Q_c(w), c = (-1)^m; ambos con cero doble en w = 0.
    K1 = max_{|w|=rho} |P_c(w)|/rho^2, K0 = max |Q_c(w)|/rho^2 (principio del máximo para P_c/w^2, Q_c/w^2)."""
    a, b = coeffs(q)
    K1 = K0 = mpf(0)
    for c in (1, -1):
        const = 0 if c == 1 else mpf(1) / 2          # T(m) = m/2 (par), q m/2 + 1/2 (impar)
        slope = mpf(1) / 2 if c == 1 else mpf(q) / 2
        for j in range(npts):
            w = rho * exp(2j * pi * j / npts)
            P = mpf(1) / 2 + (q - 1) * (1 - c * cos(pi * w)) / 4 - slope
            Q = w / 2 + ((q - 1) * w + 1) * (1 - c * cos(pi * w)) / 4 + (a + b * c * cos(pi * w)) * c * sin(pi * w) - const
            K1 = max(K1, fabs(P) / rho ** 2)
            K0 = max(K0, fabs(Q) / rho ** 2)
    K = max(K1, K0)
    lam = mpf(q + 2) / 2  # (|T(m)|+1) <= lam (|m|+1)
    print(f"E2 q={q}: K1 = {mp.nstr(K1, 6)}, K0 = {mp.nstr(K0, 6)}  =>  |f(m+w)-T(m)| <= K(|m|+1)|w|^2, K = {mp.nstr(K, 6)}, |w| <= {rho}")
    print(f"      disco D(m, δ(m)) ⊂ Fatou con δ(m) = min(ρ, 1/(2·λ·K·(|m|+1))), λ = {lam}: "
          f"δ(1) = {mp.nstr(min(rho, 1 / (2 * lam * K * 2)), 4)}, δ(1000) = {mp.nstr(1 / (2 * lam * K * 1001), 4)}")
    return K, lam


def track_width(n, q, K=40, tol=mpf("0.25"), lo=mpf("1e-12"), hi=mpf("0.49")):
    """Mayor δ (bisección, 40 pasos) tal que n±δ siguen a la órbita entera de n por K pasos con error < tol."""
    orbit = [n]
    for _ in range(K):
        orbit.append(T(orbit[-1], q))

    def ok(x):
        for k in range(1, K + 1):
            x = f(x, q)
            if fabs(x - orbit[k]) >= tol:
                return False
        return True

    if not (ok(n + lo) and ok(n - lo)):
        return mpf(0)
    for _ in range(40):
        mid = (lo + hi) / 2
        if ok(n + mid) and ok(n - mid):
            lo = mid
        else:
            hi = mid
    return lo


def E3(q, K2, lam, ns, steps):
    print(f"E3 q={q}: ancho real medido δ*(n) (sigue {steps} pasos) vs. cota δ(n) de E2")
    for n in ns:
        w = track_width(n, q, K=steps)
        bound = min(mpf("0.2"), 1 / (2 * lam * K2 * (abs(n) + 1)))
        top = max(abs(x) for x in orb(n, q, steps))
        print(f"   n={n:>6}  δ*={mp.nstr(w, 4):>10}  (|n|+1)δ*={mp.nstr(w * (abs(n) + 1), 4):>8}  "
              f"cota={mp.nstr(bound, 3):>9}  max|órbita| en {steps} pasos = {top}")


def orb(n, q, steps):
    out = [n]
    for _ in range(steps):
        out.append(T(out[-1], q))
    return out


def E4(q, lo=-40, hi=40, grid=400):
    """Busca puntos fijos y de período 2 reales y repulsores en cada (n, n+1)."""
    found = 0
    tot = 0
    worst = None
    for n in range(lo, hi):
        tot += 1
        got = False
        for p in (1, 2):
            def F(x):
                y = x
                for _ in range(p):
                    y = f(y, q)
                return y - x
            xs = [n + mpf(i + 1) / (grid + 2) for i in range(grid)]
            vals = [F(x) for x in xs]
            for i in range(grid - 1):
                if vals[i] * vals[i + 1] < 0:
                    a_, b_ = xs[i], xs[i + 1]
                    for _ in range(80):
                        m_ = (a_ + b_) / 2
                        if F(a_) * F(m_) <= 0:
                            b_ = m_
                        else:
                            a_ = m_
                    x = (a_ + b_) / 2
                    mult = mpf(1)
                    y = x
                    for _ in range(p):
                        mult *= df(y, q)
                        y = f(y, q)
                    if fabs(mult) > 1:
                        got = True
                        break
            if got:
                break
        if got:
            found += 1
        elif worst is None:
            worst = n
    print(f"E4 q={q}: intervalos (n,n+1), {lo} <= n < {hi}, con punto periódico real repulsor de período <= 2: "
          f"{found}/{tot}" + ("" if worst is None else f"  (primer intervalo sin hallazgo: ({worst},{worst+1}))"))


def E5(steps=12):
    """Baker 1984, Ej. 5.3: g(z) = z + sin z + 2π. Puntos críticos (2k+1)π, g((2k+1)π) = (2k+3)π: cadena escapante
    de puntos críticos dentro de un dominio errante. Ancho real que sigue la cadena: constante en k."""
    g = lambda z: z + sin(z) + 2 * pi
    print("E5 Baker: z + sin z + 2π, ancho real δ*(k) que sigue la órbita de (2k+1)π:")
    for k in (0, 10, 100, 1000):
        c0 = (2 * k + 1) * pi

        def ok(x):
            for j in range(1, steps + 1):
                x = g(x)
                if fabs(x - (c0 + 2 * pi * j)) >= mpf("0.5"):
                    return False
            return True
        lo, hi = mpf("1e-9"), mpf(3)
        for _ in range(40):
            mid = (lo + hi) / 2
            if ok(c0 + mid) and ok(c0 - mid):
                lo = mid
            else:
                hi = mid
        print(f"   k={k:>5}: δ* = {mp.nstr(lo, 5)}")


if __name__ == "__main__":
    for q in (3, 5):
        E1(q)
    consts = {q: E2(q) for q in (3, 5)}
    E3(3, *consts[3], ns=[1, 7, 27, 97, 871, -1, -5, -17, -1000], steps=40)
    E3(5, *consts[5], ns=[1, 7, 13, 17, 27, 97, -1, -3], steps=40)
    for q in (3, 5):
        E4(q)
    E5()
