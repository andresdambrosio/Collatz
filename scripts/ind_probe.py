#!/usr/bin/env python3
"""Sonda: mínimo de z/x en la bola NO dirigida de radio R alrededor de un x enorme con
residuos prescritos en Z_2 y Z_3 (sombras de puntos 2-ádicos / 3-ádicos).

Si x ≡ c (mod 2^K 3^L) con K, L >> R, la bola de radio R de x es (en coeficientes) la del
punto profinito (c en Z_2, c en Z_3): el mínimo de z/x mide si una regla de radio R puede
hacer bajar esa clase.  min z/x >= 1 para todo R  =>  ninguna regla finita cubre ese punto.

Uso: python3 scripts/ind_probe.py R [CAP_BITS]
"""
import random
import sys


def ball_min(x, R, cap_bits=12, mult=3):
    cap = x << cap_bits
    seen = {x}
    frontier = [x]
    best = (x, 0)
    for d in range(1, R + 1):
        nxt = []
        for y in frontier:
            cand = [y // 2] if y % 2 == 0 else [mult * y + 1]
            cand.append(2 * y)
            if y % (2 * mult) == (mult + 1) % (2 * mult):
                cand.append((y - 1) // mult)
            for z in cand:
                if z in seen or z > cap or z <= 0:
                    continue
                seen.add(z)
                nxt.append(z)
                if z < best[0]:
                    best = (z, d)
        frontier = nxt
    return best[0] / x, best[1], len(seen)


def crt(a2, K, a3, L):
    m2, m3 = 2 ** K, 3 ** L
    # x ≡ a2 (mod 2^K), x ≡ a3 (mod 3^L)
    inv = pow(m2, -1, m3)
    b = a2 % m2
    x = b + m2 * (((a3 - b) * inv) % m3)
    assert (x - a2) % m2 == 0 and (x - a3) % m3 == 0
    return x


if __name__ == "__main__":
    R = int(sys.argv[1])
    cb = int(sys.argv[2]) if len(sys.argv) > 2 else 12
    K = L = 400
    rnd = random.Random(1)
    big = 2 ** K * 3 ** L
    cases = {
        "(-1 en Z2, -1 en Z3)  [entero -1]": crt(-1, K, -1, L),
        "(-1 en Z2,  0 en Z3)": crt(-1, K, 0, L),
        "(-1 en Z2,  1 en Z3)": crt(-1, K, 1, L),
        "(-1 en Z2, 1/2 en Z3)": crt(-1, K, pow(2, -1, 3 ** L), L),
        "(-5, -5)  [ciclo -5]": crt(-5, K, -5, L),
        "(-7, -7)  [ciclo -5]": crt(-7, K, -7, L),
        "(-17,-17) [ciclo -17]": crt(-17, K, -17, L),
        "(-25,-25) [ciclo -17]": crt(-25, K, -25, L),
        "(-5 en Z2, 0 en Z3)": crt(-5, K, 0, L),
        "(-17 en Z2, 0 en Z3)": crt(-17, K, 0, L),
        "(-1/5 en Z2, -1/5 en Z3) [ciclo racional]": crt(-pow(5, -1, 2 ** K), K, -pow(5, -1, 3 ** L), L),
    }
    for i in range(4):
        cases[f"azar {i}"] = rnd.randrange(big) | 1
    for name, x in cases.items():
        x += big  # positivo y enorme
        rat, d, n = ball_min(x, R, cb)
        print(f"{name:45s} min z/x = {rat:.4g} (a distancia {d}), nodos {n}", flush=True)


def radius_needed(x, Rmax=60, mult=3):
    """Menor radio R tal que la bola no dirigida de x contiene un z < x (None si > Rmax)."""
    seen = {x}
    frontier = [x]
    for d in range(1, Rmax + 1):
        nxt = []
        for y in frontier:
            cand = [y // 2] if y % 2 == 0 else [mult * y + 1]
            cand.append(2 * y)
            if y % (2 * mult) == (mult + 1) % (2 * mult):
                cand.append((y - 1) // mult)
            for z in cand:
                if z in seen or z <= 0:
                    continue
                if z < x:
                    return d
                seen.add(z)
                nxt.append(z)
        frontier = nxt
    return None
