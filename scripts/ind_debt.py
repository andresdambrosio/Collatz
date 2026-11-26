#!/usr/bin/env python3
"""Descenso con "deuda" por clases mod 2^k (sólo hacia adelante): por qué no cierra.

Mapa acelerado T(n) = n/2 (par), (3n+1)/2 (impar).  Una regla finita con deuda es una
potencial  Phi(n) = log n + g(n mod 2^k)  que baja (en uno o varios pasos acotados) en toda
clase.  Como T^t(n) mod 2^(k-t) depende sólo de n mod 2^k, existe g si y sólo si en el grafo
de clases (r -> las dos clases compatibles con T(r)), con peso log(3/2) o log(1/2), todo
ciclo tiene peso medio < 0.  Los ciclos del grafo de clases mod 2^k de largo L <= k son
exactamente las palabras de paridad periódicas w de largo L, y su peso es  o*log3 - L*log2
(o = cantidad de unos).  Peso >= 0  <=>  3^o > 2^L  <=>  el punto periódico 2-ádico de w es
el racional NEGATIVO  x_w = c_w / (2^L - 3^o)  (c_w > 0).

Este script enumera las palabras primitivas con 3^o > 2^L (L <= LMAX), calcula x_w y marca
las que son enteras: deberían ser sólo los ciclos de -1, -5, -17 (rotaciones).  También
verifica numéricamente que las sombras  n = x_w + 2^K m  (m > 0) suben durante ~K pasos.

Uso: python3 scripts/ind_debt.py [LMAX]
"""
import sys
from fractions import Fraction
from itertools import product


def T(n):
    return n // 2 if n % 2 == 0 else (3 * n + 1) // 2


def point(w):
    """Punto fijo racional de T^L restringido a la palabra w: T^L(x) = (3^o x + c)/2^L."""
    a, c = Fraction(1), Fraction(0)  # T^j(x) = a x + c
    for bit in w:
        if bit:
            a, c = 3 * a / 2, (3 * c + 1) / 2
        else:
            a, c = a / 2, c / 2
    return c / (1 - a)  # x = a x + c


def primitive(w):
    L = len(w)
    return all(w != w[d:] + w[:d] for d in range(1, L) if L % d == 0)


def main(LMAX):
    ints = set()
    total = 0
    for L in range(1, LMAX + 1):
        cnt = 0
        for w in product((0, 1), repeat=L):
            if not primitive(w):
                continue
            o = sum(w)
            if 3 ** o <= 2 ** L:
                continue
            cnt += 1
            x = point(w)
            assert x < 0
            if x.denominator == 1:
                ints.add(int(x))
        total += cnt
        print(f"L={L:2d}: palabras primitivas expansivas {cnt}")
    print("total:", total, " puntos enteros:", sorted(ints))
    # sombras: n = x + 2^K m con x en {-1,-5,-17}: Phi = log n + g(n mod 2^k) no puede bajar
    for x in (-1, -5, -17):
        K = 60
        n = x + 2 ** K * 12345
        n0 = n
        for _ in range(K - 10):
            n = T(n)
        print(f"sombra de {x}: n0 ~ 2^{n0.bit_length()}, tras {K-10} pasos n/n0 = {n / n0:.3g}"
              f", n ≡ x mod 2^10: {(n - x) % 2 ** 10 == 0 or any((n - y) % 2**10 == 0 for y in orbit(x))}")


def orbit(x):
    out, y = [], x
    for _ in range(20):
        out.append(y)
        y = T(y)
    return out


if __name__ == "__main__":
    main(int(sys.argv[1]) if len(sys.argv) > 1 else 16)
