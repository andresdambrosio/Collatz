#!/usr/bin/env python3
"""Criba de "descenso no dirigido" por clases residuales mod 2^a 3^b (ronda 11, opción C).

Enunciado reforzado candidato S(n): "n está en la componente débil de 1 del grafo de Collatz".
Inducción fuerte: basta que todo n grande tenga, a distancia <= R en el grafo NO dirigido
(pasos hacia adelante T y hacia atrás), un m < n.  Una regla finita es una lista de clases
r mod M con un camino simbólico válido para toda la clase: x = M t + r  ->  z = P t + Q, con
(P < M) o (P = M y Q < r).  Movimientos (mapa clásico T):
  F1: y impar          -> 3y + 1
  F0: y par            -> y / 2
  B2: y                -> 2y          (siempre: 2y es predecesor de y)
  B3: y ≡ 4 (mod 6)    -> (y - 1)/3   (predecesor impar)
Un movimiento sólo vale si la condición se cumple para TODO t (divisibilidad de P y Q).

Modos: 'fwd' (sólo F: criba de Terras), 'bwd' (sólo B), 'und' (todos).
Mapa: 'q3' (3x+1) o 'q5' (5x+1: F1 -> 5y+1, B5: y ≡ 1 mod 5, y par, (y-1)/5 impar).

Uso: python3 scripts/ind_undirected.py MODO MAPA R PROF [CAP] [PATRON]  (PATRON p. ej. '22m': dos x2 y un x3)
  la criba refina las clases sobrevivientes multiplicando el módulo por 2 y por 3 (o 5)
  alternadamente hasta PROF refinamientos e informa la densidad sobreviviente.
"""
import sys
from fractions import Fraction


def moves(P, Q, mode, mult):
    out = []
    if mode in ("fwd", "und"):
        if P % 2 == 0:
            if Q % 2 == 1:
                out.append((mult * P, mult * Q + 1))
            else:
                out.append((P // 2, Q // 2))
    if mode in ("bwd", "und"):
        out.append((2 * P, 2 * Q))
        m2 = 2 * mult
        # y ≡ 1 (mod mult), y par, (y-1)/mult impar  <=>  y ≡ mult+1 (mod 2 mult)
        if P % m2 == 0 and Q % m2 == (mult + 1) % m2:
            out.append((P // mult, (Q - 1) // mult))
    return out


def descends(M, r, R, mode, mult, cap):
    """¿Hay camino de largo <= R, válido para toda la clase, a algo menor?  Devuelve el camino."""
    start = (M, r)
    seen = {start}
    frontier = [(start, "")]
    for depth in range(R):
        nxt = []
        for (P, Q), path in frontier:
            for k, (P2, Q2) in enumerate(moves(P, Q, mode, mult)):
                if (P2, Q2) in seen or P2 > cap * M:
                    continue
                if P2 < M or (P2 == M and Q2 < r):
                    return path + str(k)
                seen.add((P2, Q2))
                nxt.append(((P2, Q2), path + str(k)))
        frontier = nxt
        if not frontier:
            break
    return None


def sieve(mode, mapname, R, depth, cap=2 ** 10, verbose=True, pattern="2m"):
    mult = 3 if mapname == "q3" else 5
    M, surv = 1, [0]
    hist = []
    for d in range(depth):
        f = 2 if pattern[d % len(pattern)] == "2" else mult
        M2 = M * f
        cand = [r + M * j for r in surv for j in range(f)]
        surv = [r for r in cand if descends(M2, r, R, mode, mult, cap) is None]
        M = M2
        dens = Fraction(len(surv), M)
        hist.append((M, len(surv), float(dens)))
        if verbose:
            print(f"M={M:>12} sobreviven {len(surv):>8}  densidad {float(dens):.5f}", flush=True)
        if not surv:
            break
    return M, surv, hist


if __name__ == "__main__":
    mode, mapname, R, depth = sys.argv[1], sys.argv[2], int(sys.argv[3]), int(sys.argv[4])
    cap = int(sys.argv[5]) if len(sys.argv) > 5 else 2 ** 10
    pattern = sys.argv[6] if len(sys.argv) > 6 else "2m"
    M, surv, _ = sieve(mode, mapname, R, depth, cap, pattern=pattern)
    print("primeras sobrevivientes:", surv[:20], "mod", M)
