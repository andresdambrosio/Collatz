"""Todos los ciclos racionales positivos de 3x+1 de largo total ℓ ≤ L, y su denominador (ronda 11, `Ideas/familia_3xa.md`).

Un vector de paridad cíclico de largo ℓ con k unos (máscara de ℓ bits con el bit 0 prendido = posiciones s_0 = 0 < … < s_{k-1}
de los pasos impares) define el racional x = A/B, B = 2^ℓ − 3^k > 0, A = Σ 3^{k-1-i} 2^{s_i} (Böhm–Sontacchi).
Con g = gcd(A, B): x = (A/g)/(B/g), así que el ciclo es un ciclo PRIMITIVO del mapa 3x+d con d = B/g (siempre d | B).
  - d = 1  ⟺  B | A  ⟺  ciclo entero de 3x+1 (sólo el trivial: k=1, ℓ=2, x=1, hasta donde se sabe).
Se descartan las palabras periódicas (repiten un ciclo más corto); cada ciclo aparece k veces (una por elemento impar).

Hace dos cosas:
 (1) `catalog D`: lista los ciclos con d ≤ D (d, xmin, k, ℓ), para cruzar con `fam_cycles.py` (que es completo sólo
     para mínimos ≤ M·d; éste es completo para ℓ ≤ L).
 (2) `equi`: para cada (k, ℓ) y cada divisor e de B, compara c_e = #{palabras : e | A} con N/e (equidistribución de A
     módulo los divisores de B). El término e = B es exactamente la pregunta de 3x+1 (d = 1).
     Dos modelos: uniforme (N/e) y "con rango" (Σ_P ⌊A_P/e⌋/A_P: A_P al azar en [1, A_P]), que tiene en cuenta
     que A_P < e hace imposible e | A_P. Y un tercero, "con mínimo" (#{P : Amin_P ≥ e}/e, Amin_P = mínimo de A sobre
     las rotaciones del ciclo): si e | A_P, el ciclo de T_{B/e} tiene todos sus elementos enteros ≥ 1, así que su
     mínimo B·x_min = Amin_P es ≥ e. Es la positividad del mínimo del ciclo. Cuarto, "mínimo con rango"
     (Σ_P ⌊Amin_P/e⌋/Amin_P): además, Amin_P tiene que ser múltiplo de e.

Uso: python3 scripts/fam_necklaces.py L D salida_catalogo.tsv salida_equi.tsv"""
import sys, math
import numpy as np
from collections import defaultdict

LOG23 = math.log2(3)


def divisors(n):
    ds, i = [], 1
    while i * i <= n:
        if n % i == 0:
            ds.append(i)
            if i * i != n:
                ds.append(n // i)
        i += 1
    return sorted(ds)


def words(l):
    """Máscaras de ℓ bits con el bit 0 prendido, aperiódicas, y su A y k."""
    m = (np.arange(1 << (l - 1), dtype=np.int64) << 1) | 1
    full = (1 << l) - 1
    aper = np.ones(m.size, dtype=bool)
    for r in set(p for p in range(2, l + 1) if l % p == 0 and all(p % q for q in range(2, p))):
        s = l // r
        rot = ((m >> s) | (m << (l - s))) & full
        aper &= rot != m
    m = m[aper]
    A = np.zeros(m.size, dtype=np.int64)
    k = np.zeros(m.size, dtype=np.int64)
    for pos in range(l):
        bit = ((m >> pos) & 1).astype(bool)
        A = np.where(bit, 3 * A + (1 << pos), A)
        k += bit
    # A mínimo sobre las rotaciones que empiezan en un paso impar (= B · mínimo del ciclo racional)
    Amin = A.copy()
    for r in range(1, l):
        bit = ((m >> r) & 1).astype(bool)
        if not bit.any():
            continue
        rot = ((m >> r) | (m << (l - r))) & full
        Ar = np.zeros(m.size, dtype=np.int64)
        for pos in range(l):
            b2 = ((rot >> pos) & 1).astype(bool)
            Ar = np.where(b2, 3 * Ar + (1 << pos), Ar)
        Amin = np.where(bit, np.minimum(Amin, Ar), Amin)
    return m, A, k, Amin


def main():
    L, D, out_cat, out_eq = int(sys.argv[1]), int(sys.argv[2]), sys.argv[3], sys.argv[4]
    fc, fe = open(out_cat, 'w'), open(out_eq, 'w')
    fc.write('d\txmin\tk\tl\n')
    fe.write('k\tl\tB\tN\te\tc_e\tN_over_e\tmodel_range\tmodel_min\tmodel_min_range\n')
    for l in range(2, L + 1):
        m, A, k, Amin = words(l)
        for kk in range(1, l):
            B = (1 << l) - 3 ** kk
            if B <= 0:
                continue
            sel = k == kk
            if not sel.any():
                continue
            Ak = A[sel]
            Amk = Amin[sel]
            N = Ak.size                           # = k · (# ciclos de tipo (k, ℓ))
            g = np.gcd(Ak, B)
            d = B // g
            # (1) catálogo
            small = d <= D
            seen = set()
            for a, dd in zip(Ak[small].tolist(), d[small].tolist()):
                x = a // (B // dd)
                if (dd, x) in seen:
                    continue
                cyc, y = [], x                    # recorrer el ciclo de f_dd desde x
                while True:
                    cyc.append(y)
                    y = 3 * y + dd
                    y >>= (y & -y).bit_length() - 1
                    if y == x:
                        break
                for z in cyc:
                    seen.add((dd, z))
                fc.write(f'{dd}\t{min(cyc)}\t{kk}\t{l}\n')
            # (2) equidistribución módulo los divisores de B
            # modelo con rango: un A_P "al azar" es múltiplo de e con prob. ⌊A_P/e⌋/A_P (0 si A_P < e)
            Af = Ak.astype(np.float64)
            for e in divisors(B):
                c = int(np.count_nonzero(Ak % e == 0))
                mr = float(np.sum(np.floor(Af / e) / Af))
                mm = float(np.count_nonzero(Amk >= e)) / e
                Amf = Amk.astype(np.float64)
                mmr = float(np.sum(np.floor(Amf / e) / Amf))
                fe.write(f'{kk}\t{l}\t{B}\t{N}\t{e}\t{c}\t{N / e:.6g}\t{mr:.6g}\t{mm:.6g}\t{mmr:.6g}\n')
        print('ℓ =', l, file=sys.stderr, flush=True)
    fc.close(); fe.close()


if __name__ == '__main__':
    main()
