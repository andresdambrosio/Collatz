"""¿Se distinguen a = 1 y los demás a por la estadística de denominadores? (ronda 11, `Ideas/familia_3xa.md`).

Lee la tabla `equi` de `fam_necklaces.py` (filas k, ℓ, B, N, e, c_e y tres modelos) y compara, en unidades de CICLOS
(cada ciclo de k impares aporta k palabras), lo observado con tres modelos aleatorios para "e | A_P":
  uniforme   N/e;
  rango      Σ_P ⌊A_P/e⌋/A_P;
  mínimo     #{P : A_min(P) ≥ e}/e   (positividad del mínimo del ciclo de T_{B/e});
  mín.+rango Σ_P ⌊A_min(P)/e⌋/A_min(P) (además A_min tiene que ser múltiplo de e).
(a) por bandas de e/N (¿hay déficit sistemático en módulos grandes?);
(b) por D = B/e: ciclos de largo ≤ L con denominador que divide a D (D = 1 es 3x+1, sin el ciclo trivial).
Uso: python3 scripts/fam_model.py equi.tsv [Dmax]"""
import sys, csv, math
from collections import defaultdict


def main():
    rows = list(csv.DictReader(open(sys.argv[1]), delimiter='\t'))
    Dmax = int(sys.argv[2]) if len(sys.argv) > 2 else 60
    print('(a) banda e/N | filas | ciclos esperados: uniforme, rango, mínimo, mínimo con rango | observados  (filas con N ≥ 50, e > 1)')
    for lo, hi in [(1e-3, 1e-2), (1e-2, 1e-1), (1e-1, 1), (1, 10), (10, 1e15)]:
        n = ex = mr = mm = m2 = ob = 0
        for r in rows:
            N, e, c, k = int(r['N']), int(r['e']), int(r['c_e']), int(r['k'])
            if e == 1 or N < 50 or not (lo <= e / N < hi):
                continue
            n += 1; ex += N / e / k; mr += float(r['model_range']) / k
            mm += float(r['model_min']) / k; m2 += float(r.get('model_min_range', 'nan')) / k; ob += c / k
        print(f'  [{lo:g}, {hi:g}) | {n} | {ex:.2f}, {mr:.2f}, {mm:.2f}, {m2:.2f} | {ob:.0f}')
    U, R, E, O, E2 = (defaultdict(float) for _ in range(5))
    for r in rows:
        B, e, k = int(r['B']), int(r['e']), int(r['k'])
        D = B // e
        if D > Dmax or r['l'] == '2':        # ℓ = 2: el ciclo trivial 1 → 1 de 3x+1
            continue
        U[D] += float(r['N_over_e']) / k; R[D] += float(r['model_range']) / k
        E[D] += float(r['model_min']) / k; O[D] += int(r['c_e']) / k
        E2[D] += float(r.get('model_min_range', 'nan')) / k
    print('(b) D | ciclos con denominador | D: uniforme, mínimo, mín.+rango | observados | P(Poisson(mínimo) ≤ obs)')
    for D in sorted(E):
        lam, o = E[D], int(round(O[D]))
        p = sum(math.exp(-lam) * lam ** j / math.factorial(j) for j in range(o + 1))
        print(f'  {D:3d} | {U[D]:.2f}, {lam:.2f}, {E2[D]:.2f} | {o} | {p:.2f}')
    tot_e = sum(E[D] for D in E if D > 1); tot_o = sum(O[D] for D in O if D > 1)
    tot_e2 = sum(E2[D] for D in E2 if D > 1)
    print(f'  total D en (1, {Dmax}]: esperado {tot_e:.1f} (mín.+rango {tot_e2:.1f}), observado {tot_o:.0f}')


if __name__ == '__main__':
    main()
