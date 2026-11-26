"""Análisis del catálogo de ciclos de 3x+d (ronda 11, `Ideas/familia_3xa.md`).

Entrada: salida de `fam_cycles.py` (completo para mínimo ≤ max(M·d, piso)) y, opcional, catálogo de
`fam_necklaces.py` (completo para largo ℓ ≤ L). Imprime:
  - totales de ciclos primitivos y distribución de ω(d) (para comparar con Belaga–Mignotte 2006: d < 20000,
    6667 sistemas, 42765 primitivos, ω = 1 en 1481, ω = 2 en 1507, ω = 3 en 1005, máximo 944 en d = 14303);
  - control: d | 2^ℓ − 3^k en todo ciclo primitivo; cota de Belaga x_min ≤ d/(2^{ℓ/k} − 3) cuando ℓ/k > log₂3... (se usa
    la forma exacta x_min·(2^ℓ − 3^k) = d·A_min, y se mide x_min/d);
  - ℓ/k frente a log₂3 (¿los largos se pegan a los convergentes?), ciclos "angostos" (ℓ = ⌈k log₂3⌉);
  - qué d tienen un solo ciclo primitivo y de qué tipo es;
  - los d con más ciclos, y si son (divisores grandes de) números de Collatz 2^ℓ − 3^k;
  - cruce con el catálogo por largos (ciclos con ℓ ≤ L que la búsqueda por mínimos no vio).
Uso: python3 scripts/fam_analysis.py ciclos.tsv [collares_cat.tsv L]"""
import sys, math, csv
from collections import Counter, defaultdict

LOG23 = math.log2(3)


def load(path):
    out = []
    with open(path) as f:
        for r in csv.DictReader(f, delimiter='\t'):
            out.append((int(r['d']), int(r['xmin']), int(r['k']), int(r['l']), int(r.get('prim', 1))))
    return out


def main():
    cyc = load(sys.argv[1])
    prim = [c for c in cyc if c[4] == 1]
    ds = sorted(set(d for d in range(1, max(c[0] for c in cyc) + 1, 2) if d % 3))
    omega = Counter(c[0] for c in prim)
    print(f'sistemas d: {len(ds)} (d ≤ {ds[-1]}), ciclos totales {len(cyc)}, primitivos {len(prim)}')
    dist = Counter(omega[d] for d in ds)
    print('ω(d) = 0,1,2,3,4,5:', [dist[i] for i in range(6)])
    print('máximos ω:', sorted(((omega[d], d) for d in ds), reverse=True)[:12])

    # control de la ecuación y de d | B
    bad = 0
    for d, x, k, l, p in prim:
        B = 2 ** l - 3 ** k
        if B <= 0 or B % d:
            bad += 1
    print('control d | 2^ℓ − 3^k en primitivos: fallas =', bad)

    # Belaga (2003), según la bibliografía anotada de Lagarias: x_min ≤ d/(2^{ℓ/k} − 3) y log₂3 < ℓ/k ≤ log₂(d + 3)
    vb = sum(1 for d, x, k, l, p in prim if x > d / (2 ** (l / k) - 3) * (1 + 1e-9))
    vr = sum(1 for d, x, k, l, p in prim if not (LOG23 < l / k <= math.log2(d + 3) + 1e-12))
    print('control Belaga: violaciones de x_min ≤ d/(2^{ℓ/k}−3):', vb, '; de log₂3 < ℓ/k ≤ log₂(d+3):', vr)
    ratio = sorted(x / (d / (2 ** (l / k) - 3)) for d, x, k, l, p in prim)
    print('  x_min / cota de Belaga: mediana %.3f, máx %.3f' % (ratio[len(ratio) // 2], ratio[-1]))

    # tamaño del mínimo
    r = sorted((x / d, d, x, k, l) for d, x, k, l, p in prim)
    print('x_min/d: mediana %.3f, p90 %.3f, p99 %.3f, máx %s' % (
        r[len(r) // 2][0], r[int(.9 * len(r))][0], r[int(.99 * len(r))][0], r[-1]))
    cnt_above = Counter(int(math.log2(t[0])) if t[0] >= 1 else -1 for t in r)
    print('histograma ⌊log₂(x_min/d)⌋:', sorted(cnt_above.items()))

    # largos
    narrow = sum(1 for d, x, k, l, p in prim if l == math.ceil(k * LOG23))
    print(f'angostos (ℓ = ⌈k·log₂3⌉): {narrow} de {len(prim)}')
    ks = Counter(k for d, x, k, l, p in prim)
    print('k más frecuentes:', ks.most_common(15))
    big_k = sorted(((k, l, d, x) for d, x, k, l, p in prim), reverse=True)[:8]
    print('k más grandes (k, ℓ, d, x_min):', big_k)
    # exceso β = ℓ − k log₂3 frente al ancho máximo log₂(3 + d/x_min)... (desigualdad de ciclo)
    ex = sorted((l - k * LOG23, k, l, d) for d, x, k, l, p in prim if k >= 5)
    print('menor exceso ℓ − k log₂3 (k ≥ 5):', [(round(a, 4), k, l, d) for a, k, l, d in ex[:8]])

    # un solo primitivo
    single = [d for d in ds if omega[d] == 1]
    typ = Counter()
    for d, x, k, l, p in prim:
        if omega[d] == 1:
            typ['k=1' if k == 1 else ('k=2' if k == 2 else 'k≥3')] += 1
    print(f'd con ω(d) = 1: {len(single)}; tipo de su único ciclo: {dict(typ)}')
    print('  primeros:', single[:25])

    # d con muchos ciclos: ¿qué (k, ℓ) dominan?
    byd = defaultdict(Counter)
    for d, x, k, l, p in prim:
        byd[d][(k, l)] += 1
    for w, d in sorted(((omega[d], d) for d in ds), reverse=True)[:6]:
        (k, l), c = byd[d].most_common(1)[0]
        B = 2 ** l - 3 ** k
        print(f'  d = {d}: ω = {w}; tipo dominante (k,ℓ) = ({k},{l}) con {c} ciclos; B = {B} = {B // d}·d')

    if len(sys.argv) > 3:
        L = int(sys.argv[3])
        neck = set()
        with open(sys.argv[2]) as f:
            for row in csv.DictReader(f, delimiter='\t'):
                neck.add((int(row['d']), int(row['xmin'])))
        mine = set((d, x) for d, x, k, l, p in prim if l <= L)
        Dmax = ds[-1]
        neck = set(t for t in neck if t[0] <= Dmax)
        miss = sorted(neck - mine)
        extra = sorted(mine - neck)
        print(f'cruce ℓ ≤ {L}: collares {len(neck)}, búsqueda {len(mine)}, faltan en la búsqueda {len(miss)}, '
              f'sobran {len(extra)}')
        print('  faltantes (d, x_min, x_min/d):', [(d, x, round(x / d, 1)) for d, x in miss[:10]])


if __name__ == '__main__':
    main()
