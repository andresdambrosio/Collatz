"""Ciclos de la familia 3x+d (ronda 11, opción D: `Ideas/familia_3xa.md`).

Mapa acelerado sobre los impares positivos: f_d(x) = (3x + d) / 2^{v_2(3x+d)}, con d > 0 y gcd(d, 6) = 1.
Un ciclo tiene k impares y ℓ = p_1 + … + p_k divisiones por 2 y cumple

    x · (2^ℓ − 3^k) = d · A,   A = Σ_{i=0}^{k-1} 3^{k-1-i} 2^{p_1+…+p_i}.

Ciclo **primitivo** (Lagarias 1990): gcd(x, d) = 1 (entonces vale para todos sus elementos). Los no primitivos de T_d
son q·(ciclo primitivo de T_{d/q}) para q | d, q > 1 ("forzados"). Los primitivos de T_d son exactamente los ciclos
racionales x/d de 3x+1 con denominador d.

Método: para cada d y cada impar x0 ≤ M·d no divisible por 3, iterar f_d hasta que el valor baje de x0 (descartado:
x0 no es mínimo de un ciclo), vuelva a x0 (x0 ES el mínimo de un ciclo) o supere el tope de pasos/valor (se sigue la
órbita con enteros de Python hasta el ciclo al que cae, y x0 cuenta si es el mínimo de ese ciclo). Encuentra TODOS los ciclos con mínimo ≤ max(M·d, piso) (completo en ese rango); los de mínimo
mayor se buscan por largo con `fam_necklaces.py`.

Uso: python3 scripts/fam_cycles.py D M salida.tsv [piso [d_inicial]]   (busca mínimos ≤ max(M·d, piso), d_inicial ≤ d ≤ D)
Salida: d, xmin, k, ℓ, primitivo(0/1), vector de exponentes p_1..p_k (empezando en el mínimo)."""
import sys, math
import numpy as np

CAP_STEPS = 400
CAP_VAL = 1 << 60


def cycle_from(x, d):
    """Exponentes del ciclo que empieza en x (x es mínimo de un ciclo de f_d)."""
    ps, y = [], x
    while True:
        y = 3 * y + d
        p = (y & -y).bit_length() - 1
        y >>= p
        ps.append(p)
        if y == x:
            return ps


def resolve_pending(pairs, d):
    """pairs = [(x0, y)]: x0 no bajó de sí mismo en CAP_STEPS pasos y ahora vale y. Se sigue a y (enteros de Python)
    hasta repetir un valor, se registra el ciclo alcanzado y x0 es mínimo de ciclo sii pertenece a un ciclo del que es
    el mínimo. Devuelve (mínimos, sin decidir)."""
    cmin = {}                      # elemento de ciclo -> mínimo de su ciclo
    mins, und = [], []
    for x0, y in pairs:
        if y not in cmin:
            seen, z = {}, y
            for i in range(10 ** 6):
                if z in cmin or z in seen:
                    break
                seen[z] = i
                z = 3 * z + d
                z >>= (z & -z).bit_length() - 1
            else:
                und.append(x0)
                continue
            if z not in cmin:      # ciclo nuevo: empieza en z
                cyc, w = [z], z
                while True:
                    w = 3 * w + d
                    w >>= (w & -w).bit_length() - 1
                    if w == z:
                        break
                    cyc.append(w)
                m = min(cyc)
                for w in cyc:
                    cmin[w] = m
        if cmin.get(x0) == x0:
            mins.append(x0)
    return sorted(set(mins)), und


BLOCK = 1 << 20   # bloques de tamaño fijo: con tamaños crecientes, el malloc de macOS no reusaba memoria (~80 MB por d)


def cycles_for(d, M, floor=0):
    X = max(M * d, floor)
    mins, pend_x, pend_y = [], [], []
    for lo in range(1, X + 1, 2 * BLOCK):
        xs = np.arange(lo, min(lo + 2 * BLOCK, X + 1), 2, dtype=np.int64)
        xs = xs[xs % 3 != 0]
        x0, y = xs, xs.copy()
        for _ in range(CAP_STEPS):
            if x0.size == 0:
                break
            y = 3 * y + d
            y //= (y & -y)
            hit = y == x0
            if hit.any():
                mins.extend(x0[hit].tolist())
            big = y > CAP_VAL
            if big.any():
                pend_x.extend(x0[big].tolist()); pend_y.extend(y[big].tolist())
            keep = (y > x0) & ~big
            x0, y = x0[keep], y[keep]
        pend_x.extend(x0.tolist()); pend_y.extend(y.tolist())
    more, undecided = resolve_pending(list(zip(pend_x, pend_y)), d)
    return sorted(set(mins) | set(more)), undecided


def main():
    D, M, out = int(sys.argv[1]), int(sys.argv[2]), sys.argv[3]
    floor = int(sys.argv[4]) if len(sys.argv) > 4 else 0
    start = int(sys.argv[5]) if len(sys.argv) > 5 else 1
    nund = 0
    with open(out, 'w') as f:
        f.write('d\txmin\tk\tl\tprim\tps\n')
        for d in range(start | 1, D + 1, 2):
            if d % 3 == 0:
                continue
            mins, und = cycles_for(d, M, floor)
            if und:
                nund += len(und)
                print('sin decidir', d, und[:5], file=sys.stderr)
            for x in mins:
                ps = cycle_from(x, d)
                k, l = len(ps), sum(ps)
                # control: ecuación del ciclo
                A, s = 0, 0
                for i in range(k):
                    A += 3 ** (k - 1 - i) * 2 ** s
                    s += ps[i]
                assert x * (2 ** l - 3 ** k) == d * A
                f.write(f'{d}\t{x}\t{k}\t{l}\t{int(math.gcd(x, d) == 1)}\t{",".join(map(str, ps))}\n')
            if d % 1000 == 1:
                print('d =', d, file=sys.stderr, flush=True)
    print('sin decidir total:', nund, file=sys.stderr)


if __name__ == '__main__':
    main()
