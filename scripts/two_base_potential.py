"""Ronda 10: ¿hay una función potencial que lea el número en DOS bases a la vez?

Phi(n) = log n + sum_{ventanas de ancho k2 del binario} w2[v] + sum_{ventanas de ancho k3 en base b3} w3[v]

Las escrituras se rellenan con un símbolo 'x' a ambos lados (k-1 veces), así que las ventanas de borde
quedan incluidas. Se pide, para todo n impar >= N0, en el paso de Syracuse S(n) = (q n + 1) / 2^v:

    Phi(S(n)) <= Phi(n) - delta,         con w >= -B  (así Phi(n) >= alpha * log n - cte, alpha > 0)

Una Phi así (con delta > 0) acota toda órbita y excluye ciclos con elementos >= N0. Una potencial de un
paso existe si y sólo si la conjetura vale (el tiempo de parada sirve), así que lo que se prueba es si
alcanzan ventanas locales en dos bases.

Método: planos de corte. LP sobre una muestra (maximizar delta), buscar los n que más violan en un
conjunto grande, agregarlos, repetir. Si delta* <= 0 sobre una muestra, NO existe tal Phi (con esos k, B):
la muestra es un certificado finito de imposibilidad.

Uso: python3 scripts/two_base_potential.py Q B3 K2 K3 [B] [rondas]
  Q = 3 (Collatz) o 5 (control 5x+1); B3 = segunda base (3, o 5 para el control); K3 = 0 => sólo binario.
"""
import sys, math, random
import numpy as np
from scipy.optimize import linprog
from scipy.sparse import lil_matrix

random.seed(1)


def digits(n, b):
    s = []
    while n:
        s.append(n % b)
        n //= b
    return s[::-1]


def windows(n, b, k):
    if k == 0:
        return {}
    d = ['x'] * (k - 1) + [str(c) for c in digits(n, b)] + ['x'] * (k - 1)
    out = {}
    for i in range(len(d) - k + 1):
        key = ''.join(d[i:i + k])
        out[key] = out.get(key, 0) + 1
    return out


def syr(n, q):
    m = q * n + 1
    while m % 2 == 0:
        m //= 2
    return m


class Model:
    def __init__(self, q, b3, k2, k3, B):
        self.q, self.b3, self.k2, self.k3, self.B = q, b3, k2, k3, B
        self.idx = {}

    def feat(self, n):
        f = {}
        for key, c in windows(n, 2, self.k2).items():
            f[('2', key)] = f.get(('2', key), 0) + c
        for key, c in windows(n, self.b3, self.k3).items():
            f[('3', key)] = f.get(('3', key), 0) + c
        return f

    def delta_feat(self, n):
        m = syr(n, self.q)
        a, b = self.feat(m), self.feat(n)
        d = dict(a)
        for key, c in b.items():
            d[key] = d.get(key, 0) - c
        return math.log(m) - math.log(n), {k: v for k, v in d.items() if v}

    def solve(self, sample):
        rows = [self.delta_feat(n) for n in sample]
        for _, d in rows:
            for key in d:
                if key not in self.idx:
                    self.idx[key] = len(self.idx)
        nv = len(self.idx)
        # variables: w (nv), delta (1). Maximizar delta.
        A = lil_matrix((len(rows), nv + 1))
        bvec = np.zeros(len(rows))
        for i, (dl, d) in enumerate(rows):
            for key, c in d.items():
                A[i, self.idx[key]] = c
            A[i, nv] = 1.0
            bvec[i] = -dl
        c = np.zeros(nv + 1)
        c[nv] = -1.0
        bounds = [(-self.B, 50.0)] * nv + [(None, 10.0)]
        res = linprog(c, A_ub=A.tocsr(), b_ub=bvec, bounds=bounds, method='highs')
        if res.status != 0:
            raise RuntimeError(res.message)
        w = {key: res.x[i] for key, i in self.idx.items()}
        self.duals = [(-res.ineqlin.marginals[i], n) for i, n in enumerate(sample)]
        return res.x[nv], w

    def slack(self, n, w):
        dl, d = self.delta_feat(n)
        return dl + sum(w.get(k, 0.0) * c for k, c in d.items())  # debe ser <= -delta


def pool(q, size, N0bits=20):
    import os
    maxbits = int(os.environ.get('MAXBITS', '160'))
    P = set()
    for L in range(N0bits, maxbits):
        for _ in range(size // (maxbits - N0bits)):
            P.add(random.getrandbits(L) | 1 | (1 << (L - 1)))
        P.add((1 << L) - 1)
        P.add((1 << L) + 1)
        for _ in range(3):  # ralos en binario
            n = (1 << (L - 1)) | 1
            for _ in range(random.randint(1, 4)):
                n |= 1 << random.randrange(L)
            P.add(n)
        e = int(L / math.log2(3))
        for _ in range(3):  # ralos en base 3
            n = 3 ** e + 1 + sum(random.choice([1, 2]) * 3 ** random.randrange(e) for _ in range(random.randint(0, 3)))
            P.add(n | 1)
    for k in range(N0bits, min(90, maxbits)):  # puntos de excursiones largas
        n = (1 << k) - 1
        for _ in range(4 * k):
            n = syr(n, q)
            if n.bit_length() < N0bits or n.bit_length() > maxbits:
                break
            P.add(n)
    return [n for n in P if n % 2 == 1 and n.bit_length() >= N0bits]


def describe(n, q):
    b = bin(n)[2:]
    t = ''.join(map(str, digits(n, 3)))
    m = syr(n, q)
    v = (q * n + 1).bit_length() - m.bit_length()
    return (f"bits={len(b):3d} unos={b.count('1') / len(b):.2f} cola1={len(b) - len(b.rstrip('1')):2d} "
            f"v={v} tern2={t.count('2') / len(t):.2f} tern0={t.count('0') / len(t):.2f}  bin=...{b[-24:]}")


def report(M, top=15):
    D = sorted(M.duals, reverse=True)
    tot = sum(d for d, _ in D if d > 0)
    print(f"  restricciones activas (dual > 0): {sum(1 for d, _ in D if d > 1e-9)}; peso total {tot:.3f}")
    for d, n in D[:top]:
        print(f"    dual={d:.4f}  {describe(n, M.q)}")


def main():
    q, b3, k2, k3 = map(int, sys.argv[1:5])
    B = float(sys.argv[5]) if len(sys.argv) > 5 else 0.4
    rounds = int(sys.argv[6]) if len(sys.argv) > 6 else 15
    M = Model(q, b3, k2, k3, B)
    big = pool(q, 60000)
    sample = random.sample(big, 2000)
    print(f"q={q} bases (2,{b3}) k2={k2} k3={k3} B={B}  pool={len(big)}")
    for r in range(rounds):
        d, w = M.solve(sample)
        viol = sorted(((M.slack(n, w) + d, n) for n in big), reverse=True)
        worst = [n for s, n in viol[:400] if s > 1e-9]
        print(f"  ronda {r}: muestra={len(sample)} vars={len(M.idx)} delta*={d:.5f} violadores={sum(1 for s, _ in viol if s > 1e-9)}")
        if d <= 1e-9:
            print("  => INFACTIBLE: no hay potencial de este tipo (la muestra es el certificado)")
            report(M)
            return
        if not worst:
            print("  => sin violadores en el pool: candidato (falta verificar fuera del pool)")
            return
        sample += worst


if __name__ == '__main__':
    main()
