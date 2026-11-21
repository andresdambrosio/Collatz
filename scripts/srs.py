"""Sistema de reescritura de Yolcu–Aaronson–Heule (arXiv 2105.14697), palabra interna w de ▷w◁.
Chequea: (1) cada regla preserva el valor (aux/inicio) o aplica T acelerado (fin);
(2) toda palabra no vacía admite un paso; (3) desde ▷bin(n)◁ toda reducción (estrategia aleatoria)
llega a ▷◁ con #pasos-de-fin = tiempo de parada de T."""
import random, sys, itertools
ACT = {'f': lambda x: 2*x, 't': lambda x: 2*x+1, '0': lambda x: 3*x, '1': lambda x: 3*x+1, '2': lambda x: 3*x+2}
AUX = {'f0': '0f', 'f1': '0t', 'f2': '1f', 't0': '1t', 't1': '2f', 't2': '2t'}
START = {'0': 't', '1': 'ff', '2': 'ft'}
def val(w):
    x = 1
    for s in w: x = ACT[s](x)
    return x
def T(n): return n//2 if n % 2 == 0 else (3*n+1)//2
def steps(w):
    out = []
    if w and w[-1] == 'f': out.append(('end', w[:-1]))
    if w and w[-1] == 't': out.append(('end', w[:-1] + '2'))
    for i in range(len(w)-1):
        if w[i:i+2] in AUX: out.append(('aux', w[:i] + AUX[w[i:i+2]] + w[i+2:]))
    if w and w[0] in START: out.append(('aux', START[w[0]] + w[1:]))
    return out
# (1),(2) exhaustivo hasta longitud 7
for L in range(0, 8):
    for w in map(''.join, itertools.product('ft012', repeat=L)):
        st = steps(w)
        assert (len(st) == 0) == (L == 0), w
        for kind, w2 in st:
            assert val(w2) == (T(val(w)) if kind == 'end' else val(w)), (w, w2)
# (3)
N = int(sys.argv[1]) if len(sys.argv) > 1 else 3000
for n in range(1, N):
    w = bin(n)[3:].replace('0', 'f').replace('1', 't')
    assert val(w) == n
    ends = 0
    while w:
        kind, w = random.choice(steps(w)); ends += kind == 'end'
    m, k = n, 0
    while m != 1: m, k = T(m), k + 1
    assert ends == k, n
print("ok")
