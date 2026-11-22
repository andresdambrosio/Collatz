"""Cota inferior del largo k (pasos impares) de un ciclo de Syracuse si ningún elemento es < M:
mínimo k con un A tal que 0 < A − k·log₂3 ≤ k·log₂(1 + 1/(3M)) (sándwich de Forge)."""
from mpmath import mp, mpf, log, ceil, floor
mp.dps=60
L=log(3)/log(2)
# convergentes y semiconvergentes de log2 3 por arriba: candidatos k donde frac-gap (ceil(kL)-kL) es chico
def kmin(M):
    eps=log(1+mpf(1)/(3*M))/log(2)
    k=1
    # búsqueda por saltos usando mejores aproximaciones por arriba (A/k > L)
    # recorrer semiconvergentes: k tal que ceil(kL)-kL < k*eps ; buscamos el mínimo k
    # el mínimo está entre los "record" de ceil(kL)-kL decreciente; los generamos con el algoritmo de Stern-Brocot
    a,b,c,d=1,1,2,1   # fracciones p/q: izq a/b < L < c/d
    best=None
    while True:
        p,q=a+c,b+d
        if p/mpf(q) > L:
            c,d=p,q
            # c/d es aproximación por arriba con denominador d: record
            if (c-d*L) <= d*eps: return d
        else:
            a,b=p,q
for M in [600001,10**6,10**7,10**8,10**9,10**10,10**11,2**40,2**60,2**71]:
    print(f"M={M:.3g}: k >= {kmin(M)}")
