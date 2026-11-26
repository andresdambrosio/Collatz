# Densidad de predecesores de a (mapa clásico): fracción de n <= L cuya órbita pasa por a.
import sys
L = int(sys.argv[1])
targets = [1,2,4,5,7,10,11,13,17,23,25,31,53,101,103,1001,1009,10007,100003]
idx = {a:i for i,a in enumerate(targets)}
mask = [0]*(L+1)
for n in range(1, L+1):
    m = 0; v = n
    while True:
        if v in idx: m |= 1 << idx[v]
        if v < n: m |= mask[v]; break
        if v == 1: break
        v = v//2 if v % 2 == 0 else 3*v+1
    mask[n] = m
for a,i in idx.items():
    c = sum(1 for n in range(1,L+1) if mask[n] >> i & 1)
    print(f"a={a:>7}  dens={c/L:.5f}  a*dens={a*c/L:.3f}")
