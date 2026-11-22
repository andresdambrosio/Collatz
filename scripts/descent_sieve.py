"""Criba de Terras: impares r mod 2^j cuyo descenso no está garantizado en ≤ j pasos del mapa acelerado."""
# (1) criba: clases impares r mod 2^j cuyo descenso (T acelerado) está garantizado en <= j pasos
def survivors(j):
    out=[]
    for r in range(1,2**j,2):
        # simular con coeficientes: n = 2^j q + r ; T^i(n) = (3^a 2^{j-s} q + c) mientras la paridad está determinada
        a,s,c=0,0,r   # T^i(n) = 3^a * 2^(j-s) * q + c, con s doses usados
        desc=False
        for i in range(j):
            if s>=j: break
            if c%2==0: c//=2; s+=1
            else: c=(3*c+1)//2; a+=1; s+=1
            # T^i(n) = 3^a 2^(j-s) q + c < 2^j q + r = n para todo q ≥ 0
            if 3**a < 2**s and c < r: desc=True; break
        if not desc: out.append(r)
    return out
for j in (10,14,16,18,20):
    s=survivors(j); print(f"mod 2^{j}: sobreviven {len(s)} de {2**(j-1)} impares ({100*len(s)/2**(j-1):.2f}%)")
