"""Collatz con acarreo diferido: el anillo R_d = Z[q]/(q^d - 2) = Z[2^(1/d)].

Un elemento "positivo" x = sum a_i q^i con dígitos a_i en {0,1} (base q); como 2 = q^d,
1 + 1 = q^d: el acarreo salta d posiciones.  d = 1: los enteros (Collatz);
d -> infinito: q^d -> 0 q-ádicamente, y queda F_2[q] (sin acarreos; Hicks-Mullen-Yucas-Zavislak).

Coordenadas: x = c_0 + c_1 q + ... + c_{d-1} q^{d-1}, c_j en N (c_j = número binario con
los dígitos a_{j}, a_{j+d}, a_{j+2d}, ...).
  T_d(x) = x/q            si q | x  (c_0 par)
         = ((1+q)x + 1)/q si no     (el análogo de (3x+1)/2)
"""
import random, sys

def step(c, A="3"):
    d = len(c)
    if c[0] % 2 == 0:
        return c[1:] + (c[0] // 2,)
    # y = (1+q) x + 1   (A = "3")   o   (1+q^2) x + 1  (A = "5", requiere d >= 3 para no mezclar)
    if A == "3":
        qx = (2 * c[-1],) + c[:-1]
    else:
        qx = (2 * c[-1],) + c[:-1]
        qx = (2 * qx[-1],) + qx[:-1]
    y = tuple(a + b for a, b in zip(c, qx))
    y = (y[0] + 1,) + y[1:]
    assert y[0] % 2 == 0
    return y[1:] + (y[0] // 2,)

def size(c):  # largo en dígitos q-ádicos
    return max((x.bit_length() - 1) * len(c) + j + 1 for j, x in enumerate(c) if x) if any(c) else 0

def orbit(c, A="3", maxsteps=10**5, cap=4000):
    seen = {}
    for t in range(maxsteps):
        if c in seen:
            return "cycle", t, seen[c], c
        if size(c) > cap:
            return "escape", t, None, c
        seen[c] = t
        c = step(c, A)
    return "timeout", maxsteps, None, c

def canon_cycle(c, A):
    cyc = [c]; x = step(c, A)
    while x != c:
        cyc.append(x); x = step(x, A)
    return min(cyc), len(cyc)

if __name__ == "__main__":
    A = sys.argv[1] if len(sys.argv) > 1 else "3"
    random.seed(1)
    for d in [1, 2, 3, 4, 5, 6, 8, 12, 16, 32]:
        cycles = {}; esc = 0; tout = 0; N = 300
        for _ in range(N):
            bits = 60
            c = tuple(random.getrandbits(max(1, bits // d)) for _ in range(d))
            if not any(c): continue
            r, t, t0, x = orbit(c, A)
            if r == "cycle":
                key = canon_cycle(x, A); cycles[key] = cycles.get(key, 0) + 1
            elif r == "escape": esc += 1
            else: tout += 1
        cs = sorted(cycles.items(), key=lambda kv: -kv[1])
        print(f"d={d:3d}  ciclos={len(cs)}  escapes={esc}  timeouts={tout}  ",
              [(k[0] if d <= 4 else 'min', k[1], n) for k, n in cs[:4]])
