"""Collatz con acarreos de vida limitada: interpola entre F_2[x] (k = 0) y los enteros (k = oo).

C_k(n) = n/2 si n par; si n impar, (n + 2n + 1)/2 calculado con un sumador binario donde
cada acarreo tiene "edad": nace con edad 1 cuando a_i + b_i = 2 (o el +1 inicial), se propaga
sumando 1 a la edad, y se descarta si la edad supera k.
  k = 0: n XOR 2n XOR 1  ==  (1+x) f + 1 en F_2[x]   (Hicks-Mullen-Yucas-Zavislak: todo llega a 1)
  k = oo: 3n + 1         (Collatz)
mult = 2 da el análogo de 3n+1 (n + 2n); mult = 4 el de 5n+1 (n + 4n).
"""
import sys, random

def add_trunc(a, b, k, cin=1):
    out = 0; i = 0; carry = cin; age = 1 if cin else 0
    if k == 0: return a ^ b ^ cin
    while a or b or carry:
        x, y = a & 1, b & 1
        s = x + y + carry
        out |= (s & 1) << i
        if x + y == 2: carry, age = 1, 1
        elif s >= 2: carry, age = 1, age + 1
        else: carry, age = 0, 0
        if carry and age > k: carry, age = 0, 0
        a >>= 1; b >>= 1; i += 1
    return out

def step(n, k, mult=2):
    if n % 2 == 0: return n // 2
    m = add_trunc(n, mult * n, k) if k is not None else n + mult * n + 1
    return m // 2

def run(n, k, mult=2, maxsteps=200000, cap=3000):
    seen = {}
    t = 0
    while n not in seen:
        if n.bit_length() > cap: return "escape", t, n
        if t > maxsteps: return "timeout", t, n
        seen[n] = t; n = step(n, k, mult); t += 1
    # ciclo: devolver mínimo
    cyc = [n]; m = step(n, k, mult)
    while m != n: cyc.append(m); m = step(m, k, mult)
    return "cycle", t, (min(cyc), len(cyc))

if __name__ == "__main__":
    mult = int(sys.argv[1]) if len(sys.argv) > 1 else 2
    LIM = int(sys.argv[2]) if len(sys.argv) > 2 else 20000
    for k in [0, 1, 2, 3, 4, 5, 6, 8, 12, None]:
        cyc = {}; esc = 0; to = 0; maxt = 0
        for n in range(1, LIM):
            r, t, x = run(n, k, mult)
            if r == "cycle": cyc[x] = cyc.get(x, 0) + 1; maxt = max(maxt, t)
            elif r == "escape": esc += 1
            else: to += 1
        cs = sorted(cyc.items(), key=lambda kv: -kv[1])
        print(f"k={str(k):>4}  ciclos={len(cs)}  escapes={esc} timeouts={to} max_t={maxt}  ", cs[:6])
