# Verifica que todo n < N cae por debajo de n (lo que, por inducción, implica que llega a 1).
import sys
N = int(sys.argv[1]) if len(sys.argv) > 1 else 10**7
max_steps, worst = 0, 0
for n in range(3, N, 2):          # pares: n/2 < n inmediatamente
    if n % 4 == 1:                # 4k+1 -> 12k+4 -> 6k+2 -> 3k+1 < n
        continue
    m, s = n, 0
    while m >= n:
        m = (3*m + 1) >> 1 if m & 1 else m >> 1
        s += 1
    if s > max_steps:
        max_steps, worst = s, n
print(f"OK: todo n < {N} llega a 1. Mayor tiempo de descenso: n={worst} ({max_steps} pasos)")
