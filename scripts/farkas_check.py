import itertools, random
ACT = {'f': lambda x: 2*x, 't': lambda x: 2*x+1, '0': lambda x: 3*x, '1': lambda x: 3*x+1, '2': lambda x: 3*x+2}
def val(w):
    x = 1
    for s in w: x = ACT[s](x)
    return x
def F(n):
    if n % 3 == 1: return (n-1)//3
    if n % 6 in (0, 2): return n//2
    return (3*n+1)//2
AUX = {'f0': '0f', 'f1': '0t', 'f2': '1f', 't0': '1t', 't1': '2f', 't2': '2t'}
START = {'0': 't', '1': 'ff', '2': 'ft'}
DYN = {'1': '', '0f': '0', '1f': '1', '1t': '12', '2t': '22'}  # sufijos antes de ◁
def steps(w):
    out = []
    for l, r in DYN.items():
        if w.endswith(l): out.append(('dyn', w[:len(w)-len(l)] + r))
    for i in range(len(w)-1):
        if w[i:i+2] in AUX: out.append(('aux', w[:i] + AUX[w[i:i+2]] + w[i+2:]))
    if w and w[0] in START: out.append(('aux', START[w[0]] + w[1:]))
    return out
# 1) semántica de las reglas
for L in range(8):
    for w in map(''.join, itertools.product('ft012', repeat=L)):
        for k, w2 in steps(w):
            assert val(w2) == (F(val(w)) if k == 'dyn' else val(w)), (w, w2)
print('semántica OK')
# 2) formas normales con valor != 1
bad = {}
for L in range(1, 9):
    for w in map(''.join, itertools.product('ft012', repeat=L)):
        if not steps(w):
            bad.setdefault(val(w), w)
print('valores de formas normales != ▷◁ (primeros):', sorted(bad)[:20])
# 3) desde la representación ternaria, ¿la reducción (cualquier estrategia) llega a ▷◁?
def tern(n):
    s = ''
    while n >= 3: s = str(n % 3) + s; n //= 3
    return ('' if n == 1 else 'f') + s   # dígito líder 2 -> ▷f (vale 2)
stuck = []
for n in range(1, 2000):
    for trial in range(3):
        w = tern(n); assert val(w) == n
        while steps(w): w = random.choice(steps(w))[1]
        if w != '': stuck.append((n, w, val(w))); break
print('trabados desde ternario:', stuck[:10], len(stuck))
# 4) estrategia "más a la derecha" (paper, §4.2)
def rightmost(w):
    best = None
    for l, r in DYN.items():
        if w.endswith(l):
            pos = len(w) - len(l)
            if best is None or pos > best[0]: best = (pos, w[:pos] + r)
    for i in range(len(w)-1):
        if w[i:i+2] in AUX and (best is None or i > best[0]): best = (i, w[:i] + AUX[w[i:i+2]] + w[i+2:])
    if w and w[0] in START and best is None: best = (0, START[w[0]] + w[1:])
    return best[1] if best else None
res = []
for n in range(1, 60):
    w = tern(n); traj = [n]
    while True:
        w2 = rightmost(w)
        if w2 is None: break
        if val(w2) != val(w): traj.append(val(w2))
        w = w2
    res.append((n, w, val(w)))
print('rightmost: forma normal final != ▷◁ para', [(n, w, v) for n, w, v in res if w != ''][:12])
m = 3; t = [m]
for _ in range(6): m = F(m); t.append(m)
print('trayectoria F de 3:', t)
