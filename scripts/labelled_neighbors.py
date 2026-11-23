"""Etiquetado semántico de 𝒯 por el valor del prefijo mod m (modelo: [▷] = 1, [f]x = 2x, [t]x = 2x+1,
[d]x = 3x+d, [◁] constante). La etiqueta de un paso es el valor (mod m) del prefijo justo antes del lado
izquierdo de la regla. Para los vecinos t◁ → e◁ (e = 1: 3x−1, e = 0: 3x−3) calcula qué reglas
etiquetadas (regla, etiqueta) aparecen en ciclos del grafo de reescritura (⇒ no eliminables en el vecino).
Uso: python3 scripts/labelled_neighbors.py m [m ...]"""
import sys
sys.setrecursionlimit(100000)
sys.path.insert(0, 'scripts')
from neighbors import system, canon, scc

def val_prefix(s, i, a=3):
    # valor de la palabra s[0:i] (s empieza con '<'), sin reducir
    x = None
    for ch in s[:i]:
        if ch == '<': x = 1
        elif x is None: return None
        elif ch == 'f': x = 2 * x
        elif ch == 't': x = 2 * x + 1
        elif ch in '012': x = a * x + int(ch)
        else: return None
    return x

def lsteps(s, rules, m):
    for name, (l, r) in rules.items():
        i = s.find(l)
        while i != -1:
            v = val_prefix(s, i)
            lab = 'L' if name.startswith('<') else (v % m)
            yield (name, lab), s[:i] + r + s[i + len(l):]
            i = s.find(l, i + 1)

def analyze(c, m, starts=range(1, 200), maxlen=60):
    rules, D = system(3, c)
    seen, todo, E = set(), [canon(n) for n in starts], {}
    while todo:
        s = todo.pop()
        if s in seen or len(s) > maxlen: continue
        seen.add(s); E[s] = list(lsteps(s, rules, m)); todo += [t for _, t in E[s] if t not in seen]
    E = {s: [(n, t) for n, t in E[s] if t in seen] for s in seen}
    comp = scc(list(seen), E)
    used = {n for s in seen for n, t in E[s] if comp[s] == comp[t]}
    allrules = {(n, 'L') for n in rules if n.startswith('<')} | {(n, x) for n in rules if not n.startswith('<') for x in range(m)}
    # etiquetas alcanzables en 𝒯 mismo (no todas las combinaciones regla/etiqueta ocurren)
    return used, allrules

if __name__ == '__main__':
    for m in map(int, sys.argv[1:] or ['2', '3', '4', '8', '9']):
        u1, allr = analyze(-1, m)
        u0, _ = analyze(-3, m)
        free = sorted(allr - u1 - u0, key=str)
        print(f"m={m}: {len(allr)} reglas etiquetadas; en ciclos de 3x−1: {len(u1)}, de 3x−3: {len(u0)}; "
              f"en NINGÚN ciclo de vecinos: {len(free)}")
        print("   ", free[:40])
