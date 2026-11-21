"""Vecinos de 𝒯 (YAH) en la misma signatura: binario f,t + dígitos a-arios, mapa
x par -> x/2, x impar -> (a x + c)/2. Para a = 3 sólo cambia la regla dinámica t◁ -> e◁, e = (a+c)/2.

Para cada sistema: (1) chequea que las reglas preservan/aplican el mapa (exhaustivo, palabras cortas);
(2) explora el grafo de reescritura de palabras canónicas ▷w◁ con valor en órbitas acotadas y busca
componentes fuertemente conexas no triviales (derivaciones infinitas); (3) para cada regla ρ,
dice si ρ aparece en algún ciclo (⇒ SN(ρ/S) falso) y si S∖{ρ} todavía tiene ciclos (⇒ S∖{ρ} no termina).
Uso: python3 scripts/neighbors.py [a c] ..."""
import sys, itertools
sys.setrecursionlimit(100000)

def system(a, c):
    e = (a + c) // 2
    assert (a + c) % 2 == 0 and 0 <= e < a, (a, c)
    D = [str(d) for d in range(a)]
    rules = {}  # nombre -> (lhs, rhs) sobre la palabra con marcadores '<' (▷) y '>' (◁)
    rules['f>'] = ('f>', '>')
    rules['t>'] = ('t>', D[e] + '>')
    for bi, b in enumerate('ft'):
        for d in range(a):
            q, r = divmod(a * bi + d, 2)
            rules[b + D[d]] = (b + D[d], D[q] + 'ft'[r])
    for d in range(a):
        rules['<' + D[d]] = ('<' + D[d], '<' + bin(a + d)[3:].replace('0', 'f').replace('1', 't'))
    return rules, D

def val(w, a):
    x = 1
    for s in w:
        if s == 'f': x = 2 * x
        elif s == 't': x = 2 * x + 1
        else: x = a * x + int(s)
    return x

def Tmap(x, a, c): return x // 2 if x % 2 == 0 else (a * x + c) // 2

def steps(s, rules):
    for name, (l, r) in rules.items():
        i = s.find(l)
        while i != -1:
            yield name, s[:i] + r + s[i + len(l):]
            i = s.find(l, i + 1)

def canon(n):
    return '<' + bin(n)[3:].replace('0', 'f').replace('1', 't') + '>'

def check_semantics(a, c, rules, D):
    for L in range(0, 6):
        for w in map(''.join, itertools.product(['f', 't'] + D, repeat=L)):
            s = '<' + w + '>'
            for name, s2 in steps(s, rules):
                v, v2 = val(w, a), val(s2[1:-1], a)
                exp = Tmap(v, a, c) if name in ('f>', 't>') else v
                assert v2 == exp, (a, c, s, name, s2)

def scc(nodes, edges):
    idx, low, on, st, comp, out = {}, {}, set(), [], {}, []
    counter = [0]
    def strong(v):
        idx[v] = low[v] = counter[0]; counter[0] += 1; st.append(v); on.add(v)
        for _, w in edges[v]:
            if w not in idx: strong(w); low[v] = min(low[v], low[w])
            elif w in on: low[v] = min(low[v], idx[w])
        if low[v] == idx[v]:
            k = len(out); out.append([])
            while True:
                w = st.pop(); on.discard(w); comp[w] = k; out[k].append(w)
                if w == v: break
    for v in nodes:
        if v not in idx: strong(v)
    return comp

def analyze(a, c, starts, maxlen=60):
    rules, D = system(a, c)
    check_semantics(a, c, rules, D)
    seen, todo, edges = set(), [canon(n) for n in starts], {}
    while todo:
        s = todo.pop()
        if s in seen or len(s) > maxlen: continue
        seen.add(s)
        edges[s] = list(steps(s, rules))
        todo.extend(t for _, t in edges[s] if t not in seen)
    nodes = [s for s in seen]
    edges = {s: [(n, t) for n, t in edges[s] if t in seen] for s in nodes}
    def cyc_rules(forbid=None):
        E = {s: [(n, t) for n, t in edges[s] if n != forbid] for s in nodes}
        comp = scc(nodes, E)
        used = set()
        for s in nodes:
            for n, t in E[s]:
                if comp[s] == comp[t]: used.add(n)
        return used
    used = cyc_rules()
    print(f"a={a} c={c}: t> -> {rules['t>'][1]}  ({len(nodes)} palabras exploradas)")
    print("  reglas en algún ciclo:", sorted(used))
    print("  reglas en NINGÚN ciclo:", sorted(set(rules) - used))
    for name in rules:
        u = cyc_rules(forbid=name)
        print(f"  S∖{{{name}}}: {'tiene ciclos' if u else 'sin ciclos en lo explorado'}")
    return rules, used

if __name__ == '__main__':
    args = sys.argv[1:] or ['3', '1', '3', '-1', '3', '-3']
    for a, c in zip(args[::2], args[1::2]):
        a, c = int(a), int(c)
        starts = list(range(1, 200))
        analyze(a, c, starts)
