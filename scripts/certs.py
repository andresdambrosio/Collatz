"""Parser de los certificados de Yolcu–Aaronson–Heule (repo emreyolcu/rewriting-collatz, proofs/*.log).

Uso: python3 scripts/certs.py <dir-proofs> <nombre> [--lean]
  Parsea proofs/<nombre>.log, re-chequea en Python cada paso (independiente del prover del paper)
  y con --lean imprime las interpretaciones como código Lean.

Formato: cada paso empieza con "Natural: dimension d" o "Arctic: dimension d", luego un bloque
por símbolo "[x]: <matriz> x + <vector>" (d filas). Casilla vacía = 0 (natural) o -∞ (ártico).
Al final del paso, "Relatively top-terminating rules:" lista las reglas que se quitan.
Composición: [s1 s2 ... sn](x) = [s1]([s2](...[sn](x))).
"""
import re
import sys

NEG = None  # -∞ ártico


def parse_cell(tok, arctic):
    tok = tok.strip()
    if tok == '':
        return NEG if arctic else 0
    return int(tok)


def split_inner(inner, d):
    # columnas de igual ancho separadas por un espacio
    L = len(inner)
    w = (L - (d - 1)) // d
    assert w * d + (d - 1) == L, (inner, d)
    return [inner[k * (w + 1): k * (w + 1) + w] for k in range(d)]


def parse_symbol_block(lines, d, arctic):
    """lines: d líneas del bloque (la primera con el prefijo "[x]: ")."""
    m = re.match(r'\[(\w)\]: ', lines[0])
    sym = m.group(1)
    off = m.end()
    rows = [ln[off:] for ln in lines]
    M, v = [], []
    for r in rows:
        # matriz: desde el primer delimitador hasta el siguiente; vector: después de '+'
        segs = re.findall(r'[/\\|\[]([^/\\|\[\]]*)[/\\|\]]', r)
        assert len(segs) == 2, (r, segs)
        M.append([parse_cell(c, arctic) for c in split_inner(segs[0], d)])
        v.append(parse_cell(segs[1], arctic) if d == 1 else None)
        if d > 1:
            v[-1] = parse_cell(segs[1], arctic)
    return sym, (M, v)


def parse_log(path):
    text = open(path).read().splitlines()
    rules = []
    i = 0
    assert text[0].startswith('Rewriting system')
    reversed_ = 'reversed' in text[0]
    i = 1
    while text[i].startswith('  '):
        m = re.match(r'\s+(\S+) (->=|\|->|->) (\S*)', text[i])
        rules.append((m.group(1), m.group(3), m.group(2)))
        i += 1
    steps = []
    while i < len(text):
        m = re.match(r'(Natural|Arctic): dimension (\d+)', text[i])
        if not m:
            i += 1
            continue
        arctic = m.group(1) == 'Arctic'
        d = int(m.group(2))
        i += 1
        interp = {}
        while not re.match(r'\[\w\w+\]', text[i]):
            if re.match(r'\[\w\]: ', text[i]):
                sym, val = parse_symbol_block(text[i:i + d], d, arctic)
                interp[sym] = val
                i += d
            else:
                i += 1
        while not text[i].startswith('Relatively top-terminating rules'):
            i += 1
        i += 1
        removed = []
        while i < len(text) and text[i].startswith('  '):
            m2 = re.match(r'\s+(\S+) -> (\S*)', text[i])
            removed.append((m2.group(1), m2.group(2)))
            i += 1
        steps.append({'arctic': arctic, 'd': d, 'interp': interp, 'removed': removed})
    return reversed_, rules, steps


# ---------- aritmética ----------

def nat_comp(f, g):
    (A, a), (B, b) = f, g
    d = len(A)
    M = [[sum(A[i][j] * B[j][k] for j in range(d)) for k in range(d)] for i in range(d)]
    v = [sum(A[i][j] * b[j] for j in range(d)) + a[i] for i in range(d)]
    return M, v


def amax(x, y):
    if x is NEG:
        return y
    if y is NEG:
        return x
    return max(x, y)


def aplus(x, y):
    return NEG if x is NEG or y is NEG else x + y


def arc_comp(f, g):
    (A, a), (B, b) = f, g
    d = len(A)
    M = [[NEG] * d for _ in range(d)]
    v = [NEG] * d
    for i in range(d):
        for k in range(d):
            for j in range(d):
                M[i][k] = amax(M[i][k], aplus(A[i][j], B[j][k]))
        acc = a[i]
        for j in range(d):
            acc = amax(acc, aplus(A[i][j], b[j]))
        v[i] = acc
    return M, v


def word(interp, s, arctic):
    d = len(next(iter(interp.values()))[0])
    if arctic:
        f = ([[0 if i == j else NEG for j in range(d)] for i in range(d)], [NEG] * d)
    else:
        f = ([[1 if i == j else 0 for j in range(d)] for i in range(d)], [0] * d)
    comp = arc_comp if arctic else nat_comp
    for ch in s:
        f = comp(f, interp[ch])
    return f


def ge(x, y):  # x ≥ y
    if y is NEG:
        return True
    if x is NEG:
        return False
    return x >= y


def gg(x, y):  # x ≫ y (ártico estricto: > o ambos -∞)
    if x is NEG and y is NEG:
        return True
    if y is NEG:
        return True
    if x is NEG:
        return False
    return x > y


def check_step(rules_active, step):
    arctic, interp = step['arctic'], step['interp']
    removed = set(step['removed'])
    # monotonía débil ártica: M11 ≥ 0 o v1 ≥ 0
    if arctic:
        for s, (M, v) in interp.items():
            assert M[0][0] is not NEG or v[0] is not NEG, s
    for (l, r) in rules_active:
        (Ml, vl), (Mr, vr) = word(interp, l, arctic), word(interp, r, arctic)
        d = len(Ml)
        strict = (l, r) in removed
        for i in range(d):
            for j in range(d):
                if arctic and strict:
                    assert gg(Ml[i][j], Mr[i][j]), (l, r, 'M', i, j)
                else:
                    assert ge(Ml[i][j], Mr[i][j]), (l, r, 'M', i, j)
            if arctic and strict:
                assert gg(vl[i], vr[i]), (l, r, 'v', i)
            elif strict and i == 0:
                assert vl[0] > vr[0], (l, r, 'v0')
            else:
                assert ge(vl[i], vr[i]), (l, r, 'v', i)


def check(path):
    rev, rules, steps = parse_log(path)
    active = [(l, r) for (l, r, _) in rules]
    strict = {(l, r) for (l, r, k) in rules if k == '|->'}
    for st in steps:
        check_step(active, st)
        for rr in st['removed']:
            assert rr in strict, rr
            active.remove(rr)
            strict.discard(rr)
    assert not strict, strict
    return rev, rules, steps


def lean_val(x, arctic=False):
    if x is NEG:
        return '⊥'
    return f'WithBot.some {x}' if arctic else str(x)


def to_lean(name, steps):
    out = []
    for k, st in enumerate(steps):
        d = st['d']
        kind = 'AAff' if st['arctic'] else 'Aff'
        out.append(f'/-- `{name}`, paso {k + 1}: quita {", ".join(l + "→" + r for l, r in st["removed"])}. -/')
        out.append(f'def I_{name.replace("-", "_")}_{k + 1} : X → {kind} {d}')
        for s in 'abcdefg':
            M, v = st['interp'][s]
            a = st['arctic']
            Ms = ', '.join('![' + ', '.join(lean_val(x, a) for x in row) + ']' for row in M)
            vs = ', '.join(lean_val(x, a) for x in v)
            out.append(f'  | .{s} => ⟨![{Ms}], ![{vs}]⟩')
        out.append('')
    return '\n'.join(out)


# ---------- generación del archivo Lean de subsistemas ----------

T_RULES = ['ad', 'bd', 'ae', 'af', 'ag', 'be', 'bf', 'bg', 'ce', 'cf', 'cg']
RULE_NAME = {l: f'r{k + 1:02d}' for k, l in enumerate(T_RULES)}
PAPER = {'ad': 'f◁ → ◁', 'bd': 't◁ → 2◁', 'ae': 'f0 → 0f', 'af': 'f1 → 0t', 'ag': 'f2 → 1f',
         'be': 't0 → 1t', 'bf': 't1 → 2f', 'bg': 't2 → 2t', 'ce': '▷0 → ▷t', 'cf': '▷1 → ▷ff',
         'cg': '▷2 → ▷ft'}


def lean_subsystem(n, steps):
    """n = '01'..'11'. Devuelve definiciones + teorema `termIn_without_rNN`."""
    left = T_RULES[int(n) - 1]
    rn = RULE_NAME[left]
    out = [to_lean(f'T{n}', steps)]
    # cadena de eliminaciones, de adentro hacia afuera
    S = f'(fun ρ => ρ != .{rn})'
    lines = []
    for k, st in enumerate(steps):
        S1 = 'fun ρ => ' + ' || '.join(f'ρ == .{RULE_NAME[l]}' for l, _ in st['removed'])
        if st['arctic']:
            lines.append(f'  TermIn.removal_arc I_T{n}_{k + 1} (S₁ := {S1})\n'
                         f'    (by decide +kernel) (by decide +kernel) (by decide +kernel) <|')
        else:
            lines.append(f'  TermIn.removal_nat I_T{n}_{k + 1} (S₁ := {S1})\n'
                         f'    (by decide +kernel) (by decide +kernel) <|')
    lines.append('  termIn_noStart.mono (by decide)')
    out.append(f'/-- **`𝒯 ∖ {{{PAPER[left]}}}` termina** (sobre palabras canónicas). Certificado: '
               f'`proofs/collatz-T-{n}.log`. -/')
    out.append(f'theorem termIn_without_{rn} : TermIn {S} :=')
    out.append('\n'.join(lines))
    return '\n'.join(out) + '\n'


HEADER = '''import Collatz.Rewriting.{imp}

/-!
# Subsistemas de `𝒯` con certificados {kind}

Generado por `scripts/certs.py --gen <dir-proofs>` a partir de `proofs/collatz-T-NN.log` del
repositorio `github.com/emreyolcu/rewriting-collatz` (Yolcu–Aaronson–Heule, arXiv 2105.14697,
§4.3, Tabla 1). Las matrices se copian de los certificados; Lean las chequea con `decide +kernel`.

Para cada regla `ρ` de este archivo: `𝒯 ∖ {{ρ}}` termina sobre palabras canónicas. Esquema (el del
paper): se eliminan las reglas de inicio `ℬ` en 1 a 3 pasos con interpretaciones débilmente
monótonas, y lo que queda está contenido en `𝒯 ∖ ℬ`, que termina (`termIn_noStart`).
-/

namespace SRS

set_option maxRecDepth 20000

'''


def gen(pdir):
    for fname, imp, kind, ns in [('SubsystemsNat', 'Natural', 'naturales', ['01', '02', '03', '04', '05', '09', '10']),
                                 ('SubsystemsArc', 'Arctic', 'árticos', ['06', '07', '08', '11'])]:
        body = ''
        for n in ns:
            _, _, steps = check(f'{pdir}/collatz-T-{n}.log')
            body += lean_subsystem(n, steps) + '\n'
        open(f'Collatz/Rewriting/{fname}.lean', 'w').write(HEADER.format(imp=imp, kind=kind) + body + 'end SRS\n')
        print(f'Collatz/Rewriting/{fname}.lean escrito')
    # Farkas (sistema invertido; las condiciones en Lean usan `ρ.lhs.reverse`, `ρ.rhs.reverse`)
    _, _, steps = check(f'{pdir}/farkas.log')
    hdr = '''import Collatz.Rewriting.Arctic

/-!
# Certificado de Farkas

Generado por `scripts/certs.py --gen <dir-proofs>` a partir de `proofs/farkas.log` del repositorio
`github.com/emreyolcu/rewriting-collatz` (Yolcu–Aaronson–Heule, §4.2, ecuación (9) y Apéndice B).
Interpretación ártica de dimensión 5 para el sistema **invertido** `ℱ^rev`. Se usa en
`Collatz.Rewriting.Farkas`.
-/

namespace SRS

'''
    open('Collatz/Rewriting/FarkasCert.lean', 'w').write(hdr + to_lean('farkas', steps) + 'end SRS\n')
    print('Collatz/Rewriting/FarkasCert.lean escrito')


if __name__ == '__main__' and sys.argv[1] == '--gen':
    gen(sys.argv[2])
elif __name__ == '__main__':
    pdir, name = sys.argv[1], sys.argv[2]
    rev, rules, steps = check(f'{pdir}/{name}.log')
    print(f'-- {name}: {len(steps)} pasos, ' + ', '.join(
        ('ártico' if s['arctic'] else 'natural') + f' d={s["d"]}' for s in steps) + ', chequeo Python OK')
    if '--lean' in sys.argv:
        print(to_lean(name, steps))
