# Idea: vecinos de 𝒯 como banco de prueba para certificados de terminación

**Estado:** viva; filtro formalizado (2026-11-21)
**Frente:** ambos (vía reescritura, Fase 4)

## Enunciado
En el sistema `𝒯` de Yolcu–Aaronson–Heule la única regla que "sabe" que el mapa es `3x+1` es
la dinámica `t◁ → 2◁`: lleva `2y+1` a `3y+2`. Si se cambia sólo su lado derecho por `e◁`, con el
mismo alfabeto y los mismos lados izquierdos, el sistema simula `x ↦ (3x + 2e − 3)/2` en los impares:

| `e` | mapa en impares | ciclos |
|---|---|---|
| 2 | `(3x+1)/2` (Collatz) | ¿? |
| 1 | `(3x−1)/2` | sí (5→7→10→5, ciclo de 17, …) |
| 0 | `(3x−3)/2` | sí (punto fijo 3) |

**Principio:** un certificado de `SN(ρ/𝒯)` no puede servir también para un vecino con ciclos que use
`ρ` infinitas veces. En un álgebra monótona ordenada, eso obliga a que el certificado oriente
`t◁ ≥ 2◁` y **no** oriente `t◁ ≥ 1◁` ni `t◁ ≥ 0◁`.

## Filtro de barreras
- ¿Falla para 5n+1? Es la versión fina de esta pregunta: el vecino comparte alfabeto y 10 de 11 reglas.
- ¿Usa n > 0? Los vecinos también trabajan sobre palabras `▷w◁` (positivos); los ciclos de `3x−1`
  son los de `3x+1` en los negativos. Un certificado tiene que distinguir el signo de alguna manera.
- Lo demás no aplica: es un filtro de técnicas, no un argumento.

## Literatura
Que una prueba tenga que distinguir `3x+1` de `3x−1` es folklore. No encontré el uso explícito de los
vecinos *en la misma signatura* contra los certificados de YAH. Falta revisar en detalle a Nashida (2026).

## Evidencia numérica
- `scripts/neighbors.py`: genera la familia (binario + dígitos `a`-arios, `x ↦ (ax+c)/2`), chequea la
  semántica de las reglas de forma exhaustiva en palabras de hasta 5 letras y explora el grafo de
  reescritura desde `▷bin(n)◁`, `n < 200`.
  - Para `e = 1` y `e = 0`, **las 11 reglas aparecen en ciclos**. Por lo tanto `SN(ρ/vecino)` es falso
    para todo `ρ`: en los vecinos no se puede eliminar ninguna regla.
  - Para `e = 1` hay reglas sin las cuales no se encontraron ciclos: `f◁`, `t◁`, `f1`, `t1`, `▷0`, `▷2`.
    En cambio, `𝒯⁻ ∖ {f0}`, `∖{f2}`, `∖{t0}`, `∖{t2}` y `∖{▷1}` siguen teniendo ciclos.
- `scripts/neighbor_matrix.py` (z3): ¿orientar débilmente `𝒯` con matrices naturales (forma EWZ) obliga a
  orientar débilmente la regla vecina?
  - `d = 1`: **sí** (unsat con entradas ≤ 4, para `e = 1` y `e = 0`).
  - `d = 2` y `d = 3`: **no** (sat; aparecen modelos que separan).

- `scripts/neighbor_classes.py` (z3): filtro de clases de certificados correctas para terminación relativa.
  `sep e` pregunta si la clase puede orientar débilmente `𝒯` sin orientar `t◁ → e◁` (si no puede, la clase
  queda descartada); `rm ρ` pregunta si puede orientar débilmente `𝒯` y estrictamente `ρ`.
  - Matrices EWZ sobre `ℚ≥0` / `ℝ≥0`, `d = 1`, **sin cota en los coeficientes**: `sep` unsat para `e = 1` y
    `e = 0`, y `rm` unsat para las 11 reglas. z3 decide la aritmética real no lineal, así que es un teorema
    (no formalizado en Lean): toda interpretación afín de dimensión 1 que orienta `𝒯` orienta a los vecinos.
  - Polinomios de una variable, grado ≤ 2, coeficientes en `[0, 3]`: `sep` unsat ⇒ descartados en esa cota.
  - Matrices EWZ sobre `ℚ≥0`, `d = 2`: z3 no decide nada en 120 s por consulta (`unknown` en las 13).
    `sep` es sat de todos modos, porque los modelos naturales de `neighbor_matrix.py` también son racionales:
    el filtro **no** descarta esta clase, y `rm` queda abierto (hace falta otro solver o un encoding mejor).
  - Matrices EWZ **racionales** con entradas `k/D` (`scripts/rational_search.py`, encoding entero con matrices
    aumentadas): `d = 2`, `(D, B) ∈ {(2, 4), (3, 6), (2, 8)}`: `rm ρ` **unsat para las 11 reglas** (33 consultas).
    Ninguna interpretación racional chica elimina una regla. (Con matrices enteras y vectores racionales se
    reescala a una natural, así que lo nuevo exige matrices fraccionarias; ese es el caso que cubre la búsqueda.)
- Dimensión 1 sobre `ℝ≥0`, a mano: las reglas fuerzan `m₀ ≥ m_t ≥ m₂ ≥ m_f m_t` ⇒ `m_f = 1` ⇒ todos los
  factores de los dígitos valen 1; con traslaciones, `v_f = v_t`, `v₀ = v₁ = v₂ = c`, inicio ⇒ `c ≥ 2b`,
  `t◁ → 2◁` ⇒ `b ≥ c` ⇒ todo 0. Ninguna regla es estricta, y la vecina queda orientada de forma trivial.

## Formalización
`Collatz/Rewriting/Neighbors.lean`:
- la familia `𝒯ₑ` (`NStep e`) sobre el alfabeto completo, con `nstep_d2_iff : NStep .d2 ↔ WStep`
  (para `e = 2` es exactamente `𝒯`);
- un chequeador verificado de derivaciones (`checkWalk`, `isStep_sound`);
- `not_relSN_d1`, `not_relSN_d0`: para toda regla `ρ`, `SN(ρ/𝒯₁)` y `SN(ρ/𝒯₀)` son falsos. Los ciclos tienen
  315 pasos (desde `▷22◁`, valor 17) y 392 pasos (desde `▷220◁`), los chequea `decide +kernel` y una prueba
  de mutación confirma que un paso alterado se rechaza.

## Por qué falló / qué aprendimos
La hipótesis "la barrera de Nashida sale de los ciclos de `3x−1`" es **falsa** para dimensión ≥ 2: orientar
débilmente `𝒯` no fuerza orientar el vecino. Su barrera usa algo más que la existencia de vecinos cíclicos.
Lo que queda en pie es el filtro: toda técnica nueva tiene que fallar en `e = 0, 1`, y esos sistemas sirven
para descartar técnicas en segundos antes de buscar certificados para `𝒯`.

Las matrices racionales están fuera del alcance de Nashida (README de su repo, sección "Scope": "rational, real and
polynomial interpretations" no cubiertas), pero la búsqueda no encontró nada en las cotas probadas. Es lo esperable:
eliminar `t◁ → 2◁` equivale a una función potencial, calculada por un autómata con pesos, que baja en cada paso impar
de toda órbita, o sea a probar Collatz, y eliminar las demás implica enunciados profundos sobre ciclos hipotéticos.
**Conclusión (2026-11-21): frente de reescritura en pausa; se pasa a ciclos.**
