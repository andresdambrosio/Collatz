# Estrategia

Plan vigente (2026-09-11). Dos subproblemas, tres tramos en ciclos, constraints en divergencia.
Lo que sigue distingue *escalera* (pasos mecánicos o de plomería, sin ideas nuevas) de *muro*
(lo que la literatura no sabe hacer). Al muro no se le tiran ciclos de agentes.

## Ciclos (`NoSyracuseCycles`)

**Tramo 1 — HECHO (2026-09-13).** `k12_syracuse_cycle_length_ge`: incondicional `k ≥ 2301`.
`VerifiedBelow 600001` probado en el kernel (24 bloques de `decide +kernel`) + sándwich con
`N = 600001`. Mejorar: `N = 10^6` da `k ≥ 2966` por ~4 min más; rendimiento logarítmico.

**Tramo 2 — HECHO (2026-09-12).** `hercher_lower_bound`: `VerifiedBelow (2^71) → k ≥ 72 057 431 991`.
Sin fracciones continuas de reales: lema unimodular con dos convergentes consecutivos certificados
por los 25 dígitos de `Log23.lean`. Límite exacto del método `k = q₂₁ + q₂₂`; para mejorar hace
falta `M` mayor o la estructura de Eliahou/Simons–de Weger de los elementos del ciclo.

**Tramo 3 — muro.** De `k ≥ 10^11` a "ninguno" requiere formas lineales en logaritmos (no en
Mathlib) y, aun con eso, el caso general está abierto (Simons–de Weger cubren `m ≤ 91` picos).
No hay ruta conocida. Se documenta, no se ataca.

## Divergencia (`NoDivergence`)

No hay escalera: Tao es probabilístico. La única vía honesta es acumular constraints sobre una
órbita divergente hipotética en el mismo sistema formal y buscar que dos choquen.

Tenemos: → ∞ (`syracuse_eventually_ge_of_divergent`), densidad de doses `≤ log₂3`
(`divergent_dose_density`), exponentes aperiódicos (`sExp_not_periodic_of_divergent`), cota de
repeticiones (`divergent_repeat_bound`).

Próximas:
1. **Terras en Syracuse.** El patrón de exponentes de `j` pasos determina `x mod 2^{A(j)}`.
   Convierte patrones en clases residuales.
2. **Conteo.** Los patrones con densidad `≤ log₂3` son una fracción `2^{−cA}` de las clases
   mod `2^A`: una órbita divergente vive en un conjunto de densidad cero de clases residuales.
   Es la heurística estándar de por qué la conjetura es cierta; convertirla en contradicción es
   lo que nadie sabe hacer. Si sale algo nuevo del proyecto, sale de acá.
3. Traducción a `T` (`divergent_odd_density_T`): plomería, pero es la formulación que la
   literatura reconoce.

## Orden

1. Tramo 1 de ciclos.
2. Terras + conteo en divergencia.
3. Tramo 2 de ciclos.
4. En paralelo: PR a Mathlib con lo elemental (ecuación del ciclo, sándwich, paridad periódica
   ⇒ ciclo, `k ≤ 4`). Revisión externa gratis y contribución permanente.

## Regla

El blueprint nunca contiene un lema que sea "resolver el muro" disfrazado. Si un enunciado
necesita Baker o un argumento determinista de divergencia, se marca `muro` en `notes` y no se
despacha al formalizer.
