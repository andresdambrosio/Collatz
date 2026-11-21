# Prior art formalizado (Lean/Isabelle/Coq/Agda/HOL/Metamath/Mizar)

Búsqueda sistemática (WebSearch + WebFetch, 13-sep-2026) de qué de lo que CollatzForge
necesita/tiene ya existe formalizado en otro lado. Convención: **verificado** = abrí la
página/repo (WebFetch o `curl`) y leí contenido real; **visto en búsqueda** = solo aparece
en el resumen de resultados de WebSearch, no lo abrí directamente — tratar con más cautela.

Estado: completo para las fuentes alcanzables por búsqueda web en una sesión. No hallé
Coq/Rocq, Agda, HOL, Metamath ni Mizar con contenido real de Collatz (ver sección
correspondiente) — el ecosistema formalizado vive casi enteramente en Lean 4.

## Hallazgo que reencuadra todo lo demás

El estado del arte formalizado avanzó mucho más de lo que `CLAUDE.md`/`docs/known.md`
asumen. Hay al menos **tres proyectos de Lean 4 activos, independientes de CollatzForge,
que cubren gran parte de los ítems 2, 4, 5, 6, 8 y 9** de esta búsqueda, con resultados
más fuertes que los nuestros en varios puntos (ciclos cortos, densidad, complejidad de
palabras). Ver `msharpe248/collatz` abajo — es el más directamente competitivo.

También confirmé que **Mazur 2026 / ProofAtlas existe y es real** (no es una alucinación
de `CLAUDE.md`), y que la formulación exacta de "fracción positiva llega a 1 en tiempo
logarítmico" no es la única pieza: hay además dos resultados más fuertes ya *aceptados*
(no solo pendientes) — ver sección dedicada.

## Tabla por ítem

| # | Ítem | Qué existe | Dónde | Hipótesis externas | Veredicto |
|---|---|---|---|---|---|
| 1 | Definiciones básicas, ciclo trivial, reducción no-ciclos∧no-divergencia⇒conjetura | Misma descomposición en 2 mitades, pero como `axiom`s sin probar (no como `def : Prop` explícito) | `cognitivecomputations/collatz` (verificado) | `axiom no_non_trivial_S_cycles`, `axiom no_divergence` | existe parcialmente (mismo shape, no la disciplina de CollatzForge) |
| 2 | Ecuación del ciclo de Syracuse, cota 3^k < 2^A | `cycle_three_pow_lt` (msharpe248, verificado); "Böhm–Sontacchi cycle equation... proved for all parameters" (ccchallenge, visto en búsqueda, no abierto el repo puntual) | `msharpe248/collatz` `lean/Collatz/Cycles.lean`; ccchallenge.org (Böhm–Sontacchi 1978) | ninguna (Lean puro, sin axiomas no estándar) | existe |
| 3 | Cota Eliahou 2^A/3^k ≤ (1+1/(3N))^k, forma exacta | No encontré esa desigualdad en esa forma exacta en ningún repo. `msharpe248` cita Eliahou 1993 en bibliografía pero su cota análoga (`terras_growth_bound`) tiene otra forma algebraica; `ericmerle3789/collatz-conditional-cycles` lista "Eliahou-Steiner" como *estudio activo, no cerrado* | — | — | **no encontrado en esa forma exacta** (nuestro `cycle_sandwich`/`ascent_bound` parece ser la única formalización de precisamente esta desigualdad) |
| 4 | Vector de paridad eventualmente periódico ⇒ órbita periódica (Lagarias 1985) | `divergent_itinerary_aperiodic` (contrapositiva: divergente ⇒ itinerario nunca eventualmente periódico) | `msharpe248/collatz` `lean/Collatz/Rung1.lean` (verificado) | ninguna declarada | existe (independiente de nuestro `ParityAperiodic.lean`, mismo resultado) |
| 5 | Terras: vector de paridad de k pasos ↔ clase residual mod 2^k | `parity_of_modEq`/`modEq_of_parity` (equivalencia exacta) + `card_oddSteps` (exactamente `C(k,j)` residuos con `j` pasos impares) | `msharpe248/collatz` `lean/Collatz/Parity.lean`, `Terras.lean` (verificado); Terras 1976 listado como "being formalized" en ccchallenge.org (visto en búsqueda) | ninguna | existe |
| 6 | Inexistencia de ciclos cortos (k ≤ 11 o equivalente) | `cycle_check_183`: sin ciclo no trivial con ≤ 183 "halvings", verificado por `decide +kernel` | `msharpe248/collatz` `lean/Collatz/Cycles.lean` (verificado) | ninguna | existe, **más fuerte que la nuestra** (183 vs. nuestro k ≤ 11; ojo: su métrica es "halvings" T, no necesariamente el mismo conteo que nuestro k de pasos de Syracuse — no verifiqué la equivalencia exacta de métricas) |
| 7 | Cotas Hercher/Eliahou/Simons–de Weger condicionales a verificación computacional | `DerivedLargeKBound`: `k > 1322 ⇒ n < 2^71`, condicional a `BarinaVerification` **y además** a `BakerSeparation` (fortalecimiento de Rhin/Wu/Salikhov, **no demostrado**, declarado como conjetura de trabajo) | `ericmerle3789/collatz-conditional-cycles` (github.com/ericmerle3789/collatz-conditional-cycles), DOI Zenodo 10.5281/zenodo.19790406 (verificado vía collatz-lab.org) | `BakerSeparation` (conjetura), `BarinaVerification` (Barina 2025, igual que nuestra `VerifiedBelow`), `DerivedLargeKBound` (no es teorema publicado, derivación propia del proyecto) | existe pero **más débil y menos autocontenida que la nuestra**: nuestro `hercher_lower_bound` da `k ≥ 72 057 431 991` solo desde `VerifiedBelow 2^71`, sin conjeturar nada tipo Baker (via `cf_unimodular_gap`); este proyecto externo necesita además una forma de Baker no probada para llegar a un umbral ~65 millones de veces menor |
| 8 | Constraints sobre órbitas divergentes (densidad ≥ log2/log3, aperiodicidad, conjunto fino) | `no_descent_dichotomy` (densidad de pasos impares > log₂/log₃), `divergent_itinerary_aperiodic`, `shadow_compression`/`density_floor` (confinamiento ~4.5% del espacio de residuos) | `msharpe248/collatz` `Density.lean`, `Rung1.lean`, `Shadow.lean` (verificado) | ninguna declarada | existe, con maquinaria adicional (Sturmian/word-complexity) que nosotros no tenemos |
| 9 | Cotas certificadas de log₂3 en un asistente de prueba | Constante `log₂/log₃ ≈ 0.63093` fijada y usada como "sharp" en el no-go y en la dicotomía de densidad | `msharpe248/collatz` (verificado, sin precisión de dígitos confirmada) | ninguna | existe en al menos 2 lugares independientes (ahí y en CollatzForge, `log2_3_gt`/`log2_3_lt` a 25 dígitos) |
| 10 | Cota entrópica C(n,k) ≤ 2^{nH(k/n)} formalizada | El **hecho puntual** `binEntropy p < log 2 ↔ p ≠ 1/2` (exactamente nuestro `entropyConst_lt_one`) **ya está en Mathlib** como `Real.binEntropy_lt_log_two`, en `Mathlib.Analysis.SpecialFunctions.BinaryEntropy`. La **conexión combinatoria** `Nat.choose n k ≤ exp(n·H(k/n))` no aparece en Mathlib ni en los repos relevados (msharpe248 tiene solo la identidad exacta `card_oddSteps = C(k,j)`, no la cota entrópica) | Mathlib4 docs (verificado) | — | **existe parcialmente**: la pieza analítica (`binEntropy < log 2`) está upstream — deberíamos citarla en vez de reprobarla si no lo hacemos ya —, la pieza combinatoria (`choose_le_exp_binEntropy`) parece original nuestra |

## Repos relevados

| Repo | Qué es | Hipótesis/axiomas | Compila | Actividad | Licencia | Estado de verificación |
|---|---|---|---|---|---|---|
| [`msharpe248/collatz`](https://github.com/msharpe248/collatz) | El más solapado con CollatzForge: ciclos cortos (T≤183), Terras, densidad KL (exponente 0.8676, supera Krasikov–Lagarias 2003 x^0.84), no-go de certificados de descenso, exclusiones Sturmianas | Solo `propext`/`Classical.choice`/`Quot.sound`; **una excepción explícita**: `no_small_terras_cycle` usa el rango verificado computacionalmente 2^71 (Barina) como hipótesis explícita, igual que nuestra `VerifiedBelow`. También asume el teorema de las tres distancias en `Sturmian.lean` | Sí (`lake build`, cache de Mathlib) | Activo, commits de sep-2026 | MIT | verificado (WebFetch + `curl` a README y árbol de archivos) |
| [`ericmerle3789/collatz-conditional-cycles`](https://github.com/ericmerle3789/collatz-conditional-cycles) (sitio: [collatz-lab.org](https://collatz-lab.org/)) | Teorema condicional: no hay ciclo no trivial de Collatz salvo por 3 hipótesis externas documentadas | `BakerSeparation` (conjetura de trabajo, fortalecimiento de Rhin/Wu/Salikhov, **no probada**), `BarinaVerification` (n < 2^71), `DerivedLargeKBound` (derivación propia, no publicada) | Sí, `lake build Delta11Salikhov PASS`, 0 sorry/admit | Última validación 2026-05-08; preprint Zenodo v1.1, DOI 10.5281/zenodo.19790406 | no verificada explícitamente | verificado (WebFetch a collatz-lab.org) |
| [`johnjanik/syracuse-confinement`](https://github.com/johnjanik/syracuse-confinement) | Reducción de la conjetura completa a 9 axiomas (Baker, Rhin, Hercher, Matveev, Furstenberg, etc.) + 6 `sorry` | 9 axiomas + 6 sorrys, el más crítico una cota lineal de ν₃ sin probar | Sí (12 947 líneas, 45 archivos) | **Deprecado**, consolidado en un repo sucesor `collatz_lean` no explorado aquí | MIT | verificado (WebFetch) |
| [`cognitivecomputations/collatz`](https://github.com/cognitivecomputations/collatz) | Blueprint formal, misma descomposición en 2 mitades que nuestro `Main.lean`, pero cerrado con 2 `axiom`s sin probar en vez de hipótesis explícitas | `axiom no_non_trivial_S_cycles`, `axiom no_divergence` | no confirmado | no confirmada | no confirmada | verificado parcialmente (WebFetch, sin abrir el `.lean` fuente) |
| [`xrchz/CollatzLean`](https://github.com/xrchz/CollatzLean) | **No es prior art válido.** Afirma refutar la conjetura (`Collatz.not_conjecture`, `Collatz.exists_nonterminating_orbit`) explotando un bug real del kernel de Lean 4 en tipos inductivos anidados con parámetros fantasma (issue [leanprover/lean4#14576](https://github.com/leanprover/lean4/pull/14577), parcheado en 1 hora tras el reporte de Kiran Gopinathan, jul-2026). El autor real es Ramana Kumar. Pasó incluso el chequeador independiente `nanoda` porque este tampoco validaba el nombre de tipo en un nodo de proyección | — (la "prueba" es inválida) | posiblemente ya no compila tras el parche del kernel | fue noticia ~25-28 jul 2026, luego invalidado | — | verificado (postmortem de Leonardo de Moura + PR de fix, ambos leídos) |
| ccchallenge.org (proyecto, no un solo repo) | "Formalizando la literatura de Collatz, un paper a la vez": Terras 1976, Böhm–Sontacchi 1978 (formalizado), Eliahou 1993, Hercher 2023, Bernstein–Lagarias 1996, Krasikov–Lagarias 2003, Tao 2022, RozierTerracol 2025, EliahouVergerGaugry 2025, Knight 2026 (en progreso) | por paper | 1/367 papers formalizado, 4 en progreso, 6 listos para auditoría (a fecha de la búsqueda) | activo (mantenido por Tristan Stérin / cosmo) | no verificada | verificado el sitio (WebFetch); **no encontré** los repos individuales de cada formalización (el repo `ccchallenge-org/ccchallenge` en GitHub es el backend web del sitio, no las pruebas Lean) |

## Mazur 2026 / ProofAtlas — verificación

**Existe y es real** (WebFetch directo a proofatlas.ai). Contrario a lo que sugiere
`CLAUDE.md` ("una fracción positiva... el más fuerte después de Tao"), hay **más de un
resultado**, y algunos ya superan en fuerza al que se cita:

| Resultado | Enunciado | Estado |
|---|---|---|
| Positive-density log-time | ∃ c>0, X₀: ≥ cX enteros < X llegan a 1 en ≤ (523/50)·ln n pasos de Collatz | Lean-checked, **revisión de aceptación aún pendiente** (no es el más fuerte) |
| Natural-density log-time descent | densidad natural 1 (no solo positiva) desciende en ≤ 436·log N pasos (variante Syracuse: 145·log N) | **aceptado**, 599 archivos Lean / 182 625 líneas — supera en alcance a Tao 2019/2022 |
| Tao's almost-bounded orbits (reformalización) | densidad logarítmica 1 alcanza valor acotado | **aceptado**, 397 archivos / 124 019 líneas |
| Collatz predecessor lower bounds, exponente 0.90 | `x^0.9 ≤` cantidad de predecesores de cualquier objetivo no divisible por 3 | **aceptado** 19-jul-2026, supera Krasikov–Lagarias 2003 (0.84) |
| Positive lower density of predecessors | todo objetivo fijo (no div. por 3) tiene predecesores de densidad natural inferior positiva | **aceptado** |
| Terras log-time power-saving | ≤ `10^7 · N^(-1/100)` fracción no desciende en ≤ log n pasos acelerados | **aceptado**, 20 archivos / 2511 líneas |

Todos declaran solo `propext, Classical.choice, Quot.sound` (sin axiomas ad-hoc), según las
páginas de ProofAtlas — no verifiqué el `#print axioms` yo mismo, así que esto queda como
**visto en búsqueda/WebFetch de la página del proyecto, no auditado independientemente**.
Ninguno prueba la conjetura completa; todos lo dicen explícitamente.

## Qué de CollatzForge parece no tener precedente formalizado

- **Item 3, la desigualdad de Eliahou en su forma exacta** `2^A/3^k ≤ (1+1/(3N))^k`
  (nuestro `cycle_sandwich`). Ningún repo relevado la tiene en esa forma algebraica precisa,
  aunque varios (msharpe248, ericmerle3789) trabajan con cotas equivalentes en espíritu.
- **El lema de Hercher sin Baker**: nuestro `hercher_lower_bound` (k ≥ 72 057 431 991 desde
  solo `VerifiedBelow 2^71`, vía `cf_unimodular_gap`, sin conjeturar ninguna forma de Baker)
  parece más fuerte y más autocontenido que el único condicional equivalente encontrado
  (`ericmerle3789`, k > 1322, que además de la verificación computacional necesita una
  conjetura de tipo Baker no probada).
- La **combinación** cota entrópica + densidad de Syracuse tal como aparece en
  `entropy_bound` + `divergent_odd_density_T` de CollatzForge (conteo de clases residuales
  vía `Nat.choose` acotado por la entropía binaria) — la pieza analítica de la entropía
  ya está en Mathlib, pero la puente con el conteo de clases de Terras no la vi en ningún
  otro repo.

## Qué ya existía (y dónde)

- Ecuación del ciclo de Syracuse y `3^k < 2^A`: `msharpe248/collatz`, y (visto en búsqueda,
  no verificado el repo puntual) Böhm–Sontacchi 1978 formalizado vía ccchallenge.org.
- Terras (paridad ↔ residuos mod 2^k) y el conteo binomial exacto: `msharpe248/collatz`
  (`Parity.lean`, `Terras.lean`).
- Aperiodicidad del itinerario de una órbita divergente (Lagarias 1985, contrapositiva):
  `msharpe248/collatz` `Rung1.lean` — resultado idéntico en espíritu a nuestro
  `ParityAperiodic.lean`, hecho de forma independiente.
- No ciclos cortos, con un alcance mucho mayor (T ≤ 183 vía kernel `decide`) que nuestro
  k ≤ 11: `msharpe248/collatz` `Cycles.lean`.
- Densidad de pasos impares ≥ log₂/log₃ para divergentes, y conjunto fino/confinamiento:
  `msharpe248/collatz` `Density.lean`, `Shadow.lean` — con maquinaria extra (Sturmian) que
  nosotros no tenemos.
- `binEntropy p < log 2 ↔ p ≠ 1/2`: ya en Mathlib (`Real.binEntropy_lt_log_two`,
  `Mathlib.Analysis.SpecialFunctions.BinaryEntropy`) — deberíamos evaluar si
  `entropyConst_lt_one` puede derivarse de ahí en vez de reprobarse desde cero.
- Cotas Hercher/Eliahou/Simons–de Weger condicionales a verificación computacional:
  `ericmerle3789/collatz-conditional-cycles`, pero más débiles (k > 1322) y menos
  autocontenidas (necesitan una conjetura tipo Baker) que la nuestra.
- Mazur 2026/ProofAtlas: confirmado real, con más resultados de los que `CLAUDE.md` cita,
  algunos ya *aceptados* y más fuertes (densidad natural 1, no solo positiva).
- La reducción "no ciclos ∧ no divergencia ⇒ conjetura" como decomposición en 2 mitades:
  `cognitivecomputations/collatz`, pero con `axiom`s sin probar en lugar de la disciplina
  de hipótesis explícitas de CollatzForge (regla dura 2 de `CLAUDE.md`).

## Fuera de Lean 4: casi nada encontrado

- **Isabelle/AFP**: sin entradas de Collatz en isa-afp.org (búsqueda directa 404, y
  `site:isa-afp.org collatz` solo devuelve una mención de paso en un paper sobre funciones
  parciales mutuamente recursivas, no una formalización de Collatz).
- **Coq/Rocq**: no encontré un repo real y específico (los resultados de búsqueda sobre
  "coq collatz" devolvieron generalidades de Coq/Rocq y un formalismo de coalgebras de
  streams mencionado de pasada, sin repo identificado).
- **Agda**: nada específico; solo mención de que Cubical Agda "podría" servir para
  coalgebras finales, sin repo concreto.
- **Metamath/HOL/Mizar**: sin resultados relevantes en ninguna búsqueda.
- Conclusión: el ecosistema de formalización activa de Collatz está, a día de hoy,
  concentrado casi enteramente en Lean 4 (+ Mathlib), con ProofAtlas como plataforma nueva
  relevante.

## Advertencia sobre repos "prueba completa" que reducen a axiomas no probados

Confirma la advertencia de `CLAUDE.md`:
- `cognitivecomputations/collatz`: 2 axiomas sin probar.
- `johnjanik/syracuse-confinement`: 9 axiomas + 6 `sorry`, deprecado.
- `ericmerle3789/collatz-conditional-cycles`: honesto sobre sus 3 hipótesis, pero una de
  ellas (`BakerSeparation`) es una conjetura no demostrada, no solo una hipótesis
  computacional verificable como `VerifiedBelow`.
- `xrchz/CollatzLean`: no reduce a axiomas — explota directamente un bug del kernel. El
  caso más grave: pasó *sorry-free* y *axiom-free* por un bug real, no por una hipótesis
  declarada. Recordatorio de que "sorry-free" y "sin axioma" no bastan; hace falta que el
  kernel mismo esté sano (el bug ya está parcheado en Lean 4, PR leanprover/lean4#14577).

## Referencias verificadas vs. solo vistas en búsqueda

**Verificadas (WebFetch/curl, contenido real leído):** ccchallenge.org (home), proofatlas.ai
(research/advances/formalizations + 5 páginas de resultados individuales), postmortem de
Leonardo de Moura sobre el bug del kernel, PR leanprover/lean4#14577, `msharpe248/collatz`
(README completo + árbol de archivos vía API de GitHub), `ericmerle3789/collatz-conditional-cycles`
vía collatz-lab.org, `johnjanik/syracuse-confinement`, `cognitivecomputations/collatz`,
`xrchz/CollatzLean`, Mathlib4 docs de `BinaryEntropy`.

**Solo vistas en resultados de búsqueda (no abiertas):** el repo puntual de la formalización
de Böhm–Sontacchi 1978 dentro de ccchallenge (no identifiqué su URL exacta), el listado
completo de "10 repositorios de 6 contribuyentes" de ccchallenge, y varios repos de "prueba
completa" de baja credibilidad que aparecieron en las búsquedas (`AIDoctrine/CollatzLayerA`,
`Kobayashi2501/ak-collatz-collapse`, `twigglits/collatz-conjecture--expansion`) — no los
abrí porque el patrón de nombre ("proof candidate", "structural collapse") coincide con el
tipo de repo que `CLAUDE.md` ya pide tratar con sospecha; si se necesitan sus axiomas
exactos, hay que abrirlos antes de citarlos.
