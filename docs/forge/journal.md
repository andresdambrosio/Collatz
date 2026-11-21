# Bitácora de investigación

Cronológica. Cada entrada la escribe el scribe (`Agents/scribe.py`) al cierre de un `run`,
o un humano/Claude Code cuando el ciclo se hizo a mano. Objetivo permanente: probar
`Collatz.CollatzConjecture` en `Collatz/Main.lean` con `verify.sh` en verde.

## 2026-09-11 — Scaffold y reducción a dos subproblemas

**Probado**
- `collatz_of_noCycles_noDivergence` (`Main.lean`): `NoNontrivialCycles → NoDivergence → CollatzConjecture`. Órbita acotada ⇒ cae en un ciclo (`Finite.exists_ne_map_eq_of_infinite` sobre `Fin (B+1)`) ⇒ el ciclo es el trivial ⇒ pasa por 1. Solo axiomas estándar.
- `Basic.lean`: `oddPart_odd`, `two_pow_nu2_mul_oddPart`, `oddPart_two_mul`, `oddPart_of_odd` vía `Nat.ordCompl` y `Nat.factorization_def`.

**Aprendido**
- `padicValNat` no reduce en el kernel: `decide` falla en `nu2`/`oddPart`/`syracuse` con valores concretos. Para eso hay que reescribir con `oddPart_two_mul` + `oddPart_of_odd`. `collatz` y `T` sí reducen con `decide`.
- Los subproblemas abiertos van como `def … : Prop` e hipótesis explícitas, no como `axiom`: `#print axioms` queda limpio y el día que se prueben, `Main.lean` se instancia sin tocar nada.
- `lake build` acepta `sorry` con exit 0 (solo warning). El verifier grepea el archivo además de compilar.

## 2026-09-11 — Primer ciclo: tres lemas del blueprint, a mano

Ciclo hecho por Claude Code en sesión interactiva (sin API key todavía), siguiendo el protocolo del orquestador: archivo en `Collatz/Invariants/`, build del módulo, build global, `verify.sh`, YAML, import.

**Probado**
- `orbitBounded_of_reachesOne` (`OrbitBoundedOfReachesOne.lean`): `ReachesOne n → OrbitBounded n`. Cota `max (Finset.sup (range k) (collatz^[·] n)) 4`; la órbita de 1 vive en `{1,4,2}` (`iterate_one_mem`, inducción + `decide`). Compiló al primer intento.
- `isPeriodic_iff_T_of_odd` (`IsPeriodicIffT.lean`): para `n` impar, `IsPeriodic n ↔ ∃ k > 0, T^[k] n = n`. Además `isPeriodic_of_T_periodic` para todo `n`. Técnica: invariante de seguimiento `∃ k, T^[k] n = collatz^[j] n ∨ T^[k] n = collatz^[j+1] n`, con contadores `j ≤ 2k` (garantiza `k > 0`) y la marca "en el segundo caso `collatz^[j] n` es par" (descarta ese caso cuando `j = 2m` devuelve `n` impar). Dos intentos: `← Function.iterate_succ_apply'` falla como rewrite (patrón con metavariables); hay que reescribir hacia adelante con `(f := T)` / `(f := collatz)` explícitos.
- `syracuse_cycle_equation` (`SyracuseCycleEquation.lean`): identidad de órbita en ℕ `syracuse^[k] n · 2^{A_k} = 3^k n + Σ_{i<k} 3^{k-1-i} 2^{A_i}` con `A_i = sExpSum n i` (inducción, `calc` + `ring`, `Finset.sum_range_succ`, `mul_add`, `Finset.mul_sum`, `sum_congr` con `omega` para `k+1-1-i = (k-1-i)+1`). Corolarios: la ecuación del ciclo en ℤ (`push_cast` + `linarith`) y `two_pow_gt_three_pow_of_cycle`: en un ciclo de `k > 0` pasos, `3^k < 2^{A_k}` (`Finset.sum_pos` + `Nat.lt_of_mul_lt_mul_left`). Dos intentos: `mul_sum` necesita `mul_add` antes.

**Fallido / descartado**
- El enunciado del blueprint `0 < n → (IsPeriodic n ↔ T-periódico)` es **falso**: `n = 4` está en el ciclo `1→4→2` de `collatz` pero `T^[k] 4 ∈ {2,1}` para `k ≥ 1` (`not_T_periodic_four`, probado). `T` saltea exactamente los valores `3x+1` con `x` impar, todos pares. Corregido a "para `n` impar".

**Aprendido**
- Patrón reutilizable para puentes entre mapas (`collatz` ↔ `T`, y próximamente `collatz` ↔ `syracuse`): invariante de seguimiento con contador de pasos y marca de paridad. El mismo esqueleto debería servir para `isPeriodic_iff_syracuse_of_odd`.
- La ecuación del ciclo conviene enunciarla primero como identidad en ℕ para toda órbita (sin resta) y sacar la versión ℤ como corolario; evita todo el dolor de `Nat.sub`.
- `verify.sh` ahora imprime axiomas de los lemas de `Invariants` también (`scripts/Axioms.lean`).

**Próximos pasos**
1. `isPeriodic_iff_syracuse_of_odd`: cierra el puente collatz → syracuse, y con él `NoNontrivialCycles` pasa a depender solo de resultados sobre ciclos de `syracuse` en impares.
2. `syracuse_fixed_eq_one` (`k = 1`): de `n(2^a − 3) = 1` sale `n = 1, a = 2`. Primer "no hay ciclos cortos".
3. `sExpSum_ge` y luego `k = 2`; después pensar cotas generales (mínimo del ciclo, aproximación de `log₂ 3`).
4. Correr el loop de agentes con API key sobre estos tres y comparar con lo hecho a mano: calibra qué tan bueno es el proposer.

**Preguntas abiertas**
- Para `NoDivergence` no hay ningún lema atacable en el blueprint. Hay que decidir si la ruta es ranking (`Ranking.lean`) o densidad; ninguna tiene un primer paso formalizable obvio.

## 2026-09-11 — Eje 3: combinar lo conocido, un motor para los dos subproblemas

Cambio de estrategia acordado: además de ciclos y divergencia, un tercer eje de *constraints
sobre contraejemplos hipotéticos*, buscando novedad en la combinación de piezas conocidas
formalizadas en el mismo sistema. `docs/known.md` lista las piezas como interfaces.

**Probado**
- `syracuse_orbit_bound` (`OrbitInequality.lean`): `∀ i<k, S^i n ≥ N → N^k · 2^{A_k} · S^k n ≤ (3N+1)^k · n`. Un paso: `N(3n+1) ≤ (3N+1)n` porque `N ≤ n`; `nlinarith` lo cierra. Inducción con `calc` + `Nat.mul_le_mul_left` + `ring`. **Es el motor**: la misma desigualdad sirve para ciclos y para tramos ascendentes.
- `ascent_bound` / `ascent_bound_log`: si además `n ≤ S^k n`, entonces `N^k 2^{A_k} ≤ (3N+1)^k`, y en logs `A_k log 2 ≤ k log(3 + 1/N)`. Versión real: `Real.log_le_log`, `Real.log_mul`, `Real.log_pow` (tres veces, una por potencia), `Real.log_div`, `field_simp` para `3 + 1/N = (3N+1)/N`.
- `cycle_sandwich`: ciclo con mínimo `≥ N` ⇒ `3^k < 2^{A_k}` ∧ `2^{A_k} N^k ≤ (3N+1)^k`.
- `VerifiedRange.lean`: `VerifiedBelow M` como hipótesis; `syracuse_eq_iterate_collatz` (`collatz^[a+1] n = syracuse n` para `n` impar, vía `iterate_collatz_of_pow_dvd` y `pow_padicValNat_dvd`); `exists_iterate_collatz_eq_iterate_syracuse`; `eq_of_isPeriodic_of_reachesOne` (periódico + llega a 1 ⇒ `{1,4,2}`, con `Function.iterate_mul` + `iterate_fixed`); `syracuse_one` (por reescritura, no `decide`); y la **combinación** `cycle_sandwich_of_verified`: bajo `VerifiedBelow M`, todo ciclo no trivial cumple el sándwich con `N = M`.

**Fallido / descartado**
- Primer enunciado de `cycle_sandwich` tenía `3^k N^k < 2^A N^k`, falso para `N = 0`; se quitó el factor.
- `Function.iterate_add_apply f m n x = f^[m] (f^[n] x)`: el orden importa. `collatz^[1 + a]` aplica las `a` divisiones *antes* del `3n+1`; hay que escribir `a + 1`.
- `push_neg` está deprecado en esta Mathlib (`push Not`); `omega` maneja `¬ M ≤ n` directo.

**Aprendido**
- Con `M = 2^71` el sándwich dice `0 < A log 2 − k log 3 < k/(3·2^71)`. Es exactamente la entrada de la cadena de Eliahou/Hercher; lo único que falta son los convergentes de `log₂3` con cotas certificadas, y eso no está en Mathlib.
- La misma desigualdad de un paso da la constraint de densidad para divergentes (doses por paso impar ≤ `log₂3` asintóticamente). Ciclos y divergencia comparten motor: es la primera vez que los dos ejes tocan el mismo lema.
- Números verificados en la web: Hercher 2023, sin `m`-ciclos con `m ≤ 91`, `K ≥ 1.375·10^11` impares (condicional a verificación); Barina 2025, convergencia hasta `2^71`.

**Próximos pasos**
1. `divergent_parity_density`: empaquetar `ascent_bound_log` como constraint asintótica sobre órbitas divergentes (necesita "infinitos ascensos" y `sExpSum_add`).
2. `divergent_parity_aperiodic`: vector de paridad de una órbita divergente no es eventualmente periódico. Primera constraint estructural real sobre divergentes.
3. Scouting (no formalizar aún): ¿cómo acotar `log 3 / log 2` con racionales certificados en Lean?
4. Los pendientes de ciclos cortos (`syracuse_fixed_eq_one`, `k = 2`) siguen listos y son baratos.

**Preguntas abiertas**
- ¿La combinación 3 (paridad aperiódica) + Tao da algo? Tao controla la distribución de `n mod 3^j`; la aperiodicidad es sobre `2`-ádicos. Son ortogonales a primera vista.

## 2026-09-11 — Paridad periódica ⇒ ciclo (Lagarias 1985), sin 2-ádicos

**Probado**
- `affine_orbit_fixed` (`ParityAperiodic.lean`): toda sucesión `y : ℕ → ℕ` con `y (m+1) · 2^A = 3^p · y m + c` y `A ≥ 1` cumple `y 1 = y 0`. Prueba: `w m := (2^A − 3^p) · y m − c` en ℤ, `2^A w(m+1) = 3^p w m` por `linear_combination`, telescopa a `2^{Am} w m = 3^{pm} w 0`, `IsCoprime.dvd_of_dvd_mul_left` con `Int.isCoprime_iff_gcd_eq_one` (+ `decide` para `Int.gcd 2 3 = 1`) da `2^{Am} ∣ w 0`, y `Int.eq_zero_of_abs_lt_dvd` con `Nat.lt_two_pow_self` cierra `w 0 = 0`.
- `syracuse_periodic_of_sExp_periodic`: exponentes periódicos (período `p > 0` desde `i₀`) ⇒ `S^p (S^{i₀} n) = S^{i₀} n`. Los bloques `y m = S^{i₀ + mp} n` tienen los mismos `A` y `c` (por `sum_congr` sobre la periodicidad iterada, `sExp_periodic_iterate`), así que `syracuse_iterate_mul_two_pow` da la recurrencia afín y `affine_orbit_fixed` la cierra.
- `not_syracuseDivergent_of_periodic`, `sExp_not_periodic_of_divergent`: **toda órbita divergente tiene vector de exponentes aperiódico.** Reducción módulo `p` de los índices con `Nat.mod_add_div` + `Function.iterate_mul` + `iterate_fixed`.

**Fallido / descartado**
- La ruta del blueprint (vía `divergent_parity_density` y casos `2^A ≷ 3^p`) era innecesaria. El telescoping en ℤ maneja los dos casos a la vez: `w 0 = 0` con `c > 0` fuerza `2^A > 3^p` solo.
- `Function.iterate_mul f m n : f^[m * n] = f^[m]^[n]`: para `(f^[p])^[q]` hay que escribir `p * q`, no `q * p`; y `omega` no identifica `q * p` con `p * q` como átomos.
- Signo en `linear_combination`: `hz - hw0'`, no `hz + hw0'`.

**Aprendido**
- `affine_orbit_fixed` es un lema **abstracto sobre sucesiones**, no sobre Syracuse. Cualquier subsucesión de una órbita que satisfaga una recurrencia afín con `A, c` fijos es constante. Eso abre `divergent_no_affine_tail`: no hace falta que *toda* la cola sea periódica, alcanza con que un patrón de exponentes se repita a lo largo de una subsucesión.
- Este es el primer resultado de la sesión que no está en Mathlib ni en ningún repo Lean que conozca, y la prueba es más corta que la de Lagarias.

**Próximos pasos**
1. `divergent_no_affine_tail`: explotar `affine_orbit_fixed` sobre subsucesiones. Idea a explorar: si los exponentes de una órbita divergente están acotados por `L`, hay finitos patrones de largo `p`, y por pigeonhole algún patrón se repite infinitas veces — pero las repeticiones no son consecutivas, así que la recurrencia no encadena directamente. Ver si una versión "esparcida" del telescoping funciona.
2. `divergent_parity_density` sigue abierto y ahora es independiente.
3. `syracuse_fixed_eq_one` y ciclos cortos, baratos.

## 2026-09-11 — Cota de repeticiones y densidad de doses en divergentes

**Probado**
- `affine_orbit_dvd` (`ParityAperiodic.lean`, refactor): el telescoping ahora es finito, `∀ m < M` ⇒ `2^{AM} ∣ w₀`. La versión infinita `affine_orbit_fixed` es corolario. `affine_orbit_zero_or_large`: `w₀ = 0 ∨ 2^{AM} ≤ |w₀|` (`Int.le_of_dvd` + `dvd_abs`).
- `syracuse_repeat_bound` / `divergent_repeat_bound`: si un patrón de exponentes de largo `p` se repite `M ≥ 1` veces consecutivas desde `x = S^{i₀} n`, entonces `x` es `p`-periódico o `2^{AM} ≤ (2^A + 3^p)·x + c`. En divergentes solo queda la cota: **a altura `x` ningún bloque se repite más de `~log₂(x)/A` veces seguidas.** `|w₀| ≤ (2^A+3^p)x + c` por `abs_le` + `nlinarith`.
- `syracuse_eventually_ge_of_divergent` (`DivergentDensity.lean`): no acotada ⇒ tiende a infinito. `Set.infinite_of_forall_exists_gt` + `Set.Infinite.exists_ne_map_eq_of_mapsTo` sobre `Set.Iio N` ⇒ dos iterados iguales ⇒ periódico ⇒ acotada (`not_syracuseDivergent_of_periodic`).
- `divergent_dose_bound` (ℕ) y `divergent_dose_density` (ℝ): si `n` diverge, para todo `N` (resp. `ε > 0`) hay `i₀, j₀` con `N^j 2^{A(i₀,j)} ≤ (3N+1)^j` (resp. `A(i₀,j) log 2 ≤ j(log 3 + ε)`) para **todo** `j ≥ j₀`. Ambos compilaron al primer intento. `log(3 + 1/N) ≤ log 3 + 1/(3N)` vía `Real.log_le_sub_one_of_pos`; `gcongr` para el `calc` final.

**Fallido / descartado**
- La idea del blueprint para `divergent_no_affine_tail` (patrón repetido en subsucesión esparcida ⇒ recurrencia afín) **no funciona**: entre ocurrencias no consecutivas no hay recurrencia. Lo que sí sale es la versión consecutiva cuantitativa, que es más útil.
- `rw [← hy0, ← hy1]` reescribe las dos ocurrencias de `S^{i₀} n` y después `hy1` no matchea; el orden `← hy1, ← hy0` sí.

**Aprendido**
- "Divergente" en sentido débil (no acotada) equivale al fuerte (→ ∞) para órbitas deterministas: la prueba es pigeonhole + "ciclo ⇒ acotada". Esto simplifica todos los enunciados sobre divergentes: se puede asumir cola `≥ N` para cualquier `N`.
- El eje 3 tiene ahora **cuatro constraints** sobre una órbita divergente hipotética, todas en el mismo sistema: aperiodicidad, cota de repeticiones, → ∞, y densidad de doses `≤ log₂3`. Ninguna es nueva en prosa; la combinación formal sí es inédita hasta donde sé.

**Próximos pasos**
1. `divergent_odd_density_T`: la formulación estándar (fracción de impares en `T` ≥ `log 2/log 3`). Necesita el puente de iterados `T ↔ syracuse`.
2. Pensar si densidad + cota de repeticiones + exponentes acotados dan algo: los patrones de densidad `≤ log₂3` son una fracción exponencialmente chica de todos los patrones (entropía), y cada uno no se puede repetir mucho. Eso empieza a oler a un argumento de conteo sobre el vector de exponentes. Es el primer lugar donde una *combinación* podría dar algo no folklórico.
3. Ciclos cortos siguen pendientes y baratos.

## 2026-09-11 — Ciclos: el puente completo, k ≤ 4, y las doses forzadas

**Probado**
- `SyracuseCycles.lean`: `oddPart_iterate_collatz` (la parte impar de `collatz^[j] n` es un iterado de Syracuse, con contador `≥ 1` desde `j ≥ 1`), `syracuse_periodic_of_isPeriodic_of_odd` (la dirección difícil del puente), `exists_odd_of_isPeriodic` (un ciclo todo par bajaría estrictamente), y **`noNontrivialCycles_iff : NoNontrivialCycles ↔ NoSyracuseCycles`**. Ciclos vive ahora enteramente en Syracuse sobre impares.
- `SyracuseSmallCycles.lean`: `syracuse_fixed_eq_one` (`k=1`), `syracuse_two_periodic_eq_one` (`k=2`, nueve casos `2^{aᵢ} ∈ {2,4,≥8}` con `omega`), `cycle_sandwich_three` (**sándwich incondicional** `3^k < 2^A ≤ (10/3)^k`, porque los elementos de un ciclo no trivial son impares `≠ 1`, luego `≥ 3`), `no_syracuse_four_cycle` (no hay potencia de 2 en `(81,123]`: `interval_cases A <;> omega`), `no_syracuse_three_cycle` (`A = 5` forzado, seis composiciones, `interval_cases a₀ <;> interval_cases a₁ <;> omega`).
- `CycleDoses.lean`: `cycle_doses_of_verified`: bajo `VerifiedBelow M` y `k ≤ M`, `3^k < 2^A < 2·3^k`, o sea `A = ⌊k log₂3⌋ + 1` **forzado**. `(1+1/(3M))^k ≤ e^{k/(3M)} ≤ e^{1/3} < 2` con `Real.add_one_le_exp`, `Real.exp_nat_mul`, `Real.exp_one_lt_d9`, `lt_of_pow_lt_pow_left₀`. `unique_of_pow_sandwich`: la `A` es única.
- `sExpSum_ge : k ≤ sExpSum n k` para `n` impar.

**Fallido / descartado**
- Solo un error real: `iterate_collatz_of_all_even` con `n` implícito no se infería dentro de `by_contra`; `(n := n)` explícito.
- `simp only [...]; rfl` no cierra `sExpSum n 3 = a₀ + a₁ + a₂` (queda `0 + …` y `syracuse^[1] n`); `simp [sExpSum, Finset.sum_range_succ]` sí.

**Aprendido**
- El sándwich con `N = 3` es gratis y ya mata `k = 4` solo. Con `N` mejor (p.ej. `N = 5`: 3 llega a 1 en pocos pasos, así que un ciclo no trivial tiene todos sus elementos `≥ 5`... pero eso requiere probar `ReachesOne 3`, trivial con `decide` sobre `collatz`) el intervalo `(3^k, (3+1/N)^k]` se achica y mata más `k`. Esto es exactamente la escalera de Eliahou en miniatura: cada mejora de `N` mata más `k` sin enumerar.
- La enumeración de composiciones crece como `C(A−1, k−1)`; `interval_cases` anidado explota alrededor de `k = 5`. Hace falta un `decide` sobre una función que enumere, o una táctica.
- `cycle_doses_of_verified` es la parte "barata" de Hercher: `A` determinada por `k` para todo `k ≤ 2^71`. Lo que Hercher agrega es que `{k log₂3}` no puede ser tan chico como `k/(3·2^71)` salvo para `k` enormes, y eso son los convergentes.

**Próximos pasos**
1. `no_syracuse_cycles_small_k`: automatizar la enumeración (función `decide`-able sobre composiciones) y subir `k` hasta donde aguante el kernel.
2. Mejorar `N` sin `VerifiedBelow`: probar `ReachesOne` para los impares chicos con `decide` (3, 5, 7, …) y usar `N = 9` o más en el sándwich. Cada salto de `N` mata más `k` gratis. Ver hasta dónde se puede llegar con `decide` puro (Barina llegó a 2^71 con GPUs; el kernel de Lean con `decide` quizás a 10^4).
3. Eje 3 sigue con la traducción a `T` y la idea de conteo.

## 2026-09-11 — Terras en Syracuse y el conteo de clases

**Probado**
- `nu2_eq_of_modEq`: `nu2` depende solo de la clase mod `2^{nu2+1}` (`padicValNat_dvd_iff_le`, `pow_succ_padicValNat_not_dvd`, `Nat.ModEq.of_dvd`).
- **`pattern_iff_modEq`** (`Terras.lean`): para `x, x'` impares, mismo patrón de exponentes en `j` pasos ⇔ `x ≡ x' (mod 2^{A(x,j)+1})`. Ida: `S^j x` impar ⇒ `3^j x + c ≡ 2^A (mod 2^{A+1})`, restar, coprimalidad. Vuelta: inducción en `j` generalizando `x, x'`, dividiendo por `2^{a₀}` en ℤ (`mul_left_cancel₀`). El `+1` en el módulo es exacto: `x = 1` y `x = 25` tienen `a₀ = 2` pero difieren mod 16 → mismo patrón de 1 paso ⇔ `≡ mod 8`.
- `sExpSum_add`, `sExpSum_strictMono` (sumas parciales estrictamente crecientes para `n` impar).
- **`card_residueClasses_le`**: `#{r < 2^{A+1} impar : A(r,j) = A} ≤ C(A−1, j−1)`. Inyección `r ↦ {A(r,1), …, A(r,j−1)} ∈ powersetCard (j−1) (Ico 1 A)`; inyectividad vía `Finset.orderEmbOfFin_unique` (dos funciones estrictamente monótonas con la misma imagen son iguales) + `pattern_of_partialSums` + Terras + `Nat.ModEq.eq_of_lt_of_lt`.

**Fallido / descartado**
- Tres errores de plomería: un signo en `linear_combination`, un `push_cast` que faltaba en una hipótesis con producto de potencias casteado, y `simp only [residueClasses, ...]` que desplegó el `Finset.filter` hasta la lista subyacente (usar un lema `mem_residueClasses` con `unfold` + `rw [mem_filter]`). `simpa [Fin.lt_def]` entra en recursión infinita; `Fin.lt_def.mp h` directo.

**Aprendido**
- Terras se formaliza en ~100 líneas en Syracuse; la forma clásica sobre `T` habría necesitado el vector de paridad como `Fin k → Bool` y la biyección con `ZMod (2^k)`. La versión de exponentes es más natural para conteo porque el módulo `2^{A+1}` es exactamente el "presupuesto de doses".
- Con esto el eje 3 ya tiene toda la infraestructura para la **heurística de densidad**: una órbita divergente tiene `A ≤ j log₂3 (1+ε)` (densidad), luego cae en `≤ C(A−1, j−1)` clases (Terras), y `C(A−1,j−1) ≈ 2^{0.951 A}` frente a `2^A` clases impares (entropía, pendiente). Eso es "los divergentes viven en un conjunto de densidad cero de clases residuales", formalmente. Cruzar de "densidad cero" a "vacío" para un `n` fijo es el muro, y así queda marcado en el blueprint.

**Próximos pasos**
1. `entropy_bound`: `C(A−1, j−1) ≤ 2^{(A−1) H(…)}` con `Real.binEntropy` de Mathlib. Puramente combinatorio.
2. `divergent_in_thin_set`: el empaquetado. Con eso el eje 3 queda "completo hasta el muro".
3. Volver a ciclos: tramo 1 (`N` grande con `decide`, enumerador de composiciones).

## 2026-09-11 — Se saca del camino el loop autónomo de agentes

Decisión del usuario. El loop Python (`orchestrator → proposer → formalizer → verifier → scribe`
contra la API de Claude) estaba escrito y probado con la API mockeada, pero nunca corrió con
una key real y no lo estábamos usando: todo el trabajo se hace en sesión con Claude Code, donde
pensar el enunciado antes de escribir Lean evita quemar intentos contra enunciados falsos.

Queda en `Agents/` solo la contabilidad: `blueprint.py` + `status.py` (grafo) y `memory.py`
(JSONL + `failed/`). El código del loop está en git hasta `8c68615` y `Agents/README.md` dice
cuándo tendría sentido recuperarlo (volumen mecánico con verificación automática).

## 2026-09-11 — Primera ronda con subagentes: cuatro lemas en paralelo

Cambio de modo: el usuario pidió que Claude con subagentes haga el trabajo, colaborando él
desde acá. Despaché cuatro formalizers en paralelo (uno por archivo, compilando solo con
`lake env lean` para no pisarse), integré yo (imports, `#print axioms`, build completo,
`verify.sh`, renombres por colisión), y todo entró en verde.

**Probado**
- `Entropy.lean` (agente 1, 4 compilaciones): `choose_le_exp_binEntropy : C(n,k) ≤ exp(n·H(k/n))` — Mathlib **no** tenía la cota entrópica de binomios; probada desde `add_pow` + `Finset.single_le_sum`. Corolario `choose_pred_le_two_rpow_of_dense`: si `A ≤ j·log₂3` entonces `C(A−1,j−1) ≤ 2^{A·c}` con `c = H₂(1/log₂3)`. **`c < 1` sin certificación numérica**: `Real.binEntropy_lt_log_two : H(p) < log 2 ↔ p ≠ 1/2`, y `1/log₂3 ≠ 1/2` porque `3 ≠ 4`. Desviación razonable: exponente `A·c` en vez de `(A−1)·c` (la monotonía de `H` no baja bien a `(j−1)/(A−1)`).
- `SyracuseCyclesK5K6.lean` (agente 2, 7 compilaciones, ~75 s de kernel): **no hay ciclos de Syracuse de longitud 5 a 11**, incondicional. Enumerador `compCheck : ℕ → ℕ → (ℕ → Bool) → Bool` de composiciones por recursión estructural, puente `compCheck_orbit` probado *sobre la órbita* (no sobre listas), y `decide +kernel` (solo kernel; `decide` plano agota heartbeats desde `A = 17`). Con `SyracuseSmallCycles`: sin ciclos de longitud 1..11. `k = 12` (75582 composiciones) no termina sin poda. El agente verificó en Python que ninguna composición da candidato antes de formalizar.
- `DivergentDensityT.lean` (agente 3, 4 compilaciones): `T^[sExp x] x = syracuse x`, `T^[sExpSum x j] x = syracuse^[j] x`, contador `oddSteps`, `oddSteps_sExpSum = j`, y **`divergent_odd_density_T`**: divergente ⇒ `m·log 2 ≤ (oddSteps m + 1)(log 3 + ε)` para todo `m ≥ m₀`. La formulación estándar (fracción de impares `≥ log 2/log 3`).
- `Log23.lean` (agente 4, 5 compilaciones): **`log₂3` con 25 dígitos certificados**, 2 s. Scouting: Mathlib tiene `Real.log_three_near_10` (10 dígitos), y la serie de `artanh` acotada por ambos lados sin valor absoluto (`Real.sum_range_le_log_div`, `Real.log_div_le_sum_range_add`). Descomposición `½log 2 = artanh(1/3)` (27 términos), `½log(3/2) = artanh(1/5)` (19 términos), `norm_num` + `linarith`. 50 dígitos probados en scratch al mismo costo.

**Fallido / descartado**
- Colisiones de nombres entre agentes: `sExpSum_strictMono` (Terras vs DensityT, enunciados distintos → renombrado `sExpSum_lt_of_lt`) y `sExpSum_succ'` (Terras vs K5K6, idéntico → K5K6 importa Terras). Regla nueva para próximas rondas: pasarle a cada agente la lista de nombres ya declarados, o pedir prefijo por archivo.
- Un docstring huérfano al borrar la copia duplicada (error de parseo, un intento).

**Aprendido**
- `decide +kernel` es la herramienta para enumeraciones grandes: el elaborador se ahoga en `whnf` pero el kernel con GMP no. Sin axiomas extra.
- Las cotas numéricas de constantes trascendentes son **baratas** en Lean 4 (`norm_num` con el plugin de `BigOperators` produce el racional exacto). El tramo 2 (Hercher) ya no tiene bloqueante numérico; lo que falta es `cf_stability` (que el desarrollo en fracción continua de `L` se lea de los de `lo` y `hi`).
- Corrección honesta a algo que dije: "nadie tenía esto limpio en Lean" está sobreafirmado. Verificado: Mathlib (+ Archive + Counterexamples) no menciona Collatz; tres repos externos mirados. **No** revisé GitHub sistemáticamente, ni Zulip, ni Isabelle/Coq. Tarea pendiente antes de cualquier PR o nota.

**Próximos pasos**
1. `cf_stability` (tramo 2): con Legendre de Mathlib + estabilidad del desarrollo en intervalos + lista certificada de convergentes, sale `k ≥ K₁` para ciclos bajo `VerifiedBelow 2^71`.
2. `divergent_in_thin_set`: empaquetar densidad + Terras + entropía. Cierra el eje 3 hasta el muro.
3. Búsqueda de prior art sistemática (GitHub, Zulip, AFP, Coq) antes de hablar de novedad.
4. `k ≥ 12` con poda, y `N` grande vía `decide` (rendimiento decreciente; baja prioridad).

## 2026-09-12 — Ronda 2 (parcial): conjunto fino y exponentes acotados; tres agentes caídos por límite de sesión

Despaché cinco agentes; dos terminaron (`ThinSet.lean`, `BoundedExponents.lean`), tres murieron
al arrancar por el límite de sesión de la API (Hercher/`cf_stability`, ciclos `k ≥ 12`, prior art).
Se relanzan.

**Probado**
- `divergent_in_thin_set` / `divergent_in_thin_set_fraction` (`ThinSet.lean`): el teorema final del eje 3. Para `n` divergente y `N ≥ 2`, hay una cola donde `x = S^{i₀} n` cae en `residueClasses j A`, con `#residueClasses j A ≤ 2^{c_N·A}` y `c_N = H₂(1/log₂(3+1/N)) < 1`, luego fracción `≤ 2^{−(1−c_N)A}` de los impares mod `2^{A+1}`, con `A ≥ j → ∞`. El agente parametrizó por `N` (vía `divergent_dose_bound` en ℕ) en vez de `ε`, porque la versión log da umbral `log₂3 + ε/log 2` que no encaja con la constante exacta de `Entropy.lean`; generalizó la cota entrópica a `θ ∈ [1/2, 1]` arbitrario (`thin_choose_le_two_rpow`). `c_N < 1` otra vez sin numérica (`3 + 1/N ≠ 4`).
- `BoundedExponents.lean`: (a)-(c) empaquetados, y **(d) `residues_not_periodic_of_divergent`**: divergente con exponentes `≤ L` ⇒ `(S^i n mod 2^{L+1})_i` no es eventualmente periódica. Constraint nueva y limpia (Terras + `sExp_not_periodic_of_divergent`). El docstring prometía un `blockChanges_ge` que no existe (el agente fue interrumpido); corregido a lo que sí hay.

**Fallido / descartado**
- Rate limit de sesión (HTTP 429) mató tres agentes antes de escribir nada. `declared_names.txt` estaba en una sola línea (bug de `tr`); corregido a una por línea.

**Aprendido**
- El eje 3 está **completo hasta el muro**: → ∞, densidad, aperiodicidad, repeticiones, Terras, entropía, conjunto fino. Todo en el mismo sistema. Lo que sigue en divergencia ya no es "más constraints" sino intentar una combinación que choque, y no tengo candidata honesta.

**Próximos pasos**
1. Relanzar: `cf_stability` (Hercher), `k ≥ 12` + `N` grande, prior art.
2. Con el eje 3 cerrado, el trabajo útil restante es ciclos (tramo 1 y 2) y la búsqueda de prior art para decidir PR a Mathlib.

## 2026-09-12 — Hercher formalizado: k ≥ 72 057 431 991

El agente de `cf_stability` se colgó (watchdog de 600 s) **después** de escribir el archivo completo;
lo verifiqué y entró. Es el resultado condicional más fuerte del repo.

**Probado**
- `hercher_lower_bound` (`ContFrac.lean`): bajo `VerifiedBelow (2^71)`, todo ciclo no trivial de Syracuse tiene `k ≥ 72 057 431 991` pasos. Solo axiomas estándar.
- `cf_unimodular_gap`: el lema que reemplaza toda la teoría de fracciones continuas. Si `p/q < θ < p'/q'` con `p'q − pq' = 1`, entonces `(q,p), (q',p')` son base de ℤ², todo `(k, A)` se escribe `k = aq + bq'`, `A = ap + bp'`, y `A − kθ = −a·e + b·e'` con `e = qθ − p > 0`, `e' = p' − q'θ > 0`. Para `0 < k < q + q'` los signos de `a, b` están forzados, y sale: `A − kθ ≤ 0`, o `k = q'` con gap `e'`, o gap `≥ e + e'`, o `≥ 2e'`. Ni `GenContFract`, ni Legendre, ni estabilidad del desarrollo: álgebra lineal entera + los 25 dígitos de `Log23` para certificar `e ≈ 6.65·10⁻¹²`, `e' ≈ 1.46·10⁻¹¹`.
- `cf_cycle_gap`: lectura logarítmica del sándwich, `0 < A log 2 − k log 3 ≤ k/(3M)`.

**Fallido / descartado**
- La ruta que yo propuse (Legendre + estabilidad del desarrollo en fracción continua de un real acotado por racionales) era la pesada. El agente la evitó entera. Lección: cuando el objetivo es una cota para `k` en un rango finito, dos convergentes consecutivos + unimodularidad bastan.
- Los denominadores de convergentes que puse en el brief para los términos altos estaban mal (de memoria). El agente los recalculó en Python antes de usarlos. Regla: nunca pasar números "de memoria" en un brief; pedir verificación siempre.

**Aprendido**
- **Límite exacto del método**: en `k = q₂₁ + q₂₂` el propio `kθ` queda a `≈ 7.95·10⁻¹²` bajo un entero, menos que `k/(3·2^71 log 2) ≈ 1.47·10⁻¹¹`. El sándwich con `M = 2^71` no excluye ese `k`. Hercher llega a `1.375·10^11` porque usa más estructura del ciclo (no solo el mínimo). Para pasar de `7.2·10^10` hace falta o `M` mayor (más verificación) o la estructura de Eliahou/Simons–de Weger.
- El tramo 2 de `strategy.md` está **cerrado**. Lo que queda en ciclos es el muro (Baker) o refinar la constante.

## 2026-09-13 — Prior art: no estamos solos, y en ciclos cortos nos pasan

Reporte del scout (`docs/prior_art.md`, Sonnet, 45 búsquedas/fetches; verifiqué yo el repo principal).

**Hallazgos**
- `msharpe248/collatz` (Lean 4, MIT, activo sep-2026, solo axiomas estándar): Terras exacto, aperiodicidad de divergentes, densidad de impares `> log 2/log 3`, **sin ciclos con ≤ 183 divisiones por 2** (`decide +kernel`), densidad Krasikov–Lagarias mejorada a `x^0.8676`, exclusiones Sturmianas, no-go de certificados de descenso. Usa Barina `2^71` como hipótesis explícita, igual que nuestro `VerifiedBelow`. Su `terras_growth_bound` es una desigualdad emparentada con nuestra desigualdad de órbita pero de otra forma.
- Merle: `k > 1322` condicional a Barina **y** a una conjetura tipo Baker no probada. Nuestro `hercher_lower_bound` (`7.2·10^10`, solo Barina) es más fuerte y autocontenido.
- Mazur/ProofAtlas: real. `xrchz/CollatzLean`: explotó un bug del kernel (jul-2026, parcheado); no es prior art.
- Nada en Isabelle/Coq/Agda/Metamath/HOL/Mizar.
- `Real.binEntropy_lt_log_two` ya está en Mathlib (y ya lo usamos en `Entropy.lean`); la cota `C(n,k) ≤ exp(nH)` no aparece en ningún lado.

**Consecuencias**
- El tramo 1 de ciclos (`k ≥ 12`, subir `N`) pierde valor: msharpe248 ya está en 183 divisiones. Dejo terminar al agente en curso porque el método (subir `N` vía `decide`) es distinto, pero no invierto más ahí.
- Lo distintivo nuestro: `hercher_lower_bound`, la desigualdad de órbita como motor común, entropía + conjunto fino, el telescoping. Cualquier nota o PR se centra en eso y **cita** a msharpe248 en lo que ya tenían.
- Corrección definitiva a "nadie tenía esto limpio en Lean": falso para Terras, aperiodicidad y densidad; sí parece cierto para Hercher y el sándwich exacto.

**Próximos pasos**
1. Leer `msharpe248` en detalle (`Cycles.lean`, `Density.lean`) y anotar en `known.md` qué de lo suyo podríamos importar como interfaz (con verificación independiente, regla 6).
2. Decidir con el usuario qué sigue: refinar Hercher (estructura de Eliahou/Simons–de Weger) es donde estamos adelante; divergencia está en el muro para todos.

## 2026-09-13 — Incondicional: todo ciclo no trivial tiene k ≥ 2301

**Probado** (`SyracuseCyclesK12.lean`, 435 líneas, ~3 min de kernel, verificado independientemente)
- `k12_verifiedBelow_600001 : VerifiedBelow 600001`, **dentro del kernel**. Truco correcto (el de la verificación computacional real): basta que cada impar `3 ≤ n < M` baje por debajo de sí mismo (`k12_dropsT` con fuel, iterando `T`), y una inducción fuerte da `ReachesOne` para todos (`k12_verifiedBelow_of_dropsT`). 24 bloques de 12 500 impares, `decide +kernel` de ~5.6 s cada uno.
- `k12_cycle_sandwich_600001`: `3^k < 2^A ∧ 2^A·600001^k ≤ 1800004^k`, incondicional.
- `k12_sandwichFree` + `k12_sandwich_table_600001`: certificado decidible de que para `1 ≤ k ≤ 2300` no existe `A` admisible (con `A₀ ≈ k·1054/665` y barrido de 3; `Nat.log2` no está acelerado en el kernel).
- **`k12_syracuse_cycle_length_ge : ... → 2301 ≤ k`**, incondicional. Con `noNontrivialCycles_iff`: ningún ciclo del mapa de Collatz fuera del trivial tiene menos de 2301 pasos impares (~3647 divisiones). msharpe248 tenía 183 divisiones.
- `k12_no_syracuse_twelve_cycle` por enumeración podada (25 s); `k = 13+` por enumeración es inviable (1.6M nodos) y el sándwich los cubre igual.

**Fallido / descartado**
- Acumular mod `d` en el enumerador no acelera (el costo es el número de nodos).
- Un `decide` único sobre 10⁵ enteros es superlineal en memoria (>3 GB, no termina); bloques de 25 000 ya muestran anomalías. 12 500 es lineal.

**Aprendido**
- Tabla del agente (Python): con `N = 101` el sándwich deja 193 supervivientes en `[12, 300]`; con `N = 10⁴`, solo 200 y 253; con `N = 10⁵`, ninguno hasta 970; `N = 600001` → 2301; `N = 10⁶` daría 2966 (~4 min). Rendimiento logarítmico en `N`: cada ×10 en `N` da ~×1.5 en el `k` mínimo.
- El kernel de Lean 4 es una máquina de verificación numérica razonable: 600 000 órbitas en 2.5 minutos. Con `M = 2^71` (Barina) es imposible, pero el punto de cruce entre "lo que el kernel verifica" y "lo que hace falta" está más cerca de lo que pensaba.

**Estado de ciclos**: incondicional `k ≥ 2301`; condicional a `2^71`, `k ≥ 7.2·10^10`. Tramos 1 y 2 cerrados. Lo que sigue es el muro.
