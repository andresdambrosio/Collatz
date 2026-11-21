# Lo conocido, como interfaces

Cada resultado de la literatura escrito como **hipótesis → conclusión**, con qué necesita,
qué da, y si está formalizado acá. No es un survey: es una lista de piezas encajables.
La idea es que el proposer busque *composiciones* de estas piezas, no lemas aislados.

Convención de estado: `Lean` = probado en este repo (nombre entre backticks);
`hip` = usable solo como hipótesis explícita (`def … : Prop`); `no` = fuera de alcance hoy.

## Piezas estructurales (incondicionales)

| Pieza | Hipótesis → conclusión | Estado | Notas |
|---|---|---|---|
| Reducción | `NoNontrivialCycles ∧ NoDivergence → CollatzConjecture` | Lean `collatz_of_noCycles_noDivergence` | Pigeonhole. |
| Puente T | `n` impar → (`IsPeriodic n ↔ T`-periódico) | Lean `isPeriodic_iff_T_of_odd` | Falso para pares (`not_T_periodic_four`). |
| Puente Syracuse | `n` impar → cada `syracuse^[k] n` es un `collatz^[m] n`, `m ≥ k` | Lean `exists_iterate_collatz_eq_iterate_syracuse` | Solo la dirección fácil. Falta `IsPeriodic n → syracuse`-periódico. |
| Periódico + llega a 1 | `IsPeriodic n ∧ ReachesOne n → n ∈ {1,4,2}` | Lean `eq_of_isPeriodic_of_reachesOne` | |
| Ecuación de órbita | `S^k n · 2^{A_k} = 3^k n + Σ_{i<k} 3^{k-1-i} 2^{A_i}` | Lean `syracuse_iterate_mul_two_pow` | En ℕ, toda órbita. |
| Ecuación del ciclo | `S^k n = n → n(2^{A_k} − 3^k) = Σ…` (ℤ) | Lean `syracuse_cycle_equation` | |
| Cota inferior | `S^k n = n, k > 0 → 3^k < 2^{A_k}` | Lean `two_pow_gt_three_pow_of_cycle` | |
| Desigualdad de órbita | `∀ i<k, S^i n ≥ N → N^k 2^{A_k} S^k n ≤ (3N+1)^k n` | Lean `syracuse_orbit_bound` | **El motor.** Un paso: `N·2^a·S n ≤ (3N+1)·n`. |
| Cota superior (ciclo o ascenso) | `… ∧ n ≤ S^k n → N^k 2^{A_k} ≤ (3N+1)^k` | Lean `ascent_bound`, `ascent_bound_log` | Sirve para ciclos **y** para tramos ascendentes. |
| Sándwich del ciclo | ciclo con mín `≥ N` → `3^k < 2^{A_k}` ∧ `2^{A_k} N^k ≤ (3N+1)^k` | Lean `cycle_sandwich` | `1 < 2^A/3^k ≤ (1+1/(3N))^k`. |
| Sándwich incondicional | ciclo no trivial → `3^k < 2^A` ∧ `2^A 3^k ≤ 10^k` | Lean `cycle_sandwich_three` | `N = 3` porque los elementos son impares `≠ 1`. |
| Ciclos ⇔ Syracuse | `NoNontrivialCycles ↔ NoSyracuseCycles` | Lean `noNontrivialCycles_iff` | Todo ciclo de `collatz` contiene un impar; parte impar de la órbita = iterados de Syracuse. |
| Ciclos cortos | **no hay ciclos de Syracuse con `k ≤ 2300`, incondicional** | Lean `k12_syracuse_cycle_length_ge` (`SyracuseCyclesK12.lean`); antes `k ≤ 11` por enumeración | `VerifiedBelow 600001` en el kernel (24 bloques, "baja por debajo de sí mismo" + inducción fuerte) y sándwich con `N = 600001`. Supera los 183 halvings de msharpe248 (~115 pasos de Syracuse). |
| Verificación en el kernel | `VerifiedBelow 600001` | Lean `k12_verifiedBelow_600001` | ~0.45 ms por impar; bloques de 12 500 (bloques grandes son superlineales en memoria). `N = 10^6` costaría ~4 min. |
| Cota entrópica | `C(n,k) ≤ exp(n·H(k/n))`; densidad `A ≤ j log₂3` ⇒ `C(A−1,j−1) ≤ 2^{A·c}`, `c = H₂(1/log₂3) < 1` | Lean `choose_le_exp_binEntropy`, `choose_pred_le_two_rpow_of_dense`, `entropyConst_lt_one` | `c < 1` sin numérica: `H₂(p) < 1 ⇔ p ≠ 1/2`. No estaba en Mathlib. |
| Densidad en `T` | divergente ⇒ fracción de pasos impares de `T` `≥ log 2/(log 3 + ε)` en toda la cola (con `+1` de holgura) | Lean `divergent_odd_density_T`, `T_iterate_sExpSum_eq_syracuse_iterate`, `oddSteps_sExpSum` | Formulación estándar de la literatura. |
| Conjunto fino | divergente ⇒ `∀ N ≥ 2`, cola con `x` en `≤ 2^{c_N A}` clases mod `2^{A+1}`, `c_N < 1`; fracción `≤ 2^{−(1−c_N)A}` | Lean `divergent_in_thin_set`, `divergent_in_thin_set_fraction` | **La heurística de densidad como teorema.** No cruza a "vacío" (muro). |
| Exponentes acotados | divergente ∧ `sExp ≤ L` ⇒ residuos mod `2^{L+1}` no eventualmente periódicos | Lean `residues_not_periodic_of_divergent` | Vía Terras + aperiodicidad. |
| `log₂3` certificado | `1.584962500721156181453738929 < log₂3 < …949` (25 dígitos) | Lean `log2_3_gt`, `log2_3_lt` | Series de `artanh` con cotas de resto de Mathlib; 2 s. 50 dígitos igual de barato. |
| Doses forzadas | `VerifiedBelow M`, ciclo no trivial, `k ≤ M` → `3^k < 2^A < 2·3^k` | Lean `cycle_doses_of_verified` | `A = ⌊k log₂3⌋+1`; no necesita convergentes. |

## Piezas externas (solo como hipótesis)

| Pieza | Enunciado | Estado | Fuente |
|---|---|---|---|
| Verificación computacional | `∀ n < 2^71, ReachesOne n` | hip `VerifiedBelow M` | Barina, J. Supercomputing 81 (2025). No reproducible en el kernel. |
| Tao 2019 | casi toda órbita (densidad logarítmica) alcanza un valor `≤ f(n)` con `f → ∞` arbitrario | no | Probabilístico; no da "todas". Mazur 2026 lo formalizó parcialmente (fracción positiva). |
| Krasikov–Lagarias 2003 | `#{n ≤ x : ReachesOne n} ≥ x^{0.84}` | no | Sistema de desigualdades de diferencias. |
| Baker (formas lineales en logs) | `|A log 2 − k log 3| > exp(−C log A log k)` | no | No está en Mathlib. Es lo que cierra el caso general de ciclos en Steiner/Simons–de Weger. |
| Fracciones continuas de `log₂3` | `|A/k − log₂3| < 1/(2k²) → A/k` es convergente | evitado | No hizo falta: `cf_unimodular_gap` reemplaza Legendre + estabilidad por álgebra lineal entera con dos convergentes consecutivos certificados. |

## Combinaciones ya hechas

| Combinación | Resultado | Estado |
|---|---|---|
| **Hercher formalizado** | `VerifiedBelow 2^71 →` todo ciclo no trivial de Syracuse tiene `k ≥ 72 057 431 991` | Lean `hercher_lower_bound` (`ContFrac.lean`). Sándwich + `log₂3` a 25 dígitos + lema unimodular `cf_unimodular_gap` (sin fracciones continuas de reales). Límite exacto del método: `k = q₂₁ + q₂₂`. Hercher llega a `1.375·10^11` con más estructura del ciclo. |

| Combinación | Resultado | Estado |
|---|---|---|
| Sándwich + verificación | `VerifiedBelow M →` todo ciclo no trivial cumple `3^k < 2^{A_k}` y `2^{A_k} M^k ≤ (3M+1)^k` | Lean `cycle_sandwich_of_verified` |
| Ecuación de órbita + paridad periódica | exponentes eventualmente periódicos ⇒ la órbita es un ciclo desde `i₀`; divergente ⇒ exponentes aperiódicos | Lean `syracuse_periodic_of_sExp_periodic`, `sExp_not_periodic_of_divergent` |
| Cota de repeticiones (cuantitativa) | patrón de largo `p` repetido `M` veces seguidas desde `x` ⇒ ciclo o `2^{AM} ≤ (2^A+3^p)x + c` | Lean `syracuse_repeat_bound`, `divergent_repeat_bound` |
| No acotada ⇒ → ∞ | `SyracuseDivergent n → ∀ N, ∃ i₀, ∀ i ≥ i₀, N ≤ S^i n` | Lean `syracuse_eventually_ge_of_divergent` | Pigeonhole + ciclo ⇒ acotada. |
| Terras en Syracuse | `x, x'` impares: mismo patrón de `j` pasos ⇔ `x ≡ x' (mod 2^{A+1})` | Lean `pattern_iff_modEq` | El `+1` es exacto (`S^j x` impar). |
| Conteo de clases | `#{clases impares mod 2^{A+1} con j pasos y A doses} ≤ C(A−1, j−1)` | Lean `card_residueClasses_le` | Sumas parciales estrictamente crecientes ↪ `powersetCard`. |
| Desigualdad de órbita + → ∞ | divergente ⇒ `∀ ε>0`, cola con `A(i₀,j) log 2 ≤ j (log 3 + ε)` para `j ≥ j₀` | Lean `divergent_dose_bound` (ℕ), `divergent_dose_density` (ℝ) | Doses por paso impar `≤ log₂3` asintóticamente. |

Con `M = 2^71`: `0 < A_k log 2 − k log 3 ≤ k log(1 + 1/(3·2^71)) < k / (3·2^71)`. Es decir
`A_k/k` aproxima `log₂3` con error menor que `1/(2^71 · 3 log 2)`. Lo que falta para Hercher
es: (convergentes de `log₂3` hasta denominador `~10^11`) ⇒ `k ≥ 1.375·10^11`.

## Combinaciones candidatas (no hechas)

1. **Sándwich + convergentes.** La pieza que falta arriba. Requiere calcular convergentes de
   `log₂3` en Lean con cotas rigurosas (`Real.log` + `norm_num` no alcanza; habría que acotar
   `log 3 / log 2` con racionales via series, o importar cotas certificadas).
2. ~~Desigualdad de órbita + estructura de divergentes.~~ **Hecha** (`DivergentDensity.lean`),
   y más fuerte: no "infinitos tramos" sino "toda la cola desde `j₀`", porque no acotada ⇒ → ∞.
   Falta la traducción a `T` (fracción de pasos impares `≥ log 2/log 3`).
3. ~~Ecuación de órbita + paridad periódica.~~ **Hecha** (`ParityAperiodic.lean`), y más
   fuerte de lo previsto: no hizo falta la pieza 2 ni 2-ádicos. El lema abstracto
   `affine_orbit_fixed` (toda sucesión natural con `y_{m+1} 2^A = 3^p y_m + c`, `A ≥ 1`, es
   constante) es reutilizable para cualquier subsucesión afín de una órbita, no solo colas.
4. **Sándwich + Krasikov–Lagarias.** Sin idea concreta todavía.

## Prior art formalizado (ver `docs/prior_art.md`)

`msharpe248/collatz` tiene formalizado, independientemente: Terras (`parity_of_modEq`, `card_oddSteps = C(k,j)`), aperiodicidad (`divergent_itinerary_aperiodic`), densidad de impares (`no_descent_dichotomy`), ciclos cortos hasta 183 divisiones (`cycle_check_183`), y cosas que no tenemos (KL `x^0.8676`, Sturmianas, no-go de certificados). Antes de atacar un lema de esas áreas, mirar ahí. No copiar: verificar y citar.

## Referencias verificadas

- Hercher, *There are no Collatz m-cycles with m ≤ 91*, J. Integer Sequences 26 (2023), arXiv:2201.00406.
- Barina, *Improved verification limit for the convergence of the Collatz conjecture*, J. Supercomputing 81 (2025): verificado hasta `2^71`.
- Tao, *Almost all orbits of the Collatz map attain almost bounded values*, Forum Math. Pi (2022), arXiv:1909.03562.
- Simons, de Weger, *Theoretical and computational bounds for m-cycles of the 3n+1 problem*, Acta Arith. 117 (2005).
- Eliahou, *The 3x+1 problem: new lower bounds on nontrivial cycle lengths*, Discrete Math. 118 (1993).
