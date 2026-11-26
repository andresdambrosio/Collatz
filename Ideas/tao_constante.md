# Idea: Tao con f constante

**Estado:** pasos 1, 1b y 2 hechos; la brecha queda medida (exponencial)
**Frente:** ambos

## Enunciado
Tao (2019): para toda `f(n) → ∞`, casi todo `n` (densidad logarítmica 1) cumple `min órbita(n) < f(n)`.
Con la densidad positiva de los predecesores (M2 de ProofAtlas), **Collatz ⟺ casi todo `n` llega a 1**:
si `n₀` es un contraejemplo, su órbita tiene un `a` no divisible por 3, y los predecesores de `a` (densidad positiva)
también son contraejemplos. O sea, Collatz es "Tao con `f` constante". La pregunta: ¿dónde exactamente necesita
la prueba de Tao que `f → ∞`?

## Filtro de barreras
- ¿Falla para 5n+1? Sí: ahí casi todo diverge. Un argumento tiene que usar la deriva negativa.
- ¿Usa n > 0? Sí (densidad sobre los positivos).
- ¿Va más allá de "casi todos"? Ése es el punto: convierte "todos" en "casi todos", pero con un objetivo fijo.
- **Filtro 3x−1** (corregido en el paso 2): en 3x−1 "casi todo llega a 1" es falso (tres cuencas de densidad positiva),
  pero el enunciado de Tao es `Col_min(N) ≤ C`, y con `C ≥ 17` se cree verdadero para 3x−1. El argumento por
  contradicción (abajo) concluiría "toda órbita baja a `[1, N₀]`" en ambos mapas, y la verificación numérica cierra.
  **3x−1 no mata la vía.** (La primera versión de este filtro estaba mal.)

## Literatura
- Tao, *Almost all orbits of the Collatz map attain almost bounded values*, Forum Math. Pi 10 (2022), e12.
- M2: ProofAtlas (Lean, no arbitrado); auditado en `docs/audit_conjectureA.md`. Es la Conjetura A de Applegate–Lagarias.
- **La equivalencia ya está publicada:** Lech Mazur, comentario en el blog de Tao (6/9/2026, 22:51 UTC): con M2,
  "if any Collatz counterexample exists, the set of counterexamples has positive lower natural density", así que
  "almost all positive integers reach 1 … would suffice". Lo nuestro es sólo una verificación formal independiente
  (con M2 como hipótesis), más la versión logarítmica. Ojo: ProofAtlas ya la tiene en Lean (versión natural).
- Tao, Remark 1.4: la versión acotada ("Col_min ≤ C₀ para casi todo N") es "likely to be almost as hard to settle as the
  full Collatz conjecture, and out of reach of the methods of this paper". Nuestro teorema lo vuelve exacto.
- Mejoras posteriores (no arbitradas, asistidas por IA): Mazur/ProofAtlas (densidad natural, constantes explícitas para
  `a = 1`); jaan.allikvere (Zenodo 10.5281/zenodo.21340150, 7/2026): excepcional `O((log N₀)^{-1/29} + x^{-1/2000})`.

## Formalización
`Collatz/Density.lean` (axiomas estándar, prueba de mutación OK):
- `PredDensity`: hipótesis explícita (M2 para el mapa clásico; ver el puente, paso 1c).
- `collatz_iff_density_one`: Collatz ⟺ `#{n ≤ x : n llega a 1}/x → 1`.
- `collatz_iff_upperDensity_one`: Collatz ⟺ densidad *superior* 1 (más fuerte).
- `reachCount_le_of_not_collatz`: un contraejemplo deja a los convergentes con densidad superior `≤ 1 − c`.

- Paso 1b: `collatz_iff_logDensity_one` (Collatz ⟺ `logSum ReachesOne x / log x → 1`) y
  `collatz_iff_upperLogDensity_one`; `logSum_le_of_not_collatz` (un contraejemplo da `logSum R x ≤ (1−c) log x + K`).
  Pasaje de densidad natural a logarítmica por sumación por partes (`phi_growth`). Dos mutaciones rechazadas.

- Paso 1c (puente): `M2.Statement` transcribe literalmente el enunciado de M2 (mapa clásico, `Nat.count` sobre `n < X`,
  decidibilidad clásica) y `M2.predDensity_of_statement : M2.Statement → PredDensity`; corolario
  `collatz_iff_logDensity_one_of_M2`. Fidelidad: `scripts/m2_fidelity/M2Fidelity.lean`, compilado dentro del clon de
  ConjectureA (Lean v4.30), prueba `M2.Statement` con el teorema de ProofAtlas (axiomas estándar; la mutación `1 < c`
  falla). No se puede importar M2 directamente (~124k líneas, otra versión de Lean).
- **Prior art formal:** el paquete de ProofAtlas ya tiene en Lean la versión natural
  (`universal_reaches_one_of_arbitrarily_dense_convergence`, `positive_nonconvergence_lower_density_of_counterexample`).

## Paso 2: dónde necesita Tao que `f → ∞` (lectura de arXiv:1909.03562 v7)
- **Forma cuantitativa (Teorema 3.1):** `ε(N₀) :=` densidad log. de `{N : Col_min(N) > N₀}` `≪ (log N₀)^{-c}`, uniforme en `x`.
  Teorema 1.3 sale tomando `N₀ = inf_{N ≥ x} f(N)`: hace falta `f → ∞` sólo porque `(log N₀)^{-c}` no es 0.
- **De dónde viene el `log`:** la prueba telescopea escalas `x^{α^{-j}}` (α = 1,001) con la Prop. 1.11:
  (1.19) `P(T_x = ∞) ≪ x^{-c}` ("fácil", polinomial) y (1.20) `d_TV(Pass_x(N_{x^α}), Pass_x(N_{x^{α²}})) ≪ log^{-c} x`
  ("la más difícil"). (1.20) hereda el `log` de la Prop. 1.17: `E e(ξ·Syrac(ℤ/3ⁿ)/3ⁿ) ≪_A n^{-A}` con `n ≍ log x`.
  Tao: "it is possible that the bound in Proposition 1.17 could be improved, perhaps to as far as O(exp(−cn))", y
  (1.20) quizá "all the way to x^{-c}". No lo intenta.

## La brecha, medida
Sea `m*` el menor contraejemplo (si existe; `m* > 2⁷¹`) y `a` un elemento de su órbita no divisible por 3, con `a ≈ m*`.
Todos los predecesores de `a` son contraejemplos, así que tienen `Col_min ≥ m*`:

    c_a  ≤  ε(m* − 1)        (M2 abajo, Tao arriba)

Para una contradicción hace falta `ε(N₀) < c_a` para `a ≳ N₀`. ¿Cuánto vale `c_a`? Numéricamente
(`scripts/tree_density.py`, `n ≤ 2·10⁶`): para `a` genérico, `dens(predecesores de a) ≈ C/a` con `C` entre 1 y 30
(a = 1001: 0,0075; 10007: 0,00086). Es lo esperable: una órbita visita O(1) valores por bloque diádico, así que el
promedio de `c_a` sobre `a ∈ [A, 2A]` es `≍ 1/A`. Entonces:

- **hace falta** `ε(N₀) = o(1/N₀)` (con las constantes explícitas de M2 para todo `a`);
- **Tao da** `(log N₀)^{-c}`; lo mejor publicado (no arbitrado) `(log N₀)^{-1/29}`;
- **aun con las mejoras que Tao especula** (exp(−cn) en la Prop. 1.17, `x^{-c}` en (1.20)) se llegaría a `N₀^{-c'}`
  con `c'` chico, y hace falta `c' > 1`.

La brecha es **exponencial** (de `(log N₀)^{-c}` a `N₀^{-1}`). Y no es casual: `1/N₀` es la densidad de *un solo árbol*
de predecesores. Pedir `ε(N₀) = o(1/N₀)` es pedirle a un método probabilístico que vea conjuntos tan finos como la
cuenca de una órbita individual: es el muro de "una sola órbita" de las rondas 1–5, ahora con número.

## Por qué falló / qué aprendimos
La reducción es correcta y está verificada (no es nueva: Mazur 2026). Convierte Collatz en un enunciado de "casi todos",
pero la cota de excepciones necesaria es del tamaño de un árbol de predecesores, `≍ 1/N₀`, exponencialmente por debajo
de lo que dan los métodos de Tao. Única pregunta cuantitativa que queda viva: ¿cuál es el mejor exponente posible para
la Prop. 1.17 (decaimiento de la transformada de Fourier de las variables de Syracuse)? Aun exponencial, no alcanza solo.
