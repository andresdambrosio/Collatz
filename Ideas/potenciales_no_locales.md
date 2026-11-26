# Idea: potenciales no locales (descenso por bloques, rasgos de cola, mirada hacia adelante)

**Estado:** cerrada (ronda 11, 2026-11-26). Lo de bloques está refutado con una prueba corta; los rasgos de cola
fallan con medida exacta y testigos explícitos; el ingrediente mínimo resulta ser el funcional de excursión
`G_ε`, y que sea finito en todo `n` es equivalente a "no hay órbitas divergentes".
**Frente:** divergencia, sobre todo. Una potencial que baja también excluye ciclos grandes.

## Enunciado
La ronda 10 cerró `V = λ·largo + Σ f(ventanas)` con descenso en **cada** paso. Hay tres preguntas.
1. ¿Sirve pedir descenso por **bloques**, `V(S^{j+B} n) ≤ V(S^j n) − ε`, o en **algún** paso dentro de los próximos `B`?
2. ¿Sirven rasgos **no locales** como el largo de la tira final de unos, `t₁ = v₂(n+1)`, la distancia 2-ádica a los
   ciclos `−5` y `−17`, o el tamaño?
3. ¿Cuál es el ingrediente mínimo que haría falta, y a qué equivale?

Notación: `S` es Syracuse `(3n+1)/2^v`. Todo se mide en bits. Para una potencial de ventanas de ancho `k` uso:
- `f₁ = f(1^k)`;
- `F(z)` = peso medio por bit de `f` sobre la expansión 2-ádica periódica de `z`;
- `f̄ = 2^{−k} Σ_w f(w)`;
- `μ = λ + f̄`, el crecimiento de `V` por bit en números típicos.

## Filtro de barreras
- **¿Falla para 5n+1?** Sí, en los tres puntos:
  - el teorema de bloques no usa nada de 3x+1 salvo que la sombra de `−1` crece (`log₂3 − 1 > 0`);
  - `G_ε` es `+∞` en casi todo punto para 5x+1, porque la deriva `log₂5 − 2` es positiva.

  O sea, nada distingue: es consistente con que 5x+1 diverja.
- **¿Usa n > 0?** Las potenciales sólo usan `n > 0` a través de `log n`. Los testigos son enteros positivos que
  copian, 2-ádicamente, puntos negativos o racionales no enteros. `G_ε` es finito en los positivos si y sólo si no
  hay divergencia, y es infinito en `−1`, `−5`, `−17`, `−19/11`, …
- **¿Va más allá de mod 2^k y de "casi todos"?** Los rasgos de cola y `G_ε` son no locales. Pero `G_ε < ∞` en casi
  todo punto (Haar) es fácil (Terras, Everett). El "para todo `n`" es la conjetura.
- **¿Usa algo de 3x+1?** Sólo la deriva negativa, en `G_ε`. Es el único lugar donde aparece.

## Literatura
- **Ítem 1, ya hecho y más fuerte.** rStation **collatz_208**, Teorema A y Corolario 1 (leído).
  - Alcance: los puntajes `Σ g(ventanas) + Σ β_r v_p(n − c_r) + acotado` (centros racionales), acotados por debajo,
    no fuerzan una bajada fija ni con reloj **adaptativo** de hasta `(log₂ n)/100` pasos.
  - Método: testigos normales de Wren, más la extracción del último mínimo (Sodelin).
- **Antecedentes de un paso:** collatz_98 (Wren, vía Nashida Teorema 7.1 y Host) y Nashida, Cor. 9.1 (ventanas
  acotadas con etapas).
- **Ítem 2:** los rasgos `v₂(n − c)` con centros racionales (como `t₁`, `−5` y `−17`) **están incluidos** en
  collatz_208. collatz_3 excluye `H(n) + Φ(n mod M, v₂(n+1)) + …` para el paso impar. collatz_32 trata la barrera de
  signo.
- **Ítem 3:**
  - Terras (1976) y Everett (1977): el tiempo de parada es finito para casi todo `n`. Terras definió el tiempo de
    parada de coeficiente, y su conjetura `σ = τ` sigue abierta.
  - Rozier y Terracol (arXiv:2502.00948) estudian las secuencias "paradójicas", donde el valor supera al inicial
    después del tiempo de parada.
  - Construir una potencial como "máximo del futuro" es el recíproco estándar de Lyapunov. No encontré una fuente
    específica para Collatz (búsquedas web sin resultado), pero **no lo reclamo como nuevo**: es elemental.
- **Lo que aporta esta ronda:** una prueba elemental alternativa del caso de bloques acotados, con testigos
  **periódicos** explícitos en lugar de normales; la medida exacta de fallas de los rasgos de cola; y la identificación
  de `G_ε` como ingrediente mínimo, con su equivalencia.

## Evidencia y argumentos

### 1. Bloques: refutado (prueba elemental) [verificado numéricamente; prueba en papel, no en Lean]
**Hipótesis.** `V = λL + Σ_{i} f(w_i)` (`f` real cualquiera) está acotada por debajo en los positivos. Además, para
todo `n` grande hay `j ∈ [1, B]` con `V(S^j n) ≤ V(n) − ε`. Esto incluye el caso de bloques fijos. Iterando, en cada
ventana de tiempo `[T, T+B]` hay un `j` con `V(S^j n) ≤ V(n) − ε⌊T/B⌋`.

- **(0) `μ ≥ 0`.** El promedio de `V` sobre los `n` de largo `L` es `μL + O(1)`. Si `μ < 0`, `V` no está acotada por
  debajo.
- **(a) Sección media: `f₁ ≤ f̄`.** Sea `z_N = −3^{−N}`. Su expansión 2-ádica es periódica, con bloque
  `Q = (2^p − 1)/3^N` y `p = 2·3^{N−1}`. Tomo `n = 2^{K+M} + (c−1)2^K + (2^K − 1)` con `c ≡ z_N (mod 2^M)` y
  `K ≥ N + B + k`.
  1. Como `n ≡ −1 (mod 2^K)`, vale `S^j n = 3^j 2^{K−j}(2^M + c) − 1`.
  2. A tiempo `N`, la sección media de `M` bits (patrón `z_N`) se volvió una tira de unos (`3^N z_N = −1`), y sigue
     así hasta el tiempo `N + B`.
  3. Entonces `V(S^j n) − V(n) = M(f₁ − F(z_N)) + O_{N,B}(1)` para `j ∈ [N, N+B]`. Con `M → ∞` sale
     `f₁ ≤ F(z_N)`.
  4. Como 2 es raíz primitiva módulo `3^N`, las ventanas de `z_N` están equidistribuidas: `F(z_N) → f̄`.
- **(b) Sombra de −1: `f₁ ≥ (log₂3 − 1)λ + log₂3·f̄ + ε/B`.** Tomo `n = 2^K t − 1` con `t` uniforme de `T ≥ K log₂3`
  bits.
  1. `S^j n = 3^j 2^{K−j} t − 1`. A tiempo `j ≈ K`, el número es `3^K t − 1` con ventanas típicas en promedio. Las
     cifras bajas son exactamente uniformes, y las altas son uniformes salvo las `O(1)` de arriba.
  2. Promediando en `t`: `K(0,585λ + 1,585f̄ − f₁) + O(B) ≤ −εK/B`.
- **(a) + (b):** `0,585·μ ≤ −ε/B < 0`, que contradice (0). ∎

Para `μ > 0` el argumento tolera `B` hasta del orden de `K ~ log n`. Para `μ = 0` hace falta `B = o(log n)`. No lo
afino: collatz_208 ya tiene el enunciado fuerte.

**Experimento** (`scripts/nl_window_witness.py 400 7`): construye testigos explícitos y busca, por cálculo directo
de `V`, un bloque con `V(S^{j+B}) > V(S^j) − ε`.
- **Controles:**
  - la fórmula de la sombra tiene 0 discrepancias en 300 casos;
  - la equidistribución de `z_N` da un desvío relativo máximo de 0,025 para `k = 8`, `N = 9`;
  - el `ΔV` predicho coincide con el medido (p. ej. 4455 contra 4456 y 1243 contra 1223).
- **Resultado:** 400 potenciales al azar, con `k ∈ {3,4,5,6,8}`, `B ∈ {1, 2, 5, 20, 100}`, `f` con signo y `f`
  diseñadas para pagar la tira de unos. **Todas** tienen testigo: 320 por la sección media y 80 por la sombra.
  Ninguna quedó sin testigo.

### 2. Rasgos de cola [medida exacta + conteo directo; testigos explícitos]
`scripts/nl_tail_features.py 100000 3`. Las muestras son impares de ~2^120.

**V₁ = log₂ n + c·t₁.**
- **Dónde falla:**
  - Si `t₁ ≥ 2`, entonces `v = 1` y `t₁` baja 1, así que alcanza con `c > log₂(3/2)`.
  - Si `t₁ = 1`, entonces `v ≥ 2` y la tira nueva `t'` es geométrica e independiente. Falla si y sólo si
    `c(t' − 1) > v − log₂3 − ε`.
- **Óptimo:** entre todas las `g(t₁)`, la mejor es `g = c·t₁` con `c = log₂(3/2) + ε`, porque cualquier otra sube
  más rápido. Su medida exacta de fallas es **0,1431**; el conteo directo da 0,1428.
- **Control:** `c = 0,5`, `0,7`, `1` y `2` dan 0,643, 0,146, 0,167 y 0,214, con predicción y medida coincidentes al
  0,3 %.
- **La falla dominante:** `n ≡ 1 (mod 4)` con `v = 2` y `t' ≥ 2` (6,2 % con `t' = 2`). Es exactamente "aparece una
  tira nueva tras pocas divisiones".

**Agregar profundidades en `−5` y `−17` (V₂, V₃).**
- Con pesos promedio de ciclo (`c₅ = (2log₂3 − 3)/3 + ε` y `c₁₇ = (7log₂3 − 11)/11 + ε`), las fallas **suben** a 0,267
  y 0,314: los rasgos nuevos también saltan.
- Las sombras de `−5` y `−17` quedan pagadas en total (`ΔV = −2,3` en 150 pasos), pero no paso a paso. Pagarlas paso a
  paso pide pesos por fase.

**El problema de fondo (argumento y testigo).** Hay infinitos ciclos **racionales no enteros** de deriva positiva,
uno por cada palabra de valuaciones con `3^p > 2^D`:

| palabra de valuaciones | punto fijo racional | `3^p/2^D` |
|---|---|---|
| `(1,1,2)` | `x = −19/11` | 1,69 |
| `(1,1,1,2)` | `x = −65/49` | 2,53 |
| `(1,2,1,1,2)` | `x = −287/115` | 1,90 |

- Los positivos `≡ x (mod 2^K)` siguen la palabra durante unos `K/D` ciclos.
- Medido con `K = 900`: `log₂` crece +168, +238 y +116 bits, y `V₃` sube lo mismo. Fallan entre 50 % y 67 % de los
  pasos, y **ningún rasgo pasa de 9** en toda la órbita.
- Con finitos centros no se cubren. El conjunto `{G_ε = ∞}` de ℤ₂ es no numerable y denso.
- El tamaño (primeras cifras) no ayuda: `log n` ya está en `V`, y collatz_66/203 muestran que las cifras iniciales no
  distinguen 3x+1 de 5x+1.

### 3. Ingrediente mínimo: el funcional de excursión [elemental; verificado numéricamente]
Definiciones (en bits):
- `W₀ = 0` y `W_{j+1} = W_j + log₂3 − v_j + ε`;
- `G_ε(n) = sup_j W_j(n) = max(0, W₁(n) + G_ε(Sn))`.

**Recíproco.**
- **Basta:** `V = log₂ n + G_ε` cumple `V(Sn) − V(n) ≤ −ε + log₂(1 + 1/(3n))`. Control en `n < 10^6`: máximo de
  `ΔV + ε − log₂(1 + 1/3n)` igual a `9·10⁻¹⁵`.
- **Es necesario:** toda `V = log₂ n + g` con `g ≥ 0` que baje `ε` por paso cumple, iterando,
  `g(n) ≥ G_ε(n) − Σ_i log₂(1 + 1/(3S^i n))`.

**Equivalencia.**
1. Si alguna órbita diverge, `G_ε = ∞` en ella: `W_j = log₂(S^j n/n) + jε − o(j)`.
2. Si todas las órbitas son eventualmente periódicas (y `ε` es menor que el margen `(D − p log₂3)/p` de cada ciclo
   positivo), entonces `G_ε < ∞`.

Así que **"`G_ε` finito en todo `n`" equivale a "no hay órbitas divergentes"**, módulo el margen de ciclos
hipotéticos. Es la conjetura (mitad de divergencia), no un paso hacia ella.

**Truncaciones** `V_d = log₂ n + max_{j≤d} W_j`, que miran `d` pasos, o sea `n mod 2^{~d}`:
- falla si y sólo si la órbita bate su récord exactamente en el paso `d + 1`;
- la medida (Haar, Monte Carlo) contra enteros de ~2^400 da:

| d | 0 | 4 | 16 | 32 | 64 |
|---|---|---|---|---|---|
| Haar (Monte Carlo) | 0,498 | 0,175 | 0,035 | 0,0092 | 0,0011 |
| enteros de ~2^400 | 0,505 | 0,172 | 0,035 | 0,0085 | — |

- Decae exponencialmente, como la cola del tiempo de parada (Terras), pero **nunca es 0**: `V_d` es un rasgo de borde
  y lo mata la sombra de `−1` (ronda 10).
- En `n < 10^6` hace falta mirar hasta `J = 112` pasos (`n = 837799`; mediana 3). `J` correlaciona poco con el tiempo
  de parada (0,26) y lo supera en el 36 % de los casos: la excursión con margen sigue después de bajar de `n`.

## Formalización
Ninguna en esta ronda. Candidatos baratos:
- el recíproco `V = log n + G_ε` (elemental), aunque sólo reformula la conjetura;
- la parte (a) del teorema de bloques, la de la sección media, que es aritmética exacta con `3^N z_N = −1`.

## Por qué falló / qué aprendimos
- **Bloques:** no cambian nada. La sección media de patrón `−3^{−N}` se convierte en una tira de unos en `N` pasos y
  obliga a `f₁ ≤ f̄`; la sombra de `−1` obliga a `f₁ ≥ f̄ + 0,585μ`. Las ventanas no pueden pagar la tira de unos sin
  pagar todo. La versión adaptativa con deadline `(log n)/100` ya está en collatz_208.
- **Rasgos de cola:** pagan cada ciclo negativo concreto, pero las fallas son "aparece una tira nueva" (medida exacta
  0,143 para el mejor `t₁`). Además hay infinitos ciclos racionales no enteros de deriva positiva (`−19/11`, …) cuyas
  sombras crecen con todos los rasgos acotados. Ningún conjunto finito de centros alcanza.
- **Ingrediente mínimo:** la potencial tiene que dominar `G_ε`, la excursión máxima futura del paseo de paridades.
  Que sea finita en todos los enteros positivos **es** "no hay divergencia". Las aproximaciones finitas (`V_d`, colas)
  dejan una medida de fallas que decae exponencialmente pero nunca es 0: la diferencia entre "casi todos" y "todos".
  La única información que separa a los positivos de `{G_ε = ∞}` es la positividad con tamaño arquimediano. Es el
  mismo muro de las rondas 6–10.
