# Laboratorio de ideas: hacia una prueba completa de Collatz

Iniciado el 2026-11-23. Objetivo: la conjetura completa, no resultados laterales.

## Protocolo
1. **Idea completa**: debe decir cómo descarta *a la vez* los ciclos no triviales y la divergencia
   (o por qué una mitad se reduce a la otra).
2. **Filtro de barreras** (`PLAN.md`): ¿falla para `5n+1`? ¿usa `n > 0`? ¿va más allá de mod `2^k`
   y de "casi todos"? ¿usa algo específico de `3n+1`?
3. **Prior art**: casi todo se intentó; buscar antes de invertir.
4. **Experimento en Python** que podría refutarla.
5. **Lean** sólo para lo que sobreviva. Lean es el juez final.
6. **Registro del fracaso** con su causa exacta (un archivo por idea en `Ideas/`).

## Lecciones de Riemann / cuasi-Riemann (nov. 2026)
- Cuasi-RH (OpenAI): "no necesitó conceptos nuevos"; combinó un ingrediente existente poco explotado
  (fórmula de Dunn–Radziwiłł 2021). ⇒ **Minar la literatura en busca de herramientas que casi alcanzan.**
- RH (Alpoge + Claude, sin verificación independiente aún): entregada como biblioteca de Lean.
  ⇒ **El kernel como juez permite aceptar pruebas que nadie entiende del todo.**

## Dos hechos que toda prueba tiene que usar
- **Divergencia ⇒ estadística atípica.** Una órbita divergente promedia ≤ `log₂3 ≈ 1,585` divisiones por 2
  por paso impar (Forge: `divergent_dose_density`), cuando lo típico es 2. En `5n+1` la órbita *típica*
  diverge (alcanza con < `log₂5 ≈ 2,32`), así que una prueba tiene que explotar que en `3n+1` divergir exige
  ser atípico.
- **Ciclos ⇒ aproximación diofántica.** Un ciclo con `k` impares y `A` doses exige
  `0 < A − k·log₂3 ≤ k·log₂(1 + 1/(3·mín))`; las cotas actuales vienen de las fracciones continuas de `log₂3`.

## Ronda 1 (triage)

| # | Idea | Veredicto | Causa |
|---|---|---|---|
| 1 | Subir el "casi todos" de Tao a "todos" vía el árbol inverso: el conjunto `C` de contraejemplos es cerrado hacia adelante y hacia atrás; si tuviera densidad positiva, contradiría a Tao | **muro conocido** | Tao no distingue "baja de `f(n)`" de "llega a 1": `C` tiene mínimo `c₀` y sus órbitas bajan hasta `c₀`, compatible con Tao. Krasikov–Lagarias dan ≥ `x^0,84` elementos en un árbol, no densidad positiva |
| 2 | Función potencial calculada por autómata con pesos (generaliza la reescritura) | **bloqueada / sin resultados** | Barrera de Nashida (naturales, árticas) + nuestra búsqueda racional `d = 2` vacía (`vecinos_de_T.md`) |
| 3 | Conjugación 2-ádica (Lagarias, Bernstein): todo vector de paridad infinito lo realiza un único entero 2-ádico; divergencia ⇔ un vector atípico se realiza por un natural | **reformulación** | Equivale a la conjetura de periodicidad de Lagarias; no da palanca nueva por sí sola |
| 4 | Ciclos: método de Simons–de Weger (`m` picos) para todo `m` | **muro** | Necesita cotas de formas lineales en logaritmos (Baker) uniformes en `m`; abierto |
| 5 | **Rigidez / equidistribución**: una órbita divergente tiene estadística mod `2^j` atípica; si un teorema de rigidez forzara a toda órbita divergente a equidistribuirse, contradicción | **viva, por evaluar** | Usa el hecho de atipicidad (pasa el filtro de `5n+1` en principio). Riesgo: equidistribución de UNA órbita determinista es del tipo "normalidad de números concretos", que nadie sabe probar. Ingredientes candidatos: Furstenberg ×2×3, Host, Rudolph–Johnson; el mapa no es una acción de grupo |
| 6 | **Minería de ingredientes** (lección cuasi-RH): barrer resultados recientes (2015–2026) cercanos — dinámica 2-ádica/3-ádica, S-unidades, sumas de dígitos en bases 2 y 3 (Mauduit–Rivat y sucesores), sucesiones automáticas — buscando uno que casi alcance | **viva, por hacer** | Es un proceso, no una idea; produce candidatos para la ronda 2 |

## Ronda 1, idea 6: minería de ingredientes (2026-11-23) — resultado

Fuentes: Tao 2011 (blog, Littlewood–Offord y potencias de 2 y 3), Chang 2026 (arXiv:2603.11066),
Drmota–Spiegelhofer 2025 (arXiv:2501.00850), Spiegelhofer 2021 (arXiv:2105.11173), búsquedas sobre ×2×3 y Tao 2019.

- **Ciclos, forma precisa** (Böhm–Sontacchi, en Tao 2011): no existen `k ≥ 1` y `0 = a₁ < … < a_{k+1}` con
  `(2^{a_{k+1}} − 3^k)·n = Σᵢ 3^{k−i} 2^{aᵢ}` y `n > 1`. Es una afirmación **puntual de no divisibilidad**.
  Littlewood–Offord da equidistribución módulo `q = 2^a − 3^k`, pero no puede excluir el residuo 0.
  Según Tao, una prueba necesita teoría de trascendencia o una "separación exponencial" nueva entre potencias de 2 y 3.
  Problema de juguete que propone: los dígitos en base 3 de `2^n` (Erdős; Dimitrov–Howe: un contraejemplo
  necesita ≥ 25 potencias de 3).
- **Dígitos en bases 2 y 3**: Drmota–Spiegelhofer prueban que `(s₂(n), s₃(n))` toma casi todos los pares (densidad).
  Son resultados **distribucionales** (Baker + subespacio p-ádico). No tocan la no divisibilidad puntual.
- **×2×3**: progreso reciente (Rudolph–Johnson "sin dinámica", 2026), pero sin puente directo con Collatz;
  el mapa de Syracuse no es una acción de grupo.
- **Tao 2019**: sin mejoras; él mismo dice que pasar de "casi todos" a una cota absoluta es tan difícil como la conjetura.
- **Chang 2026 (antecedente directo de este laboratorio)**: colaboración humano + Claude + GPT, 233 páginas, 29 enfoques,
  ~630 "resultados formales" (no verificados en ningún asistente de pruebas, por lo que pude ver). Su conclusión
  ("Paradigm Exhaustion"): todos chocan con el mismo obstáculo, la **brecha distribucional → puntual**.

**Conclusión:** no apareció ningún ingrediente que "casi alcance" al estilo cuasi-RH. Todas las herramientas fuertes
cercanas son distribucionales; lo que falta es siempre un enunciado puntual (una órbita, una divisibilidad).
Cualquier idea de la ronda 2 tiene que atacar esa brecha de frente, o no vale la pena.

## Ronda 2, opción 1: catálogo de Chang (2026-11-23)

Leído de arXiv:2603.11066v6, §13 (lista de los 29 paradigmas) y §F.2. Su "Teorema 13.1" no es un
teorema matemático, es una evaluación: los 29 dan resultados de densidad 1 y mueren en el paso a "todo n".
**Coincidencias con nuestra ronda 1:** idea 1 = su #13 (amplificación de Tao) y #14 (Borel–Cantelli);
idea 2 = #16 (potencial 2-ádico) y #6 (autómatas); idea 3 = #3, #15 y #22 (2-ádicos); **idea 5 = su #4
(rigidez de medidas: inaplicable, porque ×3+1 ≠ ×3 y el exponente es variable)**. Las cuatro ya estaban muertas.

Otros callejones registrados por ellos (a evitar): espectral (gap uniforme ⇒ equidistribución, no órbitas
individuales), S-unidades/subespacio (aparecen primos fuera de {2,3}), Baker (ya capturado por fracciones continuas),
martingalas, criba modular (bypass de Mersenne: `2^L − 1` sobrevive a profundidad `L − 1`), Fourier booleano,
compacidad en ℤ₂, coalescencia de órbitas, suma de dígitos (sólo en esperanza), Iwasawa, LLL, entropía.

Lo abierto que dejan: (a) **divergencia**: ¿puede un natural sostener infinitas rondas "sin descenso"
manteniendo compatibles sus polinomios de acarreo a toda escala? ("no hay obstrucción combinatoria de
profundidad finita"); (b) **ciclos**: obstrucción de logaritmo discreto (`2^{v_j} ≡ T_j mod D`, `v_j ∈ [0, F]`),
100 % de bloqueo computacional para `L ≤ 500`, sin prueba para todo `L`.

**Advertencias:** nada está verificado en un asistente de pruebas; abunda el lenguaje de "teorema" para
evaluaciones; 630 "resultados" sin prueba de la conjetura. Lección para nosotros: el volumen no es progreso.

**Qué deja vivo:** sólo métodos *puntuales por naturaleza*, que no pasen por densidad:
1. certificados de terminación (reescritura; son puntuales, pero tienen la barrera de Nashida en las clases simples);
2. no divisibilidad para ciclos (Tao: trascendencia o separación nueva entre potencias de 2 y 3);
3. problemas de juguete puntuales (Erdős: dígitos ternarios de `2^n`) como entrenamiento del músculo que falta.

## Ronda 3: certificados de terminación con etiquetado semántico aritmético (2026-11-23)

Idea: etiquetar `𝒯` con el valor del prefijo mod `m` (modelo de Zantema: `[▷] = 1`, `[f]x = 2x`, `[t]x = 2x+1`,
`[d]x = 3x+d`, `[◁]` constante; 𝒯 termina ⇔ 𝒯_m termina) y buscar matrices sobre el sistema etiquetado.
Está fuera del alcance declarado de Nashida e inyecta la información mod 3 que usa su barrera.
- `scripts/labelled_neighbors.py`: reglas etiquetadas que NO aparecen en ciclos de los vecinos 3x−1 / 3x−3
  (en lo explorado): `m = 2`: 1/19; `m = 3`: 0/27; `m = 4`: 5/35; `m = 8`: 22/67; `m = 9`: 33/75
  (con `m` grande hay más porque los ciclos de los vecinos tocan pocos valores: el filtro sólo no las descarta).
- `scripts/labelled_search.py` (z3, matrices naturales EWZ): `m ∈ {2,3,4}, d = 1, B = 6`: **unsat**;
  `m = 2, d = 2, B = 3`: **unsat**; `m = 3, d = 2, B = 3`: unknown. Control positivo (sin reglas de inicio): sat.

**Lo que aprendimos (más importante que el resultado):** eliminar una regla etiquetada `ρ_x` es el teorema
"en toda derivación infinita, `ρ` se aplica con prefijo ≡ `x` (mod `m`) sólo finitas veces". Para una órbita
divergente, que recorrería todos los residuos (equidistribución), eso es tan difícil como Collatz. **Toda
eliminación informativa de una regla es tan difícil como la conjetura**; las que no lo son resultan triviales.
Es la brecha densidad → puntual en versión reescritura: un certificado de terminación de `𝒯` *es* una prueba,
con forma de función potencial calculada por un autómata con pesos, y nada indica que exista uno de tamaño razonable.
Las búsquedas chicas no pueden encontrarlo salvo que exista una estructura que nadie vio.

## Ronda 4: obstrucción de logaritmo discreto de Chang para ciclos (2026-11-23) — colapsa

Leído en Chang §(vi), resultados 591–630. Ecuación del ciclo `m·D = Q`, `D = 2^E − 3^L`, `F = E − L`.
- "`D > 2^F` para todo `L ≥ 3`" equivale a `β = E − L·log₂3 > −log₂(1 − 2^{−L})`: una cota inferior de forma
  lineal en logaritmos (Laurent 2008) más cómputo hasta `L ≤ 2500`. Correcto pero modesto.
- El "bloqueo del 100 %" es sólo para ciclos cuya sucesión de divisiones por 2 es **constante por tramos con
  `k ≤ 3` tramos** (`k = 2` hasta `L ≤ 500`, `k = 3` hasta `L ≤ 30`), verificado computacionalmente.
- **Eso es más débil que lo conocido:** los ciclos de `m` picos de Steiner (1977, `m = 1`, todo `L`),
  Simons–de Weger (2005, `m ≤ 68`, luego 76) y **Hercher (2023, JIS 26: no hay `m`-ciclos con `m ≤ 91`, todo `L`)**
  cubren justamente las sucesiones con pocos tramos, para toda longitud, vía Baker + reducción con LLL/fracciones continuas.
- El caso general (cualquier cantidad de tramos) es el problema de ciclos completo.

**Conclusión:** la "pregunta abierta" de Chang sobre ciclos es una versión más débil de resultados publicados; atacarla
es atacar los ciclos en general, cuyo estado del arte es Hercher `m ≥ 92` (y `≥ 1,1·10¹¹` impares con verificación a `2^71`).
Cualquier avance real exige una idea para ciclos con **muchos** tramos, donde Baker deja de servir porque la forma
lineal tiene `m` términos.

## Ronda 5: problema de juguete de Erdős (dígitos ternarios de 2^n) (2026-11-23)

Estado: el enunciado completo (sólo 1, 4, 256 sin dígito 2) y la versión débil (finitas excepciones) están **abiertos**.
Computacional: `n ≤ 2·3^45` (Saye 2022, JIS 25). Teoremas: `#{n ≤ X excepcionales} ≤ 1,62·X^{log₃2}` (Narkiewicz 1980;
Lagarias 2009 lo extiende a `λ·2^n` 3-ádico), dimensiones de Hausdorff de los conjuntos excepcionales (Lagarias);
Dimitrov–Howe (arXiv:2105.06440): 1, 4, 256 son las únicas potencias de 2 que son suma de ≤ 25 potencias distintas de 3,
con congruencias elementales. Idowu (arXiv:2610.03789, sin arbitrar): reformulación con repunits, sin prueba.

Blanco natural: la pregunta abierta de Lagarias, `O(X^β)` con `β < log₃2`, combinando el método de los dígitos finales
(3-ádico: `2^n mod 3^k` depende de `n mod 2·3^{k−1}`) con el de los iniciales (rotación por `θ = log₃2`).
Análisis: restringir la rotación a la progresión `n ≡ r (mod 3^k)` exige controlar la discrepancia de `m·(3^k θ) mod 1`,
o sea los dígitos en base 3 de `hθ` a partir de la posición `k`. Baker sólo da corridas `≤ (C−1)k`, inútil.
Hace falta información tipo **normalidad de `log₃2` en base 3** (órbita ×3 de `θ`): barrera de Furstenberg.

## Síntesis de las cinco rondas

Todas las vías terminan en el mismo problema: **probar algo sobre la estadística de UNA órbita concreta**:
- Collatz (divergencia): la órbita de Syracuse de un número (Chang: "brecha distribucional → puntual");
- Collatz (ciclos con muchos picos): no divisibilidad sin herramienta diofántica (Baker sirve sólo con pocos picos);
- reescritura: toda eliminación informativa de una regla equivale a controlar residuos a lo largo de una órbita;
- Erdős: la órbita ×3 de `log₃2` (normalidad);
- Furstenberg ×2×3: órbitas individuales.

La matemática actual no tiene herramientas para enunciados puntuales de este tipo en ningún caso conocido. El
laboratorio no encontró una vía con chances razonables. Los resultados verificados del proyecto (Lean) son
reformulaciones, barreras y cotas, no avances hacia la prueba.

## Próximos pasos
- Idea 5: precisar qué teorema de rigidez haría falta y en qué espacio, y ver numéricamente cuán atípica
  es una órbita larga "forzada" (vectores de paridad con densidad alta realizados por Terras).
- Idea 6: búsqueda bibliográfica dirigida (sumas de dígitos simultáneas en bases 2 y 3 es el candidato
  más natural: un número tiene que "verse" a la vez en ambas bases).

## Ronda 6: deformar el análogo resuelto de 𝔽₂[x] hacia ℤ, agregando acarreos (2026-11-23) — viva
Detalle en `Ideas/acarreos.md`. En 𝔽₂[x] la conjetura está demostrada (Hicks–Mullen–Yucas–Zavislak 2008) y equivale
a 3n+1 **sin acarreos** (Monks 2025). Primera familia, `ℤ[2^{1/d}]` (acarreo diferido): todo diverge para `d ≥ 2`
(se pierde la contracción arquimediana); descartada. Segunda, `C_k` (acarreos que mueren tras `k` posiciones):
interpola entre 𝔽₂[x] (`k = 0`) y ℤ (`k = ∞`). No se observa divergencia para ningún `k`, hay ciclos espurios y,
para `k = 2` y `k ≥ 4`, excursiones lineales como en ℤ. Pasa el filtro 5n+1 para `k ≥ 4`.
**Cerrada:** no hay potencial local monótono para `C_2` (LP infactible hasta ventanas de 7 bits; `C_0` factible, Collatz
infactible). Todos los `C_k` son biyecciones de ℤ₂ que conservan la medida, conjugadas al shift como Collatz: la
dificultad aparece completa con acarreos de largo 2. Lo que distingue los problemas es sólo la positividad y el tamaño arquimediano.

## Ronda 7: Berg–Meinardus / Opfer (análisis complejo) (2026-11-23) — cerrada
Detalle en `Ideas/berg_meinardus.md`. `K = ker U ∩ ker V` ≅ funciones constantes en las componentes del grafo de
Collatz: la condición de holomorfía es vacía (coeficientes 0/1), y la formulación es "el grafo es conexo" en otro idioma.
El hueco de Opfer (2011): su algoritmo de aniquilación es el mapa de Collatz comprimido (verificado para ℓ < 2·10⁵),
así que su Teorema 4.17 es la conjetura: la prueba es circular. Szegő y Mahler/Cobham (Adamczewski–Bell) no aplican.
**Síntesis de las rondas 6–7:** en todas las traducciones probadas (2-ádica, polinomial, acarreos, analítica), el problema
se ve igual o se vuelve trivial. Lo que nunca viaja es la interacción entre el tamaño real y la estructura 2-ádica.
