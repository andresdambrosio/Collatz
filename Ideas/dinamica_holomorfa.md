# Idea: dinámica holomorfa de una extensión entera de Collatz (ronda 11, opción B)

**Estado:** refutada como vía (cerrada): la maquinaria no distingue 3x+1 de 5x+1 y sólo "ve" lo que uno le pone en la interpolación
**Frente:** ambos (sobre todo divergencia)

Etiquetas: **[verificado]** = cálculo propio reproducible (script indicado), **[elemental]** = argumento propio corto,
no formalizado en Lean, **[literatura]** = afirmado en una fuente que leí (se dice cuál), **[no leído]** = sólo conozco la
reseña o el resumen, **[heurístico]**, **[abierto]**.

## Enunciado
Extender `T(n) = n/2` (par), `(3n+1)/2` (impar) a una función entera `f : ℂ → ℂ` y usar la teoría de Fatou–Julia de
funciones enteras trascendentes. La esperanza: "una órbita entera divergente obliga a `f` a tener un objeto `X`
(dominio errante, dominio de Baker, punto de escape en el conjunto de Fatou), y `X` es imposible para esta `f`".

Dos extensiones concretas (en `scripts/hol_lsw.py` y `scripts/hol_naive.py`), para `qx+1` con `q ∈ {3, 5}`:
- **crítica (LSW):** `f(z) = z/2 + ((q−1)z+1)/2 · (1−cos πz)/2 + (α + β cos πz) sin πz`, `α = (q−1)/(4π)`, `β = −(q+1)/(4π)`.
  Cumple `f(n) = T(n)` y `f'(n) = 0` en todo entero. Con `q = 3` es la `f₀` de Letherman–Schleicher–Wood (la fórmula
  coincide con la que transcribe Lagarias). **[verificado]** para `|n| ≤ 200`, error < 10⁻⁵⁵ (E1).
- **ingenua:** `g(z) = z/2 + ((q−1)z+1)/2 · (1−cos πz)/2`, con `g'(n) = 1/2` (par) o `q/2` (impar): la derivada en los
  enteros es la pendiente del tramo afín.

## Filtro de barreras
- **¿Falla para 5n+1?** No: todo lo que se prueba para `q = 3` vale palabra por palabra para `q = 5` (E1–E4, N1–N4).
  Para 5x+1 la misma maquinaria dice "si `7` diverge, hay un dominio errante", y eso **tampoco** se sabe probar.
- **¿Usa n > 0?** La extensión crítica no: los ciclos −1, −5, −17 son superatractores igual que {1, 2}. La ingenua sí
  distingue el signo de los ciclos, pero sólo a través de la identidad elemental del multiplicador (abajo), que es la
  ecuación del ciclo `2^A ≷ 3^k` reescrita.
- **¿Más allá de mod 2^k / de "casi todos"?** Lo que la dinámica ve en un entero depende sólo de los datos de
  interpolación a lo largo de su órbita (valores y derivadas), o sea del vector de paridad: es información 2-ádica.
- **¿Usa la deriva log(3/4)?** Sólo en la extensión ingenua y sólo como exponente de Lyapunov **típico** (estadístico):
  `½ log(3/4)` en el ciclo {1,2}. A lo largo de una órbita concreta la derivada es `|T^k(n)|/|n|` salvo un factor
  acotado: no agrega nada al tamaño.

## Literatura
- **Letherman, Schleicher, Wood (1999)**, "The 3n+1 problem and holomorphic dynamics", *Experimental Math.* 8(3) 241–251,
  DOI 10.1080/10586458.1999.10504402. **[no leído]**: Project Euclid y Taylor & Francis bloquean la descarga automática.
  Lo que sigue viene de la reseña de Lagarias (math/0309224, entrada 115) **[literatura]** y del resumen del editor:
  familia `f_h = f₀ + h(z) sin²πz` (`h` entera arbitraria), todas con `ℤ ⊂ ` puntos críticos; **ℤ ⊂ Fatou**; la componente
  de Fatou de un entero está en la cuenca de un ciclo superatractor o es un **dominio errante** (conjeturan que esto
  último no pasa); **ningún entero está en un dominio de Baker**; existe una órbita divergente ⟺ `f₀` tiene un dominio
  errante que contiene un entero; dos enteros distintos están en componentes distintas, salvo quizás −1 y −2; el eje real
  tiene puntos de Julia entre enteros consecutivos (salvo quizás entre −2 y −1); toda `f_h` tiene al menos un punto
  crítico fuera del eje real.
- **Chamberland (1996)**, DCDIS 2, 495–509, extensión real `x + 1/4 − (x/2 + 1/4) cos πx`. **[no leído]**, según
  Lagarias: derivada schwarziana negativa en ℝ⁺, dos ciclos atractores en `[µ₁, µ₃]` ({1,2} y uno no entero cerca de
  {1,19; 2,14}), **todo ciclo entero positivo no trivial sería atractor**; dinámica caótica en un conjunto de medida 0.
- **Urata (2002)** **[no leído]**, según Lagarias II (math/0608208, entrada 109): una `F` entera para el mapa de Syracuse
  con `F' = 0` en los impares **positivos**; prueba que los impares positivos están en Fatou y los **negativos en Julia**.
  Es la misma lección que abajo: el signo aparece porque se eligió poner puntos críticos sólo en los positivos.
- **Dumont–Reiter (2001, 2003)**, Wang–Yu (2007–08): imágenes de cuencas y tiempos de escape, sin teoremas de este tipo
  (reseñas de Lagarias II; el preprint de Dumont–Reiter lo leí: sólo menciona a LSW).
- **Dağlı et al. (arXiv:2611.11641, 11/2026, preprint, cs.LO)** **[sólo resumen]**: otra extensión entera con
  multiplicador 3/4 en {1,2}, linealización de Koenigs, exponente de Lyapunov 2-ádico `½ ln(3/4)`, 20 teoremas en Lean.
  Dejan abierto que todo entero caiga en la cuenca. Coincide con nuestra extensión ingenua (N1, N2).
- **Teoría general** (leída en el survey de Sixsmith, arXiv:1709.09095) **[literatura]**:
  - clase de Eremenko–Lyubich `B` (valores singulares acotados): `I(f) ⊂ J(f)` (EL92, Teo. 1), luego no hay dominios
    errantes que escapan ni dominios de Baker;
  - lema de expansión (EL92, Lema 6.1 del survey): en `B`, `|z f'(z)/f(z)| → ∞` cuando `f(z) → ∞` (y Sixsmith 2014: eso
    caracteriza a `B`);
  - clase de Speiser `S` (finitos valores singulares): sin dominios errantes (Goldberg–Keen 1986, EL92);
  - Bishop (Acta Math. 2015): **hay** funciones en `B` con dominios errantes (oscilantes);
  - Bergweiler–Haruta–Kriete–Meier–Terglane (1993): las funciones límite finitas en un dominio errante están en el
    conjunto postsingular.
- **Ejemplo modelo** **[literatura, vía arXiv:2409.18496 que cita a Baker 1984, Ej. 5.3]**: `z + sin z + 2π` tiene un
  dominio errante que contiene a `π` y escapa a ∞. Sus puntos críticos `(2k+1)π` forman una cadena `(2k+1)π ↦ (2k+3)π`:
  **exactamente** la forma que tendría una órbita divergente de Collatz en la extensión LSW (cadena de puntos críticos
  que escapa). **[verificado]** (E5): el ancho real que sigue la cadena es 1,4973 para `k = 0, 10, 100, 1000`.

## Evidencia numérica y argumentos
Scripts: `scripts/hol_lsw.py` (E1–E5, ~6 s) y `scripts/hol_naive.py` (N1–N4, ~5 s).

**E2 — "ℤ ⊂ Fatou" con constantes explícitas [elemental + verificado].** Para la extensión crítica,
`f(m+w) − T(m) = m·P_c(w) + Q_c(w)` con `c = (−1)^m` y `P_c, Q_c` con cero doble en 0. Por el principio del máximo
en `|w| = 0,2`: `|f(m+w) − T(m)| ≤ K(|m|+1)|w|²` con `K = 2,726` (q = 3) y `K = 5,099` (q = 5). Como
`|T(m)|+1 ≤ λ(|m|+1)` con `λ = (q+2)/2`, la cantidad `v_k = λK(|m_k|+1)|w_k|` cumple `v_{k+1} ≤ v_k²`: el disco
`D(m, 1/(2λK(|m|+1)))` sigue a la órbita entera para siempre, con error que tiende a 0 doble-exponencialmente. Así
`f^k` converge al ciclo o tiende a ∞ uniformemente en el disco: **todo entero está en Fatou, cualquiera sea su destino**,
para 3x+1, para 5x+1 y para los negativos (es, sospecho, el argumento de LSW). El crecimiento de la órbita, a lo sumo
geométrico, nunca le gana a la contracción cuadrática: la deriva no interviene.

**E3 — el ancho medido no conoce el destino [verificado].** `(|n|+1)·δ*(n)` vale ≈ 0,29–0,73 para órbitas que llegan a
1 y para los ciclos −1, −5, −17 en 3x+1, y ≈ 0,10–0,42 en 5x+1, **incluida la órbita de 7**, que en 40 pasos sube a
417 208 (y en 1000 pasos a `e^{103,6}·7`, N2). La cota de E2 se cumple siempre (es entre 4 y 15 veces más chica).

**E4 / N4 — separación [verificado para |n| < 40; elemental en general].** Hay un punto fijo o 2-periódico real repulsor
(⊂ J) en cada intervalo `(n, n+1)`: 79/80 para la crítica con q = 3, **la excepción es justo (−2, −1)**, como en LSW;
80/80 con q = 5. Para la ingenua: 78/80 y 79/80, y lo que falta está pegado al punto fijo repulsor −1, que ya está en J.
Esbozo general: `T(n) − n` alterna de signo, así que hay un punto fijo `x*` en cada `(n, n+1)`; ahí el peso de paridad
`(1 − cos πx)/2` vale ≈ 1/2, o sea `sin πx* ≈ ±1`, y `|f'(x*)| ≈ π|n|/2 > 1`.

**N1 — la extensión ingenua ve el signo de los ciclos [verificado, exacto].** El multiplicador de un ciclo de `g` es
`q^k/2^A = ∏_{n_i impar} 1/(1 + 1/(q n_i))`: < 1 si el ciclo es positivo, > 1 si es negativo. 3x+1: {1,2} → 3/4;
−1 → 3/2; −5 → 9/8; −17 → 2187/2048. 5x+1: {1,…} → 25/32; los ciclos de 13 y 17 → 125/128; −1 → 5/4. Es la
ecuación del ciclo (`2^A > 3^k` ⟺ ciclo positivo) en otro idioma, y vale igual para 5x+1.

**N2 + una proposición [elemental, no formalizada].** Para `g`, `|(g^k)'(n)| = q^{#impares}/2^k = (|T^k(n)|/|n|)·∏(1+1/(q n_i))^{−1}`
(numéricamente: 103,525 vs 103,596 en log para 5x+1 desde 7, 1000 pasos). Si `n ∈ F(g)` con componente `U_k ∋ g^k(n)`
simplemente conexa, Schwarz–Pick + Koebe dan `|(g^k)'(n)| ≤ 4·dist(g^k n, J)/dist(n, ∂U)`, y por la separación
`dist(·, J) ≤ 1`. Entonces **una órbita entera divergente de `g` está en J(g)**. Con la convención de `g`:
no hay divergencia ⟺ `ℤ⁺ ⊂ F(g)` (los ciclos positivos son atractores). La hipótesis de conexión simple no la verifiqué
(en LSW debe estar tratada; no pude leer el paper).

**N3 — ninguna de las dos está en la clase B [elemental + literatura].** En los pares, `|n f'(n)/f(n)|` vale 0 (crítica)
o 1 (ingenua): acotado mientras `f(n) → ∞`, y eso contradice el lema de expansión de EL. En general: **una extensión
de T en la clase B necesita `|f'(2m)| ≥ (log m − C)/(8π)`**. Además, los valores críticos reales de `g` llegan a 599
(q = 3) en `[0, 400]`: el conjunto singular no está acotado.

## Formalización
Nada en Lean. Lo formalizable y chico: la identidad del multiplicador (N1) y la cota de superatracción (E2) como
desigualdades sobre `ℂ`. No vale la pena: no acerca a la conjetura.

## Por qué falló / qué aprendimos
**Causa exacta.** En cualquier extensión entera, lo que la dinámica sabe de un entero `n` es el *jet* de la interpolación
a lo largo de su órbita (valores `T(n_i)` y derivadas `f'(n_i)`), y las derivadas son **datos libres** (interpolación de
Hermite). Lo que se elige es lo que se obtiene:
1. **Derivadas nulas (LSW)**: ℤ ⊂ Fatou gratis (E2), y "divergencia ⟺ dominio errante con un entero" es una
   **reformulación**. Para excluir el dominio errante haría falta un teorema de no errancia; los que existen piden
   `S` (Sullivan/Goldberg–Keen/EL), y la extensión no está ni en `B` (N3). El modelo `z + sin z + 2π` muestra que una
   cadena de puntos críticos que escapa dentro de un dominio errante es perfectamente posible. Y lo mismo vale para 5x+1,
   donde la divergencia que todos creen también daría dominios errantes: **la teoría no puede probar ni refutar ninguno
   de los dos**. Lo único probado de verdad (ningún entero en un dominio de Baker) sale de la separación de los enteros
   (E4): un dominio de Baker periódico tendría que contener dos enteros distintos de la órbita.
2. **Derivadas = pendientes (ingenua, Dağlı et al.)**: aparecen la deriva (Lyapunov `½ log(3/4)`, típico) y el signo de
   los ciclos (N1), pero la divergencia queda en J (N2), que es un lugar permitido. Probar `ℤ⁺ ⊂ F(g)` es probar que toda
   órbita cae en la cuenca de {1,2}: **es la conjetura** (la parte de divergencia).
3. **Clase B o S**, donde sí hay teoremas: el lema de expansión obliga a derivadas grandes en los enteros (`≳ log m`) y
   entonces una órbita divergente vive en `J(f)` sin contradicción. Para que un entero esté en Fatou, su órbita tiene
   que caer en una cuenca: otra vez la conjetura.

En las tres opciones una órbita divergente tiene un lugar consistente (dominio errante o conjunto de Julia). Ningún
teorema general de dinámica trascendente distingue una `f` que interpola 3x+1 de una que interpola 5x+1: la única
diferencia está en la aritmética de las órbitas, que la teoría no ve. Es la ronda 7 otra vez (la estructura sin el tamaño),
ahora con la topología de Fatou en lugar de las series de potencias.

**Lo que quedó sin probar.** No leí LSW: sus pruebas (en particular la separación para todo `n` y el tratamiento de las
componentes múltiplemente conexas) no están chequeadas por mí. La proposición de N2 depende de la conexión simple. La
separación E4 está verificada sólo para `|n| < 40` y esbozada en general. **[abierto, en la literatura]**: si `f₀` tiene
dominios errantes (LSW conjeturan que no), si existe una extensión de T en la clase S y qué haría su dinámica.

## Fuentes
- Lagarias, *The 3x+1 problem: an annotated bibliography (1963–1999)*, arXiv:math/0309224 (entradas 35, 115, 170–171);
  *… II (2000–2009)*, arXiv:math/0608208 (entradas 29, 109–112, 118). Leídas.
- Letherman–Schleicher–Wood, Exp. Math. 8 (1999) 241–251, DOI 10.1080/10586458.1999.10504402. No leído.
- Chamberland, DCDIS 2 (1996) 495–509. No leído.
- Sixsmith, *Dynamics in the Eremenko–Lyubich class*, arXiv:1709.09095 (Lema 6.1, Teo. 6.1, Teo. 11.2). Leído en parte.
- Eremenko–Lyubich, Ann. Inst. Fourier 42 (1992); Goldberg–Keen, ETDS 6 (1986); Bishop, Acta Math. (2015);
  Bergweiler–Haruta–Kriete–Meier–Terglane, Ann. Acad. Sci. Fenn. (1993). Citados a través de Sixsmith (no releídos).
- Baker, Proc. LMS (1984), Ej. 5.3 (citado a través de arXiv:2409.18496).
- Dağlı et al., arXiv:2611.11641 (preprint). Sólo el resumen.
