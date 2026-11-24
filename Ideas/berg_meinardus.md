# Idea: la ecuación funcional de Berg–Meinardus (análisis complejo)

**Estado:** cerrada: la formulación es combinatoria disfrazada de análisis (ronda 7 del laboratorio, 2026-11-23)
**Frente:** ambos

## Enunciado (Berg–Meinardus 1994/1995, en la notación de Opfer 2011)
`H` = funciones holomorfas en el disco unidad `D`. Con `λ = e^{2πi/3}`:
- `U[h](z) = h(z) + h(−z) − 2h(z²)`
- `H[h](z) = (h(z²) + λh(λz²) + λ²h(λ²z²)) / (3z)`, `V[h](z) = 2H[h](z) − h(z³) + h(−z³)`
- `K = ker U ∩ ker V ⊇ Δ₂ = ⟨1, z/(1−z)⟩`. **Teorema (B–M, Wirsching):** Collatz ⇔ `K = Δ₂`.

## Qué es en realidad (lo verificamos)
- `ker V` (B–M, fórmula (38)): `h = η₀ + η₁ z/(1−z) + Σ η_j t_j(z)`, donde `t_j` suma `z^m` sobre la **cadena de
  pasos impares** `j, (3j+1)/2, …` hasta el primer par (Collatz modificado). Cada exponente aparece una sola vez.
- Imponer `U[h] = 0` da el sistema `η_j = η_{j''}` (Opfer, Teo. 4.3–4.4), que **iguala los coeficientes a lo largo
  de las órbitas de Collatz**. Entonces `K / Δ₂` ≅ funciones constantes en cada componente del grafo de Collatz
  (con la normalización en la componente del 1).
- **La condición analítica es vacía:** la indicadora de una componente tiene coeficientes en {0, 1}, y esa serie
  converge en `D` siempre. Toda componente extra (un ciclo no trivial o un árbol divergente) da un elemento extra
  de `K`, sin ninguna restricción. La formulación es "el grafo de Collatz es conexo", escrito como núcleo de operadores.
- El análisis sólo podría ver el **tamaño** a través del comportamiento en el borde `|z| = 1`, o sea la densidad
  de la componente. Eso es información distribucional: el mismo muro de siempre.

## El hueco de Opfer (2011), verificado
Preprint Hamburger Beiträge 2011-09. Nota del autor (17/06/2011): la afirmación de la p. 11, que el conjunto de
vértices del "grafo de aniquilación" contiene cada par `2n ≥ 6` exactamente una vez, "has turned out to be incomplete".
**Diagnóstico:** el paso del "Algoritmo 4.9 de aniquilación" es `ℓ ↦ E/2`, donde `E` es el final par de la cadena impar
que contiene a `ℓ`. **Es el mapa de Collatz comprimido.** Lo comprobamos para todo `3 ≤ ℓ < 200 000`, con 0 discrepancias.
Su Tabla 4.8 (326 → 368 → 184 → 92 → 46 → 80 → 40 → 20 → 10 → 8) es la órbita de Collatz de 163.
El Teorema 4.17 ("siempre termina en 8") **es la conjetura de Collatz**, y el argumento del árbol la supone:
la prueba es circular.

## Ganchos analíticos que miré y por qué no sirven
- **Szegő (1922):** una serie con finitos coeficientes distintos es racional o tiene el círculo unidad como borde
  natural. La indicadora de una componente infinita no periódica tiene borde natural. Eso es cierto pero no da
  contradicción (cf. arXiv:1408.6884: las generatrices de órbitas inversas casi siempre tienen borde natural).
- **Funciones de Mahler (análogo de Cobham, Adamczewski–Bell 2017):** una serie que es 2-Mahler y 3-Mahler a la vez
  es racional. Las indicadoras de componentes no tienen por qué ser k-Mahler: eso exigiría que la componente sea un
  conjunto k-automático, y no hay razón. `ker U` sólo pide `a_{2m} = a_m` (valores libres en los impares).
- (Literatura a verificar antes de publicar: Adamczewski–Bell, "A problem about Mahler functions", Ann. SNS Pisa 2017.)

## Lección
Igual que en la ronda 6: la formulación ve la estructura (2-ádica/combinatoria) y no ve el tamaño arquimediano,
salvo como densidad. Las equivalencias "en otro idioma" conservan la dificultad intacta, a menos que el idioma
traiga un teorema de rigidez que use el tamaño. No encontramos ninguno.

## Formalizable (chico y útil)
`opfer_annihilation_eq_collatz`: el paso de aniquilación es la iteración de Collatz, así que el Teorema 4.17 de
Opfer ⇔ Collatz. Es un ejemplo limpio de cómo Lean detecta pruebas circulares.

## Fuentes
- Opfer, hbam2011-09, preprint.math.uni-hamburg.de/public/papers/hbam/hbam2011-09.pdf
- Berg–Meinardus, Results Math. 25 (1994) 1–12; Rostock. Math. Kolloq. 48 (1995) 11–18.
- Berg–Opfer, CMFT 13 (2013) 225–236 (valores iniciales negativos).
