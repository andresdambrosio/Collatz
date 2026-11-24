---
layout: post
title: "Un ciclo de Collatz necesitaría al menos 15 601 pasos impares"
date: 2026-11-24 12:00:00 -0300
ref: cycles
tldr: "Si algún número volviera alguna vez a sí mismo, ese ciclo necesitaría al menos 15 601 pasos impares. Esta cota está verificada por completo en el kernel de Lean, sin hipótesis sin probar, y mejora la anterior de 2301. El truco: no hace falta que los números lleguen a 1, solo que bajen por debajo de sí mismos."
---

Hay solo dos formas de que la conjetura de Collatz sea falsa: que alguna órbita crezca para siempre, o que
alguna órbita forme un **ciclo** y vuelva a su número inicial sin pasar por el 1. Este post es sobre los ciclos.

## Por qué los ciclos tienen que ser largos

Usemos el mapa acelerado: un impar $$n$$ va a $$(3n+1)/2^a$$, donde dividimos por 2 tantas veces ($$a$$)
como haga falta para volver a tener un impar. Supongamos que un ciclo visita los impares $$n_1, \dots, n_k$$
y divide por 2 un total de $$A$$ veces. Si multiplicamos los pasos a lo largo de la vuelta, todos los
$$n_i$$ se cancelan y queda

$$2^A = \prod_{i=1}^{k} \left(3 + \frac{1}{n_i}\right).$$

De ahí salen dos cosas. Primero, $$2^A > 3^k$$. Segundo, si todos los números del ciclo son al menos $$M$$,
entonces $$2^A \le (3 + 1/M)^k$$. Tomando logaritmos:

$$0 < A - k\log_2 3 \le k \log_2\!\left(1 + \frac{1}{3M}\right) \approx \frac{k}{3M\ln 2}.$$

En palabras: $$A/k$$ tiene que ser una aproximación **extremadamente buena** de $$\log_2 3 = 1{,}58496\ldots$$
por arriba. Las aproximaciones racionales tan buenas necesitan denominadores grandes, y la fracción continua
de $$\log_2 3$$ dice exactamente qué tan grandes. Así que cuanto más grande es $$M$$, más largo tiene que ser
cualquier ciclo.

## De dónde sale M

La forma clásica de conseguir $$M$$: verificar por computadora que todo número menor que $$M$$ llega a 1.
Entonces un ciclo no puede contener esos números. Nuestra librería anterior hacía exactamente eso, dentro del
kernel, con $$M = 600\,001$$, y eso daba $$k \ge 2301$$.

Pero "llega a 1" es más de lo que necesitamos. Mirá el número **más chico** de un ciclo: por definición, su
órbita nunca baja de él. Así que alcanza con verificar que todo impar $$1 < n < M$$ en algún momento **baja
por debajo de sí mismo**. Ese chequeo es mucho más barato, y se abarata todavía más con un viejo truco de
Terras (1976): para la mayoría de las clases de residuos módulo $$2^{20}$$, los primeros 20 pasos son iguales
para todos los números de la clase, y se puede probar la bajada para toda la clase de una vez, en forma simbólica.

| Paso | Cantidad |
|---|---|
| Clases de residuos impares mod $$2^{20}$$ | 524 288 |
| Clases que bajan simbólicamente (para todo número de la clase) | 496 959 (94,8 %) |
| Números restantes menores que $$M = 78 \cdot 2^{20} = 81\,788\,928$$, chequeados uno por uno | 2 131 661 |
| Espera más larga antes de bajar | 376 pasos |

Con $$M = 81\,788\,928$$, la desigualdad de arriba no deja lugar para ningún $$k \le 15\,600$$. La primera
longitud que permite es $$k = 15\,601$$, el denominador de una reducida de la fracción continua de $$\log_2 3$$.

<span class="tag verified">verificado en Lean</span> **Todo ciclo de Collatz no trivial tiene al menos
15 601 pasos impares**
([`cycle_period_ge_15601`](https://github.com/andresdambrosio/Collatz/blob/main/Collatz/CycleBound/Final.lean)).
Todo se calcula dentro del kernel de Lean, sin solvers externos, sin `native_decide` y sin hipótesis. La criba
simbólica y los chequeos número por número están en
[`Collatz/CycleBound.lean`](https://github.com/andresdambrosio/Collatz/blob/main/Collatz/CycleBound.lean). Los
2048 bloques de cómputo los genera
[`scripts/gen_cycle_blocks.py`](https://github.com/andresdambrosio/Collatz/blob/main/scripts/gen_cycle_blocks.py).

## Una lección sobre la memoria

La primera versión de este cálculo me colgó la notebook, varias veces. El kernel de Lean recuerda cada
resultado intermedio hasta terminar un teorema, y le habíamos pedido que chequeara bloques grandes en 16
archivos **en paralelo**. Medido después: unos 3,4 GB por bloque, por 16, en una máquina de 16 GB. La versión
final usa 2048 teoremas chicos (unos 0,65 GB cada uno), encadenados para que compilen a lo sumo dos archivos a
la vez. Tarda unos 30 minutos, una sola vez.

## Perspectiva

¿Qué tan bueno es 15 601? Honestamente, modesto, y el método no es nuestro: es de Eliahou (1993), que con una
verificación hasta $$2^{40}$$ ya había probado que un ciclo tiene longitud al menos 17 087 915. Nuestro script
reproduce ese número exacto a partir de $$M = 2^{40}$$. Con la verificación por computadora de Barina hasta
$$2^{71}$$ (2025, no verificada en Lean), el mismo método da unos $$7 \times 10^{10}$$. Eso lo tenemos como teorema
de Lean *con la verificación como hipótesis explícita*
([`hercher_lower_bound`](https://github.com/andresdambrosio/Collatz/blob/main/Collatz/Forge/Invariants/ContFrac.lean)).
<span class="tag lit">literatura</span> La literatura además descarta los ciclos con hasta 91 "mínimos locales",
de cualquier longitud (Hercher, 2023).

El valor real es que este número está **verificado de punta a punta por una máquina**. Y muestra el límite del
método: la cota crece más o menos como $$\sqrt{M}$$. Ninguna cantidad de cómputo convierte "muy largo" en
"imposible". Para eso hace falta una idea, y de eso se trata el próximo post.

## Referencias

- S. Eliahou, "The 3x+1 problem: new lower bounds on nontrivial cycle lengths", *Discrete Mathematics* 118
  (1993), 45–56. [doi:10.1016/0012-365X(93)90052-U](https://doi.org/10.1016/0012-365X(93)90052-U)
- R. Terras, "A stopping time problem on the positive integers", *Acta Arithmetica* 30 (1976), 241–252.
  [doi:10.4064/aa-30-3-241-252](https://doi.org/10.4064/aa-30-3-241-252)
- D. Barina, "Improved verification limit for the convergence of the Collatz conjecture", *The Journal of
  Supercomputing* 81 (2025), artículo 810. [doi:10.1007/s11227-025-07337-0](https://doi.org/10.1007/s11227-025-07337-0)
- C. Hercher, "There are no Collatz m-cycles with m ≤ 91", *Journal of Integer Sequences* 26 (2023), artículo 23.3.5.
  [cs.uwaterloo.ca/journals/JIS/VOL26/Hercher/hercher5.html](https://cs.uwaterloo.ca/journals/JIS/VOL26/Hercher/hercher5.html)
