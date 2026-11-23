---
layout: post
title: "Hola, Collatz: voy a intentar demostrarla, en público"
date: 2026-11-23 06:00:00 -0300
ref: hello
tldr: "La conjetura de Collatz es uno de los problemas abiertos más simples de la matemática. Mi objetivo es demostrarla, compartiendo todo en el camino, con cada resultado verificado por el asistente de pruebas Lean. Acá están el problema, el plan y los primeros resultados."
---

## El problema

Elegí un número entero positivo. Si es par, dividilo por dos. Si es impar, multiplicalo por tres y sumale uno.
Repetí.

Empezando en 7:

$$7 \to 22 \to 11 \to 34 \to 17 \to 52 \to 26 \to 13 \to 40 \to 20 \to 10 \to 5 \to 16 \to 8 \to 4 \to 2 \to 1.$$

Empezando en 27, el recorrido tarda 111 pasos y sube hasta 9.232 antes de volver a caer a 1.

La **[conjetura de Collatz](https://es.wikipedia.org/wiki/Conjetura_de_Collatz)**, propuesta por Lothar Collatz en 1937, dice que, empieces donde empieces, siempre terminás en 1. Cualquiera la
entiende en diez segundos; nadie pudo demostrarla en casi noventa años. Se le atribuye a Paul Erdős la frase
"la matemática quizás no está preparada para problemas así" (según relata
[Lagarias, 1985](https://doi.org/10.1080/00029890.1985.11971528)).

Lo que se sabe <span class="tag lit">literatura</span>:

- Se verificó por computadora para todo número inicial menor que $$2^{71}$$, unos
  $$2{,}4 \times 10^{21}$$ ([Barina, 2025](https://doi.org/10.1007/s11227-025-07337-0)).
- [Terence Tao demostró en 2019](https://arxiv.org/abs/1909.03562) que *casi todos* los números iniciales llegan a valores *casi* acotados. Es el
  resultado más fuerte hasta hoy, y todavía no dice nada sobre *cada* número.

Y lo que no: si vale para todos los números está <span class="tag open">abierto</span>.

## El objetivo

**Mi objetivo es demostrar la conjetura de Collatz**, y compartir todo en el camino: los avances, los
callejones sin salida y las razones de cada uno.

Sé cómo suena. Mucha gente anunció demostraciones de Collatz, y todas resultaron equivocadas. Por eso este
proyecto sigue [reglas]({{ '/es/reglas/' | relative_url }}) estrictas, y la primera es la importante:
**una máquina decide qué es verdad.**

Todo vive en un repositorio público escrito en [Lean 4](https://lean-lang.org), un asistente de pruebas.
El kernel de Lean es un programa chico que chequea cada paso de cada demostración. Si acepta un teorema, el
teorema es correcto, lo haya escrito quien lo haya escrito. Eso importa acá, porque trabajo con un asistente
de IA ([Claude](https://www.anthropic.com/claude), de Anthropic) que escribe buena parte del código. En las últimas semanas, sistemas de IA
participaron en resultados serios sobre la hipótesis de Riemann: una demostración de una versión más débil, la
[hipótesis "cuasi-Riemann"](https://www.quantamagazine.org/ai-proved-the-quasi-riemann-hypothesis-what-happens-now-20261019/),
y una [demostración anunciada de la hipótesis completa](https://www.aljazeera.com/news/2026/11/21/riemann-hypothesis-has-the-worlds-most-famous-maths-problem-been-cracked),
entregada como una biblioteca de Lean y todavía sin verificación independiente. Quiero averiguar hasta dónde puede llegar esta forma de trabajar con Collatz.

Cada afirmación de este blog lleva una etiqueta: <span class="tag verified">verificado en Lean</span>,
<span class="tag lit">literatura</span>, <span class="tag heur">heurística</span> o
<span class="tag open">abierto</span>. La conjetura misma sigue <span class="tag open">abierta</span> hasta
que Lean acepte una demostración.

## Primeros resultados

Las primeras semanas fueron para construir las bases. Cada uno de estos puntos va a tener su propia entrada:

- **Dos maneras en que la conjetura podría fallar.** Es falsa si y solo si algún número vuelve a sí mismo sin
  pasar por 1, o algún número crece para siempre. <span class="tag verified">verificado en Lean</span>
  ([`collatz_iff`](https://github.com/andresdambrosio/Collatz/blob/main/Collatz/Reductions.lean))
- **Collatz como un juego de palabras.** En 2021, [Yolcu, Aaronson y Heule](https://arxiv.org/abs/2105.14697) mostraron que la conjetura equivale
  a un juego que reescribe palabras cortas con 11 reglas. Chequeé en Lean su teorema y los certificados que
  encontraron por computadora. En el camino encontré, y arreglé, un pequeño hueco en uno de sus
  argumentos. <span class="tag verified">verificado en Lean</span>
  ([`collatz_iff_terminatesAll`](https://github.com/andresdambrosio/Collatz/blob/main/Collatz/Rewriting/AllWords.lean))
- **Un primer número nuevo.** Si existe un ciclo, necesita al menos **15.601** pasos impares. Mi cota anterior,
  también chequeada de punta a punta en Lean, era 2.301. <span class="tag verified">verificado en Lean</span>
  ([`cycle_period_ge_15601`](https://github.com/andresdambrosio/Collatz/blob/main/Collatz/CycleBound/Final.lean))
- **Un laboratorio de ideas.** También empecé a probar ideas apuntadas a la conjetura completa, y a escribir
  por qué falla cada una. Las primeras lecciones son duras, y las voy a contar con honestidad.

Nada de esto demuestra Collatz. Es la base sobre la que voy a construir.

## Seguí el proyecto

Las próximas entradas van a llegar a medida que avance el trabajo. Las voy a anunciar en X:
[@andresdambrosio](https://x.com/andresdambrosio). El
[repositorio](https://github.com/andresdambrosio/Collatz) es abierto: si tenés una idea, una corrección o una
demostración en Lean, las contribuciones son bienvenidas.

## Referencias

- El problema de L. Collatz: [Conjetura de Collatz](https://es.wikipedia.org/wiki/Conjetura_de_Collatz), Wikipedia (panorama e historia).
- J. C. Lagarias, "The 3x+1 problem and its generalizations", *American Mathematical Monthly* 92 (1985), 3–23.
  [doi:10.1080/00029890.1985.11971528](https://doi.org/10.1080/00029890.1985.11971528)
- D. Barina, "Improved verification limit for the convergence of the Collatz conjecture", *The Journal of
  Supercomputing* 81 (2025), 810. [doi:10.1007/s11227-025-07337-0](https://doi.org/10.1007/s11227-025-07337-0)
- T. Tao, "Almost all orbits of the Collatz map attain almost bounded values", *Forum of Mathematics, Pi* 10 (2022).
  [arXiv:1909.03562](https://arxiv.org/abs/1909.03562)
- E. Yolcu, S. Aaronson, M. J. H. Heule, "An Automated Approach to the Collatz Conjecture", *Journal of Automated
  Reasoning* (2023). [arXiv:2105.14697](https://arxiv.org/abs/2105.14697)
- Sobre los anuncios de la hipótesis de Riemann: [Quanta Magazine (oct. 2026)](https://www.quantamagazine.org/ai-proved-the-quasi-riemann-hypothesis-what-happens-now-20261019/),
  [Al Jazeera (nov. 2026)](https://www.aljazeera.com/news/2026/11/21/riemann-hypothesis-has-the-worlds-most-famous-maths-problem-been-cracked).
- [Lean 4](https://lean-lang.org) y [Mathlib](https://github.com/leanprover-community/mathlib4).
