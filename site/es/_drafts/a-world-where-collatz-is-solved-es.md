---
layout: post
title: "Un mundo donde Collatz está resuelto, y por qué la prueba no viaja"
date: 2026-11-24 09:00:00 -0300
ref: solved-cousin
tldr: "Hay un primo cercano del problema de Collatz donde la conjetura está demostrada: la aritmética binaria sin acarreos. Construimos una escalera de mundos desde ese primo hasta los enteros de verdad, dejando que los acarreos viajen un poco más en cada escalón. Toda la dificultad aparece ya en el primer escalón, con acarreos que viajan apenas dos lugares. En el camino, verificamos en Lean que una prueba anunciada en 2011 era circular."
---

El [post del laboratorio]({{ '/es/2026/11/23/five-rounds-one-orbit-es/' | relative_url }}) terminó contra
un muro: todo lo que probamos se reducía a demostrar algo sobre una órbita concreta. Esta semana
intentamos otro truco, viejo en matemática: **llevar el problema a un mundo donde sea más fácil, resolverlo
ahí y volver.** No funcionó, pero la forma en que falló nos mostró con precisión dónde vive la dificultad.

## Las reglas en binario

En binario, el paso de Collatz es mecánico. Dividir por 2 un número par es borrar el 0 del final. Y
$$3n + 1 = n + 2n + 1$$, donde $$2n$$ es $$n$$ corrido un lugar a la izquierda. Así queda $$3 \cdot 7 + 1$$:

```
    0111      (7)
  + 1110      (14 = el 7 corrido)
  +    1
  -------
   10110      (22)
```

Columna por columna, de derecha a izquierda, cada columna se pasa y le deja un **acarreo** ("me llevo uno")
a la siguiente, y el último cae en una columna nueva arriba de todo. El 7, de 3 cifras, se volvió el 22, de
5 cifras. **Los números pueden crecer solo porque los acarreos llegan hasta arriba.**

## El primo donde Collatz está demostrado

Ahora pensá en un mundo donde $$1 + 1 = 0$$ y **no te llevás nada**: cada columna se suma sola. La misma
cuenta da

```
    0111
  + 1110
  +    1
  -------
    1000      (columna por columna, sin acarreos)
```

y al dividir por 2 queda `100`: sigue teniendo 3 cifras. Esto pasa siempre. Sin acarreos, $$n + 2n$$ tiene
exactamente una cifra más que $$n$$, el resultado termina siempre en 0 y dividir por 2 le saca esa cifra.
**El largo nunca crece.** Una sucesión que nunca crece no se puede escapar al infinito, y con un chequeo de
que no haya ciclos sueltos, la conjetura en ese mundo es un teorema. <span class="tag lit">literatura</span>
Ese mundo es el anillo $$\mathbb{F}_2[x]$$ de polinomios con coeficientes módulo 2, donde $$x$$ hace de 2 y
$$1 + x$$ hace de 3. Hicks, Mullen, Yucas y Zavislak probaron en 2008 que todo polinomio llega a 1 (y Snapp
y Tracy, de forma independiente). Monks observó en 2025 que ese mapa es literalmente "$$3n+1$$ en binario
sin acarreos".

## Una escalera de mundos

Entonces nos preguntamos: ¿qué pasa en el medio? Construimos una familia de mundos $$C_k$$ donde un acarreo
puede viajar **como máximo $$k$$ columnas** y después se apaga:

- $$C_0$$: los acarreos se apagan al nacer. Es el mundo polinomial, el resuelto.
- $$C_2$$, $$C_4$$, …: los acarreos viajan un poco más.
- $$C_\infty$$: los acarreos no se apagan nunca. Es el problema de Collatz de verdad.

Así queda $$3 \cdot 5 + 1$$ en el mundo real y en $$C_2$$:

```
 real:   0101 + 1010 + 1 = 10000  (16)     el acarreo corre hasta arriba de todo
 C_2:    0101 + 1010 + 1 = 01100  (12)     el mismo acarreo se apaga a las dos columnas
```

El plan: probar $$C_2$$, después $$C_4$$, y ver dónde se rompe la prueba fácil.
(Un primer intento, un anillo donde los acarreos saltan lejos en vez de apagarse, manda todos los números
al infinito. Rompe el equilibrio de "multiplico por 3, divido por 4" que hace plausible a Collatz, así que
lo descartamos.)

<span class="tag heur">heurística</span> Lo que muestra la computadora, con todos los valores iniciales
menores que 20 000:

- En ningún mundo $$C_k$$ hubo órbitas que se escaparan al infinito.
- Algunos mundos tienen **ciclos falsos** que nunca llegan a 1. En $$C_2$$ el más chico es
  $$3 \to 5 \to 6 \to 3$$, y siguen apareciendo a tamaños mayores (encontramos ciclos de hasta 21 cifras
  binarias). Así que en $$C_k$$ la pregunta correcta es "¿algo se escapa?", no "¿todo llega a 1?".
- El análogo de $$5n+1$$ se escapa para $$k = 4, 6, 8$$ (los valores que probamos), igual que en los enteros
  de verdad. La escalera pasa el mismo control de cordura que tiene que pasar cualquier argumento sobre Collatz.

Y acá viene la sorpresa. ¿Con qué frecuencia un paso impar hace que el número gane una cifra?

| mundo | $$C_0$$ | $$C_2$$ | $$C_4$$ | $$C_8$$ | Collatz de verdad |
|---|---|---|---|---|---|
| crecimiento en un paso impar | 0 % | 48 % | 55 % | 58 % | 58,5 % |

(Medido en números de 4000 cifras. En el Collatz de verdad el valor exacto es $$\log_2(3/2) \approx 58{,}5\,\%$$,
consecuencia de la ley de Benford para las primeras cifras.) **Con acarreos que viajan apenas dos columnas,
los números ya crecen casi tan seguido como en el problema real.** El primer escalón ya es tan empinado como
toda la escalera.

## Vistos desde abajo, todos estos mundos son iguales

<span class="tag verified">verificado en Lean</span> Hay una razón estructural. En todo mundo $$C_k$$,
y también en Collatz, cada cifra de $$n + 2n + 1$$ es la cifra correspondiente de $$n$$, XOR algo que depende
solo de las cifras de *abajo*. Una regla con esa forma se puede deshacer columna por columna, así que si
mirás solo las últimas $$m$$ cifras, el paso es una permutación de todas las terminaciones posibles, para
todo $$m$$ y para *cualquier* regla de acarreo
([`Collatz.Carries.out_injective_below`](https://github.com/andresdambrosio/Collatz/blob/main/Collatz/Carries.lean)).
<span class="tag lit">literatura</span> Vistos desde las
últimas cifras, el mundo polinomial, todos los $$C_k$$ y Collatz se comportan **exactamente igual**. En la
jerga, todos son conjugados al mismo shift sobre los enteros 2-ádicos, como muestra Monks para el caso
polinomial. Lo único que los distingue es el **tamaño** del número: cómo crece por arriba.

Por eso la prueba polinomial no puede subir la escalera. Se apoya en un único hecho, "el largo nunca
crece", y ese hecho deja de valer apenas algún acarreo puede llegar arriba. No se degrada de a poco:
simplemente deja de ser cierto.

## A la caza de una función energía

Los ingenieros conocen el truco de la **función de Lyapunov**: una cantidad que nunca aumenta a lo largo del
movimiento, como la energía de un sistema con rozamiento. Si encontráramos una para $$C_2$$ que nunca aumente
y valga al menos la cantidad de cifras, ninguna órbita podría escaparse. En el mundo polinomial, el largo
mismo funciona.

<span class="tag heur">heurística</span> (Son cálculos exactos, con un programa lineal y un solver SAT,
pero no están verificados en Lean.)

- **No existen energías locales.** Buscamos energías armadas contando patrones cortos de cifras, más
  términos que miran las últimas y las primeras cifras. Un programa lineal encuentra los mejores pesos o
  demuestra que no existen. En el mundo polinomial encuentra una enseguida. Para $$C_2$$ y para Collatz no
  existe ninguna. La razón, que se lee en el dual del programa, es una familia de **números ralos** como
  `111010000010`: un bloque de unos arriba, otro abajo y ceros en el medio. El bloque de abajo decide qué
  pasos son impares. El de arriba crece en los pasos impares. Una energía que solo mira ventanitas no puede
  saber que los pasos pares que vienen después van a compensar ese crecimiento.
- **Energías globales, armadas con productos de matrices.** Estas ven el número entero de una vez, y son
  la herramienta detrás del [enfoque de reescritura]({{ '/es/2026/11/24/collatz-as-a-rewriting-game-es/' | relative_url }}).
  Con un solver SAT, no hay ninguna con matrices de hasta $$3 \times 3$$. Hay búsquedas más grandes corriendo.

## Un desvío: una prueba de 2011 que suponía su conclusión

Hay otro "cambio de mundo" clásico: Berg y Meinardus (1994) tradujeron Collatz a un par de ecuaciones
funcionales para funciones holomorfas en el disco unidad. <span class="tag lit">literatura</span> Collatz es
cierta si y solo si esas ecuaciones tienen únicamente el espacio obvio de soluciones, de dimensión dos.
Desarmadas, las soluciones son exactamente las funciones constantes a lo largo de las órbitas de Collatz. La
condición analítica no agrega nada: una serie indicadora con coeficientes 0 y 1 siempre converge en el disco.
Así que la traducción es "el grafo de Collatz es conexo", escrito como análisis.

En 2011, Gerhard Opfer anunció una prueba por esta vía. Un mes después retiró la afirmación: escribió que un
paso de su argumento "has turned out to be incomplete" (resultó incompleto). Quisimos saber exactamente por qué.
<span class="tag verified">verificado en Lean</span> Su paso clave es un "algoritmo de aniquilación" sobre
números pares. Lo formalizamos tal como está escrito en su paper, chequeamos que reproduce sus tablas y
demostramos que **un paso de aniquilación es un tramo del propio mapa de Collatz**. Así que su Teorema 4.17
("el algoritmo siempre termina en 8") es *equivalente* a la conjetura de Collatz
([`Collatz.Opfer.theorem_4_17_iff_collatz`](https://github.com/andresdambrosio/Collatz/blob/main/Collatz/Opfer.lean)).
Por ejemplo, su Tabla 4.8 (326 → 368 → 184 → … → 8) es la órbita de Collatz de 163 (bajo el mapa
$$x \mapsto x/2$$ o $$(3x+1)/2$$), duplicada y saltando cada tramo de pasos impares de una vez. El argumento
del árbol que dio para el Teorema 4.17 supone lo que quiere demostrar. Para que quede claro el crédito: el
problema lo encontró el propio Opfer, y nosotros solo lo ubicamos formalmente.

## Lo que aprendimos

Cada traducción que probamos esta semana (polinomios, escaleras de acarreos, números 2-ádicos, análisis
complejo) o se ve exactamente igual de difícil que Collatz o se vuelve trivial. Lo que nunca hace el viaje es
siempre lo mismo: **la interacción entre el tamaño de un número y sus últimas cifras.** Las últimas cifras
deciden qué pasa (par o impar). El tamaño decide si el número se escapa. No conocemos ninguna herramienta
que controle las dos cosas a la vez para un número individual. Es una versión más precisa del muro del post
anterior, y es lo que cualquier prueba de verdad va a tener que superar. <span class="tag open">abierto</span>

Todo el código está en el repositorio: `scripts/carry_trunc.py`, `carry_potential*.py` y `carry_srs*.py`, y
las notas del laboratorio están en [`Ideas/acarreos.md`](https://github.com/andresdambrosio/Collatz/blob/main/Ideas/acarreos.md)
y [`Ideas/berg_meinardus.md`](https://github.com/andresdambrosio/Collatz/blob/main/Ideas/berg_meinardus.md).

## Referencias

- K. Hicks, G. L. Mullen, J. L. Yucas, R. Zavislak, "A Polynomial Analogue of the 3n+1 Problem",
  *American Mathematical Monthly* 115 (2008), 615–622.
  [doi:10.1080/00029890.2008.11920572](https://doi.org/10.1080/00029890.2008.11920572)
- B. Snapp, M. Tracy, "The Collatz Problem and Analogues", *Journal of Integer Sequences* 11 (2008),
  artículo 08.4.7. [cs.uwaterloo.ca/journals/JIS/VOL11/Snapp/snapp.html](https://cs.uwaterloo.ca/journals/JIS/VOL11/Snapp/snapp.html)
- K. G. Monks, "On q-analogs of the 3x+1 dynamical system" (2025).
  [arXiv:2508.10153](https://arxiv.org/abs/2508.10153)
- L. Berg, G. Meinardus, "Functional equations connected with the Collatz problem", *Results in
  Mathematics* 25 (1994), 1–12. [doi:10.1007/BF03323136](https://doi.org/10.1007/BF03323136)
- G. Opfer, "An analytic approach to the Collatz 3n+1 problem", Hamburger Beiträge zur Angewandten
  Mathematik 2011-09 (con la nota del autor del 17 de junio de 2011).
  [preprint.math.uni-hamburg.de](https://preprint.math.uni-hamburg.de/public/papers/hbam/hbam2011-09.pdf)
- E. Yolcu, S. Aaronson, M. J. H. Heule, "An Automated Approach to the Collatz Conjecture",
  *Journal of Automated Reasoning* (2023). [arXiv:2105.14697](https://arxiv.org/abs/2105.14697)
