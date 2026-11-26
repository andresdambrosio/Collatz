---
layout: post
title: "No hay un método general: Conway y Kurtz–Simon, verificados en Lean"
date: 2026-11-26 09:00:00 -0300
ref: undecidable
tldr: "Si se cambian un poco las reglas de Collatz, la pregunta '¿todo número llega a 1?' se vuelve indecidible: ningún algoritmo puede responderla para todas esas reglas. Es un teorema de Conway (1972) y de Kurtz y Simon (2007), ahora verificado por completo en Lean. No dice que Collatz sea indecidible. Dice que una prueba tiene que usar algo propio de 3n+1."
---

*Cuarto post. El [primero]({{ site.baseurl }}/es/2026/11/23/hola-collatz/) presentó el problema y el plan.
El [segundo]({{ site.baseurl }}/es/2026/11/24/collatz-as-a-rewriting-game-es/) verificó una reformulación de la
conjetura entera, y el [tercero]({{ site.baseurl }}/es/2026/11/25/cycles-need-15601-odd-steps-es/) una cota para
los ciclos. Ese terminaba diciendo que lo que hace falta ahora es una idea. Antes de buscarla, conviene saber cómo
**no puede** ser una idea ganadora. De eso trata este post.*

## La familia

Collatz usa una regla para los pares y otra para los impares. Generalicemos: elegimos un módulo $$D$$ y, para cada
resto $$j$$ módulo $$D$$, una regla afín $$n \mapsto a_j n + b_j$$, con coeficientes racionales elegidos para
que el resultado sea siempre un número entero. Collatz es el caso $$D = 2$$, con $$n/2$$ y $$3n+1$$.

Todo mapa de esta familia plantea la misma pregunta: **¿todo número positivo termina llegando a 1?** Para
$$3n+1$$ nadie lo sabe. ¿Podría haber un procedimiento general que tome la tabla de reglas y conteste sí o no?

## Conway (1972): no

<span class="tag verified">verificado en Lean</span> Hay **un mapa fijo** de la forma
$$n \mapsto a_{n \bmod D} \cdot n$$ para el que ningún algoritmo puede decidir, dado $$m$$, si la órbita de
$$2^m$$ vuelve a tocar una potencia de 2. Lo mismo vale para "toca el 1"
([`conway_undecidable_fixed`](https://github.com/andresdambrosio/Collatz/blob/main/Collatz/Conway.lean)). En
consecuencia, ningún algoritmo resuelve el problema cuando el mapa es parte del dato
(`conway_undecidable`, `conway_undecidable_one`, en el mismo archivo).

La razón es que estos mapas pueden **correr programas**. La cadena que verificamos, eslabón por eslabón:

1. **El problema de la detención.** Ningún algoritmo decide si un programa termina. Ya estaba en Mathlib
   ([`Computability/Halting.lean`](https://github.com/leanprover-community/mathlib4/blob/master/Mathlib/Computability/Halting.lean)).
2. **Programas → máquinas de registros.** Toda función computable se convierte en un programa sobre registros que
   sólo sabe sumar 1, restar 1 y repetir mientras un registro no sea cero
   ([`Conway/Compile.lean`](https://github.com/andresdambrosio/Collatz/blob/main/Collatz/Conway/Compile.lean),
   [`Conway/Minsky.lean`](https://github.com/andresdambrosio/Collatz/blob/main/Collatz/Conway/Minsky.lean)).
3. **Máquinas de registros → fracciones.** Es el truco de Conway, que después se llamó FRACTRAN. Se guardan todos
   los registros en **un solo número**, como exponentes de primos, $$2^{r_0}\, 3^{r_1}\, 5^{r_2} \cdots$$, más un
   primo para el estado de la máquina. Cada instrucción es una fracción. Por ejemplo, multiplicar por
   $$3 \cdot 11 / 7$$ significa "estando en el estado 7, sumá 1 al registro del 3 y pasá al estado 11". Sólo se
   puede dividir por un primo si está, y eso es justo la pregunta "¿el registro es distinto de cero?"
   ([`Conway/Fractran.lean`](https://github.com/andresdambrosio/Collatz/blob/main/Collatz/Conway/Fractran.lean)).
4. **Fracciones → la familia.** Qué fracción se aplica depende sólo del resto de $$n$$ al dividir por el producto
   de los denominadores. Eso es un mapa de la forma de arriba.

Al final, la órbita de $$2^m$$ llega a una potencia de 2 exactamente cuando el programa número $$m$$ termina. Un
algoritmo para la primera pregunta resolvería la segunda.

## Kurtz y Simon (2007): "todo número" es todavía más difícil

El teorema de Conway habla de **un número inicial** por vez. Collatz pregunta por **todos**. Kurtz y Simon
probaron que para mapas afines (con un $$+b_j$$, como $$3n+1$$), "toda órbita llega a 1" es tan difícil como
"este programa termina con **toda** entrada", que está un nivel más arriba en la jerarquía aritmética ($$\Pi_2$$).

<span class="tag verified">verificado en Lean</span> Su Teorema 1, tal cual: hay una traducción computable de
programas a mapas afines tal que **el programa termina con toda entrada si y sólo si toda órbita de su mapa llega
a 1**
([`allReachOne_iff_total`](https://github.com/andresdambrosio/Collatz/blob/main/Collatz/KurtzSimon.lean)).
En consecuencia, el conjunto de mapas afines en los que toda órbita llega a 1 no es semidecidible, y su
complemento tampoco (`allReachOne_not_re`, `allReachOne_not_core`).

<span class="tag lit">literatura</span> Lo que no formalizamos: la definición misma de $$\Pi_2$$ y el hecho de
que la totalidad es $$\Pi_2$$-completa. Mathlib todavía no tiene la jerarquía aritmética.

Lo difícil, comparado con Conway, es que ahora importa **todo** número, no sólo los prolijos que codifican un
cálculo. Un $$n$$ cualquiera es basura: dos estados de la máquina a la vez, ningún estado, registros con valores
absurdos. Tres ideas la domestican:

1. **La basura viaja intacta y después se gasta.** Escribimos $$n$$ como (primos de la máquina) × $$u$$, donde
   $$u$$ no tiene primos de la máquina. Las fracciones sólo miran los primos de la máquina, así que $$u$$ viaja sin
   cambios. Cuando no queda ningún primo de la máquina, una regla afín de reserva, $$n \mapsto (n+1)/2$$, achica
   estrictamente el número, así que la basura termina agotándose
   ([`Conway/Affine.lean`](https://github.com/andresdambrosio/Collatz/blob/main/Collatz/Conway/Affine.lean)).
2. **Programas que se detienen desde cualquier lado.** Las configuraciones rotas se limpian, pero lo que queda
   puede ser la máquina a mitad de un cálculo, con disparates en los registros. Entonces el programa tiene que
   detenerse desde **toda** configuración. Lo garantizamos armándolo sólo con bucles `for` acotados, que siempre
   terminan aunque se empiece por la mitad
   ([`Conway/Mortal.lean`](https://github.com/andresdambrosio/Collatz/blob/main/Collatz/Conway/Mortal.lean)).
3. **Un bucle externo que se corrige solo.** El único bucle no acotado es
   `while F(m, x) ≠ 0: x := x + 1`. Cada vuelta borra los registros y recarga $$m$$ desde la tabla, no desde un
   registro que la basura podría ensuciar. Si se arranca a mitad de camino, a lo sumo la primera vuelta da
   cualquier cosa, y de ahí en más todo es correcto
   ([`Conway/Outer.lean`](https://github.com/andresdambrosio/Collatz/blob/main/Collatz/Conway/Outer.lean)).

## Qué es nuestro y qué no

- Los teoremas son de Conway y de Kurtz y Simon. Lo nuestro es la **verificación formal**. Todo compila con
  `lake build`, y `#print axioms` muestra sólo los tres axiomas estándar de Lean: sin `sorry`, sin
  `native_decide`.
- La idea central de Kurtz y Simon es de ellos: convertir una máquina en otra que se detiene desde *cualquier*
  configuración, con un cálculo interno acotado que valida cada paso del externo. Nuestro bucle externo es una
  variante del suyo.
- <span class="tag lit">literatura</span> Kurtz–Simon es un paper de conferencia, y la bibliografía anotada de
  Lagarias señala que no da pruebas detalladas. El borrador que leímos tiene la sección 3 vacía. Así que la
  limpieza aritmética de la basura que describimos arriba es una construcción nuestra, y bien puede ser distinta de
  la que tenían en mente los autores.
- No encontramos una formalización previa de Kurtz–Simon en ningún asistente de pruebas. La indecidibilidad de
  FRACTRAN ya estaba formalizada en Coq, por Larchey-Wendling y Forster, como paso hacia el décimo problema de
  Hilbert.

## Qué dice y qué no

**No** dice que Collatz sea indecidible. El teorema habla de la familia. Un miembro particular, como $$3n+1$$,
puede tener igual una prueba que use sus propiedades.

Lo que sí dice es que esa prueba **no puede ser un método general**: cualquier cosa que sólo use "afín por clases de
restos, y en promedio los números achican" valdría también para mapas en los que la pregunta no tiene respuesta
algorítmica. Una prueba de Collatz tiene que usar algo específico del $$3$$ y del $$2$$. Ese es el filtro que ahora
tiene que pasar cada idea de nuestro laboratorio.

## Referencias

- J. H. Conway, "Unpredictable iterations", *Proceedings of the 1972 Number Theory Conference*, University of
  Colorado, Boulder (1972), 49–52.
- J. H. Conway, "FRACTRAN: A simple universal programming language for arithmetic", en *Open Problems in
  Communication and Computation*, Springer (1987), 4–26.
  [doi:10.1007/978-1-4612-4808-8_2](https://doi.org/10.1007/978-1-4612-4808-8_2)
- S. A. Kurtz y J. Simon, "The undecidability of the generalized Collatz problem", *Theory and Applications
  of Models of Computation (TAMC 2007)*, LNCS 4484 (2007), 542–553.
  [doi:10.1007/978-3-540-72504-6_49](https://doi.org/10.1007/978-3-540-72504-6_49)
- J. C. Lagarias, "The 3x+1 problem: an annotated bibliography, II (2000–2009)".
  [arXiv:math/0608208](https://arxiv.org/abs/math/0608208)
- D. Larchey-Wendling y Y. Forster, "Hilbert's tenth problem in Coq", *FSCD 2019*, LIPIcs 131 (2019), 27:1–27:20.
  [doi:10.4230/LIPIcs.FSCD.2019.27](https://doi.org/10.4230/LIPIcs.FSCD.2019.27)
