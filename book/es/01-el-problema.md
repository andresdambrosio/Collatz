# 1. El problema

## El juego

Elegí un número entero positivo. Aplicá esta regla:

- si es **par**, dividilo por 2;
- si es **impar**, multiplicalo por 3 y sumale 1.

Repetí con el resultado. Desde 6:

```text
6 → 3 → 10 → 5 → 16 → 8 → 4 → 2 → 1 → 4 → 2 → 1 → …
```

Al llegar a 1, el juego entra en el ciclo $1 \to 4 \to 2 \to 1$ y se repite para siempre. Desde 7:

```text
7 → 22 → 11 → 34 → 17 → 52 → 26 → 13 → 40 → 20 → 10 → 5 → 16 → 8 → 4 → 2 → 1
```

Y desde 27, que es famoso: tarda **111 pasos** en llegar a 1 y en el camino sube hasta **9232**. Números chiquitos
generan recorridos larguísimos y caóticos.

**Conjetura de Collatz** (Lothar Collatz, 1937). *Empieces por el número que empieces, siempre terminás
llegando a 1.*

A la sucesión $n, T(n), T(T(n)), \dots$ la llamamos la **órbita** de $n$ (o su *recorrido*). En notación,

$$T(n) = \begin{cases} n/2 & n \text{ par,} \\ 3n+1 & n \text{ impar,} \end{cases}
\qquad T^k(n) = \underbrace{T(T(\cdots T}_{k}(n))).$$

La conjetura dice: para todo $n \ge 1$ existe $k$ con $T^k(n) = 1$.

## La versión acelerada

Si $n$ es impar, $3n+1$ es par, así que el paso siguiente es siempre dividir por 2. Conviene juntar los dos
pasos:

$$T_{\rm ac}(n) = \begin{cases} n/2 & n \text{ par,} \\ (3n+1)/2 & n \text{ impar.} \end{cases}$$

Desde 7: $7 \to 11 \to 17 \to 26 \to 13 \to 20 \to 10 \to 5 \to 8 \to 4 \to 2 \to 1$. Es el mismo camino con
algunos pasos salteados, y la conjetura es la misma con cualquiera de las dos versiones. Hay una tercera, el
**mapa de Syracuse**, que sólo mira los impares: un impar $n$ va a $(3n+1)/2^a$, donde $2^a$ es la mayor potencia
de 2 que divide a $3n+1$. Desde 7: $7 \to 11 \to 17 \to 13 \to 5 \to 1$.

Las tres versiones aparecen en el código. Cada una es cómoda para algo: la clásica para enunciar, la acelerada
para las cuentas con restos y la de Syracuse para los ciclos.

## ¿Por qué uno *cree* que es cierta?

Hay un argumento heurístico (**no** es una demostración) muy convincente. Con la versión acelerada, un número
grande es par o impar "como si tiraras una moneda". Si es par, se divide por 2. Si es impar, se multiplica por
aproximadamente $3/2$. En promedio, cada paso multiplica por

$$\sqrt{\tfrac{3}{2} \cdot \tfrac{1}{2}} = \sqrt{\tfrac34} \approx 0{,}866 < 1.$$

O sea que, en promedio, achica. Un recorrido típico baja. **[Experimento]** Por computadora se verificó que todo
número menor que $2^{71} \approx 2{,}4 \cdot 10^{21}$ llega a 1 ([Barina, 2025](99-bibliografia.md)).

¿Por qué no alcanza? Porque los números son infinitos, y porque "en promedio baja" no dice nada sobre *un*
número concreto. Un contraejemplo podría ser enorme, y su órbita podría crecer para siempre: ninguna computadora
lo vería terminar.

## Los filtros: lo que una prueba tiene que usar

Cambiá el 3 por un 5 (el juego "$5n+1$"). El promedio pasa a ser $\sqrt{5/4} > 1$: los números típicos **crecen**.
Además, $5n+1$ tiene ciclos que no pasan por 1. Desde 13:

```text
13 → 66 → 33 → 166 → 83 → 416 → 208 → 104 → 52 → 26 → 13
```

Esto da la primera lección metodológica del libro, que vamos a usar todo el tiempo:

> **Filtro de $5n+1$.** Si una supuesta demostración de Collatz funcionaría igual para $5n+1$, está mal, porque
> para $5n+1$ la conclusión es falsa. Toda prueba tiene que usar, en algún lugar, que el número es 3 y no 5.

Hay otros filtros parecidos, y los vamos a ver reaparecer:

- **Filtro de los negativos.** Con enteros negativos, $3n+1$ tiene ciclos: $-1 \to -2 \to -1$, o
  $-5 \to -14 \to -7 \to -20 \to -10 \to -5$, o uno de largo 18 que pasa por $-17$. Una prueba tiene que usar que
  el número es **positivo**.
- **Filtro de "casi todos".** Un argumento probabilístico o de densidad da "casi todos", no "todos".
- **Filtro de las últimas cifras.** Un argumento que sólo mira el resto al dividir por $2^k$ no alcanza (capítulo 3).

## Lo que se sabe

- **[Literatura]** Terras (1976): *casi todos* los números (la proporción tiende a 100 %) llegan en algún momento
  por debajo de su valor inicial.
- **[Literatura]** Tao (2019): casi todos los números llegan a valores "casi acotados". Sigue siendo un "casi
  todos" (capítulo 9).
- **[Lean]** Todo ciclo distinto de $1 \to 4 \to 2 \to 1$ tiene al menos 15 601 pasos (capítulo 5).
- **[Lean]** Para generalizaciones del juego, la pregunta "¿llega a 1?" es **indecidible**: no hay un algoritmo
  general que la conteste (Conway, 1972; Kurtz y Simon, 2007; capítulo 10).
- **[Abierto]** La conjetura.

## Ejercicios

1. (Papel) Calculá la órbita de 9 con la versión clásica. ¿Cuántos pasos tarda en llegar a 1?
2. (Papel) Mostrá que si $n \equiv 3 \pmod 4$, entonces $T_{\rm ac}(n)$ es impar. (Escribí $n = 4k+3$ y calculá
   $(3n+1)/2$.) Concluí que esos números siempre hacen al menos dos "subidas" seguidas.
3. (Papel) Verificá el ciclo de $-5$. ¿Por qué no contradice la conjetura?
4. (Computadora) Escribí un programa que, para cada $n \le 10^6$, calcule cuántos pasos tarda en llegar a 1.
   ¿Cuál es el que más tarda?
5. (Computadora) Para $5n+1$, encontrá todos los ciclos a los que llegan los números menores que 1000. (Hay
   tres: el que pasa por 1, el que pasa por 13 y el que pasa por 17.)
6. (Para pensar) El argumento heurístico usa que la paridad "es una moneda". ¿Por qué esto es razonable para
   números grandes y cuál es exactamente el punto donde deja de ser una demostración?
