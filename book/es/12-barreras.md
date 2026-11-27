# 12. Barreras: por qué fallan los métodos locales

> Código y notas: `Collatz/Carries.lean`, `Ideas/LAB.md`, `Ideas/acarreos.md`, `Ideas/dos_bases.md`,
> `Ideas/potenciales_no_locales.md`, `Ideas/induccion_reforzada.md`, `scripts/carry_*.py`, `scripts/two_base_exact.py`

## La idea

Los capítulos anteriores fueron, casi todos, sobre verificar lo que ya se sabía. Este cuenta el **laboratorio**:
once rondas de intentos propios de acercarse a la prueba, todos fallidos, y lo que aprendimos de por qué fallan.
Una barrera bien entendida le ahorra trabajo al próximo que lo intente.

El protocolo de cada ronda fue siempre el mismo:

1. **Idea completa**: tiene que decir cómo descarta *a la vez* ciclos y divergencia.
2. **Filtros**: ¿falla para $5n+1$? ¿usa que $n > 0$? ¿va más allá de las últimas cifras y de "casi todos"?
3. **Antecedentes**: casi todo ya se intentó, así que hay que buscar antes de invertir.
4. **Un experimento** que pueda refutar la idea.
5. **Lean**, sólo para lo que sobreviva.
6. **Registrar el fracaso** con su causa exacta.

## Rondas 1 a 5: siempre el mismo lugar

Probamos subir el "casi todos" de Tao a "todos" con el árbol de predecesores, funciones potenciales calculadas por
autómatas, la conjugación 2-ádica, ciclos con el método de picos, rigidez y equidistribución, el catálogo de 29
paradigmas de Chang (2026) y el problema de juguete de Erdős sobre las cifras ternarias de $2^n$. Todas las vías
terminan en el mismo punto: **probar algo sobre la estadística de UNA órbita concreta**. Las herramientas fuertes
que existen (dígitos en dos bases, dinámica $\times 2 \times 3$, sumas exponenciales) son **distribucionales**:
hablan de proporciones, y a Collatz le falta siempre un enunciado **puntual**.

## Ronda 6: la escalera de acarreos

**[Literatura]** En los polinomios con coeficientes en $\mathbb{F}_2 = \{0, 1\}$, donde $1 + 1 = 0$, el análogo de
Collatz **está demostrado** (Hicks, Mullen, Yucas y Zavislak, 2008). Leído en binario, ese mapa es $3n+1$ **sin
acarreos**: se suma `n + 2n + 1` olvidando todos los "me llevo uno". Sin acarreos el número nunca se alarga, y con
finitas cifras posibles no hay divergencia.

Construimos una escalera entre los dos mundos: en $C_k$ cada acarreo tiene una edad y muere si recorre más de $k$
columnas. $C_0$ son los polinomios (resuelto) y $C_\infty$ es Collatz.

- **[Lean]** Con *cualquier* regla de acarreo, el paso es inyectivo sobre las últimas $m$ cifras
  (`out_injective_below`). Mirados desde abajo, $C_0$, $C_2$ y Collatz son el mismo sistema: una biyección de los
  enteros 2-ádicos que mezcla las cifras como una moneda. Lo que los distingue es sólo el **tamaño**.
- **[Experimento]** Ya en $k = 2$ aparecen excursiones largas, ciclos falsos (como $3 \to 5 \to 6 \to 3$) y la
  estadística de Collatz. **La dificultad aparece completa con acarreos de largo 2.**
- **[Experimento]** No hay potencial local (largo + pesos de ventanas de cifras) para $C_2$ ni para Collatz. Los
  testigos son números **ralos**, con bloques de unos separados por muchos ceros: cada bloque evoluciona por su
  cuenta, y ningún término local puede "saber" que más adelante la paridad compensa. Es la **barrera de
  localidad**.
- **[Experimento]** Tampoco hay certificados árticos de "largo acotado" chicos: con SAT, UNSAT hasta matrices
  $4 \times 4$ (y parcialmente $5 \times 5$). El potencial verdadero necesita una cantidad de estados que crece
  exponencialmente con las cifras leídas.

## Rondas 7 y 8: análisis complejo y la barrera de signo

La ronda 7 fue Berg–Meinardus (capítulo 11): el análisis complejo dice "el grafo es conexo" en otro idioma. La
ronda 8 leyó los papers de rStation, que ya habían llegado a lo mismo que nosotros por otro lado y lo habían
probado como teorema. Los certificados de tamaño fijo mueren en los **ciclos negativos** $-1$, $-5$, $-17$ y en sus
sombras, que se acumulan a toda profundidad 2-ádica: es la **barrera de signo**. Ningún método de estados finitos
distingue a los positivos de esos puntos periódicos negativos.

## Ronda 10: dos bases a la vez

Collatz es una pelea entre dos bases: multiplicar por 3 es fácil en base 3 y dividir por 2 es fácil en base 2.
¿Una potencial que lea las dos escrituras a la vez? **[Experimento]** Con un test exacto sobre autómatas
(`scripts/two_base_exact.py`), la mejor potencial posible es la más tonta, el largo en bits, y las ventanas en una
o dos bases no mejoran **nada**. La razón: $-1$ es un punto fijo que se escribe `…1111` en binario y `…2222` en
ternario, y los números $6^K m - 1$ se ven quietos en las dos bases mientras crecen.

## Ronda 11: cuatro ideas raras

- **Potenciales no locales.** La única potencial que funciona es "cuánto va a crecer la órbita en el futuro", y que
  eso sea finito para todo $n$ **es** que no haya divergencia. La potencial buscada es media conjetura.
- **Dinámica holomorfa.** Al extender Collatz a una función entera del plano complejo, las derivadas en los enteros
  son datos libres: la teoría devuelve lo que uno le pone y no distingue $3x+1$ de $5x+1$.
- **Inducción reforzada.** Reglas finitas que dejan bajar a $n$ por cualquier camino del grafo, hacia adelante o
  hacia atrás, mejoran pero se estancan. Hay puntos **mixtos**, como el que vale $-1$ en $\mathbb{Z}_2$ y $0$ en
  $\mathbb{Z}_3$: hacia adelante imitan a $-1$, y hacia atrás no tienen predecesores.
- **La familia $3x + a$.** Promediar sobre todos los $a$ diluye el caso $a = 1$: otra vez "en promedio" contra
  "en este caso".

## La síntesis

> En todas las traducciones que probamos (2-ádica, polinomial, acarreos, analítica, reescritura, dos bases), el
> problema o se ve igual o se vuelve trivial. Lo que **nunca viaja** de un idioma a otro es la interacción entre el
> **tamaño real** del número (cuántas cifras tiene, si es positivo) y su **estructura de últimas cifras**.

Los métodos ven datos locales (restos, cifras, derivadas) o promedios, y en esos datos los ciclos negativos y sus
sombras son indistinguibles de los positivos. Lo que separa a los positivos es su **tamaño a lo largo de toda la
órbita**, y ninguna herramienta conocida lo captura.

## Qué es nuestro y qué no

La escalera $C_k$ y los tests exactos en dos bases no los encontramos en la literatura (búsqueda no exhaustiva).
Las barreras de signo y de ventanas están probadas en rStation (collatz_3, 32, 40, 66, 98, 208), y la nuestra de
localidad es parecida. Todo lo de este capítulo es **[Experimento]** salvo `out_injective_below`.

## Ejercicios

1. (Papel) Calculá $5 \mapsto ?$ en $C_2$ y verificá el ciclo falso $3 \to 5 \to 6 \to 3$.
2. (Papel) Mostrá que $n = 6^K m - 1$ termina en $K$ unos en binario y en $K$ doses en ternario.
3. (Para pensar) Elegí una idea tuya para probar Collatz y pasala por los filtros: ¿funcionaría para $5n+1$? ¿Y para
   el ciclo de $-5$?
