# Intentando demostrar Collatz: el recorrido completo

*Un libro de bitácora, escrito para que se entienda desde cero.*

Estado al 24 de noviembre de 2026 (23:30). Proyecto: [github.com/andresdambrosio/Collatz](https://github.com/andresdambrosio/Collatz).

---

## Cómo leer este libro

Este texto cuenta, en orden, todo lo que hicimos para intentar demostrar la conjetura de Collatz: qué
probamos, qué verificamos con una computadora, qué ideas se cayeron y por qué, y qué descubrimos que otros ya
habían hecho. Para seguirlo alcanza con saber qué es una división, qué es una potencia y un poco de álgebra de
secundario. Cada concepto nuevo se explica la primera vez que aparece. Al final hay un glosario.

Usamos cuatro etiquetas para que siempre quede claro qué tan firme es cada afirmación:

- **[Lean]**: está demostrado y lo chequeó una computadora (el asistente de pruebas Lean). Es lo más firme que hay.
- **[Literatura]**: lo demostró otra persona y está publicado; no lo verificamos nosotros.
- **[Experimento]**: lo vimos en cálculos con computadora, pero no es una demostración.
- **[Abierto]**: nadie sabe.

Una advertencia, la más importante de todo el libro: **la conjetura de Collatz sigue abierta**. Nada de lo que
sigue la demuestra. Lo que conseguimos son reformulaciones verificadas, cotas, barreras (explicaciones de por qué
ciertos caminos no pueden funcionar) y una auditoría de trabajo ajeno. Es poco comparado con el objetivo, y
es mucho comparado con lo que se suele poder verificar sobre este problema.

---

# Parte I. El problema

## Capítulo 1. El juego

Elegí un número entero positivo. Aplicá esta regla:

- si es **par**, dividilo por 2;
- si es **impar**, multiplicalo por 3 y sumale 1.

Repetí con el resultado. Por ejemplo, desde 6:

```
6 → 3 → 10 → 5 → 16 → 8 → 4 → 2 → 1 → 4 → 2 → 1 → …
```

Al llegar a 1 el juego entra en el ciclo 1 → 4 → 2 → 1 y se repite para siempre.

**La conjetura de Collatz** (Lothar Collatz, 1937): *empieces por el número que empieces, siempre terminás
llegando a 1.*

Probalo con 7:

```
7 → 22 → 11 → 34 → 17 → 52 → 26 → 13 → 40 → 20 → 10 → 5 → 16 → 8 → 4 → 2 → 1
```

Y con 27, que es famoso: tarda **111 pasos** y en el camino sube hasta **9232** antes de bajar a 1. Números
chiquitos generan recorridos larguísimos y caóticos. Esa mezcla de reglas simples y comportamiento salvaje es lo
que hace al problema tan atractivo y tan difícil.

### La versión acelerada

Si `n` es impar, `3n + 1` es siempre par (impar por impar es impar, más uno es par). Entonces el paso siguiente
siempre va a ser dividir por 2. Conviene juntar los dos pasos en uno:

$$T(n) = \begin{cases} n/2 & \text{si } n \text{ es par} \\ (3n+1)/2 & \text{si } n \text{ es impar} \end{cases}$$

Con esta versión, desde 7: `7 → 11 → 17 → 26 → 13 → 20 → 10 → 5 → 8 → 4 → 2 → 1`. Es el mismo camino con
algunos pasos salteados. La conjetura es la misma con cualquiera de las dos versiones (y eso también está
verificado en Lean, ver el capítulo 5).

### Lo que se sabe sin demostración

- **[Literatura]** Por computadora se verificó que todo número menor que $2^{71} \approx 2{,}4 \cdot 10^{21}$
  llega a 1 (Barina, 2025). Eso no es una prueba: los números son infinitos.
- **[Literatura]** Terras (1976) probó que *casi todos* los números (en el sentido de la densidad: la proporción
  tiende a 100 %) en algún momento bajan por debajo de su valor inicial.
- **[Literatura]** Tao (2019) probó algo mucho más fuerte: casi todos los números llegan a valores "casi acotados".
  Sigue siendo un "casi todos", y él mismo dice que pasar a "todos" es tan difícil como la conjetura.
- **[Lean]** Conway (1972) mostró que si se generaliza el juego (otras reglas según el resto al dividir por
  un número fijo), la pregunta "¿este número llega a una potencia de 2?" se vuelve **indecidible**: no existe
  ningún algoritmo general que la conteste. Lo verificamos en Lean (capítulo 7b). Kurtz y Simon (2007) probaron
  que la versión "¿*todo* número llega a 1?" también es indecidible. Verificamos en Lean que no es ni
  semidecidible ni co-semidecidible (capítulo 7b). Nada de
  esto dice que Collatz sea indecidible, pero sí que no hay un método universal: cualquier prueba tiene que usar
  algo propio de "3n + 1".

> **Para pensar.** ¿Por qué la verificación hasta $2^{71}$, por enorme que sea, no prueba nada?
> (Respuesta: porque un contraejemplo podría ser mayor; además, como veremos, un número que no llega a 1
> podría tener un recorrido que crece para siempre, y eso ninguna computadora lo puede ver terminar.)

## Capítulo 2. ¿Por qué uno *cree* que es cierta?

Hay un argumento heurístico (no es una demostración) muy convincente.

Con el mapa acelerado `T`, un número grande es par o impar "como si tiraras una moneda". Si es par, se divide
por 2. Si es impar, se multiplica por aproximadamente 3/2. En promedio, por paso, el número se multiplica por

$$\sqrt{\tfrac{3}{2} \cdot \tfrac{1}{2}} = \sqrt{\tfrac{3}{4}} \approx 0{,}866 < 1.$$

O sea: en promedio, achica. Un recorrido típico baja.

Pero mirá qué pasa si cambiamos el 3 por un 5 (el juego "5n + 1"): ahora el promedio es
$\sqrt{5/2 \cdot 1/2} = \sqrt{5/4} > 1$, y los números típicos **crecen**. Además 5n + 1 tiene ciclos que no pasan
por 1. Por ejemplo, desde 13:

```
13 → 66 → 33 → 166 → 83 → 416 → 208 → 104 → 52 → 26 → 13
```

Esto nos da la primera lección metodológica, que vamos a usar todo el tiempo:

> **Filtro de 5n + 1.** Si una supuesta demostración de Collatz funcionaría igual para 5n + 1, está mal, porque
> para 5n + 1 la conclusión es falsa. Toda prueba tiene que usar, en algún lugar, que el número es 3 y no 5.

Hay otros filtros parecidos:

- **Filtro de los negativos.** Con enteros negativos, 3n + 1 tiene ciclos: −1 → −1, o −5 → −7 → −10 → −5. Una
  prueba tiene que usar que el número es positivo.
- **Filtro de "casi todos".** Un argumento probabilístico o de densidad da "casi todos", no "todos".
- **Filtro de las últimas cifras.** Un argumento que sólo mira el resto al dividir por $2^k$ no alcanza (lo vemos
  en el capítulo 4).

## Capítulo 3. Las dos maneras de fallar

Supongamos que la conjetura fuera falsa. Hay un número `n` que nunca llega a 1. Su recorrido es una sucesión
infinita de enteros positivos. Hay sólo dos posibilidades:

1. **El recorrido se repite** (entra en un **ciclo** que no es 1 → 2 → 1). Si alguna vez un número vuelve a
   aparecer, desde ahí todo se repite.
2. **El recorrido nunca repite un número.** Entonces tiene infinitos números distintos, y como hay finitos enteros
   por debajo de cualquier valor, el recorrido tiene que **crecer sin límite** (diverger).

> **[Lean]** `collatz_iff`: la conjetura de Collatz es equivalente a "no hay ciclos no triviales **y** no hay
> recorridos divergentes" (archivo `Collatz/Reductions.lean`).

Esto parte el problema en dos frentes: **ciclos** y **divergencia**. En el archivo `Collatz/Main.lean` están los
dos enunciados abiertos, `no_nontrivial_cycles` y `no_divergent_orbits`, marcados con `sorry` (la palabra de Lean
para "esto no está demostrado"). El teorema final, `collatz_conjecture`, se arma con esos dos.

## Capítulo 4. La primera idea: alcanza con bajar

Esta es la primera idea que exploramos, y la que más conviene entender bien porque reaparece en todo el libro.

### Paso 1: bajar en vez de llegar a 1

En lugar de probar "todo número llega a 1", alcanza con probar algo que parece más débil:

> *Todo número `n > 1` en algún momento llega a un valor **menor que `n`**.*

¿Por qué alcanza? Por **inducción fuerte**, el dominó de la matemática. Supongamos que ya sabemos que todos los
números menores que `n` llegan a 1. Si `n` en algún momento baja a un `m < n`, entonces desde ahí sigue el
recorrido de `m`, que llega a 1. Así que `n` también llega. Como el 1 llega (trivialmente), cae el 2, después el
3, y así todos.

Otra forma de verlo, por el absurdo: si hubiera números que no llegan a 1, tomá **el más chico** de todos. Ese
número, por hipótesis, en algún momento baja a uno menor. Pero ese menor sí llega a 1 (porque nuestro número era
el contraejemplo más chico), y entonces el nuestro también llega. Contradicción.

> **[Lean]** `collatz_of_descent` (archivo `Collatz/Basic.lean`):
>
> ```lean
> theorem collatz_of_descent
>     (H : ∀ n, n > 1 → ∃ k, iter k n < n ∧ iter k n ≥ 1) : Collatz := by
>   intro n hn
>   induction n using Nat.strongRecOn with
>   | _ n ih => ...
> ```
>
> Se lee: "si todo `n > 1` tiene algún `k` tal que el número después de `k` pasos es menor que `n` (y al menos 1),
> entonces vale Collatz". `Nat.strongRecOn` es exactamente la inducción fuerte.

### Paso 2: los fáciles

- **Los pares bajan en un paso**: `n → n/2 < n`. **[Lean]** `even_descends`.
- **Los de la forma 4k + 1 bajan en tres pasos** (con la versión clásica):
  `4k+1 → 12k+4 → 6k+2 → 3k+1`, y `3k + 1 < 4k + 1` si `k ≥ 1`. **[Lean]** `one_mod_four_descends`.

Ya cubrimos la mitad (pares) y un cuarto más (4k + 1). Faltan los de la forma **4k + 3**, una cuarta parte.

### Paso 3: el problema de los 4k + 3

Con la versión acelerada, mirá cuánto tardan algunos 4k + 3 en bajar:

| n | recorrido hasta bajar de n |
|---|---|
| 3 | 3 → 5 → 8 → 4 → **2** |
| 7 | 7 → 11 → 17 → 26 → 13 → 20 → 10 → **5** |
| 11 | 11 → 17 → 26 → 13 → 20 → **10** |
| 19 | 19 → 29 → 44 → 22 → **11** |
| 27 | 27 → 41 → 62 → 31 → 47 → … (59 pasos, llega a 4616) … → **23** |

Uno puede seguir partiendo en casos: mirar el resto módulo 8, módulo 16, módulo 32… En cada nivel, la mayoría de
las clases de restos baja en una cantidad fija de pasos, **para todos los números de esa clase a la vez**
(Terras, 1976). Pero siempre queda alguna clase rebelde.

La peor es la de los números $2^k - 1$ (en binario, `111…1`). Con la versión acelerada, `n = 2^k − 1` hace

$$2^k - 1 \;\to\; 3\cdot 2^{k-1} - 1 \;\to\; 3^2\cdot 2^{k-2} - 1 \;\to\; \cdots \;\to\; 3^k - 1,$$

**subiendo** durante `k` pasos seguidos. Por ejemplo 31 = 2⁵ − 1: `31 → 47 → 71 → 107 → 161 → 242`. Por más
fino que mires el resto módulo $2^k$, la clase de $-1$ sube durante `k` pasos. Por eso ningún argumento que
sólo mire las últimas `k` cifras binarias puede cerrar el problema: es el **filtro de las últimas cifras**.

**Moraleja del capítulo.** Lo que se puede hacer con "casos según las últimas cifras" cubre casi todo, pero nunca
todo. Es la primera aparición de la brecha que va a perseguirnos en todo el libro: **"casi todos" contra
"todos"**.

> **Para pensar.** Si `n ≡ 3 (mod 4)`, ¿por qué `T(n)` es impar? (Escribí `n = 4k + 3` y calculá
> `(3n + 1)/2 = 6k + 5`.) Por eso los 4k + 3 siempre hacen al menos dos pasos de "subida" seguidos.

## Capítulo 5. Lean, el juez

Una demostración matemática es una cadena de pasos lógicos. Un **asistente de pruebas** como **Lean** es un
programa al que le escribís la demostración en un lenguaje formal, y él chequea cada paso. Si Lean la acepta,
no hay error de razonamiento posible (salvo un error en el propio Lean, que es muy raro y del que hablaremos en
el capítulo 14).

Tres cosas para entender cómo lo usamos:

1. **`sorry`** es la forma de decir "esto lo dejo sin demostrar". Lean acepta el archivo pero marca la deuda.
   Nuestro teorema principal, `collatz_conjecture`, depende de dos `sorry`: los dos frentes abiertos.
2. **Los axiomas.** Toda demostración en Lean descansa en unos pocos axiomas básicos de la matemática
   (`propext`, `Classical.choice`, `Quot.sound`). Con el comando `#print axioms` se puede pedir la lista de
   axiomas que usa un teorema. Si aparece `sorryAx`, hay un `sorry` escondido en alguna parte. Nuestra regla:
   **nada se declara demostrado si no compila sin errores y su lista de axiomas es la estándar**. El chequeo
   está en `scripts/Axioms.lean`.
3. **El kernel.** El corazón de Lean es un núcleo chico (el *kernel*) que hace el chequeo final. Todo lo demás
   (las tácticas, la automatización) produce algo que el kernel revisa. Cuando un cálculo enorme se hace
   "dentro del kernel" (`decide +kernel`), el resultado tiene la misma garantía que una prueba escrita a mano.

Mathlib es la gran biblioteca de matemática de Lean, mantenida por la comunidad. Nuestro proyecto la usa.

También usamos un principio de trabajo: **calcular antes de formalizar.** Toda afirmación se prueba primero con
Python en millones de casos; recién si sobrevive, se escribe en Lean.

### Nuestro punto de partida: CollatzForge

Este proyecto heredó una biblioteca anterior nuestra, **CollatzForge** (unas 3500 líneas de Lean sin `sorry`),
que está en `Collatz/Forge/`. Entre otras cosas tenía:

- **[Lean]** la verificación, dentro del kernel, de que todo número menor que 600 001 llega a 1;
- **[Lean]** que todo ciclo no trivial tiene al menos **2301** pasos impares;
- **[Lean]** el retrato de un hipotético recorrido divergente: tendría que tener, a la larga, una proporción de
  pasos impares inusualmente alta: en promedio, a lo sumo $\log_2 3 \approx 1{,}585$ divisiones por 2 por cada
  paso impar, cuando lo típico es 2.

`Collatz/Bridge.lean` prueba que las definiciones de CollatzForge (que usa la versión acelerada) y las de este
proyecto (versión clásica) dicen lo mismo.

---

# Parte II. Lo que verificamos

## Capítulo 6. Los ciclos tienen que ser larguísimos: 15 601

### La ecuación de un ciclo

Usemos el mapa de los impares: un impar `n` va a $(3n+1)/2^a$, dividiendo por 2 todas las veces (`a`) que haga
falta para volver a un impar. Supongamos un ciclo que visita los impares $n_1, \dots, n_k$ y divide por 2 un total
de `A` veces. Multiplicando todos los pasos alrededor del ciclo, los `n_i` se cancelan y queda

$$2^A = \prod_{i=1}^{k} \left(3 + \frac{1}{n_i}\right).$$

De acá salen dos cosas:

- $2^A > 3^k$ (cada factor es mayor que 3);
- si todos los números del ciclo son al menos `M`, entonces $2^A \le (3 + 1/M)^k$.

Tomando logaritmos:

$$0 < A - k\log_2 3 \le k \log_2\!\left(1 + \frac{1}{3M}\right).$$

En palabras: $A/k$ tendría que ser una aproximación **buenísima** de $\log_2 3 = 1{,}58496\ldots$ Las
aproximaciones racionales muy buenas necesitan denominadores grandes, y la **fracción continua** de $\log_2 3$
dice exactamente cuán grandes. Cuanto más grande es `M`, más largo tiene que ser el ciclo.

### De dónde sale M

La forma clásica: verificar por computadora que todo número menor que `M` llega a 1. Así lo hacía CollatzForge
con M = 600 001, y salía k ≥ 2301.

Pero "llegar a 1" es más de lo necesario. Mirá el **menor** número del ciclo: por definición, su recorrido nunca
baja de él. Entonces alcanza con verificar que todo impar `1 < n < M` en algún momento **baja de sí mismo**: la
misma idea del capítulo 4, ahora usada para ciclos. Y eso se abarata mucho con el truco de Terras: para la
mayoría de las clases de restos módulo $2^{20}$, los primeros 20 pasos son iguales para todos los números de la
clase, y se puede probar que bajan **de una vez para toda la clase**, simbólicamente.

| Paso | Cantidad |
|---|---|
| Clases impares módulo $2^{20}$ | 524 288 |
| Clases que bajan simbólicamente (para todo número de la clase) | 496 959 (94,8 %) |
| Números restantes menores que $M = 78 \cdot 2^{20} = 81\,788\,928$, chequeados uno por uno | 2 131 661 |
| Espera más larga antes de bajar | 376 pasos |

> **[Lean]** `cycle_period_ge_15601`: todo ciclo no trivial de Collatz tiene al menos **15 601** pasos impares.
> Todo calculado dentro del kernel, sin programas externos ni hipótesis (archivos `Collatz/CycleBound.lean` y
> `Collatz/CycleBound/`, generados por `scripts/gen_cycle_blocks.py`).

### Una lección sobre la memoria

La primera versión de este cálculo colgó la computadora varias veces. El kernel guarda todo resultado intermedio
hasta terminar cada teorema, y le habíamos pedido verificar bloques grandes en 16 archivos **en paralelo**: unos
3,4 GB por bloque, por 16, en una máquina de 16 GB. La versión final usa 2048 teoremas chicos (0,65 GB cada uno)
encadenados para que compilen a lo sumo dos a la vez. Tarda unos 30 minutos, una sola vez. Desde entonces, toda
corrida pesada se mide primero y se lanza con un "guardián" que la frena si la memoria libre baja demasiado.

### Perspectiva honesta

- El método **no es nuestro**: es de Eliahou (1993), que con verificación hasta $2^{40}$ ya había probado
  k ≥ 17 087 915. Nuestro script reproduce ese número exacto. Lo nuestro es la **verificación formal**
  completa.
- **[Literatura]** Con la verificación hasta $2^{71}$ la cota es de unos $7 \cdot 10^{10}$; en Lean lo tenemos
  como teorema *con esa verificación como hipótesis explícita* (`hercher_lower_bound`).
- **[Literatura]** Hercher (2023): no hay ciclos con hasta 91 "picos" (mínimos locales), de cualquier largo.
- La cota crece más o menos como $\sqrt{M}$. Ninguna cantidad de cómputo transforma "muy largo" en "imposible".
  Para eso hace falta una idea.

## Capítulo 7. Collatz como un juego de reescribir palabras

### La reformulación de Yolcu, Aaronson y Heule (2021)

Escribí un número como una palabra de siete letras:

- dos cifras **binarias**: `f` (cero) y `t` (uno);
- tres cifras **ternarias**: `0`, `1`, `2`;
- dos marcadores de borde: `▷` (principio) y `◁` (final).

Se lee de izquierda a derecha arrancando con el valor 1 en `▷`: `f` hace $x \mapsto 2x$, `t` hace
$x \mapsto 2x+1$, y una cifra ternaria `d` hace $x \mapsto 3x + d$. Así, `▷t◁` vale 3 y `▷ft◁` vale 5
(1 → 2 → 5). Un mismo número tiene muchas escrituras.

El juego tiene **11 reglas**, que se pueden aplicar en cualquier lugar de la palabra:

| Regla | Qué le hace al valor |
|---|---|
| `f◁ → ◁` | divide por 2 un par |
| `t◁ → 2◁` | manda un impar $2y+1$ a $3y+2 = (3(2y+1)+1)/2$ |
| `f0 → 0f`, `f1 → 0t`, `f2 → 1f`, `t0 → 1t`, `t1 → 2f`, `t2 → 2t` | nada: pasan una cifra binaria por encima de una ternaria |
| `▷0 → ▷t`, `▷1 → ▷ff`, `▷2 → ▷ft` | nada: reescriben en binario la primera cifra ternaria |

Las dos primeras son el mapa `T`. Las otras nueve no cambian el valor: mueven las cifras ternarias hacia la
izquierda hasta "disolverlas" en binario. El 3 completo:

```
▷t◁ → ▷2◁ → ▷ft◁ → ▷f2◁ → ▷1f◁ → ▷fff◁ → ▷ff◁ → ▷f◁ → ▷◁
 3     5     5      8      8      8       4      2     1
```

**El teorema.** Collatz es cierta **si y sólo si** este juego siempre termina, elijas las reglas que elijas
(en el idioma de la reescritura: *el sistema termina*).

> **[Lean]** `collatz_iff_terminates` (`Collatz/Rewriting.lean`) sobre las palabras `▷w◁`, y
> `collatz_iff_terminatesAll` (`Collatz/Rewriting/AllWords.lean`) sobre **todas** las palabras de siete letras
> (Lema 3.16 del paper). Nuestra prueba de esta segunda es distinta de la del paper.

### Certificados: el centro de todo

¿Para qué sirve traducir Collatz a un juego de palabras? Porque para la terminación de juegos de reescritura
existen **certificados** que una computadora puede encontrar.

Un **certificado** es un objeto finito y concreto que se puede chequear mecánicamente y que, una vez chequeado,
garantiza un enunciado infinito. El ejemplo de juguete: si a cada letra le asignás un peso (un número natural) de
modo que **cada regla baje estrictamente el peso total** de la palabra, el juego termina, porque un número natural
no puede bajar para siempre. Los pesos son el certificado: son pocos números, y chequear que cada regla baja es
una cuenta finita.

En la práctica se usan pesos más ricos: **matrices**. A cada letra se le asigna una matriz, el "peso" de una
palabra es el producto de las matrices de sus letras, y se exige que cada regla no haga subir ese producto (y que
alguna lo haga bajar). Hay dos aritméticas típicas:

- **naturales**: la suma y el producto de siempre;
- **árticas** (o *max-plus*): la "suma" es el máximo y el "producto" es la suma. Se usa $-\infty$ como "cero".

Una técnica clave es **sacar reglas de a una**: si un certificado hace que *todas* las reglas no suban el peso y
*una* lo baje estrictamente, entonces esa regla sólo se puede usar finitas veces, y se puede borrar del problema.

### Lo que verificamos

- **[Literatura]** Yolcu, Aaronson y Heule encontraron, con computadora, certificados para cada uno de los 11
  subsistemas que se obtienen borrando una regla (cada uno termina) y para una variante de Farkas.
- **[Lean]** Escribimos un verificador de interpretaciones matriciales naturales y árticas en Lean y volvimos a
  chequear todos esos certificados (`SRS.termIn_without`, `SRS.Farkas.farkas_convergent`). Hasta donde
  encontramos, nunca se habían verificado en un asistente de pruebas.
- **Un hueco.** En la §4.2 del paper se dice que aplicar siempre "la reescritura posible más a la derecha" simula
  la trayectoria. Esa estrategia se traba en tres palabras cortas: `▷t◁`, `▷f◁` y `▷ft◁`. La conclusión sigue
  valiendo; Lean necesitó un invariante extra y un chequeo finito.

### La trampa: la barrera de Nashida

Sacar una regla hace el problema mucho más fácil. El premio es un certificado para el sistema **completo**: eso
sería una demostración de Collatz.

- **[Literatura]** Nashida (2026, formalizado en Lean) demostró que las interpretaciones matriciales naturales y
  árticas, usadas solas, **nunca** pueden sacar ni una regla del sistema completo, en ninguna dimensión.
- **[Lean]** Nuestro filtro de **vecinos**: si cambiás `t◁ → 2◁` por `t◁ → 1◁`, el juego simula $(3x-1)/2$, que
  tiene ciclos (por ejemplo 5 → 7 → 10 → 5). En ese sistema vecino no se puede sacar ninguna regla
  (`SRS.Neighbor.not_relSN_d1`, `Collatz/Rewriting/Neighbors.lean`). Moraleja: cualquier certificado tiene que
  "ver" la diferencia entre la cifra 2 y la cifra 1 en esa única regla. Es la versión fina del filtro de 5n + 1.
- **[Experimento]** Probamos también matrices con entradas racionales (fuera del alcance de Nashida): nada en las
  cotas que buscamos.

### Clases por las que toda órbita mala tiene que pasar

Yolcu, Aaronson y Heule usaron la reescritura para probar enunciados parciales del tipo "toda órbita que no llega a
1 pasa por un número que deja resto 2 al dividirlo por 8". Se dice que esa clase está **forzada**. Dejaron abiertas
cuatro clases módulo 8: {1}, {5}, {7} y {5, 7}. Si se probara {5, 7}, por ejemplo, alcanzaría con estudiar los
números que dejan resto 5 o 7.

Un paper de rStation (collatz_32, 2026) da un certificado más simple que la reescritura:

- se dibuja el **grafo de residuos** módulo $2^g$: a dónde puede ir el resto de un número en un paso;
- en las partes del grafo con muchos caminos, una "energía" $\log_2 x + \Phi(\text{resto})$ que baja en cada paso;
- en las partes que son un solo ciclo, un "pin": el único número 2-ádico que da vueltas por ese ciclo. Si el pin no
  es un entero positivo, ningún entero puede quedarse ahí para siempre.

- **[Lean]** Formalizamos una versión **entera** de ese certificado y probamos que es correcta
  (`Collatz.Forced.Cert.forced`, `Collatz/Forced.lean`):
  - la energía pasa a ser $x^M \cdot 2^{\Phi}$, que se divide por 2 en cada paso, cosa imposible para siempre;
  - el pin pasa a ser un entero $D \cdot x - P$ que se multiplica por 3 o se divide por 2, así que tiene que ser 0;
  - los números chicos los cubre la verificación de Forge hasta 600 000.
- **[Lean]** Con certificados generados por `scripts/drift_cert.py`, el kernel verifica 24 clases forzadas
  (`Collatz/Forced/Certs.lean`): las diez de Yolcu–Aaronson–Heule módulo 4 y 8 (otra prueba independiente de las
  mismas), {6} y {12} módulo 16, y las clases que collatz_32 presenta como no derivables de lo anterior:
  - {9, 15} y {11, 15} módulo 16;
  - {27, 28} módulo 32;
  - nueve ternas módulo 32, como {7, 25, 30}.

  Por ejemplo: *toda órbita que no llega a 1 pasa por un número que deja resto 9 o 15 al dividirlo por 16*.
- **[Lean]** El más fuerte de la familia es `Collatz.Forced.forced_Bc13`: *toda órbita que no llega a 1 pasa
  por un número $\equiv 7 \pmod 8$ o por uno que coincide módulo $2^{13}$ con un punto del ciclo negativo
  $-5 \to -14 \to -7 \to -20 \to -10 \to -5$*.
  - Es lo más cerca que llega el método a la clase abierta {7}: lo que hay que agregar a "7 mod 8" son justo las
    sombras del ciclo de $-5$.
  - Con módulo $2^{14}$ esa clase ya no tiene certificado; collatz_32 lo prueba y nuestro certificador lo confirma.
  - El grafo tiene 7163 nodos. Para que el kernel lo chequee, las tablas del certificado son árboles binarios
    indexados por los bits del residuo. Compila en unos dos minutos.
- **[Literatura]** Esas clases las encontró collatz_32 (no arbitrado). Lo nuestro es la verificación formal. Las
  cuatro clases abiertas siguen abiertas: el mismo paper prueba que estos certificados no pueden con ellas, en
  ninguna resolución, por la "barrera de signo" de los ciclos negativos
  (`docs/prior_art_rstation.md`). Nuestro certificador lo confirma: falla en las cuatro.

## Capítulo 7b. Conway: no hay un método general

### El enunciado

Una **función de Collatz generalizada multiplicativa** elige un número $D$ y, para cada resto $j$ al dividir
por $D$, una fracción $a_j$; después manda $n \mapsto a_j \cdot n$ cuando $n$ deja resto $j$ (las fracciones
están elegidas para que el resultado sea siempre entero). Collatz es parecido, pero no es exactamente de esta
familia: $3n + 1$ suma un 1, no sólo multiplica.

- **[Lean]** Hay una función así, **fija**, para la que ningún algoritmo decide, dado $m$, si alguna iteración
  de $2^m$ (al menos un paso) es una potencia de 2 (`Conway.conway_undecidable_fixed`). Lo mismo para "alguna
  iteración vale 1". Y por lo tanto tampoco hay algoritmo para el problema con la función como dato
  (`Conway.conway_undecidable`, `Conway.conway_undecidable_one`). Es el teorema de Conway (1972, *Unpredictable
  iterations*), en la forma en que lo citan Kurtz y Simon (2007).

### Cómo se prueba (la cadena)

La idea es que estas funciones pueden **simular una computadora**. Si pudiéramos predecir sus órbitas,
podríamos resolver el problema de la detención, que Turing probó imposible. La cadena, eslabón por eslabón:

1. **Problema de la detención** (ya está en Mathlib): no se puede decidir si un programa termina con entrada 0.
   Lo empaquetamos en una sola función universal $U(m)$ = "correr el programa número $m$".
2. **De funciones recursivas a programas WHILE** (`Collatz/Conway/Compile.lean`). Mathlib describe las funciones
   computables con siete reglas (cero, sucesor, proyección, composición, recursión primitiva, búsqueda del
   primer cero). Para cada regla escribimos un programa con registros que sólo sabe sumar 1, restar 1 y repetir
   "mientras el registro no sea cero", y probamos que termina exactamente cuando la función está definida.
3. **De WHILE a máquinas de Minsky** (`Collatz/Conway/Minsky.lean`): una lista de instrucciones "sumá 1 y saltá" y
   "si es cero saltá acá, si no restá 1 y saltá allá". La máquina se detiene sii el programa termina.
4. **De Minsky a FRACTRAN** (`Collatz/Conway/Fractran.lean`). El truco de Conway: guardar todos los registros en
   **un solo número**, como exponentes de primos ($2^{r_0} \cdot 3^{r_1} \cdot 5^{r_2} \cdots$), y el
   estado de la máquina en un primo más. Cada instrucción es una fracción: multiplicar por $3 \cdot 11/7$
   significa "estando en el estado 7, sumá 1 al registro del 3 y pasá al estado 11". Dividir por un primo sólo se
   puede si el primo está, y eso es justo la pregunta "¿el registro es distinto de cero?".
5. **De FRACTRAN a Collatz generalizado** (`Collatz/Conway.lean`): qué fracción se aplica depende sólo del resto
   de $n$ al dividir por el producto de los denominadores. Eso es exactamente una función de la familia.

Al final, la órbita de $2^m$ toca una potencia de 2 sii el programa número $m$ termina. Si hubiera un
algoritmo para lo primero, lo habría para lo segundo.

### La versión "todo número llega a 1" (Kurtz y Simon)

La pregunta de Collatz no es "¿*este* número llega?", sino "¿*todos* llegan?". Kurtz y Simon (2007) probaron que,
para funciones de la familia **afín** ($n \mapsto a_j n + b_j$ según el resto $j$, como $3n+1$), esa pregunta es
todavía más difícil: es $\Pi_2$-completa, el mismo nivel que "¿este programa termina con *toda* entrada?".

- **[Lean]** El conjunto de funciones afines (dadas por $D$ y una tabla) para las que toda órbita llega a 1
  **no es semidecidible** (`Conway.allReachOne_not_re`) y **su complemento tampoco**
  (`Conway.allReachOne_not_core`). En particular, es indecidible (`Conway.allReachOne_undecidable`). Debajo de
  ambos está `Conway.ks_reduction`. Para toda $F$ recursiva primitiva arma, de forma computable, funciones afines
  genuinas en las que toda órbita llega a 1 sii $\forall x\, \exists x' \ge x,\ F(m, x') = 0$. Esa es
  exactamente la forma $\Pi_2$.
- **[Lean]** El Teorema 1 de Kurtz y Simon, tal cual: hay una traducción computable de programas a funciones
  afines tal que **el programa termina con toda entrada sii toda órbita llega a 1**
  (`Conway.allReachOne_iff_total`). Como "¿termina con toda entrada?" es el problema $\Pi_2$-completo de
  referencia, esto es la $\Pi_2$-dureza.
- **[Literatura]** Lo que no formalizamos: la definición de la clase $\Pi_2$ y la prueba de que la totalidad es
  $\Pi_2$-completa. Mathlib no tiene la jerarquía aritmética.

Lo nuevo respecto de Conway es que ahora hay que controlar **todos** los números, no sólo los que codifican una
computación prolija. Tres ideas lo resuelven:

1. **La basura viaja intacta.** Todo $n$ se escribe como (primos de la máquina) × $u$, con $u$ sin primos de la
   máquina. Las fracciones sólo miran los primos de la máquina, así que $u$ no cambia. Cuando no queda ningún
   primo de la máquina, se aplica la regla afín $n \mapsto (n+1)/2$, que achica estrictamente a $u$. Por eso
   la basura se termina gastando (`Collatz/Conway/Affine.lean`).
2. **Configuraciones rotas.** Si hay dos estados a la vez, se borran de a pares. Si no hay estado, se borran los
   registros. Lo que queda es una configuración cualquiera de la máquina, quizás a mitad de un cálculo, con
   registros absurdos. Por eso la máquina tiene que detenerse **desde cualquier configuración** ("mortalidad"). Lo
   garantizamos usando sólo bucles `for`, que siempre terminan aunque se empiece por la mitad
   (`Collatz/Conway/Mortal.lean`).
3. **Un bucle externo que se corrige solo** (`Collatz/Conway/Outer.lean`): `mientras F(m, x) ≠ 0: x := x + 1`.
   Cada vuelta limpia los registros y recarga $m$ con una sola instrucción "sumá $m$". Así $m$ queda en la tabla
   (como un factor $2^m$ en dos fracciones) y no en un registro que la basura podría ensuciar. Si arrancamos a
   mitad de camino, a lo sumo la primera vuelta da cualquier cosa, y de ahí en más todo es correcto.

Con $F(m,x)$ = "el programa $m$ ya se detuvo a los $x$ pasos" sale que el conjunto no es semidecidible. Con su
negación sale que el complemento tampoco lo es (`Collatz/KurtzSimon.lean`).

### Qué es nuestro y qué no

- Los teoremas son de Conway (1972) y de Kurtz y Simon (2007). Lo nuestro es **la verificación formal**. En una
  búsqueda no encontramos una formalización previa de Kurtz–Simon en ningún asistente de pruebas.
- **[Literatura]** Cómo se compara con el original:
  - La idea central es de ellos: convertir una máquina en otra que se detiene desde *toda* configuración, con un
    cálculo interno acotado por un reloj, que siempre termina, que habilita cada paso del cálculo externo. En el
    borrador de 2006 que vimos es su Teorema 2.3.
  - Nuestra versión del bucle externo es distinta: `mientras F(m, x) ≠ 0: x++`, con $F$ recursiva primitiva,
    compilada sólo con bucles `for`.
  - Ese borrador no tiene la parte aritmética (la sección 3 está vacía). Según la bibliografía anotada de Lagarias,
    la versión publicada "no da pruebas detalladas". La limpieza de la basura dentro del número (pares de estados,
    registros sueltos, la regla $(n+1)/2$) la armamos nosotros.
  - Ellos reducen directamente desde la totalidad ("¿el programa termina con toda entrada?"). Nosotros pasamos
    por la forma $\Pi_2$ general: elegimos $F(c, \langle k, t\rangle) = 0$ cuando las entradas $0, \dots, k$
    terminan en $t$ pasos, con $t$ mínimo.
- **[Literatura]** Ya existe una formalización en Coq de la indecidibilidad de FRACTRAN (Larchey-Wendling y
  Forster, en la *Coq Library of Undecidability Proofs*, usada para el décimo problema de Hilbert). En una
  búsqueda rápida no encontramos una en Lean, pero no lo descartamos.
- La función fija se construye pero no la escribimos: tiene una cantidad enorme de restos. Interesa que existe.

> **Para pensar.** ¿Por qué esto no prueba que Collatz sea indecidible? (Respuesta: porque habla de *la
> familia*; para una función particular, como $3n+1$, puede haber una prueba que use sus propiedades. Lo que sí
> dice es que una prueba de Collatz no puede ser un método que sirva para todas.)

---

# Parte III. El laboratorio

## Capítulo 8. El método

A partir del 23 de noviembre armamos un "laboratorio de ideas" (`Ideas/LAB.md`) con un protocolo fijo:

1. **Idea completa:** tiene que decir cómo descarta *a la vez* ciclos y divergencia.
2. **Filtro de barreras:** ¿falla para 5n + 1? ¿usa que n > 0? ¿va más allá de las últimas cifras y de "casi
   todos"? ¿usa algo propio de 3n + 1?
3. **Prior art:** casi todo ya se intentó; buscar antes de invertir.
4. **Experimento** en Python que podría refutarla.
5. **Lean** sólo para lo que sobreviva.
6. **Registrar el fracaso** con su causa exacta.

Dos hechos que toda prueba tiene que usar:

- **Divergir es ser atípico.** Un recorrido divergente tendría que hacer muchas más subidas que lo normal. En
  5n + 1, en cambio, el recorrido *típico* diverge.
- **Un ciclo es una aproximación diofántica** (la desigualdad del capítulo 6).

## Capítulo 9. Rondas 1 a 5: todas terminan en el mismo lugar

**Ronda 1 (triage).** Seis ideas: subir el "casi todos" de Tao a "todos" usando el árbol de predecesores;
funciones potenciales calculadas por autómatas; la conjugación 2-ádica; ciclos con el método de picos para todo
número de picos; teoremas de rigidez y equidistribución; y minería de la literatura reciente. Las cuatro primeras
chocaban con muros conocidos.

**Minería de ingredientes** (la lección de la casi-prueba de la hipótesis de Riemann de 2026: a veces la clave es
una herramienta existente poco explotada). Todas las herramientas fuertes cercanas (dígitos simultáneos en bases 2
y 3, dinámica ×2×3, sumas exponenciales) son **distribucionales**: hablan de proporciones. A Collatz le falta
siempre un enunciado **puntual**: sobre una órbita, sobre una divisibilidad.

**Ronda 2: el catálogo de Chang (2026).** Un trabajo de 233 páginas (humano + IAs) que recorre 29 paradigmas y
concluye que todos mueren en la misma brecha "distribucional → puntual". Nuestras ideas de la ronda 1 ya estaban
ahí. Lección: el volumen no es progreso, y nada de ese trabajo está verificado formalmente.

**Ronda 3: certificados con etiquetas aritméticas.** Etiquetar cada letra del juego de palabras con el valor del
prefijo módulo `m` y buscar matrices. Resultado: nada en las búsquedas, y algo más importante: **sacar una regla
etiquetada equivale a probar que, a lo largo de toda órbita, cierto resto aparece finitas veces**, lo cual es tan
difícil como Collatz.

**Ronda 4: la "obstrucción de logaritmo discreto" de Chang para ciclos.** Al leerla en detalle, resultó más débil
que lo ya publicado (Hercher 2023 cubre más).

**Ronda 5: el problema de juguete de Erdős** (¿las potencias de 2 mayores que 256 siempre tienen un dígito 2 en
base 3?). También abierto, y también termina pidiendo algo sobre una órbita concreta (la normalidad de
$\log_3 2$ en base 3).

**Síntesis de las cinco rondas.** Toda vía termina en el mismo problema: **probar algo sobre la estadística de
UNA órbita concreta.** La matemática actual no tiene herramientas para enunciados puntuales de ese tipo en ningún
caso conocido.

## Capítulo 10. Ronda 6: la escalera de acarreos

Esta es la ronda más larga y la que sigue corriendo en la computadora mientras escribimos.

### La idea: hay un mundo donde Collatz está resuelto

**[Literatura]** En el mundo de los polinomios con coeficientes 0 y 1 (donde $1 + 1 = 0$, llamado
$\mathbb{F}_2[x]$), el análogo de Collatz **está demostrado**: todo polinomio llega a 1 (Hicks, Mullen, Yucas y
Zavislak, 2008). Monks (2025) observó que, leído en binario, ese mapa es **3n + 1 sin acarreos**: en vez de
sumar `n + 2n + 1`, se hace la suma binaria "olvidando" todos los "me llevo uno" (es el XOR).

¿Por qué ahí es fácil? Porque sin acarreos, el número **nunca se alarga**: la cantidad de cifras no crece. Con
finitas cifras posibles, un recorrido no puede diverger.

**La pregunta:** construir una escalera de problemas que vaya del mundo fácil (sin acarreos) al difícil (los
enteros), y ver en qué escalón se rompe la prueba.

### Primer intento: acarreos diferidos (descartado)

Usar una base "raíz d-ésima de 2", donde `1 + 1` se lleva `d` lugares más arriba. **[Experimento]** Para todo
`d ≥ 2` todos los recorridos divergen: se pierde que, en promedio, el número achica. Lección: la interpolación
tiene que conservar el tamaño real de los enteros.

### Segundo intento: acarreos que mueren, $C_k$

$C_k$ hace lo mismo que Collatz, pero al sumar `n + 2n + 1` en binario, **cada acarreo tiene una edad**: nace con
edad 1, cada lugar que avanza suma 1, y si la edad pasa de `k`, se pierde.

- $C_0$: no hay acarreos. Es el mundo de los polinomios (resuelto).
- $C_\infty$: los acarreos nunca mueren. Es Collatz.

**Ejemplo con k = 2.** En Collatz, 5 → (15 + 1)/2 = 8. En $C_2$, al sumar `101 + 1010 + 1`, el acarreo del `+1`
viaja dos lugares y en el tercero se muere; el resultado es `1100` = 12, y 12/2 = **6**. Entonces en $C_2$:

```
3 → 5 → 6 → 3 → 5 → 6 → …     (¡un ciclo falso!)
7 → 11 → 9 → 12 → 6 → 3 → …
```

**[Experimento]** Lo que se observa:

- `k = 0, 1`: el largo nunca crece; trivial.
- `k = 2` y `k ≥ 4`: hay excursiones largas (el número llega a crecer proporcionalmente a su largo), como en
  Collatz, pero **ningún recorrido diverge**.
- Hay **ciclos falsos**, así que "todo llega a 1" es falso en $C_k$. El análogo correcto de la conjetura es
  "**no hay recorridos divergentes**".
- La estadística ("cuánto sube o baja el largo en promedio") ya en `k = 2` es prácticamente la de Collatz.

> **[Lean]** `Collatz/Carries.lean`: con cualquier regla de acarreos, el paso `n ↦ n + 2n + 1` es inyectivo
> sobre las últimas `m` cifras (`out_injective_below`). Consecuencia: todos los $C_k$, como Collatz y como el
> mundo de los polinomios, son biyecciones de los enteros 2-ádicos (números con infinitas cifras binarias hacia la
> izquierda) que mezclan las cifras igual que una moneda.

**Primera conclusión.** "Mirando las últimas cifras", $C_0$, $C_2$ y Collatz son **el mismo sistema**. Lo que
los distingue es sólo qué números son positivos y cómo se mide su tamaño. Basta un acarreo de largo 2 para que la
dificultad aparezca completa: no viene de los acarreos largos.

### ¿Hay una función potencial local para $C_2$?

Una **función potencial** es una cantidad que no sube en ningún paso. Si existiera una que además crece con el
largo del número, el largo quedaría acotado y no habría divergencia. Buscamos potenciales de la forma

$$V(n) = \text{largo}(n) + \sum f(\text{ventanas de } w \text{ cifras})$$

(más, en una segunda versión, términos que miran las cifras de los bordes). Encontrar `f` es un **programa
lineal** (un problema de optimización que la computadora resuelve exactamente).

**[Experimento]**

- $C_0$: hay potencial (el largo solo; es la prueba de los polinomios).
- Collatz y $C_2$: **no hay**, para ventanas de hasta 7 cifras.

El programa lineal además devuelve **testigos** de por qué falla: números **ralos** (bloques de unos separados
por muchos ceros, como `111010000010`). Cada bloque evoluciona por su cuenta: el de abajo decide la paridad y el
de arriba crece en los pasos impares. Ningún término local puede "saber" que más adelante la paridad va a
compensar. Esos testigos no divergen de verdad: lo que falla es la clase de certificado. Llamamos a esto la
**barrera de localidad**: hace falta un potencial que lea todo el número.

### Certificados de largo acotado

Para leer todo el número volvimos a la reescritura, pero con un blanco nuevo y más chico. Escribimos $C_k$ como
un juego de palabras (`scripts/carry_srs.py`): una "cabeza" `H` recorre la palabra de derecha a izquierda
haciendo la suma con acarreos truncados, cifra por cifra. Simula $C_k$ exactamente (chequeado para n < 3000), y
con `k = ∞` simula Collatz.

Ahora no pedimos que el juego termine (en $C_2$ hay ciclos, así que no termina). Pedimos algo más modesto:

> **Certificado de largo acotado.** Matrices árticas para cada letra tales que (a) **ninguna regla hace subir**
> el peso (orientación débil) y (b) el peso de una palabra es al menos su cantidad de cifras.

Si existe, el peso no sube nunca, así que la cantidad de cifras queda acotada en todo recorrido, y entonces
**no hay divergencia**. Para Collatz sería la mitad de la conjetura. Este tipo de certificado **no lo cubre la
barrera de Nashida**, que habla de orientación estricta.

**Cómo es el peso ártico.** Con matrices `d × d` en la aritmética max-plus, el peso de una palabra es la entrada
de arriba a la izquierda del producto de sus matrices. Intuición: es el valor del "mejor camino" a través de un
autómata con `d` estados, donde cada letra suma un puntaje según el estado. Con `d = 1` es sólo sumar pesos de
letras; con `d` más grande, el peso puede "recordar" contexto.

**Por qué `d = 1` no alcanza** (y esto se entiende a mano). En $C_2$, el paso `3 → 5` hace `11 → 101`: el número
**gana una cifra**. Si cada cifra pesa al menos 1, esa cifra nueva hay que pagarla con algo, y con pesos fijos por
letra no hay de dónde. Con `d` más grande, la cabeza `H` puede traer "crédito" acumulado. La pregunta es si alguna
dimensión alcanza.

### La búsqueda con SAT

Buscar las matrices es un problema enorme de combinatoria. Lo traducimos a **SAT**: una fórmula lógica gigante con
variables verdadero/falso que es satisfacible si y sólo si el certificado existe. Cada entrada de matriz (un número
de 0 a `B`, o $-\infty$) se codifica con variables "x ≥ 0", "x ≥ 1", …, y los productos max-plus se escriben como
compuertas lógicas. Un **solver SAT** (usamos CaDiCaL) responde:

- **SAT**: encontró una asignación; o sea, un certificado. Se verifica aparte y se lleva a Lean.
- **UNSAT**: demostró que no hay ninguna. Es un "no existe" exhaustivo dentro de esos tamaños.

**[Experimento]** Resultados para $C_2$:

| Dimensión `d` | Entradas hasta `B` | Resultado |
|---|---|---|
| 1 | ≤ 4 | UNSAT |
| 2 | ≤ 5 | UNSAT |
| 3 | ≤ 6 | UNSAT (7 min) |
| 4 | ≤ 3 | UNSAT (2 h) |
| 5 | ≤ 3 | 5 de 9 casos UNSAT; 4 sin decidir en 8 h (ver abajo) |

Los **núcleos insatisfacibles** (el subconjunto mínimo de reglas que ya impide el certificado) cuentan dónde está la
obstrucción: en `d = 1` son exactamente las 4 reglas del paso `3 → 5`; en `d = 2` y `3`, la maquinaria del ciclo
falso `3 → 5 → 6 → 3`. Incluso "congelando" los números chicos (para sacar los ciclos falsos del medio), Collatz
sigue UNSAT en `d ≤ 3`: **cada paso de crecimiento de una órbita chica tiene que pagarse con crédito, y en
dimensión chica no alcanza.**

**[Experimento]** Además, $C_2$ tiene ciclos falsos cada vez más grandes (de 3, 6, 9, 11, 15, 18, 19, 20, 21…
cifras), probablemente infinitos. Un certificado de largo acotado tiene que convivir con todos ellos.

### La corrida 5 × 5 (24/11, 13:31 a 23:23)

La búsqueda con `d = 5, B = 3` no terminó en 3 horas. La relanzamos partida en 9 casos (*cube and conquer*: se
fija de antemano el peso de las letras `0` y `1`, cada uno entre 1 y 3), con dos trucos más:

- **Ruptura de simetría:** reordenar los estados del autómata no cambia nada, así que se exige un orden fijo y se
  evita revisar soluciones repetidas.
- **Portafolio:** los casos difíciles los atacan a la vez dos versiones de CaDiCaL (1.5.3 y 1.9.5); alcanza con
  que cualquiera termine.

| Caso (peso de `0`, peso de `1`) | Resultado |
|---|---|
| (1,3), (2,3), (3,1), (3,2), (3,3) | UNSAT, en segundos |
| (1,1), (1,2), (2,1), (2,2) | **sin decidir**: ninguna de las dos versiones terminó en 8 h |

Conclusión honesta: no hay certificado 5 × 5 con entradas hasta 3 en 5 de los 9 casos, y en los otros 4 la pregunta
quedó abierta. Con esta codificación el problema ya no entra en 8 horas. No esperamos un SAT ahí, por lo que se ve
en la sección siguiente.

### El potencial verdadero no es "de memoria finita"

Para entender por qué los certificados no aparecen medimos el **potencial verdadero**: para cada número, cuántas
cifras más que ahora va a llegar a tener su recorrido. Después contamos cuántas clases distintas de prefijos hay que
distinguir para conocerlo (el criterio de Myhill–Nerode). Ese conteo es una cota inferior de los estados de un
autómata determinista que lo calcule exacto.

| Sistema | Clases a medida que se alarga el prefijo leído |
|---|---|
| $C_0$, $C_1$ | 1, 1, 1, … (alcanza con el largo: por eso dan SAT) |
| $C_3$ | 1, 2, 4, 8, 15, 25, 44, 69, 104, 159, 244, 366, 532 (≈ ×1,5 por cifra) |
| $C_2$ | 1, 2, 4, 8, …, 2048, 4095 (prácticamente todo prefijo es distinto) |

**[Experimento]** El potencial mínimo no lo calcula ningún autómata chico. No es una prueba de imposibilidad (un
certificado puede usar un peso mayor que el mínimo, y las matrices árticas son autómatas no deterministas, más
compactos), pero es evidencia fuerte de que la vía de las matrices de tamaño fijo está cerrada para $C_2$ y para
Collatz. Es la barrera de localidad otra vez, ahora medida.

### Un error corregido: el crecimiento de $C_3$ no parece acotado

Durante un tiempo creímos que en $C_3$ el largo crecía a lo sumo unas pocas cifras (5 o 6): eso decían todos los
números menores que $2^{21}$ y muestras al azar de hasta 160 bits. Al intentar demostrarlo, apareció que era un
**artefacto de mirar números chicos**. Los números que más crecen tienen un prefijo elegido arriba y una tira larga de
unos abajo: la tira fuerza muchos pasos impares seguidos, y mientras tanto el prefijo va ganando cifras.

| Largo total del número | 16 | 32 | 64 | 128 | 256 |
|---|---|---|---|---|---|
| Mayor crecimiento encontrado | 5 | 7 | 11 | 19 | 25 |

**[Experimento]** El crecimiento máximo sigue subiendo con el largo, y lo visto es compatible con un ritmo sublineal de $1{,}5\sqrt{L}$ (el cociente con
$\sqrt{L}$ se mantiene entre 1,2 y 1,7, mientras que el cociente con $L$ baja y el cociente con $\log L$ sube). Son
cotas inferiores (la búsqueda puede no encontrar los peores casos). Una lectura heurística: durante la racha de pasos
impares, lo que las cifras de arriba crecen *de más* (respecto de duplicar) se mueve como un paseo al azar sin
tendencia, que en $L$ pasos se aleja unas $\sqrt{L}$ posiciones. En $C_2$ y en Collatz esa tendencia es positiva y
el crecimiento es lineal.

Tampoco hay certificados árticos para $C_3$ con matrices de hasta 4 × 4 (el 4 × 4 tardó 3 h 44 min en dar UNSAT), ni siquiera permitiendo entradas
negativas ("ártico bajo cero") ni congelando los números chicos; los núcleos de la contradicción son pasos reales de
crecimiento como `111 → 1011` (7 → 11). La pregunta que queda, ahora bien planteada, es **[Abierto]**: ¿demostrar
que $C_3$ no diverge, con un potencial que tolere un excedente del orden de $\sqrt{L}$?

Los resultados quedan en `.sat_runs/` (fuera del repositorio) y el detalle en `Ideas/acarreos.md`.

### La reducción que conecta con Collatz

Si a lo largo de un recorrido de Collatz ninguna cadena de acarreos de `n + 2n + 1` supera largo `k`, ese recorrido
es idéntico al de $C_k$. Así que: *si $C_k$ no tiene divergencias, toda divergencia de Collatz tiene cadenas de
acarreo arbitrariamente largas*. Siendo honestos, eso es poco: los números grandes típicos ya tienen cadenas
largas. El valor está en entender el mecanismo, no en la reducción.

## Capítulo 11. Ronda 7: análisis complejo (Berg–Meinardus y Opfer)

**[Literatura]** Berg y Meinardus (1994) tradujeron Collatz a una pregunta sobre funciones holomorfas en el disco:
Collatz equivale a que el núcleo de ciertos dos operadores sea exactamente un espacio chico conocido.

Al desarmarlo vimos que la condición analítica es **vacía**: los elementos del núcleo corresponden a funciones
constantes en cada "componente" del grafo de Collatz, y las series que aparecen tienen coeficientes 0 y 1, que
convergen siempre. La formulación dice "el grafo de Collatz es conexo" en otro idioma. El análisis sólo podría ver
el tamaño a través de densidades: el mismo muro de siempre.

**El hueco de Opfer (2011).** Opfer publicó una supuesta prueba usando esta traducción y luego reconoció que
estaba incompleta. Diagnosticamos el problema: su "algoritmo de aniquilación" **es el mapa de Collatz comprimido**.
Su Tabla 4.8 (326 → 368 → 184 → 92 → 46 → 80 → 40 → 20 → 10 → 8) es la órbita de 163. Su Teorema 4.17 ("el
algoritmo siempre termina en 8") es la conjetura misma, y la prueba la supone: es **circular**.

> **[Lean]** `theorem_4_17_iff_collatz` (`Collatz/Opfer.lean`): el Teorema 4.17 de Opfer es equivalente a la
> conjetura de Collatz. El archivo reproduce sus tablas. Es un ejemplo limpio de cómo un asistente de pruebas
> desenmascara una prueba circular.

## Capítulo 12. La síntesis: tamaño contra últimas cifras

Después de siete rondas, la lección más clara es esta:

> En todas las traducciones que probamos (2-ádica, polinomial, acarreos, analítica, reescritura), el problema o se
> ve igual o se vuelve trivial. Lo que **nunca viaja** de un idioma a otro es la interacción entre el **tamaño
> real** del número (cuántas cifras tiene, si es positivo) y su **estructura de últimas cifras** (2-ádica).

Los mundos donde Collatz es fácil son aquellos donde el tamaño no fluctúa (polinomios). En cuanto el tamaño puede
fluctuar (un solo acarreo de largo 2 alcanza), aparece la dificultad completa. Cualquier prueba tiene que usar las
dos cosas a la vez, y ninguna herramienta conocida lo hace para órbitas individuales.

---

# Parte IV. Lo que hicieron otros

## Capítulo 13. Prior art: lo que encontramos después

Una regla del laboratorio es buscar antes de invertir. Aun así, el 24 de noviembre descubrimos dos cosas
importantes que deberíamos haber visto antes:

- **rstation.ai**, una comunidad de agentes de IA con unos 180 artículos sobre Collatz revisados por agentes.
  Varios se parecen mucho a lo nuestro: los artículos 3 y 32 (potenciales con tamaño + restos, una "barrera de
  signo") se parecen a nuestra barrera de localidad; el 40 (no hay certificados árticos que lean desde la cifra
  menos significativa para ciertas clases) se parece a nuestra búsqueda ártica; el 66 ("hace falta información
  de las primeras cifras de órbitas individuales") se parece a nuestra síntesis. Lo que publiquemos sobre esto
  tiene que citarlos.
- **ProofAtlas** y el resultado **M2**: los predecesores de todo número positivo no divisible por 3 tienen
  densidad inferior positiva (verificado en Lean, asistido por IA, no arbitrado). Esto cambia el panorama del
  "casi todos", como se ve en el capítulo siguiente.

Lo que todavía no encontramos en la literatura (búsqueda no exhaustiva): la familia $C_k$ como interpolación por
acarreos.

## Capítulo 14. La auditoría de la Conjetura A

Naoufal El Jaouhari (@elnaou en X) nos recomendó sus trabajos. Uno de ellos es una prueba en Lean de la
**Conjetura A de Applegate y Lagarias** (1995):

> Para cada entero `a` no divisible por 3 existe una constante $c_a > 0$ tal que la cantidad de enteros $n$ con
> $|n| \le x$ cuyo recorrido pasa por `a` es al menos $c_a \cdot x$, para todo $x \ge |a|$.

En criollo: todo número (no múltiplo de 3) es "visitado" por una proporción positiva de los enteros.

La auditamos con el máximo rigor que pudimos:

1. Compilación desde cero de los 464 módulos, sin errores.
2. Búsqueda de "vías de escape" (`sorry`, axiomas nuevos, código no verificado): ninguna.
3. Un enunciado propio, escrito a mano desde cero (con chequeos como `T 7 = 11`), demostrado con su teorema:
   sólo los tres axiomas estándar.
4. `leanchecker --fresh`: el kernel de Lean vuelve a chequear todo desde cero. OK.
5. Comparamos el enunciado con el texto de Applegate–Lagarias: coincide exacto.
6. Lo que él copió de ProofAtlas es idéntico byte a byte al original publicado (comparamos huellas SHA-256).
7. **Kernel independiente:** exportamos las 44 663 declaraciones y las chequeamos con **nanoda**, un kernel de
   Lean escrito por otra gente en otro lenguaje (Rust). OK.
8. **Prueba de mutación:** reemplazamos a propósito la prueba central por otra que no corresponde y nanoda la
   rechazó. Así sabemos que el chequeo realmente mira las pruebas.

¿Por qué tanto? Porque en 2026 circuló una "refutación" de Collatz en Lean que explotaba un error del kernel. Para
que esta prueba estuviera mal, el mismo error tendría que estar en Lean y en nanoda a la vez.

**Conclusión:** la Conjetura A está verificada en Lean tal como fue enunciada. Falta sólo una lectura humana de la
matemática de M2. El informe está en inglés en `docs/audit_conjectureA.md`.

**La consecuencia importante.** Con `a = 1`: **una proporción positiva de los enteros llega a 1** [Lean, trabajo
ajeno]. Y M2 implica además que si hay un contraejemplo, hay una proporción positiva de contraejemplos. Entonces:

> Collatz ⇔ la proporción de números que llegan a 1 tiende a 100 %.

Esto **no** demuestra Collatz, pero convierte la vieja brecha "casi todos → todos" en algo más preciso.

---

# Parte V. Dónde estamos

## Capítulo 15. Balance honesto

### Lo que está verificado en Lean (nuestro trabajo)

| Teorema | Qué dice | ¿Es nuevo? |
|---|---|---|
| `collatz_iff` | Collatz ⇔ sin ciclos y sin divergencia | Clásico; la verificación es nuestra |
| `collatz_of_descent` | alcanza con que todo `n > 1` baje | Clásico |
| `cycle_period_ge_15601` | ciclos con ≥ 15 601 pasos impares | Método de Eliahou; la verificación formal completa es nuestra |
| `collatz_iff_terminates(All)` | Collatz ⇔ el juego de 11 reglas termina | De YAH; la formalización es nuestra |
| `termIn_without`, `farkas_convergent` | los certificados de YAH son correctos | Primera verificación formal que encontramos; hallamos un hueco en §4.2 |
| `not_relSN_d1`, `not_relSN_d0` | en los vecinos 3x − 1 y 3x − 3 no se saca ninguna regla | Filtro propio |
| `theorem_4_17_iff_collatz` | la prueba de Opfer es circular | Diagnóstico propio |
| `out_injective_below` | la suma con acarreos truncados es inyectiva | Propio (chico) |

`collatz_conjecture` sigue con `sorry`.

### Lo que aprendimos

1. Todos los caminos terminan pidiendo algo sobre **una órbita concreta**, no sobre la mayoría.
2. La dificultad aparece completa **con acarreos de largo 2**: no es cosa de números gigantes.
3. Los certificados que miran pedazos locales del número no alcanzan (**barrera de localidad**); hace falta leer
   todo el número, y los certificados árticos chicos tampoco aparecen (hasta 4 × 4, y 5 × 5 parcial). El potencial
   verdadero no se puede leer con memoria finita chica.
6. Hay que desconfiar de "acotado" cuando sólo se miraron números chicos: en $C_3$ el crecimiento parecía de 6 cifras
   y lo que se ve es un crecimiento compatible con $\sqrt{L}$.
4. Lo que nunca se traduce es la interacción entre **tamaño** y **últimas cifras**.
5. Mucho de lo que encontramos ya lo había encontrado otra gente (rstation). La honestidad sobre la novedad es
   parte del trabajo.

### Hacerlo en público

El repositorio es público (licencia Apache-2.0) y hay un blog en inglés y español
([andresdambrosio.github.io/Collatz](https://andresdambrosio.github.io/Collatz/)). Publicados: la presentación,
"Collatz como un juego de reescribir palabras", la cota de 15 601 y "No hay un método general" (Conway y
Kurtz–Simon, 26/11). Los borradores anteriores (el laboratorio, "un
mundo donde Collatz está resuelto" y una página de estado) se descartaron el 25/11. Los nuevos tienen que citar
rStation y el resultado de densidad positiva (`docs/prior_art_rstation.md`).

### Lo que sigue

1. $C_3$: medir mejor el ritmo $\sqrt{L}$ y buscar una prueba de que no diverge (o un argumento de que sí).
2. Repensar el laboratorio con la nueva equivalencia "Collatz ⇔ densidad de convergentes → 1": ¿qué falta entre
   Tao y densidad 1?
3. Leer a fondo rstation y la matemática de M2.
4. Un artículo sobre la verificación formal (reescritura + hueco + cota 15 601).
5. `Collatz/Frontier.lean`: un atlas de enunciados abiertos con sus reducciones verificadas.

---

# Apéndices

## A. Glosario

- **Acarreo**: el "me llevo uno" de la suma.
- **Ártica (aritmética)** o **max-plus**: la "suma" es el máximo y el "producto" es la suma; $-\infty$ hace de cero.
- **Certificado**: objeto finito, chequeable mecánicamente, que garantiza un enunciado infinito.
- **Ciclo no trivial**: un recorrido que vuelve a un número sin pasar por 1.
- **Cube and conquer**: partir un problema SAT en casos fijando algunas variables, y resolverlos en paralelo.
- **Densidad**: la proporción de números con una propiedad, en el límite.
- **Divergencia**: un recorrido que crece sin límite.
- **Fracción continua**: forma de escribir un número que da sus mejores aproximaciones racionales.
- **Inducción fuerte**: si cada caso se deduce de los anteriores, valen todos.
- **Kernel**: el núcleo chico de Lean que hace el chequeo final.
- **Lean**: asistente de pruebas; chequea demostraciones paso a paso.
- **Mapa acelerado `T`**: `n/2` si es par, `(3n + 1)/2` si es impar.
- **Núcleo insatisfacible**: subconjunto de restricciones que ya es contradictorio por sí solo.
- **Orientar (débil/estricto)**: que una regla no haga subir (débil) o haga bajar (estricto) el peso.
- **Programa lineal**: optimizar una función lineal con restricciones lineales.
- **Reescritura**: juego de reemplazar pedazos de palabras según reglas.
- **SAT / solver SAT**: el problema de decidir si una fórmula lógica se puede hacer verdadera; programa que lo resuelve.
- **`sorry`**: marca de "no demostrado" en Lean.
- **2-ádico**: mirar un número por sus últimas cifras binarias, con infinitas cifras posibles hacia la izquierda.

## B. Referencias principales

- J. C. Lagarias (ed.), *The Ultimate Challenge: The 3x+1 Problem*, AMS (2010).
- R. Terras, "A stopping time problem on the positive integers", *Acta Arith.* 30 (1976).
- T. Tao, "Almost all orbits of the Collatz map attain almost bounded values", *Forum Math. Pi* 10 (2022), arXiv:1909.03562.
- D. Barina, "Improved verification limit for the convergence of the Collatz conjecture", *J. Supercomputing* 81 (2025).
- S. Eliahou, "The 3x+1 problem: new lower bounds on nontrivial cycle lengths", *Discrete Math.* 118 (1993).
- C. Hercher, "There are no Collatz m-cycles with m ≤ 91", *J. Integer Seq.* 26 (2023).
- E. Yolcu, S. Aaronson, M. Heule, "An Automated Approach to the Collatz Conjecture", *J. Autom. Reasoning* 67 (2023), arXiv:2105.14697.
- H. Nashida, preprint (2026), doi:10.5281/zenodo.23147025.
- Hicks, Mullen, Yucas, Zavislak, *Amer. Math. Monthly* 115 (2008) 615–622.
- K. Monks, arXiv:2508.10153 (2025).
- L. Berg, G. Meinardus, *Results Math.* 25 (1994); G. Opfer, preprint Hamburger Beiträge 2011-09.
- D. Applegate, J. Lagarias, *Math. Comp.* 64 (1995), doi:10.1090/S0025-5718-1995-1270612-0.
- N. El Jaouhari, ConjectureA (Lean), github.com/neljaouh/ConjectureA, Zenodo 23025918.
- C. Chang, arXiv:2603.11066 (2026).
- J. H. Conway, "Unpredictable iterations", *Proc. 1972 Number Theory Conf.*, Univ. of Colorado, Boulder (1972) 49–52.
- S. A. Kurtz, J. Simon, "The undecidability of the generalized Collatz problem", *TAMC 2007*, LNCS 4484, 542–553.
- D. Larchey-Wendling, Y. Forster, "Hilbert's Tenth Problem in Coq", *FSCD 2019* (extendida: arXiv:2003.04604).

## C. Mapa del repositorio

| Archivo | Capítulo |
|---|---|
| `Collatz/Basic.lean`, `Collatz/Reductions.lean`, `Collatz/Main.lean` | 3, 4 |
| `Collatz/Forge/`, `Collatz/Bridge.lean` | 5 |
| `Collatz/CycleBound.lean`, `Collatz/CycleBound/` | 6 |
| `Collatz/Rewriting.lean`, `Collatz/Rewriting/` | 7 |
| `Collatz/Conway.lean`, `Collatz/Conway/` | 7b |
| `Ideas/LAB.md` | 8, 9 |
| `Ideas/acarreos.md`, `Collatz/Carries.lean`, `scripts/carry_*.py`, `scripts/run_cubes.sh` | 10 |
| `Ideas/berg_meinardus.md`, `Collatz/Opfer.lean` | 11 |
| `docs/audit_conjectureA.md` | 14 |
| `PLAN.md` | 15 |
