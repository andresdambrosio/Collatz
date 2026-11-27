# 11. Leer pruebas ajenas: Opfer y la Conjetura A

> Código: `Collatz/Opfer.lean`. Informe: `docs/audit_conjectureA.md` (en inglés).

## La idea

Cada tanto aparece una "prueba de Collatz". Casi todas están mal, y encontrar dónde está mal suele ser muy
trabajoso: son textos largos, con notación propia, y el error está escondido en una frase que parece inocente.

Un asistente de demostración cambia el juego, en los dos sentidos:

- **Para desarmar una prueba en papel**, se formaliza el paso sospechoso y se mira qué dice en realidad.
- **Para creerle a una prueba en Lean**, no alcanza con que "compile": hay que auditar qué dice el enunciado, qué
  axiomas usa y si el propio Lean es confiable.

Este capítulo cuenta un caso de cada tipo.

## Opfer (2011): una prueba circular

### La historia

**[Literatura]** Berg y Meinardus (1994) tradujeron Collatz a una pregunta sobre funciones holomorfas en el disco:
Collatz equivale a que el núcleo de cierto par de operadores sea exactamente un espacio chico conocido. En 2011,
Gerhard Opfer anunció una prueba de la conjetura por ese camino. Poco después, él mismo reconoció que estaba
incompleta.

Al desarmar la traducción vimos que la condición analítica es casi **vacía**. Los elementos del núcleo
corresponden a funciones constantes en cada "componente" del grafo de Collatz, y las series que aparecen tienen
coeficientes 0 y 1, que siempre convergen. La formulación dice "el grafo de Collatz es conexo" en otro idioma.

### El paso clave

La prueba de Opfer depende de su Teorema 4.17: su **algoritmo de aniquilación** (Algoritmo 4.10), aplicado a
cualquier par $v \ge 6$, termina en 8. El algoritmo combina dos rutinas:

- *forward* (Alg. 3.1): mientras $j$ sea impar, $j \mapsto (3j + 1)/2$; devuelve el primer valor par;
- *backward* (Alg. 3.4): mientras $m \ge 5$ y $3 \mid m + 1$, $m \mapsto (2m - 1)/3$.

Un paso de aniquilación sobre $v$ es *forward(backward($v/2$))*. Su Tabla 4.8 muestra la corrida desde 326:

```text
326 → 368 → 184 → 92 → 46 → 80 → 40 → 20 → 10 → 8
```

Comparala con la órbita acelerada de $163 = 326/2$:

```text
163 → 245 → 368 → 184 → 92 → 46 → 23 → 35 → 53 → 80 → 40 → 20 → 10 → 5 → 8 → …
```

Es la **misma órbita**, comprimida: el algoritmo salta los tramos impares. Su Teorema 4.17 ("el algoritmo siempre
termina en 8") es la conjetura de Collatz, y su argumento del "árbol de aniquilación" supone lo que quiere probar.

## En Lean

```lean
def fwd (j : ℕ) : ℕ :=
  if h : j % 2 = 1 then fwd ((3 * j + 1) / 2) else j
termination_by padicValNat 2 (j + 1)

def bwd (m : ℕ) : ℕ :=
  if h : 5 ≤ m ∧ (m + 1) % 3 = 0 then bwd ((2 * m - 1) / 3) else m

def annih (v : ℕ) : ℕ := fwd (bwd (v / 2))

/-- El Teorema 4.17 de Opfer, tal como lo usa su prueba. -/
def Theorem_4_17 : Prop := ∀ v, 6 ≤ v → v % 2 = 0 → ∃ i, annih^[i] v = 8

theorem theorem_4_17_iff_collatz : Theorem_4_17 ↔ CollatzConjecture
```

Un detalle lindo: Lean exige probar que `fwd` termina. La medida `padicValNat 2 (j + 1)` es la cantidad de veces que
2 divide a $j + 1$, y cada paso impar la baja en uno, porque $(3j+1)/2 + 1 = 3 \cdot (j+1)/2$. Es la tira final
de unos del capítulo 3: un impar que termina en $k$ unos hace exactamente $k$ subidas seguidas.

El archivo también reproduce las Tablas 3.6 y 4.8 de Opfer con `decide`. Así sabemos que formalizamos *su*
algoritmo y no otro.

## La Conjetura A: auditar una prueba en Lean

### El enunciado

**Conjetura A (Applegate y Lagarias, 1995).** Para cada entero $a$ no divisible por 3 existe $c_a > 0$ tal que la
cantidad de enteros $n$ con $|n| \le x$ cuya órbita pasa por $a$ es al menos $c_a x$, para todo $x \ge |a|$.

En criollo: todo número no múltiplo de 3 es "visitado" por una proporción positiva de los enteros. En 2026,
Naoufal El Jaouhari publicó una prueba en Lean, construida sobre el resultado M2 de ProofAtlas (capítulo 9).

### La auditoría

¿Cómo se audita una prueba en Lean de decenas de miles de líneas, escrita en buena parte por IA?

1. **Compilar desde cero** los 464 módulos. Sin errores.
2. **Buscar vías de escape**: `sorry`, axiomas nuevos, `native_decide`, código no verificado (`implemented_by`, `@[extern]`,
   `unsafe`), opciones que apagan el chequeo del kernel (`debug.skipKernelTC`). Ninguna.
3. **Escribir el enunciado propio**, a mano y desde cero, con controles (por ejemplo, que el mapa cumple `T 7 = 11`),
   y probarlo con su teorema. Si su enunciado dijera otra cosa que la Conjetura A, esto fallaría. Pasó, con los
   tres axiomas estándar.
4. **`leanchecker --fresh`**: el kernel de Lean vuelve a chequear todo desde cero, fuera del entorno de compilación.
5. **Comparar con el paper**: el enunciado coincide exacto con el preprint de Applegate y Lagarias.
6. **Comparar huellas** (SHA-256): lo copiado de ProofAtlas es idéntico al original publicado.
7. **Kernel independiente.** Exportamos las 44 663 declaraciones y las chequeamos con **nanoda**, un kernel de Lean
   escrito por otra gente, en otro lenguaje (Rust).
8. **Prueba de mutación.** Reemplazamos a propósito la prueba central por otra que no corresponde, y nanoda la
   rechazó. Así sabemos que el chequeo independiente realmente mira las pruebas.

¿Por qué tanto? Porque en 2026 circuló una "refutación" de Collatz en Lean que explotaba un **error del kernel**.
Para que esta prueba estuviera mal, el mismo error tendría que estar en Lean y en nanoda a la vez.

**Conclusión.** La Conjetura A está verificada en Lean tal como fue enunciada. Falta una lectura humana de la
matemática de M2. La consecuencia con $a = 1$: **una proporción positiva de los enteros llega a 1**.

## Qué es nuestro y qué no

- **[Lean]** El diagnóstico formal de Opfer (`theorem_4_17_iff_collatz`) es nuestro. Que la prueba estaba
  incompleta lo había reconocido el propio Opfer. No buscamos a fondo si alguien ya había señalado que el algoritmo
  es la órbita de Collatz comprimida.
- **[Literatura]** La prueba de la Conjetura A es de El Jaouhari, sobre M2 de ProofAtlas. Lo nuestro es la
  auditoría.

## Ejercicios

1. (Papel) Verificá que $(3j+1)/2 + 1 = 3(j+1)/2$ para $j$ impar, y concluí que `fwd` termina.
2. (Papel) Mostrá que `bwd` recorre la órbita hacia atrás: si $m = (3j+1)/2$ con $j$ impar, entonces
   $j = (2m-1)/3$.
3. (Computadora) Calculá `annih` desde 54 y compará con la órbita acelerada de 27.
4. (Para pensar) En la auditoría, ¿qué error detecta el paso 3 que ningún otro paso detecta?
