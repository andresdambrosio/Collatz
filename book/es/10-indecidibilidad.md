# 10. No hay un método general: Conway y Kurtz–Simon

> Código: `Collatz/Conway.lean`, `Collatz/Conway/` (`While`, `Compile`, `Minsky`, `Fractran`, `Mortal`, `Outer`,
> `Affine`), `Collatz/KurtzSimon.lean`

## La idea

Collatz es un caso de una familia: elegís un número $D$ y, según el resto de $n$ al dividir por $D$, aplicás una
regla afín distinta. Collatz es el caso $D = 2$, con $n/2$ y $3n+1$.

En 1972, John Conway demostró algo sorprendente: hay funciones de esa familia que **simulan computadoras**.
Entonces, predecir sus órbitas es tan difícil como predecir si un programa termina, y eso, por un teorema de
Turing, es imposible en general. En 2007, Stuart Kurtz y Janos Simon probaron que la pregunta de Collatz
propiamente dicha, "¿**toda** órbita llega a 1?", es todavía más difícil para la familia.

Esto **no** dice que Collatz sea indecidible. Dice que no hay un método universal: cualquier prueba tiene que usar
algo propio de $3n + 1$. Es el filtro de $5n + 1$ llevado al extremo.

## La matemática

### Computabilidad en dos párrafos

Una función es **computable** si hay un programa que la calcula. Un conjunto de naturales es **decidible** si hay
un programa que, dado $n$, termina siempre y responde si $n$ está o no. Es **semidecidible** (o *r.e.*) si hay un
programa que termina exactamente en los $n$ que están (en los otros puede correr para siempre).

**Teorema (Turing, 1936).** El conjunto de los programas que terminan con entrada 0 (el *problema de la
detención*) es semidecidible (basta correrlos) pero no decidible. Su complemento no es semidecidible.

La técnica para probar que algo es indecidible es la **reducción**: si pudieras decidir $X$, podrías decidir la
detención. Entonces $X$ es indecidible.

### El teorema de Conway

Una **función de Collatz generalizada multiplicativa** es $g(n) = a_{n \bmod D} \cdot n$, con fracciones $a_j$
elegidas para que el resultado sea siempre entero.

**Teorema (Conway, 1972).** Hay una función así, **fija**, para la que ningún algoritmo decide, dado $m$, si alguna
iteración de $2^m$ (al menos un paso) es una potencia de 2.

La prueba es una cadena de simulaciones.

1. **Problema de la detención** (Mathlib). Lo empaquetamos en una sola función universal: "correr el programa
   número $m$".
2. **De funciones recursivas a programas WHILE** (`Compile.lean`). Mathlib describe las funciones computables con
   unas pocas reglas (cero, sucesor, proyección, composición, recursión primitiva, búsqueda del primer cero). Para
   cada regla escribimos un programa con registros que sólo sabe sumar 1, restar 1 y repetir "mientras el registro
   no sea cero", y probamos que termina exactamente cuando la función está definida.
3. **De WHILE a máquinas de Minsky** (`Minsky.lean`): una lista de instrucciones del tipo "sumá 1 y saltá" y "si es
   cero saltá acá, si no restá 1 y saltá allá".
4. **De Minsky a FRACTRAN** (`Fractran.lean`). El truco de Conway: guardar todos los registros en **un solo
   número**, como exponentes de primos ($2^{r_0} 3^{r_1} 5^{r_2} \cdots$), y el estado de la máquina en un primo
   más. Cada instrucción es una fracción: multiplicar por $3 \cdot 11 / 7$ significa "estando en el estado 7, sumá
   1 al registro del 3 y pasá al estado 11". Dividir por un primo sólo se puede si el primo está, y eso es
   exactamente la pregunta "¿el registro es distinto de cero?".
5. **De FRACTRAN a Collatz generalizado** (`Conway.lean`). Qué fracción se aplica depende sólo del resto de $n$ al
   dividir por el producto de los denominadores: es una función de la familia.

Al final, la órbita de $2^m$ toca una potencia de 2 si y sólo si el programa $m$ termina.

### La versión "todos llegan a 1": Kurtz y Simon

Ahora la familia es **afín**: $n \mapsto a_j n + b_j$ según el resto $j$, como $3n + 1$.

**Teorema (Kurtz y Simon, 2007).** El conjunto de las funciones afines generalizadas para las que toda órbita
llega a 1 no es semidecidible, y su complemento tampoco. (De hecho es $\Pi_2$-completo: el mismo nivel que "¿este
programa termina con **toda** entrada?".)

Lo nuevo respecto de Conway es que ahora hay que controlar **todos** los números, no sólo los que codifican una
computación prolija. Tres ideas lo resuelven:

1. **La basura viaja intacta.** Todo $n$ se escribe como (primos de la máquina) × $u$, con $u$ sin primos de la
   máquina. Las fracciones sólo miran los primos de la máquina, así que $u$ no cambia. Cuando no queda ningún primo
   de la máquina se aplica $n \mapsto (n+1)/2$, que achica a $u$. La basura se termina gastando (`Affine.lean`).
2. **Configuraciones rotas.** Si hay dos estados a la vez, se borran de a pares. Si no hay estado, se borran los
   registros. Lo que queda es una configuración cualquiera de la máquina, quizás a mitad de un cálculo y con
   registros absurdos. Por eso la máquina tiene que detenerse **desde cualquier configuración** ("mortalidad"), y lo
   garantizamos usando sólo bucles `for`, que siempre terminan aunque se empiece por la mitad (`Mortal.lean`).
3. **Un bucle externo que se corrige solo** (`Outer.lean`): `mientras F(m, x) ≠ 0: x := x + 1`. Si arrancamos a mitad
   de camino, a lo sumo la primera vuelta da cualquier cosa, y de ahí en más todo es correcto.

Con $F(m, x)$ = "el programa $m$ ya se detuvo a los $x$ pasos", toda órbita llega a 1 si y sólo si
$\forall x\ \exists x' \ge x,\ F(m, x') = 0$, y eso pasa si y sólo si el programa **no** se detiene. Como el
complemento de la detención no es semidecidible, el conjunto tampoco.

## En Lean

```lean
theorem conway_undecidable_fixed :
    ∃ g : ℕ → ℕ, ∃ D, 0 < D ∧ (∃ a : ℕ → ℚ, ∀ n, (g n : ℚ) = a (n % D) * n) ∧
      ¬ ComputablePred (fun m => ∃ i, 1 ≤ i ∧ ∃ k, g^[i] (2 ^ m) = 2 ^ k) ∧
      ¬ ComputablePred (fun m => ∃ i, 1 ≤ i ∧ g^[i] (2 ^ m) = 1)
```

Leámoslo con cuidado, porque acá el enunciado es todo:

- `∃ g D, 0 < D ∧ (∃ a : ℕ → ℚ, ∀ n, g n = a (n % D) * n)`: hay una función que **es** de la familia
  multiplicativa, con coeficientes racionales que dependen sólo del resto.
- `¬ ComputablePred (...)`: el predicado "alguna iteración de $2^m$ es potencia de 2" no es decidible. Lo mismo para
  "alguna iteración vale 1".

`ComputablePred` es la noción de Mathlib de "decidible por un programa", definida a través de las funciones
recursivas parciales. No la inventamos nosotros, y eso es importante: un enunciado de indecidibilidad con una
noción casera de "algoritmo" podría estar vacío.

```lean
/-- Toda órbita (de enteros positivos) llega a 1. -/
def AllReachOne (p : ℕ × List (ℕ × ℕ × ℕ)) : Prop := ∀ n, 0 < n → ∃ i, (agcf p.1 p.2)^[i] n = 1

/-- **"Toda órbita llega a 1" no es r.e.** -/
theorem allReachOne_not_re : ¬ REPred AllReachOne

/-- **Teorema 1 de Kurtz–Simon.** -/
theorem allReachOne_iff_total :
    ∃ ι : Code → ℕ × List (ℕ × ℕ × ℕ), Computable ι ∧
      (∀ c, AllReachOne (ι c) ↔ ∀ y, (c.eval y).Dom) ∧
      ∀ c, ∃ a b : ℕ → ℚ, ∀ n, (agcf (ι c).1 (ι c).2 n : ℚ) =
        a (n % (ι c).1) * n + b (n % (ι c).1)
```

`agcf D t` es la función afín dada por el módulo `D` y una tabla `t`. `allReachOne_iff_total` dice: hay una
traducción **computable** `ι` de programas a funciones afines tal que el programa `c` termina con toda entrada
(`∀ y, (c.eval y).Dom`) si y sólo si toda órbita de `ι c` llega a 1. La última línea garantiza que lo que sale es
una función afín genuina, con coeficientes que dependen sólo del resto.

## Qué es nuestro y qué no

- **[Literatura]** Los teoremas son de Conway (1972) y de Kurtz y Simon (2007). Existe una formalización en Coq de
  la indecidibilidad de FRACTRAN (Larchey-Wendling y Forster, *Coq Library of Undecidability Proofs*).
- **[Lean]** La formalización es nuestra (unas 3000 líneas). En una búsqueda no encontramos una formalización previa
  de Kurtz–Simon en ningún asistente de demostración.
- La idea central de Kurtz y Simon (convertir una máquina en otra que se detiene desde *toda* configuración) es de
  ellos. El borrador de 2006 que pudimos ver no tiene la parte aritmética, y según la bibliografía anotada de
  Lagarias la versión publicada "no da pruebas detalladas". La limpieza de la basura dentro del número (pares de
  estados, registros sueltos, la regla $(n+1)/2$) y el bucle externo con $F$ recursiva primitiva los armamos
  nosotros.
- **[Literatura]** Lo que no formalizamos: la definición de la clase $\Pi_2$ y la prueba de que la totalidad es
  $\Pi_2$-completa. Mathlib no tiene la jerarquía aritmética.

## Ejercicios

1. (Papel) El programa FRACTRAN de una sola fracción $3/2$, aplicado a $2^a 3^b$, ¿qué calcula?
2. (Papel) ¿Por qué un $u$ sin primos de la máquina no cambia al aplicar las fracciones?
3. (Papel) Mostrá que $n \mapsto (n+1)/2$, aplicado a un impar $u > 1$, da un número menor que $u$.
4. (Para pensar) ¿Por qué estos teoremas no prueban que Collatz sea indecidible? ¿Qué tendría que pasar para que
   lo fuera, en algún sentido razonable? (Pista: Collatz es un único enunciado, verdadero o falso.)
