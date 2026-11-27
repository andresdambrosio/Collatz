# 2. Lean, en lo mínimo indispensable

> Código: `Collatz/Basic.lean`

## Qué es un asistente de demostración

Una demostración matemática es una cadena de pasos lógicos. Un **asistente de demostración** como
[Lean 4](https://lean-lang.org/) es un programa al que le escribís la demostración en un lenguaje formal, y él
chequea cada paso. Si Lean la acepta, no hay error de razonamiento posible, salvo un error en el propio Lean (muy
raro: en el capítulo 11 contamos uno y cómo protegerse).

**Mathlib** ([The mathlib Community, 2020](99-bibliografia.md)) es la gran biblioteca de matemática de Lean,
mantenida por miles de personas. La usamos para todo lo que no es específico de Collatz: logaritmos, límites,
computabilidad, etc.

## Definiciones

Así empieza `Collatz/Basic.lean`:

```lean
def T (n : Nat) : Nat := if n % 2 = 0 then n / 2 else 3 * n + 1
```

Se lee: "`T` es una función que toma un natural `n` y devuelve un natural: si el resto de `n` al dividir por 2 es
0, devuelve `n / 2`; si no, `3 * n + 1`". `Nat` son los naturales $\{0, 1, 2, \dots\}$, `%` es el resto y `/` es
la división entera.

```lean
def iter : Nat → Nat → Nat
  | 0,     n => n
  | k + 1, n => iter k (T n)
```

`iter k n` es $T^k(n)$, definido por recursión: aplicar `T` cero veces no hace nada, y aplicarlo $k+1$ veces es
aplicarlo una vez y después $k$ veces más. El tipo `Nat → Nat → Nat` dice "toma dos naturales y devuelve uno".

```lean
/-- La conjetura (NO demostrada): todo n ≥ 1 llega a 1. -/
def Collatz : Prop := ∀ n, n ≥ 1 → ∃ k, iter k n = 1
```

`Collatz` no es un número sino un **enunciado** (`Prop`): "para todo `n`, si `n ≥ 1`, existe `k` tal que
`iter k n = 1`". Que podamos *escribir* este enunciado no quiere decir que lo hayamos demostrado. Definirlo es
gratis. Demostrarlo es el problema.

Esta es la primera de las comparaciones "papel contra Lean" que hacemos en cada capítulo. ¿Dice `Collatz` lo
mismo que la conjetura? Sí: pide $n \ge 1$, porque el 0 es un punto fijo ($T(0) = 0$) y nunca llega a 1, y pide
que *algún* iterado sea 1, que es lo que dice la conjetura.

## Calcular

Lean también es un lenguaje de programación:

```lean
#eval T 27                                     -- 82
#eval iter 111 27                              -- 1
#eval (List.range 12).map (fun k => iter k 7)
-- [7, 22, 11, 34, 17, 52, 26, 13, 40, 20, 10, 5]
```

## Teoremas y demostraciones

Un teorema es una afirmación con su demostración:

```lean
theorem even_descends (n : Nat) (h : n % 2 = 0) (hn : n ≥ 2) : iter 1 n < n := by
  simp [iter, T, h]; omega
```

- Lo que va entre paréntesis son las **hipótesis**: `n` es un natural, `h` dice que es par y `hn` que es al menos 2.
- Lo que va después de los dos puntos es la **conclusión**: `iter 1 n < n`.
- Después de `:= by` viene la demostración, escrita con **tácticas**: instrucciones que transforman lo que falta
  probar. `simp [iter, T, h]` desarma las definiciones y usa `h` para elegir la rama `n / 2`. Lo que queda es
  `n / 2 < n` sabiendo `n ≥ 2`, y `omega` lo cierra: es un procedimiento que decide cualquier desigualdad lineal
  entre enteros.

Se puede ver el estado en cada paso con el editor (VS Code con la extensión de Lean): uno pone el cursor después
de cada táctica y ve qué queda por probar. Es la mejor manera de leer el código de este libro.

Algunas tácticas que vas a ver seguido:

| Táctica | Qué hace |
|---|---|
| `intro x` | "sea `x`": para probar `∀ x, P x`, toma un `x` cualquiera |
| `exact e` | cierra el objetivo con el término `e` |
| `obtain ⟨k, hk⟩ := h` | de `h : ∃ k, P k`, saca un testigo `k` y el hecho `hk : P k` |
| `induction n with ...` | inducción |
| `simp`, `omega`, `ring` | automatización: simplificar, aritmética lineal, álgebra de anillos |
| `decide` | decide un enunciado finito calculando |

## `sorry`, axiomas y el kernel

Tres cosas para saber en qué confiar.

1. **`sorry`** es la forma de decir "esto lo dejo sin demostrar". Lean acepta el archivo pero marca la deuda. El
   teorema principal del proyecto, `collatz_conjecture`, depende de dos `sorry`: los dos frentes abiertos
   (capítulo 4).

2. **Los axiomas.** Toda demostración en Lean descansa en unos pocos axiomas: `propext`, `Classical.choice` y
   `Quot.sound`. El comando `#print axioms` lista los que usa un teorema:

   ```lean
   #print axioms collatz_of_descent
   -- 'collatz_of_descent' depends on axioms: [propext, Quot.sound]
   ```

   Si aparece `sorryAx`, hay un `sorry` escondido en alguna parte. Regla del proyecto: **nada se declara
   demostrado si no compila y su lista de axiomas es la estándar**.

3. **El kernel.** El corazón de Lean es un núcleo chico, el *kernel*, que hace el chequeo final. Las tácticas y
   la automatización producen un término de prueba que el kernel revisa. Si una táctica tiene un bug, el kernel
   rechaza su resultado.

## Calcular dentro de la prueba: `decide` y `native_decide`

Muchas pruebas de este libro incluyen cálculos enormes: "todo número menor que 600 001 llega a 1", "estas
matrices cumplen estas 11 desigualdades". Hay dos formas de hacerlos.

- **`decide`** (y su variante `decide +kernel`) hace que el **kernel** evalúe el cálculo. Es lento pero tiene la
  misma garantía que una prueba a mano.
- **`native_decide`** compila el cálculo a código de máquina y le cree al resultado. Es rapidísimo, pero agrega un
  axioma: la confianza en el compilador.

```lean
#print axioms collatz_upto_1000
-- [propext, Quot.sound, collatz_upto_1000._native.native_decide.ax_1_1]
```

`collatz_upto_1000` es el único resultado del proyecto que usa `native_decide`, y lo usa a propósito, para mostrar
la diferencia. Todos los cálculos importantes (las cotas de ciclos, los certificados) están hechos con
`decide +kernel`.

## Ejercicios

1. (Lean) Usá `#eval` para calcular cuántos pasos tarda 97 en llegar a 1. (Pista: probá `iter k 97` para varios
   `k`, o escribí una función recursiva con combustible.)
2. (Lean) Probá `example : T 6 = 3 := rfl`. ¿Por qué alcanza con `rfl` ("las dos cosas son iguales por cálculo")?
3. (Lean) Probá que si `n` es impar, `T n = 3 * n + 1`. (Pista: imitá `even_descends`.)
4. (Papel) ¿Por qué `Collatz` pide `n ≥ 1`? ¿Qué pasaría si lo sacáramos?
