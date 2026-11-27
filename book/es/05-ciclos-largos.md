# 5. Los ciclos tienen que ser larguísimos

> Código: `Collatz/CycleBound.lean`, `Collatz/CycleBound/` (generado por `scripts/gen_cycle_blocks.py`),
> `Collatz/Bridge.lean`, `Collatz/Forge/Invariants/`

## La idea

¿Puede haber un ciclo distinto de $1 \to 4 \to 2 \to 1$? Nadie lo sabe. Pero se puede probar que, si existe, es
**enorme**: tiene que dar muchísimas vueltas antes de cerrarse. La razón es una cuenta de una línea y un poco de
teoría de números: un ciclo es una aproximación racional *demasiado buena* de $\log_2 3$.

## La matemática

### La ecuación de un ciclo

Usemos el mapa de Syracuse: un impar $n$ va a $(3n+1)/2^{a}$, con $a \ge 1$ la cantidad de veces que hay que
dividir por 2 para volver a un impar. Supongamos un ciclo que visita los impares $n_1, \dots, n_k$ (con
$n_{k+1} = n_1$), dividiendo por 2 un total de $A = a_1 + \cdots + a_k$ veces:

$$n_{i+1} = \frac{3 n_i + 1}{2^{a_i}}, \qquad\text{o sea}\qquad 2^{a_i} n_{i+1} = 3 n_i + 1.$$

Multiplicando las $k$ igualdades, el producto de los $n_{i+1}$ a la izquierda es el mismo que el de los $n_i$
(es el mismo ciclo, corrido), y se cancela:

$$2^A = \prod_{i=1}^{k} \frac{3 n_i + 1}{n_i} = \prod_{i=1}^{k} \left(3 + \frac{1}{n_i}\right).$$

Cada factor es mayor que 3. Si además todos los números del ciclo son al menos $M$, cada factor es a lo sumo
$3 + 1/M$. Entonces

$$3^k < 2^A \le \left(3 + \frac{1}{M}\right)^k,$$

y tomando logaritmos en base 2 y dividiendo por $k$:

$$0 \;<\; \frac{A}{k} - \log_2 3 \;\le\; \log_2\!\left(1 + \frac{1}{3M}\right) \approx \frac{1}{3M \ln 2}.$$

En palabras: $A/k$ es una aproximación de $\log_2 3 = 1{,}58496\ldots$ por arriba, con error menor que algo del
orden de $1/M$. Cuanto más grande es $M$, mejor tiene que ser la aproximación.

### Fracciones continuas

Las mejores aproximaciones racionales de un número las da su **fracción continua**. Para $\log_2 3$, los
convergentes son

$$\frac11,\ \frac21,\ \frac32,\ \frac85,\ \frac{19}{12},\ \frac{65}{41},\ \frac{84}{53},\ \frac{485}{306},\
\frac{1054}{665},\ \frac{24727}{15601},\ \frac{50508}{31867},\ \dots$$

Un teorema clásico dice que una fracción $A/k$ que aproxima mejor que todos los convergentes con denominador
menor tiene que tener denominador grande. Concretamente: si todo número del ciclo es al menos
$M = 81\,788\,928$, la desigualdad de arriba **no tiene solución con $k < 15\,601$**. La primera solución es
justamente el convergente $24727/15601$.

**[Experimento]** Es fácil comprobarlo por computadora: para cada $k$, el único candidato es
$A = \lceil k \log_2 3 \rceil$, y basta ver que $A/k - \log_2 3$ es demasiado grande para todo $k < 15\,601$.
**[Lean]** En el proyecto no lo comprobamos así: está demostrado en el kernel, con aritmética exacta de enteros
(sin logaritmos), en la forma $3^k < 2^A$ y $2^A M^k \le (3M+1)^k$.

### ¿De dónde sale $M$?

La forma clásica de obtener $M$: verificar por computadora que todo número menor que $M$ llega a 1. Así, ningún
número del ciclo puede ser menor que $M$, porque llegaría a 1 y no estaría en un ciclo no trivial.

Pero "llegar a 1" es más de lo necesario. Mirá el **menor** número de un ciclo: por definición, su órbita nunca
baja de él. Entonces alcanza con verificar que todo impar $1 < n < M$ en algún momento **baja de sí mismo**. Es la
misma idea del capítulo 3, ahora usada para ciclos.

**Lema.** Si todo impar $1 < n < M$ tiene un iterado de Syracuse menor que $n$, todo elemento de un ciclo no
trivial es al menos $M$.

*Demostración.* Sea $m$ el mínimo del ciclo. Si $m < M$, tiene un iterado menor que él, que también está en el
ciclo. Contradicción con que es el mínimo. Así que $m \ge M$, y todos los demás también. $\blacksquare$

Y bajar es mucho más barato de verificar que llegar a 1, gracias al truco de Terras (capítulo 3): para la mayoría
de las clases módulo $2^{20}$, los primeros pasos son iguales para todos los números de la clase y se puede probar
**simbólicamente**, para toda la clase a la vez, que bajan.

| Paso | Cantidad |
|---|---|
| Clases impares módulo $2^{20}$ | 524 288 |
| Clases que bajan simbólicamente | 496 959 (94,8 %) |
| Números restantes menores que $M = 78 \cdot 2^{20} = 81\,788\,928$, chequeados uno por uno | 2 131 661 |
| Espera más larga antes de bajar | 376 pasos |

## En Lean

La hipótesis "todo impar chico baja":

```lean
/-- Todo impar `1 < n < M` tiene un iterado de Syracuse menor que él. -/
def DescendsBelow (M : ℕ) : Prop :=
  ∀ n, n % 2 = 1 → 1 < n → n < M → ∃ i, syracuse^[i] n < n
```

El lema del mínimo:

```lean
/-- Bajo `DescendsBelow M`, un elemento de un ciclo no trivial de Syracuse es `≥ M`. -/
theorem syracuse_cycle_ge_of_descends {M n k : ℕ} (hD : DescendsBelow M) (hn : n % 2 = 1)
    (hk : 0 < k) (h : syracuse^[k] n = n) (hne : n ≠ 1) : M ≤ n
```

La prueba toma el mínimo del conjunto finito $\{T^i(n) : i < k\}$ con `Finset.min'` y sigue el argumento de papel.

La ecuación del ciclo en forma entera ("sándwich"):

```lean
theorem cycle_sandwich_of_descends {M n k : ℕ} (hD : DescendsBelow M) (hn : n % 2 = 1)
    (hk : 0 < k) (h : syracuse^[k] n = n) (hne : n ≠ 1) :
    3 ^ k < 2 ^ sExpSum n k ∧ 2 ^ sExpSum n k * M ^ k ≤ (3 * M + 1) ^ k
```

`sExpSum n k` es $A$, la cantidad total de divisiones por 2 en $k$ pasos.

### El descenso simbólico de Terras

```lean
def symDesc (K₀ r : ℕ) : ℕ → ℕ → ℕ → Bool
  ...
  | K, c, fuel + 1 =>
    if K < K₀ ∧ c < r then true
    else if K % 2 = 1 then false
    else if c % 2 = 0 then symDesc K₀ r (K / 2) (c / 2) fuel
    else symDesc K₀ r (3 * K / 2) ((3 * c + 1) / 2) fuel

theorem symDesc_sound {K₀ r : ℕ} : ∀ {K c fuel : ℕ}, symDesc K₀ r K c fuel = true →
    ∀ q, ∃ s, T^[s] (K * q + c) < K₀ * q + r
```

La idea: representamos *todos* los números $n = K q + c$ de la clase a la vez, con $q$ libre. Mientras $K$ sea par,
la paridad de $Kq + c$ es la de $c$ y no depende de $q$, así que podemos dar un paso para toda la clase:
`T_lin_even` y `T_lin_odd` prueban que el resultado vuelve a tener la forma $K' q + c'$. Si en algún momento
$K' < K_0$ y $c' < r$, entonces $K' q + c' < K_0 q + r$ para todo $q$: **toda la clase bajó**. `symDesc_sound` es
el teorema de corrección del programa, el mismo patrón del capítulo 3.

### El teorema

```lean
/-- **Todo ciclo no trivial de `T` tiene período al menos 15601.** Incondicional. -/
theorem cycle_period_ge_15601 {n p : ℕ} (hn : n ≥ 1) (hp : p ≥ 1) (h : iter p n = n)
    (hnt : ¬ InTrivialCycle n) : 15601 ≤ p
```

Está enunciado con las definiciones de la raíz (el `iter` y el `InTrivialCycle` de los capítulos 3 y 4), así que se
puede leer sin saber nada de Syracuse. El puente `cycle_period_ge_of` (en `Bridge.lean`) traduce la cota para
Syracuse (pasos impares) a una cota para el período de $T$, que es todavía mayor.

### Una lección sobre la memoria

La primera versión de este cálculo colgó la computadora varias veces. El kernel guarda todos los resultados
intermedios hasta terminar cada teorema, y le habíamos pedido verificar bloques grandes en 16 archivos **en
paralelo**: unos 3,4 GB por bloque, por 16, en una máquina de 16 GB. La versión final usa 2048 teoremas chicos
(0,65 GB cada uno), encadenados para que se compilen a lo sumo dos a la vez. Tarda unos 30 minutos, una sola vez.
La moraleja vale para cualquier verificación grande: medir primero y lanzar con un "guardián" que frene si se acaba
la memoria.

## Qué es nuestro y qué no

- **[Literatura]** El método (descenso + fracciones continuas) es de **Eliahou (1993)**, que con verificación hasta
  $2^{40}$ obtuvo $k \ge 17\,087\,915$. Nuestro script reproduce ese número exacto. El número 15 601 **no es
  nuevo** como cota: es mucho más débil que las conocidas.
- Lo nuestro es la **verificación formal completa en el kernel**, sin hipótesis ni programas externos.
  CollatzForge ya tenía 2301 (con verificación hasta 600 001). El descenso en lugar de la convergencia lo subió a
  15 601.
- La cota crece más o menos como $\sqrt{M}$ (con saltos, según los convergentes). Ninguna cantidad de cómputo convierte "muy largo" en "imposible". Para eso
  hace falta una idea.

## Ejercicios

1. (Papel) Supongamos un ciclo con un solo impar $n$ ($k = 1$). Mostrá que $2^A = 3 + 1/n$ obliga a $n = 1$. (Es
   el ciclo trivial.)
2. (Papel) Con $k = 2$: mostrá que $2^A = (3 + 1/n_1)(3 + 1/n_2)$ obliga a $A = 4$ y llegá a una contradicción
   para $n_1, n_2 > 1$.
3. (Papel) ¿Por qué el ciclo de $-5$ (capítulo 1) no contradice la ecuación? Calculá $\prod (3 + 1/n_i)$ para
   $n_i \in \{-5, -7\}$.
4. (Computadora) Calculá los convergentes de $\log_2 3$ y verificá que, con $M = 81\,788\,928$, el primer $k$ que
   admite un $A$ es 15 601.
5. (Computadora) ¿Qué $M$ haría falta para obligar a $k \ge 31\,867$?
