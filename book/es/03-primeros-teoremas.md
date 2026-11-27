# 3. Definiciones y primeros teoremas

> Código: `Collatz/Basic.lean`

## La idea

Antes de atacar la conjetura conviene probar lo que *sí* se puede: que algunas familias de números llegan a 1, y
que el problema se puede reducir a algo que parece más débil. Este capítulo recorre `Collatz/Basic.lean`, que
tiene 69 líneas y no usa Mathlib: es un buen lugar para aprender a leer Lean.

## La matemática

### Iterar es componer

**Lema.** $T^{a+b}(n) = T^b(T^a(n))$.

*Demostración.* Por inducción en $a$. Si $a = 0$, los dos lados son $T^b(n)$. Si vale para $a$ (y todo $n$),
entonces $T^{(a+1)+b}(n) = T^{a+b}(T(n)) = T^b(T^a(T(n))) = T^b(T^{a+1}(n))$. $\blacksquare$

### Las potencias de 2

**Proposición.** $T^m(2^m) = 1$.

*Demostración.* $2^{m+1}$ es par, así que $T(2^{m+1}) = 2^m$, y por inducción. $\blacksquare$

### Bajar en vez de llegar a 1

Esta es la idea más importante del capítulo, y reaparece en todo el libro.

**Teorema (reducción por descenso).** Si todo $n > 1$ tiene algún iterado $T^k(n)$ con $1 \le T^k(n) < n$,
entonces vale la conjetura.

*Demostración.* Por **inducción fuerte**: supongamos que todos los $m$ con $1 \le m < n$ llegan a 1, y probemos que
$n$ llega. Si $n = 1$, ya está. Si no, por hipótesis hay un $k$ con $m = T^k(n)$, $1 \le m < n$. Por la hipótesis
inductiva $m$ llega a 1: $T^j(m) = 1$. Entonces $T^{k+j}(n) = T^j(T^k(n)) = 1$. $\blacksquare$

Otra forma de verlo, por el absurdo: si hubiera contraejemplos, tomá **el más chico**. Ese número baja a uno
menor, que no es contraejemplo y llega a 1. Entonces el nuestro también llega. Contradicción.

### Los fáciles

- **Los pares bajan en un paso:** $n \mapsto n/2 < n$.
- **Los $4k+1$ (con $k \ge 1$) bajan en tres pasos:** $4k+1 \to 12k+4 \to 6k+2 \to 3k+1$, y $3k+1 < 4k+1$.

Ya cubrimos la mitad de los números (los pares) y un cuarto más (los $4k+1$). Faltan los $4k+3$.

### El problema de los $4k+3$

Con la versión acelerada, mirá cuánto tardan algunos $4k+3$ en bajar de sí mismos:

| $n$ | recorrido hasta bajar de $n$ | pasos |
|---|---|---|
| 3 | 3 → 5 → 8 → 4 → **2** | 4 |
| 7 | 7 → 11 → 17 → 26 → 13 → 20 → 10 → **5** | 7 |
| 11 | 11 → 17 → 26 → 13 → 20 → **10** | 5 |
| 19 | 19 → 29 → 44 → 22 → **11** | 4 |
| 27 | 27 → 41 → 62 → … (sube hasta 4616) … → **23** | 59 |

Uno puede seguir partiendo en casos según el resto módulo 8, 16, 32… La observación clave es de
**Terras (1976)**: si $n \equiv r \pmod{2^k}$, los primeros $k$ pasos de la versión acelerada (si son pares o
impares) dependen *sólo de $r$*. Así que, para muchas clases $r$, se puede probar de una vez **para todos los
números de la clase** que bajan en a lo sumo $k$ pasos. Por ejemplo, para $n = 4q + 1$, el cálculo de arriba vale
para todo $q$.

**[Experimento]** Proporción de clases módulo $2^k$ que bajan así, simbólicamente:

| $k$ | 2 | 3 | 4 | 5 | 8 | 10 | 16 | 20 |
|---|---|---|---|---|---|---|---|---|
| clases que bajan | 50 % | 62,5 % | 75 % | 84,4 % | 92,2 % | 93,7 % | 96,8 % | 97,4 % |

**[Literatura]** Terras probó que esa proporción tiende a 100 %. Pero siempre queda alguna clase rebelde, y la
peor es la de los números $2^k - 1$, que en binario son `111…1`. Con la versión acelerada:

$$2^k - 1 \;\to\; 3 \cdot 2^{k-1} - 1 \;\to\; 3^2 \cdot 2^{k-2} - 1 \;\to\; \cdots \;\to\; 3^k - 1,$$

**subiendo** durante $k$ pasos seguidos. Por ejemplo, $31 = 2^5 - 1$: $31 \to 47 \to 71 \to 107 \to 161 \to 242$.
Por más fino que mires el resto módulo $2^k$, la clase de $-1$ sube durante $k$ pasos. ¿Por qué "$-1$"? Porque
$2^k - 1 \equiv -1 \pmod{2^k}$, y $-1$ es un punto fijo del mapa acelerado: $(3 \cdot (-1) + 1)/2 = -1$. Los números
$2^k m - 1$ son **sombras** del ciclo negativo $\{-1\}$: durante $k$ pasos no se pueden distinguir de él mirando
las últimas cifras. Este fenómeno, las sombras de los ciclos negativos, es el villano de todo el libro.

**Moraleja.** Lo que se puede hacer con "casos según las últimas cifras" cubre casi todo, pero nunca todo. Es la
primera aparición de la brecha **"casi todos" contra "todos"**.

### Verificar por computadora

Para un número concreto, "llega a 1" se puede chequear calculando. Lo que no se puede es chequear infinitos.
Pero sí finitos: podemos verificar formalmente que todo $n \le 1000$ llega a 1.

## En Lean

### Iterar es componer

```lean
theorem iter_add (a b n : Nat) : iter (a + b) n = iter b (iter a n) := by
  induction a generalizing n with
  | zero => simp [iter]
  | succ a ih => rw [Nat.succ_add]; simp [iter, ih]
```

`induction a generalizing n` hace inducción en `a` *para todo `n`*: la hipótesis inductiva `ih` vale para
cualquier `n`, que es lo que hace falta porque en el paso inductivo aparece `T n` en lugar de `n`. Es exactamente
el "y todo $n$" de la prueba en papel.

### Los $4k+1$

```lean
/-- Los n ≡ 1 (mod 4), n > 1, descienden en tres pasos: 4k+1 → 12k+4 → 6k+2 → 3k+1. -/
theorem one_mod_four_descends (n : Nat) (h : n % 4 = 1) (hn : n > 1) : iter 3 n < n := by
  have h2 : n % 2 = 1 := by omega
  have e1 : (3*n+1) % 2 = 0 := by omega
  have e2 : ((3*n+1)/2) % 2 = 0 := by omega
  simp [iter, T, h2, e1, e2]; omega
```

Los tres `have` son los tres hechos de paridad que deciden qué rama de `T` se toma en cada paso: $n$ es impar,
$3n+1$ es par y $(3n+1)/2$ es par. Con eso, `simp` calcula los tres pasos y `omega` cierra
$(3n+1)/4 < n$.

### La reducción por descenso

```lean
theorem collatz_of_descent
    (H : ∀ n, n > 1 → ∃ k, iter k n < n ∧ iter k n ≥ 1) : Collatz := by
  intro n hn
  induction n using Nat.strongRecOn with
  | _ n ih =>
    by_cases h1 : n = 1
    · exact ⟨0, h1⟩
    · obtain ⟨k, hk, hk1⟩ := H n (by omega)
      obtain ⟨j, hj⟩ := ih _ hk hk1
      exact ⟨k + j, by rw [iter_add]; exact hj⟩
```

Es la prueba en papel, línea por línea:

- `Nat.strongRecOn` es la inducción fuerte: `ih` dice que todo `m < n` (con `m ≥ 1`) llega a 1.
- `by_cases h1 : n = 1` separa el caso base.
- `obtain ⟨k, hk, hk1⟩ := H n _` saca de la hipótesis el `k` con `iter k n < n` y `iter k n ≥ 1`.
- `obtain ⟨j, hj⟩ := ih _ hk hk1` aplica la hipótesis inductiva a `m = iter k n`.
- `⟨k + j, _⟩` es el testigo final, e `iter_add` hace la cuenta $T^{k+j}(n) = T^j(T^k(n))$.

### Verificación hasta 1000

```lean
def reachesWithin : Nat → Nat → Bool
  | 0,     n => n == 1
  | f + 1, n => n == 1 || reachesWithin f (T n)

theorem reachesWithin_sound (f n : Nat) (h : reachesWithin f n = true) : ∃ k, iter k n = 1 := ...

theorem collatz_upto_1000 : ∀ n, 1 ≤ n → n ≤ 1000 → ∃ k, iter k n = 1 := by
  have hall : (List.range 1000).all (fun i => reachesWithin 200 (i+1)) = true := by native_decide
  ...
```

El patrón es típico y vale la pena aprenderlo: (1) un **programa** que devuelve `true` o `false`
(`reachesWithin f n`: "¿llega a 1 en a lo sumo `f` pasos?"), (2) un teorema de **corrección** que dice que si el
programa dice `true`, el enunciado matemático vale, y (3) **correr** el programa dentro de la prueba. Así se
verifican los cálculos grandes del libro. En `Collatz/Forge/` el mismo patrón, con `decide +kernel`, verifica que
todo número menor que 600 001 llega a 1.

## Qué es nuestro y qué no

Todo esto es clásico. La reducción por descenso es folklore, y la observación de las clases es de Terras (1976).
Lo nuestro es sólo la escritura en Lean.

## Ejercicios

1. (Papel) Mostrá que los $n \equiv 3 \pmod{16}$ bajan en 4 pasos de la versión acelerada, para todo $n$ de la
   clase. (Escribí $n = 16q + 3$ y seguí los pasos.)
2. (Papel) Mostrá que la clase de $7 \bmod 8$ no baja en 3 pasos de la versión acelerada: después de 3 pasos,
   $n = 8q + 7$ va a $27q + 26$.
3. (Lean) Probá que los $n \equiv 2 \pmod 4$ bajan en un paso.
4. (Lean) Imitando `one_mod_four_descends`, probá que si $n \equiv 3 \pmod{16}$, entonces `iter 6 n < n`. (Contá bien: cada paso impar de la acelerada son dos pasos de la clásica.)
5. (Computadora) Reproducí la tabla de proporciones de Terras. ¿Cuántas clases módulo $2^{10}$ no bajan en 10 pasos?
6. (Para pensar) ¿Por qué la reducción por descenso no resuelve el problema? ¿Qué parte de la hipótesis es la
   difícil?
