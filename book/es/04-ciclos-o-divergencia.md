# 4. Dos maneras de fallar: ciclos o divergencia

> Código: `Collatz/Reductions.lean`, `Collatz/Main.lean`, `Collatz/Bridge.lean`

## La idea

Supongamos que la conjetura fuera falsa: hay un $n$ que nunca llega a 1. Su órbita es una sucesión infinita de
enteros positivos, y hay sólo dos posibilidades:

1. **La órbita se repite**: algún número vuelve a aparecer y, desde ahí, todo se repite. Es un **ciclo** distinto
   de $1 \to 4 \to 2 \to 1$.
2. **La órbita nunca repite un número.** Entonces tiene infinitos números distintos y, como hay finitos enteros
   por debajo de cualquier cota, **crece sin límite** (diverge).

Esto parte el problema en dos frentes, **ciclos** y **divergencia**, que se atacan con herramientas muy distintas.
Los ciclos son un problema de aritmética (capítulo 5). La divergencia es un problema de dinámica, y es el más
misterioso.

## La matemática

**Definiciones.**
- $n$ está en el **ciclo trivial** si $n \in \{1, 2, 4\}$.
- **Sin ciclos no triviales:** si $n \ge 1$, $p \ge 1$ y $T^p(n) = n$, entonces $n$ está en el ciclo trivial.
- **Sin divergencia:** para todo $n \ge 1$ existe $B$ con $T^k(n) \le B$ para todo $k$.

**Teorema.** Collatz $\iff$ (sin ciclos no triviales) $\wedge$ (sin divergencia).

*Demostración.*

($\Leftarrow$) Sea $n \ge 1$. Por "sin divergencia", la órbita vive en $\{0, 1, \dots, B\}$, que tiene $B+1$
elementos. Entre los $B+2$ valores $T^0(n), \dots, T^{B+1}(n)$ hay dos iguales (**palomar**): $T^x(n) = T^y(n)$
con $x < y$. Entonces $m = T^x(n)$ cumple $T^{y-x}(m) = m$: es periódico. Como $m \ge 1$ (los iterados de un
positivo son positivos), "sin ciclos" dice que $m \in \{1, 2, 4\}$, y de ahí llega a 1 en a lo sumo dos pasos.

($\Rightarrow$, ciclos) Si $T^p(n) = n$ y $n$ llega a 1 en $k$ pasos, entonces $n = T^{pk}(n) = T^{pk - k}(1)$,
que está en $\{1, 2, 4\}$ porque el ciclo trivial es cerrado bajo $T$.

($\Rightarrow$, divergencia) Si $n$ llega a 1 en $k$ pasos, la órbita está acotada por
$\max(T^0(n), \dots, T^{k-1}(n), 4)$. $\blacksquare$

## En Lean

```lean
def InTrivialCycle (m : Nat) : Prop := m = 1 ∨ m = 2 ∨ m = 4

/-- Todo punto periódico (n ≥ 1) está en el ciclo trivial. -/
def NoNontrivialCycles : Prop :=
  ∀ n p, n ≥ 1 → p ≥ 1 → iter p n = n → InTrivialCycle n

/-- Toda órbita que empieza en n ≥ 1 está acotada. -/
def NoDivergentOrbits : Prop :=
  ∀ n, n ≥ 1 → ∃ B, ∀ k, iter k n ≤ B
```

Comparemos con el papel. `NoNontrivialCycles` habla de *puntos periódicos* y no de "ciclos". Es lo mismo: un
ciclo es el conjunto de iterados de un punto periódico, y si un punto de un ciclo no trivial estuviera en
$\{1, 2, 4\}$, todo el ciclo sería el trivial. Ojo con `p ≥ 1`: sin esa condición, todo `n` sería "periódico de
período 0".

El palomar es un lema de Mathlib:

```lean
theorem exists_periodic_of_bounded {n B : Nat} (hB : ∀ k, iter k n ≤ B) :
    ∃ i p, p ≥ 1 ∧ iter p (iter i n) = iter i n := by
  obtain ⟨x, -, y, -, hxy, hf⟩ := Finset.exists_ne_map_eq_of_card_lt_of_maps_to
    (s := Finset.range (B + 2)) (t := Finset.range (B + 1)) (f := fun k => iter k n)
    ...
```

`Finset.exists_ne_map_eq_of_card_lt_of_maps_to` dice: si una función va de un conjunto finito `s` a otro `t` más
chico, hay dos elementos distintos con la misma imagen. Acá `s` son los tiempos $0, \dots, B+1$ y `t` los valores
$0, \dots, B$.

El teorema principal:

```lean
theorem collatz_iff : Collatz ↔ NoNontrivialCycles ∧ NoDivergentOrbits :=
  ⟨fun h => ⟨noCycles_of_collatz h, noDivergence_of_collatz h⟩,
   fun ⟨hc, hd⟩ => collatz_of_noCycles_noDivergence hc hd⟩
```

Un "si y sólo si" (`↔`) se prueba con un par de funciones: una que convierte pruebas de la izquierda en pruebas
de la derecha y otra al revés.

### Lo que falta, escrito

`Collatz/Main.lean` tiene los dos frentes abiertos, marcados con `sorry`, y arma la conjetura con ellos:

```lean
/-- Frente 1 (abierto): no hay ciclos distintos de 1 → 4 → 2 → 1. -/
theorem no_nontrivial_cycles : NoNontrivialCycles := by
  sorry

/-- Frente 2 (abierto): ninguna órbita se va a infinito. -/
theorem no_divergent_orbits : NoDivergentOrbits := by
  sorry

theorem collatz_conjecture : Collatz :=
  collatz_iff.mpr ⟨no_nontrivial_cycles, no_divergent_orbits⟩
```

Si alguna vez alguien reemplaza esos dos `sorry` por pruebas, `collatz_conjecture` queda demostrado sin cambiar
nada más. `#print axioms collatz_conjecture` hoy muestra `sorryAx`: así tiene que ser.

### Dos bibliotecas, un puente

El proyecto heredó una biblioteca anterior, **CollatzForge** (`Collatz/Forge/`, unas 3500 líneas sin `sorry`), que
usa sus propias definiciones: `Collatz.collatz` (el mapa clásico, escrito con la iteración de Mathlib
`f^[k]`), `Collatz.T` (el **acelerado**) y `Collatz.syracuse`. `Collatz/Bridge.lean` prueba que las dos
convenciones dicen lo mismo:

```lean
theorem T_eq_collatz : T = Collatz.collatz := rfl

theorem iter_eq_iterate (k n : ℕ) : iter k n = Collatz.collatz^[k] n := ...

theorem collatz_iff_forge : Collatz ↔ Collatz.CollatzConjecture := ...
theorem noNontrivialCycles_iff_forge : NoNontrivialCycles ↔ Collatz.NoNontrivialCycles := ...
theorem noDivergentOrbits_iff_forge : NoDivergentOrbits ↔ Collatz.NoDivergence := ...
```

Que `T_eq_collatz` se pruebe con `rfl` quiere decir que las dos definiciones son *literalmente* la misma función.
Los puentes son aburridos pero importantes: sin ellos, un teorema sobre `Collatz.T` podría estar hablando de otra
cosa.

## Lo que se sabe de cada frente

- **Ciclos.** **[Lean]** Todo ciclo no trivial tiene al menos 15 601 pasos impares (capítulo 5). **[Literatura]**
  Con la verificación hasta $2^{71}$, al menos 72 057 431 991 pasos ([Hercher, 2023](99-bibliografia.md); en Lean lo
  tenemos con esa verificación como hipótesis explícita, `hercher_lower_bound`). Hercher prueba además que no hay
  ciclos con hasta 91 "picos", de cualquier largo.
- **Divergencia.** **[Lean, Forge]** Una órbita divergente tendría que ser muy atípica: a la larga, a lo sumo
  $\log_2 3 \approx 1{,}585$ divisiones por 2 por cada paso impar, cuando lo típico es 2. **[Abierto]** Todo lo
  demás.

## Qué es nuestro y qué no

La dicotomía es folklore. Lo nuestro es la formalización y los puentes entre convenciones.

## Ejercicios

1. (Papel) En la prueba de ($\Leftarrow$), ¿dónde se usa que los iterados de un positivo son positivos? ¿Qué
   pasaría con el 0?
2. (Papel) Mostrá que en $5n+1$ "sin divergencia" es *heurísticamente* falso: ¿cuál es el factor promedio por paso?
3. (Lean) Probá `InTrivialCycle 4 → InTrivialCycle (T 4)`. (Pista: `decide` después de desplegar.)
4. (Papel) ¿Por qué `NoNontrivialCycles` necesita la hipótesis `n ≥ 1`? (Pista: calculá `T 0`.)
