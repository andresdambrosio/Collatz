import Mathlib

/-!
# Vistos desde abajo, todos los "Collatz con acarreos" son biyecciones

Escribimos un entero 2-ádico como su sucesión de cifras binarias `a : ℕ → Bool` (`a i` = cifra de `2^i`).
El paso impar de Collatz calcula `n + 2n + 1` con un sumador que recorre las columnas de abajo hacia arriba
llevando un estado de acarreo. En la columna `i` suma la cifra `a i` de `n`, la cifra `a (i-1)` de `2n`
y el acarreo, y la cifra de salida es el XOR de las tres.

* Collatz de verdad: el estado es "me llevo 1 o no".
* `C_k` (ver `scripts/carry_trunc.py` e `Ideas/acarreos.md`): además lleva la "edad" del acarreo, y lo
  apaga cuando recorrió más de `k` columnas.
* `C_0` = el mapa polinomial de 𝔽₂[x] (Hicks–Mullen–Yucas–Zavislak 2008): los acarreos mueren al nacer.

**Teorema (`out_injective_below`):** para *cualquier* regla de acarreo, si dos sucesiones de cifras dan la
misma salida en las columnas `< m`, coinciden en las columnas `< m`. O sea, el paso es inyectivo, y por lo
tanto biyectivo, sobre las terminaciones de `m` cifras, para todo `m`. La razón: la cifra de salida `i` es
la cifra de entrada `i`, XOR algo que depende sólo de las columnas de abajo.
-/

namespace Collatz.Carries

/-- La cifra de `2n` en la columna `i`: la de `n` en `i - 1` (y `0` en la columna `0`). -/
def shifted (a : ℕ → Bool) : ℕ → Bool
  | 0 => false
  | i + 1 => a i

variable {σ : Type*}

/-- Estado del acarreo al entrar a la columna `i`, para una regla `step` y un estado inicial `init`
(el `+1` de `3n + 1` entra como acarreo inicial). -/
def carry (step : Bool → Bool → σ → σ) (init : σ) (a : ℕ → Bool) : ℕ → σ
  | 0 => init
  | i + 1 => step (a i) (shifted a i) (carry step init a i)

/-- Cifra de salida de `n + 2n + 1` en la columna `i`: XOR de las dos cifras y el bit de acarreo. -/
def out (step : Bool → Bool → σ → σ) (init : σ) (bit : σ → Bool) (a : ℕ → Bool) (i : ℕ) : Bool :=
  xor (xor (a i) (shifted a i)) (bit (carry step init a i))

theorem shifted_congr {a b : ℕ → Bool} {i : ℕ} (h : ∀ j < i, a j = b j) : shifted a i = shifted b i := by
  cases i with
  | zero => rfl
  | succ i => exact h i (Nat.lt_succ_self i)

/-- El acarreo en la columna `i` depende sólo de las columnas de abajo. -/
theorem carry_congr (step : Bool → Bool → σ → σ) (init : σ) {a b : ℕ → Bool} :
    ∀ i, (∀ j < i, a j = b j) → carry step init a i = carry step init b i := by
  intro i
  induction i with
  | zero => intro _; rfl
  | succ i ih =>
    intro h
    have hi : a i = b i := h i (Nat.lt_succ_self i)
    have hlow : ∀ j < i, a j = b j := fun j hj => h j (Nat.lt_succ_of_lt hj)
    simp only [carry, hi, shifted_congr hlow, ih hlow]

/-- **Inyectividad sobre las últimas `m` cifras, para cualquier regla de acarreo.** -/
theorem out_injective_below (step : Bool → Bool → σ → σ) (init : σ) (bit : σ → Bool)
    {a b : ℕ → Bool} (m : ℕ) (h : ∀ i < m, out step init bit a i = out step init bit b i) :
    ∀ i < m, a i = b i := by
  induction m with
  | zero => intro i hi; omega
  | succ m ih =>
    have hlow : ∀ i < m, a i = b i := ih (fun i hi => h i (Nat.lt_succ_of_lt hi))
    intro i hi
    rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hi | rfl
    · exact hlow i hi
    · have hm := h i (Nat.lt_succ_self i)
      simp only [out, shifted_congr hlow, carry_congr step init i hlow] at hm
      cases ha : a i <;> cases hb : b i <;> simp_all

/-! ## Las reglas concretas -/

/-- Regla de acarreo de `C_k` (`k = none`: Collatz de verdad). Estado `(acarreo, edad)`: nace con edad 1
cuando las dos cifras son 1, se propaga sumando 1 a la edad y se apaga si la edad pasa de `k`. -/
def stepC (k : Option ℕ) (x y : Bool) (c : Bool × ℕ) : Bool × ℕ :=
  let s := x.toNat + y.toNat + c.1.toNat
  let nc : Bool × ℕ := if x && y then (true, 1) else if 2 ≤ s then (true, c.2 + 1) else (false, 0)
  match k with
  | none => nc
  | some k => if nc.1 && decide (k < nc.2) then (false, 0) else nc

/-- El paso impar de `C_k` (y de Collatz, con `k = none`) es inyectivo sobre las últimas `m` cifras. -/
theorem stepC_injective_below (k : Option ℕ) {a b : ℕ → Bool} (m : ℕ)
    (h : ∀ i < m, out (stepC k) (true, 1) Prod.fst a i = out (stepC k) (true, 1) Prod.fst b i) :
    ∀ i < m, a i = b i :=
  out_injective_below (stepC k) (true, 1) Prod.fst m h

end Collatz.Carries
