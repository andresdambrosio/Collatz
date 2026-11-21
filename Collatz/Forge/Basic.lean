import Mathlib

/-!
# Collatz — definiciones básicas

Este módulo fija las definiciones que usa todo el proyecto. Nada de teoría aquí:
solo los mapas, las funciones auxiliares y los lemas triviales de reescritura.

* `collatz n`: el mapa clásico, `n / 2` si `n` es par y `3n + 1` si es impar.
* `T n`: el mapa acelerado, `n / 2` si par y `(3n + 1) / 2` si impar.
* `nu2 n`: valuación 2-ádica (`padicValNat 2 n`).
* `oddPart n`: `n / 2 ^ nu2 n`, la parte impar de `n`.
* `syracuse n`: el mapa de Syracuse sobre impares, `oddPart (3n + 1)`.
* `ReachesOne n`: la órbita de `n` bajo `collatz` pasa por `1`.
* `CollatzConjecture`: todo `n > 0` satisface `ReachesOne`.

Convención: trabajamos en `ℕ` y tratamos `0` como caso degenerado (`collatz 0 = 0`);
todos los enunciados serios piden `0 < n`.
-/

namespace Collatz

/-- El mapa de Collatz: `n / 2` si `n` es par, `3n + 1` si es impar. -/
def collatz (n : ℕ) : ℕ := if n % 2 = 0 then n / 2 else 3 * n + 1

/-- El mapa acelerado `T`: `n / 2` si `n` es par, `(3n + 1) / 2` si es impar. -/
def T (n : ℕ) : ℕ := if n % 2 = 0 then n / 2 else (3 * n + 1) / 2

/-- Valuación 2-ádica: el mayor `k` con `2 ^ k ∣ n` (y `0` para `n = 0`). -/
abbrev nu2 (n : ℕ) : ℕ := padicValNat 2 n

/-- Parte impar de `n`: `n` dividido por su mayor potencia de `2`. -/
def oddPart (n : ℕ) : ℕ := n / 2 ^ nu2 n

/-- El mapa de Syracuse: `3n + 1` seguido de quitar todos los factores `2`. -/
def syracuse (n : ℕ) : ℕ := oddPart (3 * n + 1)

/-- La órbita de `n` bajo `collatz` pasa por `1`. -/
def ReachesOne (n : ℕ) : Prop := ∃ k, collatz^[k] n = 1

/-- El enunciado de la conjetura. `Main.lean` es el único lugar que la demuestra. -/
def CollatzConjecture : Prop := ∀ n, 0 < n → ReachesOne n

/-! ## Reescritura del mapa -/

@[simp] theorem collatz_of_even {n : ℕ} (h : n % 2 = 0) : collatz n = n / 2 := by
  simp [collatz, h]

@[simp] theorem collatz_of_odd {n : ℕ} (h : n % 2 = 1) : collatz n = 3 * n + 1 := by
  simp [collatz, h]

theorem collatz_zero : collatz 0 = 0 := rfl
theorem collatz_one : collatz 1 = 4 := rfl
theorem collatz_two : collatz 2 = 1 := rfl
theorem collatz_four : collatz 4 = 2 := rfl

theorem T_of_even {n : ℕ} (h : n % 2 = 0) : T n = n / 2 := by
  simp [T, h]

theorem T_of_odd {n : ℕ} (h : n % 2 = 1) : T n = (3 * n + 1) / 2 := by
  simp [T, h]

/-! ## Positividad -/

theorem collatz_pos {n : ℕ} (hn : 0 < n) : 0 < collatz n := by
  unfold collatz
  split <;> omega

theorem iterate_pos {n : ℕ} (hn : 0 < n) (k : ℕ) : 0 < collatz^[k] n := by
  induction k with
  | zero => simpa
  | succ k ih => rw [Function.iterate_succ_apply']; exact collatz_pos ih

theorem T_pos {n : ℕ} (hn : 0 < n) : 0 < T n := by
  unfold T
  split <;> omega

/-! ## Parte impar y Syracuse -/

theorem oddPart_eq_ordCompl (n : ℕ) : oddPart n = ordCompl[2] n := by
  unfold oddPart nu2
  rw [Nat.factorization_def n Nat.prime_two]

theorem two_pow_nu2_mul_oddPart (n : ℕ) : 2 ^ nu2 n * oddPart n = n := by
  rw [oddPart_eq_ordCompl]
  unfold nu2
  rw [← Nat.factorization_def n Nat.prime_two]
  exact Nat.ordProj_mul_ordCompl_eq_self n 2

theorem oddPart_odd {n : ℕ} (hn : n ≠ 0) : Odd (oddPart n) := by
  rw [oddPart_eq_ordCompl]
  exact Nat.odd_iff.mpr (Nat.two_dvd_ne_zero.mp (Nat.not_dvd_ordCompl Nat.prime_two hn))

theorem oddPart_pos {n : ℕ} (hn : 0 < n) : 0 < oddPart n := by
  rw [oddPart_eq_ordCompl]
  exact Nat.ordCompl_pos 2 hn.ne'

theorem oddPart_le (n : ℕ) : oddPart n ≤ n := by
  rw [oddPart_eq_ordCompl]
  exact Nat.ordCompl_le n 2

theorem nu2_of_odd {n : ℕ} (h : Odd n) : nu2 n = 0 :=
  padicValNat.eq_zero_of_not_dvd (Nat.two_dvd_ne_zero.mpr (Nat.odd_iff.mp h))

theorem oddPart_of_odd {n : ℕ} (h : Odd n) : oddPart n = n := by
  unfold oddPart
  rw [nu2_of_odd h, pow_zero, Nat.div_one]

theorem nu2_two_mul {n : ℕ} (hn : n ≠ 0) : nu2 (2 * n) = nu2 n + 1 := by
  unfold nu2
  rw [padicValNat.mul two_ne_zero hn, padicValNat_self, add_comm]

theorem oddPart_two_mul {n : ℕ} (hn : n ≠ 0) : oddPart (2 * n) = oddPart n := by
  unfold oddPart
  rw [nu2_two_mul hn, pow_succ', Nat.mul_div_mul_left _ _ two_pos]

theorem syracuse_odd (n : ℕ) : Odd (syracuse n) :=
  oddPart_odd (by omega)

theorem syracuse_pos (n : ℕ) : 0 < syracuse n :=
  oddPart_pos (by omega)

/-- La órbita de Syracuse de un impar es toda impar. -/
theorem iterate_syracuse_odd {n : ℕ} (hn : n % 2 = 1) (k : ℕ) : syracuse^[k] n % 2 = 1 := by
  cases k with
  | zero => simpa
  | succ k => rw [Function.iterate_succ_apply']; exact Nat.odd_iff.mp (syracuse_odd _)

/-! ## Sanity checks -/

theorem reachesOne_one : ReachesOne 1 := ⟨0, rfl⟩
theorem reachesOne_two : ReachesOne 2 := ⟨1, rfl⟩
theorem reachesOne_four : ReachesOne 4 := ⟨2, rfl⟩

example : ReachesOne 6 := ⟨8, by decide⟩
example : ReachesOne 7 := ⟨16, by decide⟩
/-- `nu2`/`oddPart` no reducen en el kernel (`padicValNat` no es `decide`-able);
para valores concretos, reescribir con `oddPart_two_mul` y `oddPart_of_odd`. -/
example : syracuse 7 = 11 := by
  show oddPart 22 = 11
  rw [show (22 : ℕ) = 2 * 11 by norm_num, oddPart_two_mul (by norm_num),
    oddPart_of_odd (by decide)]

end Collatz
