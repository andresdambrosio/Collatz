import Collatz.Forge.Basic
import Collatz.Forge.Invariants.SyracuseCycleEquation
import Collatz.Forge.Invariants.ParityAperiodic
import Collatz.Forge.Invariants.OrbitInequality
import Collatz.Forge.Invariants.VerifiedRange

/-!
# Ciclos cortos de Syracuse

Los casos `k = 1` y `k = 2` de "no hay ciclos no triviales", incondicionales y por
aritmética finita.

* `k = 1`: `2^a · n = 3n + 1`. Si `a ≤ 1` el lado izquierdo es `≤ 2n`; si `a ≥ 3` es `≥ 8n`;
  queda `a = 2`, `4n = 3n + 1`, `n = 1`.
* `k = 2`: con `x = S n`, `2^{a₀} x = 3n + 1` y `2^{a₁} n = 3x + 1`. Nueve casos según
  `2^{aᵢ} ∈ {2, 4, ≥ 8}`, todos lineales; el único que sobrevive es `a₀ = a₁ = 2`, `n = x = 1`.

Estos casos no usan la ecuación del ciclo general: son más baratos hechos a mano.

**Sándwich incondicional.** En un ciclo no trivial todos los elementos son impares y `≠ 1`,
luego `≥ 3`, y `cycle_sandwich` con `N = 3` da `3^k < 2^A` y `2^A · 3^k ≤ 10^k` sin ninguna
hipótesis externa. Para `k = 4` no hay potencia de `2` en `(81, 123]`: **no hay 4-ciclos**
(`no_syracuse_four_cycle`). Para `k = 3, 5, 6, …` sí hay una `A` candidata y hace falta
enumerar composiciones; para eso está `CycleDoses.lean` y, más adelante, cotas mejores de `N`.
-/

namespace Collatz

theorem pow_two_cases {a : ℕ} (ha : 1 ≤ a) : 2 ^ a = 2 ∨ 2 ^ a = 4 ∨ 8 ≤ 2 ^ a := by
  rcases a with _ | _ | _ | a
  · omega
  · left; rfl
  · right; left; rfl
  · right; right
    calc 8 = 2 ^ 3 := by norm_num
      _ ≤ 2 ^ (a + 3) := Nat.pow_le_pow_right two_pos (by omega)

/-- **`k = 1`.** El único punto fijo de Syracuse es `1`. -/
theorem syracuse_fixed_eq_one {n : ℕ} (h : syracuse n = n) : n = 1 := by
  have hid := two_pow_sExp_mul_syracuse n
  rw [h] at hid
  have hpos : 0 < n := by
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · have := syracuse_pos 0; omega
    · exact hn
  have ha : 1 ≤ sExp n := by
    by_contra h0
    have : sExp n = 0 := by omega
    rw [this] at hid; omega
  rcases pow_two_cases ha with hp | hp | hp
  · rw [hp] at hid; omega
  · rw [hp] at hid; omega
  · have := Nat.mul_le_mul_right n hp; omega

/-- **`k = 2`.** Ningún impar distinto de `1` tiene período `2` bajo Syracuse. -/
theorem syracuse_two_periodic_eq_one {n : ℕ} (hn : n % 2 = 1) (h : syracuse^[2] n = n) :
    n = 1 := by
  set x := syracuse n with hx
  have h0 : 2 ^ sExp n * x = 3 * n + 1 := two_pow_sExp_mul_syracuse n
  have h1 : 2 ^ sExp x * n = 3 * x + 1 := by
    have := two_pow_sExp_mul_syracuse x
    rwa [show syracuse x = n from h] at this
  have ha0 : 1 ≤ sExp n := sExp_pos_of_odd hn
  have ha1 : 1 ≤ sExp x := sExp_pos_of_odd (Nat.odd_iff.mp (syracuse_odd n))
  have hxpos : 1 ≤ x := syracuse_pos n
  rcases pow_two_cases ha0 with hp | hp | hp <;>
  rcases pow_two_cases ha1 with hq | hq | hq <;>
  · try rw [hp] at h0
    try rw [hq] at h1
    try have h8 := Nat.mul_le_mul_right x hp
    try have h9 := Nat.mul_le_mul_right n hq
    omega

/-- En un ciclo no trivial todos los elementos son `≥ 3`. -/
theorem three_le_of_cycle {n k : ℕ} (hn : n % 2 = 1) (h : syracuse^[k] n = n) (hne : n ≠ 1) :
    ∀ i < k, 3 ≤ syracuse^[i] n := by
  intro i hi
  have hodd := iterate_syracuse_odd hn i
  have hne1 : syracuse^[i] n ≠ 1 := fun h1 => hne (eq_one_of_iterate_syracuse_eq_one h hi.le h1)
  omega

/-- **Sándwich incondicional.** Un ciclo no trivial de `k > 0` pasos cumple
`3^k < 2^A` y `2^A · 3^k ≤ 10^k`. -/
theorem cycle_sandwich_three {n k : ℕ} (hn : n % 2 = 1) (hk : 0 < k) (h : syracuse^[k] n = n)
    (hne : n ≠ 1) : 3 ^ k < 2 ^ sExpSum n k ∧ 2 ^ sExpSum n k * 3 ^ k ≤ 10 ^ k := by
  have := cycle_sandwich (N := 3) hk (by omega) (three_le_of_cycle hn h hne) h
  simpa using this

/-- **`k = 4`.** No hay 4-ciclos de Syracuse: ninguna potencia de `2` cae en `(81, 123]`. -/
theorem no_syracuse_four_cycle {n : ℕ} (hn : n % 2 = 1) (h : syracuse^[4] n = n) : n = 1 := by
  by_contra hne
  obtain ⟨h1, h2⟩ := cycle_sandwich_three hn (by norm_num) h hne
  set A := sExpSum n 4
  have hA : A ≤ 13 := by
    by_contra hA
    have : 2 ^ 14 ≤ 2 ^ A := Nat.pow_le_pow_right two_pos (by omega)
    omega
  interval_cases A <;> omega

/-- La ecuación de órbita para `k = 3`, desplegada. -/
theorem syracuse_three_eq (n : ℕ) :
    syracuse^[3] n * 2 ^ (sExp n + sExp (syracuse n) + sExp (syracuse^[2] n)) =
      27 * n + 9 + 3 * 2 ^ sExp n + 2 ^ (sExp n + sExp (syracuse n)) := by
  have := syracuse_iterate_mul_two_pow n 3
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, sExpSum_succ, sExpSum_zero] at this
  simpa [pow_succ, add_assoc] using this

/-- **`k = 3`.** No hay 3-ciclos de Syracuse: `A = 5` está forzado y ninguna de las seis
composiciones de `5` en tres partes da `5 ∣ 9 + 3·2^{a₀} + 2^{a₀+a₁}`. -/
theorem no_syracuse_three_cycle {n : ℕ} (hn : n % 2 = 1) (h : syracuse^[3] n = n) : n = 1 := by
  by_contra hne
  obtain ⟨h1, h2⟩ := cycle_sandwich_three hn (by norm_num) h hne
  have hA : sExpSum n 3 = sExp n + sExp (syracuse n) + sExp (syracuse^[2] n) := by
    simp [sExpSum, Finset.sum_range_succ]
  rw [hA] at h1 h2
  set a₀ := sExp n with ha₀
  set a₁ := sExp (syracuse n) with ha₁
  set a₂ := sExp (syracuse^[2] n) with ha₂
  have hp₀ : 1 ≤ a₀ := sExp_pos_of_odd hn
  have hp₁ : 1 ≤ a₁ := sExp_pos_of_odd (iterate_syracuse_odd hn 1)
  have hp₂ : 1 ≤ a₂ := sExp_pos_of_odd (iterate_syracuse_odd hn 2)
  -- 27 < 2^A ≤ 37 ⇒ A = 5
  have hA5 : a₀ + a₁ + a₂ = 5 := by
    have hle : a₀ + a₁ + a₂ ≤ 5 := by
      by_contra hc
      have : 2 ^ 6 ≤ 2 ^ (a₀ + a₁ + a₂) := Nat.pow_le_pow_right two_pos (by omega)
      omega
    have hge : 5 ≤ a₀ + a₁ + a₂ := by
      by_contra hc
      have : 2 ^ (a₀ + a₁ + a₂) ≤ 2 ^ 4 := Nat.pow_le_pow_right two_pos (by omega)
      omega
    omega
  have heq := syracuse_three_eq n
  rw [h, ← ha₀, ← ha₁, ← ha₂, hA5] at heq
  -- 32 n = 27 n + 9 + 3·2^{a₀} + 2^{a₀+a₁}
  have hb₀ : a₀ ≤ 3 := by omega
  have hb₁ : a₁ ≤ 3 := by omega
  interval_cases a₀ <;> interval_cases a₁ <;> omega

end Collatz
