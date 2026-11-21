import Collatz.Forge.Basic

/-!
# La ecuación del ciclo de Syracuse

Sea `n₀ = n`, `nᵢ₊₁ = syracuse nᵢ`, y `aᵢ = nu2 (3 nᵢ + 1)` el número de doses que quita
el paso `i`. Un paso es `2^{aᵢ} · nᵢ₊₁ = 3 nᵢ + 1`. Desenrollando `k` pasos, con
`Aᵢ = a₀ + ⋯ + aᵢ₋₁`:

  `nₖ · 2^{Aₖ} = 3^k · n + Σ_{i<k} 3^{k-1-i} · 2^{Aᵢ}`.

Es una identidad en `ℕ`, sin restas, que vale para toda órbita (`syracuse_iterate_mul_two_pow`).

Si además `nₖ = n` (ciclo), queda la **ecuación del ciclo** en `ℤ`:

  `n · (2^{Aₖ} − 3^k) = Σ_{i<k} 3^{k-1-i} · 2^{Aᵢ}`  (`syracuse_cycle_equation`),

y como el lado derecho es positivo, `2^{Aₖ} > 3^k` (`two_pow_gt_three_pow_of_cycle`):
todo ciclo de `k` pasos de Syracuse quita en total más de `k · log₂ 3` doses. Esta es la
primera restricción aritmética real sobre ciclos y el punto de partida para
`NoNontrivialCycles`.
-/

namespace Collatz

open Finset

/-- Exponente que quita `syracuse` en `n`: `nu2 (3n + 1)`. -/
def sExp (n : ℕ) : ℕ := nu2 (3 * n + 1)

theorem two_pow_sExp_mul_syracuse (n : ℕ) : 2 ^ sExp n * syracuse n = 3 * n + 1 :=
  two_pow_nu2_mul_oddPart (3 * n + 1)

/-- Exponentes acumulados a lo largo de los primeros `k` pasos de la órbita de `n`. -/
def sExpSum (n k : ℕ) : ℕ := ∑ j ∈ range k, sExp (syracuse^[j] n)

theorem sExpSum_zero (n : ℕ) : sExpSum n 0 = 0 := by simp [sExpSum]

theorem sExpSum_succ (n k : ℕ) :
    sExpSum n (k + 1) = sExpSum n k + sExp (syracuse^[k] n) :=
  sum_range_succ _ _

/-- Identidad de la órbita: `nₖ · 2^{Aₖ} = 3^k n + Σ_{i<k} 3^{k-1-i} 2^{Aᵢ}`. -/
theorem syracuse_iterate_mul_two_pow (n k : ℕ) :
    syracuse^[k] n * 2 ^ sExpSum n k =
      3 ^ k * n + ∑ i ∈ range k, 3 ^ (k - 1 - i) * 2 ^ sExpSum n i := by
  induction k with
  | zero => simp [sExpSum_zero]
  | succ k ih =>
    have hx := two_pow_sExp_mul_syracuse (syracuse^[k] n)
    rw [sExpSum_succ, pow_add, Function.iterate_succ_apply']
    calc syracuse (syracuse^[k] n) * (2 ^ sExpSum n k * 2 ^ sExp (syracuse^[k] n))
        = (2 ^ sExp (syracuse^[k] n) * syracuse (syracuse^[k] n)) * 2 ^ sExpSum n k := by ring
      _ = (3 * syracuse^[k] n + 1) * 2 ^ sExpSum n k := by rw [hx]
      _ = 3 * (syracuse^[k] n * 2 ^ sExpSum n k) + 2 ^ sExpSum n k := by ring
      _ = 3 * (3 ^ k * n + ∑ i ∈ range k, 3 ^ (k - 1 - i) * 2 ^ sExpSum n i)
            + 2 ^ sExpSum n k := by rw [ih]
      _ = 3 ^ (k + 1) * n + ∑ i ∈ range (k + 1), 3 ^ (k + 1 - 1 - i) * 2 ^ sExpSum n i := by
          rw [sum_range_succ, mul_add, mul_sum]
          have h1 : ∀ i ∈ range k,
              3 * (3 ^ (k - 1 - i) * 2 ^ sExpSum n i) = 3 ^ (k + 1 - 1 - i) * 2 ^ sExpSum n i := by
            intro i hi
            have : k + 1 - 1 - i = (k - 1 - i) + 1 := by
              have := mem_range.mp hi
              omega
            rw [this, pow_succ]
            ring
          rw [sum_congr rfl h1]
          simp only [Nat.add_sub_cancel, Nat.sub_self, pow_zero, one_mul]
          ring

/-- **Ecuación del ciclo.** Si `syracuse^[k] n = n`, entonces
`n · (2^{Aₖ} − 3^k) = Σ_{i<k} 3^{k-1-i} · 2^{Aᵢ}` en `ℤ`. -/
theorem syracuse_cycle_equation {n k : ℕ} (h : syracuse^[k] n = n) :
    (n : ℤ) * (2 ^ sExpSum n k - 3 ^ k) =
      ∑ i ∈ range k, (3 : ℤ) ^ (k - 1 - i) * 2 ^ sExpSum n i := by
  have := syracuse_iterate_mul_two_pow n k
  rw [h] at this
  have hz := congrArg (fun x : ℕ => (x : ℤ)) this
  push_cast at hz
  linarith

/-- En un ciclo de longitud `k > 0` se quitan más de `k log₂ 3` doses. -/
theorem two_pow_gt_three_pow_of_cycle {n k : ℕ} (hk : 0 < k)
    (h : syracuse^[k] n = n) : 3 ^ k < 2 ^ sExpSum n k := by
  have hid := syracuse_iterate_mul_two_pow n k
  rw [h] at hid
  have hpos : 0 < ∑ i ∈ range k, 3 ^ (k - 1 - i) * 2 ^ sExpSum n i := by
    apply sum_pos
    · intro i _
      positivity
    · exact nonempty_range_iff.mpr hk.ne'
  have : 3 ^ k * n < n * 2 ^ sExpSum n k := by omega
  rw [mul_comm] at this
  exact Nat.lt_of_mul_lt_mul_left this

end Collatz
