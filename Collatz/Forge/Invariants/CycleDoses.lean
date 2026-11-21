import Collatz.Forge.Basic
import Collatz.Forge.Invariants.VerifiedRange

/-!
# El número de doses de un ciclo está forzado

Del sándwich (`cycle_sandwich_of_verified`): bajo `VerifiedBelow M`, un ciclo no trivial de
`k` pasos de Syracuse con `A` doses cumple `3^k < 2^A` y `2^A · M^k ≤ (3M + 1)^k`.

Si además `k ≤ M`, entonces `(3M + 1)^k < 2 · (3M)^k` (porque `(1 + 1/(3M))^k ≤ e^{k/(3M)}
≤ e^{1/3} < 2`), y queda

  `3^k < 2^A < 2 · 3^k`.

Es decir: **`A` es el único entero con `2^{A-1} < 3^k < 2^A`**, `A = ⌊k log₂ 3⌋ + 1`. En un
ciclo no trivial (con `k ≤ 2^71`, que cubre todo lo imaginable) el número total de doses no
es un grado de libertad: lo fija `k`. Esta es la forma en que la aproximación diofántica
de `log₂ 3` entra al problema, y no necesita fracciones continuas: solo la verificación
computacional y la desigualdad de órbita.
-/

namespace Collatz

/-- `e^{1/3} < 2`. -/
theorem exp_third_lt_two : Real.exp (1 / 3) < 2 := by
  have h1 : Real.exp (1 / 3) ^ 3 = Real.exp 1 := by
    rw [← Real.exp_nat_mul]; norm_num
  have h2 : Real.exp 1 < 8 := by
    have := Real.exp_one_lt_d9
    linarith
  have h3 : Real.exp (1 / 3) ^ 3 < 2 ^ 3 := by rw [h1]; norm_num; exact h2
  exact lt_of_pow_lt_pow_left₀ 3 (by norm_num) h3

/-- `(3M + 1)^k < 2 · (3M)^k` para `1 ≤ k ≤ M`. -/
theorem pow_lt_two_mul_pow {M k : ℕ} (hM : 0 < M) (hk : k ≤ M) :
    (3 * M + 1) ^ k < 2 * (3 * M) ^ k := by
  have hMr : (0 : ℝ) < M := by exact_mod_cast hM
  have key : ((3 * M + 1 : ℝ)) ^ k < 2 * (3 * M) ^ k := by
    have h1 : (3 * M + 1 : ℝ) = (3 * M) * (1 + 1 / (3 * M)) := by field_simp
    rw [h1, mul_pow]
    have h2 : (1 + 1 / (3 * M) : ℝ) ^ k ≤ Real.exp (1 / (3 * M)) ^ k :=
      pow_le_pow_left₀ (by positivity)
        (by linarith [Real.add_one_le_exp (1 / (3 * M : ℝ))]) k
    rw [← Real.exp_nat_mul] at h2
    have h3 : (k : ℝ) * (1 / (3 * M)) ≤ 1 / 3 := by
      have hkr : (k : ℝ) ≤ M := by exact_mod_cast hk
      rw [mul_one_div, div_le_div_iff₀ (by positivity) (by norm_num)]
      linarith
    have h5 : (1 + 1 / (3 * M) : ℝ) ^ k < 2 :=
      calc _ ≤ Real.exp (k * (1 / (3 * M))) := h2
        _ ≤ Real.exp (1 / 3) := Real.exp_le_exp.mpr h3
        _ < 2 := exp_third_lt_two
    have h6 : (0 : ℝ) < (3 * M : ℝ) ^ k := by positivity
    nlinarith
  exact_mod_cast key

/-- **Doses forzadas.** Bajo `VerifiedBelow M`, un ciclo no trivial de `k ≤ M` pasos tiene
`3^k < 2^A < 2 · 3^k`. -/
theorem cycle_doses_of_verified {M n k : ℕ} (hV : VerifiedBelow M) (hn : n % 2 = 1)
    (hk : 0 < k) (hkM : k ≤ M) (h : syracuse^[k] n = n) (hne : n ≠ 1) :
    3 ^ k < 2 ^ sExpSum n k ∧ 2 ^ sExpSum n k < 2 * 3 ^ k := by
  obtain ⟨h1, h2⟩ := cycle_sandwich_of_verified hV hn hk h hne
  refine ⟨h1, ?_⟩
  have hM : 0 < M := by omega
  have h3 := pow_lt_two_mul_pow hM hkM
  have : 2 ^ sExpSum n k * M ^ k < 2 * 3 ^ k * M ^ k :=
    calc _ ≤ (3 * M + 1) ^ k := h2
      _ < 2 * (3 * M) ^ k := h3
      _ = 2 * 3 ^ k * M ^ k := by rw [mul_pow]; ring
  exact Nat.lt_of_mul_lt_mul_right this

/-- El entero `A` con `3^k < 2^A < 2 · 3^k` es único. -/
theorem unique_of_pow_sandwich {k A B : ℕ} (hA : 3 ^ k < 2 ^ A ∧ 2 ^ A < 2 * 3 ^ k)
    (hB : 3 ^ k < 2 ^ B ∧ 2 ^ B < 2 * 3 ^ k) : A = B := by
  by_contra hne
  rcases Nat.lt_or_gt_of_ne hne with hlt | hlt
  · have : 2 ^ (A + 1) ≤ 2 ^ B := Nat.pow_le_pow_right two_pos hlt
    rw [pow_succ] at this
    omega
  · have : 2 ^ (B + 1) ≤ 2 ^ A := Nat.pow_le_pow_right two_pos hlt
    rw [pow_succ] at this
    omega

/-- Bajo `VerifiedBelow M`, dos ciclos no triviales con el mismo `k ≤ M` tienen el mismo
número total de doses. -/
theorem cycle_doses_eq_of_verified {M n n' k : ℕ} (hV : VerifiedBelow M)
    (hn : n % 2 = 1) (hn' : n' % 2 = 1) (hk : 0 < k) (hkM : k ≤ M)
    (h : syracuse^[k] n = n) (h' : syracuse^[k] n' = n') (hne : n ≠ 1) (hne' : n' ≠ 1) :
    sExpSum n k = sExpSum n' k :=
  unique_of_pow_sandwich (cycle_doses_of_verified hV hn hk hkM h hne)
    (cycle_doses_of_verified hV hn' hk hkM h' hne')

end Collatz
