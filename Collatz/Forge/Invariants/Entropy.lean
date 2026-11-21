import Mathlib

/-!
# Cota entrópica de los coeficientes binomiales

Lema puramente combinatorio/analítico, sin Collatz.

**Idea matemática.** Para `0 ≤ k ≤ n` y `p = k/n`, el binomio de Newton da
`1 = (p + (1-p))^n = Σᵢ C(n,i) pⁱ (1-p)^{n-i} ≥ C(n,k) pᵏ (1-p)^{n-k}`, luego
`C(n,k) ≤ p^{-k} (1-p)^{-(n-k)} = exp(k log p⁻¹ + (n-k) log (1-p)⁻¹) = exp(n · H(p))`,
donde `H(p) = p log p⁻¹ + (1-p) log (1-p)⁻¹` es la entropía binaria en nats
(`Real.binEntropy` de Mathlib). En base 2: `C(n,k) ≤ 2^{n · H₂(k/n)}`.

**Corolario para el proyecto.** Sea `θ = 1 / log₂ 3 ≈ 0.6309 ∈ (1/2, 1)`. Si la densidad
de doses es `A ≤ j · log₂ 3` (es decir `j/A ≥ θ`), como `H` es decreciente en `[1/2, 1]`,
`H(j/A) ≤ H(θ)`, y por lo tanto `C(A, j) ≤ 2^{A · c}` con `c = H(θ)/log 2 = H₂(θ) ≈ 0.951`.
Lo esencial es `c < 1`, que sale de `θ ≠ 1/2` (porque `3 ≠ 4`) vía `binEntropy_lt_log_two`,
sin ninguna certificación numérica. También `C(A-1, j-1) ≤ C(A, j) ≤ 2^{A · c}`.
-/

namespace Collatz

open Real Finset

/-- Cota entrópica: para `k ≤ n`, `C(n,k) ≤ exp(n · H(k/n))` con `H = Real.binEntropy` (nats). -/
theorem choose_le_exp_binEntropy (n k : ℕ) (hk : k ≤ n) :
    (n.choose k : ℝ) ≤ Real.exp (n * Real.binEntropy (k / n)) := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · obtain rfl : k = 0 := Nat.le_zero.1 hk
    simp
  rcases Nat.eq_zero_or_pos k with rfl | hk0
  · simp
  rcases eq_or_lt_of_le hk with rfl | hkn
  · have : (k : ℝ) / k = 1 := div_self (by positivity)
    simp [this]
  set p : ℝ := k / n with hp
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hp0 : 0 < p := by positivity
  have hp1 : p < 1 := by rw [hp, div_lt_one hn']; exact_mod_cast hkn
  have h1p : 0 < 1 - p := by linarith
  -- Binomio de Newton: el término `k` de `(p + (1-p))^n = 1` es `≤ 1`.
  have key : (n.choose k : ℝ) * (p ^ k * (1 - p) ^ (n - k)) ≤ 1 := by
    have h := add_pow p (1 - p) n
    rw [show p + (1 - p) = 1 by ring, one_pow] at h
    refine le_trans ?_ h.symm.le
    have := Finset.single_le_sum
      (f := fun i => p ^ i * (1 - p) ^ (n - i) * (n.choose i : ℝ))
      (fun i _ => by positivity) (Finset.mem_range.2 (Nat.lt_succ_of_le hk))
    simpa [mul_comm, mul_left_comm, mul_assoc] using this
  have hpos : 0 < p ^ k * (1 - p) ^ (n - k) := by positivity
  have h2 : (n.choose k : ℝ) ≤ (p ^ k * (1 - p) ^ (n - k))⁻¹ := by
    rw [← one_div, le_div_iff₀ hpos]; exact key
  -- Identificación del inverso con `exp(n · H(p))`.
  have hnp : (n : ℝ) * p = k := by rw [hp]; field_simp
  have hn1p : (n : ℝ) * (1 - p) = ((n - k : ℕ) : ℝ) := by
    rw [Nat.cast_sub hk, hp]; field_simp
  have h3 : (p ^ k * (1 - p) ^ (n - k))⁻¹ = Real.exp (n * Real.binEntropy p) := by
    rw [Real.binEntropy, mul_add, ← mul_assoc, ← mul_assoc, hnp, hn1p, Real.exp_add,
      ← Real.log_pow, ← Real.log_pow, Real.exp_log (by positivity), Real.exp_log (by positivity),
      mul_inv, inv_pow, inv_pow]
  rw [← h3]; exact h2

/-- `θ = 1 / log₂ 3 ≈ 0.6309`: el umbral de densidad de doses `A/j ≤ log₂ 3`. -/
noncomputable def entropyTheta : ℝ := 1 / Real.logb 2 3

/-- `c = H₂(θ) = H(θ) / log 2 ≈ 0.951`: exponente de la cota `C(A,j) ≤ 2^{c·A}`. -/
noncomputable def entropyConst : ℝ := Real.binEntropy entropyTheta / Real.log 2

lemma one_lt_logb_two_three : 1 < Real.logb 2 3 := by
  rw [Real.lt_logb_iff_rpow_lt (by norm_num) (by norm_num)]; norm_num

lemma logb_two_three_lt_two : Real.logb 2 3 < 2 := by
  rw [Real.logb_lt_iff_lt_rpow (by norm_num) (by norm_num)]; norm_num

lemma entropyTheta_lt_one : entropyTheta < 1 := by
  unfold entropyTheta
  rw [div_lt_one (by linarith [one_lt_logb_two_three])]
  exact one_lt_logb_two_three

lemma two_inv_lt_entropyTheta : (2 : ℝ)⁻¹ < entropyTheta := by
  unfold entropyTheta
  rw [one_div, inv_lt_inv₀ (by norm_num) (by linarith [one_lt_logb_two_three])]
  exact logb_two_three_lt_two

lemma entropyTheta_mem_Icc : entropyTheta ∈ Set.Icc (2 : ℝ)⁻¹ 1 :=
  ⟨two_inv_lt_entropyTheta.le, entropyTheta_lt_one.le⟩

/-- Lo esencial: la constante entrópica es estrictamente menor que 1, porque `θ ≠ 1/2`. -/
theorem entropyConst_lt_one : entropyConst < 1 := by
  unfold entropyConst
  rw [div_lt_one (Real.log_pos (by norm_num))]
  exact Real.binEntropy_lt_log_two.2 two_inv_lt_entropyTheta.ne'

theorem entropyConst_nonneg : 0 ≤ entropyConst := by
  unfold entropyConst
  exact div_nonneg (Real.binEntropy_nonneg (by linarith [two_inv_lt_entropyTheta])
    entropyTheta_lt_one.le) (Real.log_pos (by norm_num)).le

/-- Si `j/A ≥ θ` (con `j ≤ A`), entonces `H(j/A) ≤ H(θ)` por monotonía decreciente en `[1/2,1]`. -/
lemma binEntropy_le_of_theta_le {x : ℝ} (hθ : entropyTheta ≤ x) (hx : x ≤ 1) :
    Real.binEntropy x ≤ Real.binEntropy entropyTheta :=
  Real.binEntropy_strictAntiOn.antitoneOn entropyTheta_mem_Icc
    ⟨two_inv_lt_entropyTheta.le.trans hθ, hx⟩ hθ

/-- `2^{A · c} = exp(A · H(θ))`. -/
lemma two_rpow_mul_entropyConst (A : ℝ) :
    (2 : ℝ) ^ (A * entropyConst) = Real.exp (A * Real.binEntropy entropyTheta) := by
  rw [Real.rpow_def_of_pos (by norm_num)]
  congr 1
  unfold entropyConst
  have : Real.log 2 ≠ 0 := (Real.log_pos (by norm_num)).ne'
  field_simp

/-- **Cota entrópica con densidad.** Si `j ≤ A` y `A ≤ j · log₂ 3`, entonces
`C(A, j) ≤ 2^{A · c}` con `c = entropyConst < 1`. -/
theorem choose_le_two_rpow_of_dense (A j : ℕ) (hj : j ≤ A)
    (hd : (A : ℝ) ≤ j * Real.logb 2 3) :
    (A.choose j : ℝ) ≤ (2 : ℝ) ^ ((A : ℝ) * entropyConst) := by
  rw [two_rpow_mul_entropyConst]
  refine (choose_le_exp_binEntropy A j hj).trans ?_
  rcases Nat.eq_zero_or_pos A with rfl | hA
  · simp
  have hA' : (0 : ℝ) < A := by exact_mod_cast hA
  have hL : 0 < Real.logb 2 3 := by linarith [one_lt_logb_two_three]
  have hθ : entropyTheta ≤ (j : ℝ) / A := by
    unfold entropyTheta
    rw [div_le_div_iff₀ hL hA']
    linarith
  have hx : (j : ℝ) / A ≤ 1 := by
    rw [div_le_one hA']; exact_mod_cast hj
  apply Real.exp_le_exp.2
  exact mul_le_mul_of_nonneg_left (binEntropy_le_of_theta_le hθ hx) hA'.le

/-- Versión con `C(A-1, j-1)`, la que aparece en el conteo de clases de Terras:
`C(A-1, j-1) ≤ C(A, j) ≤ 2^{A · c}`. -/
theorem choose_pred_le_two_rpow_of_dense (A j : ℕ) (hj1 : 1 ≤ j) (hj : j ≤ A)
    (hd : (A : ℝ) ≤ j * Real.logb 2 3) :
    ((A - 1).choose (j - 1) : ℝ) ≤ (2 : ℝ) ^ ((A : ℝ) * entropyConst) := by
  refine le_trans ?_ (choose_le_two_rpow_of_dense A j hj hd)
  have h : (A - 1).choose (j - 1) ≤ A.choose j := by
    obtain ⟨a, rfl⟩ : ∃ a, A = a + 1 := ⟨A - 1, by omega⟩
    obtain ⟨b, rfl⟩ : ∃ b, j = b + 1 := ⟨j - 1, by omega⟩
    simp only [Nat.add_sub_cancel, Nat.choose_succ_succ]
    exact Nat.le_add_right _ _
  exact_mod_cast h

end Collatz
