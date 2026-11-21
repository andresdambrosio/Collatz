import Collatz.Forge.Basic
import Collatz.Forge.Invariants.DivergentDensity
import Collatz.Forge.Invariants.Terras
import Collatz.Forge.Invariants.Entropy

/-!
# Una órbita divergente vive en un conjunto fino

**Teorema final del eje de divergencia.** Empaqueta tres piezas ya probadas, sin
matemática nueva:

1. `divergent_dose_bound` (DivergentDensity): si `n` diverge, para todo `N` hay una cola
   `x = S^{i₀} n` y un `j₀` tales que `N^j · 2^{A} ≤ (3N+1)^j` para todo `j ≥ j₀`, con
   `A = A(x, j) = sExpSum x j` las doses de los primeros `j` pasos. En logaritmos:
   `A ≤ j · log₂(3 + 1/N)`.
2. `card_residueClasses_le` (Terras): las clases impares mod `2^{A+1}` con patrón de `j`
   pasos y `A` doses son a lo sumo `C(A−1, j−1)`. Y `x` cae en una de ellas: la suya, porque
   por Terras el patrón depende solo de `x mod 2^{A+1}`.
3. La cota entrópica (Entropy): `C(A, j) ≤ 2^{A · H₂(j/A)}`, y `H₂` es decreciente en
   `[1/2, 1]`, así que `j/A ≥ θ` da `C(A, j) ≤ 2^{A · H₂(θ)}`.

**Sobre el parámetro `N`.** La cota (1) da la densidad `A ≤ j · log₂(3 + 1/N)`, no
`A ≤ j · log₂ 3` exacto, así que el umbral es `θ_N = 1 / log₂(3 + 1/N)` en vez de
`θ = 1 / log₂ 3 = entropyTheta`, y la constante es `c_N = thinConst N = H₂(θ_N)`. Para
`N ≥ 2` vale `2 < 3 + 1/N < 4`, luego `1/2 < θ_N < 1` y `c_N < 1` estrictamente (porque
`θ_N ≠ 1/2`, sin certificación numérica). Cuando `N → ∞`, `θ_N → θ` y `c_N → entropyConst`;
el `N` juega el papel del `ε` del blueprint, pero de forma exacta en lugar de asintótica.

**Enunciado.** Si `n` es impar y diverge, para todo `N ≥ 2` existen `i₀, j₀` tales que
para todo `j ≥ j₀`, con `x = S^{i₀} n` y `A = A(x, j)`:

* `x mod 2^{A+1} ∈ residueClasses j A` (es su propia clase);
* `|residueClasses j A| ≤ 2^{c_N · A}` con `c_N < 1`;
* `A ≤ j · log₂(3 + 1/N)`.

Como hay `2^A` impares mod `2^{A+1}`, la fracción de clases admisibles es
`≤ 2^{−(1 − c_N) · A}` (`divergent_in_thin_set_fraction`), y `A ≥ j → ∞`, así que tiende a
cero exponencialmente. Es la formalización exacta de "casi ningún número diverge".

**Muro.** Convertir esto en contradicción para UN `n` fijo no es posible con este argumento:
un `n` fijo puede perfectamente estar en el conjunto fino. Ningún lema de este archivo
pretende cruzar de "densidad cero" a "vacío".
-/

namespace Collatz

open Real Finset

/-! ## Pieza (1): todo impar cae en su propia clase residual -/

/-- Reducir mod `2^{A+1}` preserva la paridad. -/
theorem thin_mod_two_pow_succ_odd {x : ℕ} (hx : x % 2 = 1) (m : ℕ) :
    x % 2 ^ (m + 1) % 2 = 1 := by
  rw [Nat.mod_mod_of_dvd _ (dvd_pow_self 2 (Nat.succ_ne_zero m))]
  exact hx

/-- `x mod 2^{A+1}` tiene el mismo patrón de `j` pasos que `x` (Terras, vuelta), luego las
mismas `A` doses. -/
theorem thin_sExpSum_mod (x j : ℕ) (hx : x % 2 = 1) :
    sExpSum (x % 2 ^ (sExpSum x j + 1)) j = sExpSum x j := by
  have hodd := thin_mod_two_pow_succ_odd hx (sExpSum x j)
  have hmod : x ≡ x % 2 ^ (sExpSum x j + 1) [MOD 2 ^ (sExpSum x j + 1)] :=
    (Nat.mod_modEq _ _).symm
  exact (sExpSum_eq_of_pattern j (pattern_of_modEq j hx hodd hmod)).symm

/-- Todo impar `x` cae en `residueClasses j (A(x, j))`: su propia clase mod `2^{A+1}`. -/
theorem thin_mod_mem_residueClasses {x : ℕ} (hx : x % 2 = 1) (j : ℕ) :
    x % 2 ^ (sExpSum x j + 1) ∈ residueClasses j (sExpSum x j) := by
  rw [mem_residueClasses]
  exact ⟨Nat.mod_lt _ (by positivity), thin_mod_two_pow_succ_odd hx _, thin_sExpSum_mod x j hx⟩

/-! ## Pieza (3): cota entrópica con umbral `θ` arbitrario en `[1/2, 1]` -/

/-- Cota entrópica parametrizada: si `j ≤ A` y `θ · A ≤ j` con `θ ∈ [1/2, 1]`, entonces
`C(A, j) ≤ 2^{A · H₂(θ)}` con `H₂(θ) = binEntropy θ / log 2`. Generaliza
`choose_le_two_rpow_of_dense` (que es el caso `θ = entropyTheta`). -/
theorem thin_choose_le_two_rpow {θ : ℝ} (hθ0 : 2⁻¹ ≤ θ) (hθ1 : θ ≤ 1) (A j : ℕ)
    (hj : j ≤ A) (hd : θ * A ≤ j) :
    (A.choose j : ℝ) ≤ (2 : ℝ) ^ ((A : ℝ) * (Real.binEntropy θ / Real.log 2)) := by
  have hlog : Real.log 2 ≠ 0 := (Real.log_pos (by norm_num)).ne'
  have h2 : (2 : ℝ) ^ ((A : ℝ) * (Real.binEntropy θ / Real.log 2)) =
      Real.exp (A * Real.binEntropy θ) := by
    rw [Real.rpow_def_of_pos (by norm_num)]
    congr 1
    field_simp
  rw [h2]
  refine (choose_le_exp_binEntropy A j hj).trans ?_
  rcases Nat.eq_zero_or_pos A with rfl | hA
  · simp
  have hA' : (0 : ℝ) < A := by exact_mod_cast hA
  have hθ : θ ≤ (j : ℝ) / A := by
    rw [le_div_iff₀ hA']; exact hd
  have hx : (j : ℝ) / A ≤ 1 := by
    rw [div_le_one hA']; exact_mod_cast hj
  apply Real.exp_le_exp.2
  refine mul_le_mul_of_nonneg_left ?_ hA'.le
  exact Real.binEntropy_strictAntiOn.antitoneOn ⟨hθ0, hθ1⟩ ⟨hθ0.trans hθ, hx⟩ hθ

/-- Versión con `C(A−1, j−1)`, la que aparece en `card_residueClasses_le`. -/
theorem thin_choose_pred_le_two_rpow {θ : ℝ} (hθ0 : 2⁻¹ ≤ θ) (hθ1 : θ ≤ 1) (A j : ℕ)
    (hj1 : 1 ≤ j) (hj : j ≤ A) (hd : θ * A ≤ j) :
    ((A - 1).choose (j - 1) : ℝ) ≤ (2 : ℝ) ^ ((A : ℝ) * (Real.binEntropy θ / Real.log 2)) := by
  refine le_trans ?_ (thin_choose_le_two_rpow hθ0 hθ1 A j hj hd)
  have h : (A - 1).choose (j - 1) ≤ A.choose j := by
    obtain ⟨a, rfl⟩ : ∃ a, A = a + 1 := ⟨A - 1, by omega⟩
    obtain ⟨b, rfl⟩ : ∃ b, j = b + 1 := ⟨j - 1, by omega⟩
    simp only [Nat.add_sub_cancel, Nat.choose_succ_succ]
    exact Nat.le_add_right _ _
  exact_mod_cast h

/-! ## El umbral `θ_N` y la constante `c_N` -/

/-- `θ_N = 1 / log₂(3 + 1/N)`: el umbral de densidad que da `divergent_dose_bound` con
parámetro `N`. Tiende a `entropyTheta = 1 / log₂ 3` cuando `N → ∞`. -/
noncomputable def thinTheta (N : ℕ) : ℝ := 1 / Real.logb 2 (3 + 1 / N)

/-- `c_N = H₂(θ_N)`: exponente de la cota `|residueClasses j A| ≤ 2^{c_N · A}`.
Tiende a `entropyConst ≈ 0.951` cuando `N → ∞`; es `< 1` para todo `N ≥ 2`. -/
noncomputable def thinConst (N : ℕ) : ℝ := Real.binEntropy (thinTheta N) / Real.log 2

theorem thin_one_lt_logb {N : ℕ} (hN : 1 ≤ N) : 1 < Real.logb 2 (3 + 1 / (N : ℝ)) := by
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  rw [Real.lt_logb_iff_rpow_lt (by norm_num) (by positivity), Real.rpow_one]
  have : (0 : ℝ) < 1 / N := by positivity
  linarith

theorem thin_logb_lt_two {N : ℕ} (hN : 2 ≤ N) : Real.logb 2 (3 + 1 / (N : ℝ)) < 2 := by
  have hNr : (2 : ℝ) ≤ N := by exact_mod_cast hN
  rw [Real.logb_lt_iff_lt_rpow (by norm_num) (by positivity)]
  have : (N : ℝ)⁻¹ ≤ 2⁻¹ := inv_anti₀ (by norm_num) hNr
  norm_num
  linarith

theorem thinTheta_lt_one {N : ℕ} (hN : 1 ≤ N) : thinTheta N < 1 := by
  unfold thinTheta
  rw [div_lt_one (by linarith [thin_one_lt_logb hN])]
  exact thin_one_lt_logb hN

theorem two_inv_lt_thinTheta {N : ℕ} (hN : 2 ≤ N) : (2 : ℝ)⁻¹ < thinTheta N := by
  unfold thinTheta
  rw [one_div, inv_lt_inv₀ (by norm_num) (by linarith [thin_one_lt_logb (by omega : 1 ≤ N)])]
  exact thin_logb_lt_two hN

/-- **Lo esencial:** `c_N < 1` para todo `N ≥ 2`, porque `θ_N ≠ 1/2` (`3 + 1/N ≠ 4`). -/
theorem thinConst_lt_one {N : ℕ} (hN : 2 ≤ N) : thinConst N < 1 := by
  unfold thinConst
  rw [div_lt_one (Real.log_pos (by norm_num))]
  exact Real.binEntropy_lt_log_two.2 (two_inv_lt_thinTheta hN).ne'

theorem thinConst_nonneg {N : ℕ} (hN : 2 ≤ N) : 0 ≤ thinConst N := by
  unfold thinConst
  exact div_nonneg (Real.binEntropy_nonneg (by linarith [two_inv_lt_thinTheta hN])
    (thinTheta_lt_one (by omega)).le) (Real.log_pos (by norm_num)).le

/-- La cota entrópica con el umbral `θ_N`: si `1 ≤ j ≤ A` y `A ≤ j · log₂(3 + 1/N)`, entonces
`C(A−1, j−1) ≤ 2^{c_N · A}`. -/
theorem thin_choose_pred_le_of_dense {N : ℕ} (hN : 2 ≤ N) (A j : ℕ) (hj1 : 1 ≤ j) (hj : j ≤ A)
    (hd : (A : ℝ) ≤ j * Real.logb 2 (3 + 1 / N)) :
    ((A - 1).choose (j - 1) : ℝ) ≤ (2 : ℝ) ^ ((A : ℝ) * thinConst N) := by
  have hL : 0 < Real.logb 2 (3 + 1 / (N : ℝ)) := by linarith [thin_one_lt_logb (by omega : 1 ≤ N)]
  refine thin_choose_pred_le_two_rpow (two_inv_lt_thinTheta hN).le (thinTheta_lt_one (by omega)).le
    A j hj1 hj ?_
  unfold thinTheta
  rw [div_mul_eq_mul_div, one_mul, div_le_iff₀ hL]
  exact hd

/-- Cota de clases: `|residueClasses j A| ≤ 2^{c_N · A}` bajo la densidad `A ≤ j · log₂(3 + 1/N)`. -/
theorem thin_card_residueClasses_le {N : ℕ} (hN : 2 ≤ N) {A j : ℕ} (hj1 : 1 ≤ j) (hj : j ≤ A)
    (hd : (A : ℝ) ≤ j * Real.logb 2 (3 + 1 / N)) :
    ((residueClasses j A).card : ℝ) ≤ (2 : ℝ) ^ ((A : ℝ) * thinConst N) := by
  refine le_trans ?_ (thin_choose_pred_le_of_dense hN A j hj1 hj hd)
  exact_mod_cast card_residueClasses_le hj1 A

/-- De la cota de clases a la fracción: entre los `2^A` impares mod `2^{A+1}`, la fracción
admisible es `≤ 2^{−(1 − c) · A}`. -/
theorem thin_fraction_le {c : ℝ} {A : ℕ} {s : Finset ℕ}
    (h : (s.card : ℝ) ≤ (2 : ℝ) ^ ((A : ℝ) * c)) :
    (s.card : ℝ) / 2 ^ A ≤ (2 : ℝ) ^ (-((A : ℝ) * (1 - c))) := by
  rw [div_le_iff₀ (by positivity)]
  calc (s.card : ℝ) ≤ (2 : ℝ) ^ ((A : ℝ) * c) := h
    _ = (2 : ℝ) ^ (-((A : ℝ) * (1 - c))) * 2 ^ A := by
      rw [← Real.rpow_natCast, ← Real.rpow_add (by norm_num)]
      congr 1; ring

/-! ## Pieza (2): de la cota ℕ a la densidad en `logb` -/

/-- `N^j · 2^A ≤ (3N+1)^j` ⇒ `A ≤ j · log₂(3 + 1/N)`. -/
theorem thin_dose_le_logb {N A j : ℕ} (hN : 0 < N) (h : N ^ j * 2 ^ A ≤ (3 * N + 1) ^ j) :
    (A : ℝ) ≤ j * Real.logb 2 (3 + 1 / N) := by
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have hcast : ((N : ℝ) ^ j * 2 ^ A) ≤ (3 * N + 1) ^ j := by exact_mod_cast h
  have hlog := Real.log_le_log (by positivity) hcast
  rw [Real.log_mul (by positivity) (by positivity), Real.log_pow, Real.log_pow,
    Real.log_pow] at hlog
  have e : (3 + 1 / N : ℝ) = (3 * N + 1) / N := by field_simp
  rw [Real.logb, e, Real.log_div (by positivity) hNr.ne', ← mul_div_assoc,
    le_div_iff₀ (Real.log_pos (by norm_num)), mul_sub]
  linarith

/-! ## El teorema -/

/-- **Una órbita divergente vive en un conjunto fino.** Si `n` es impar y diverge, para todo
`N ≥ 2` hay una cola `x = S^{i₀} n` y un `j₀ ≥ 1` tales que, para todo `j ≥ j₀`, con
`A = A(x, j)` las doses de los siguientes `j` pasos:

1. `x mod 2^{A+1}` es una de las clases de `residueClasses j A` (es la suya);
2. hay a lo sumo `2^{c_N · A}` de esas clases, con `c_N = thinConst N < 1`;
3. la densidad de doses está controlada: `A ≤ j · log₂(3 + 1/N)`.

Es la formalización exacta de "casi ningún número diverge": las clases donde una órbita
divergente puede vivir son una fracción `2^{−(1−c_N) A}` de los impares mod `2^{A+1}`. -/
theorem divergent_in_thin_set {n : ℕ} (hn : n % 2 = 1) (hdiv : SyracuseDivergent n)
    {N : ℕ} (hN : 2 ≤ N) :
    ∃ i₀ j₀, 1 ≤ j₀ ∧ ∀ j, j₀ ≤ j →
      let x := syracuse^[i₀] n
      let A := sExpSum x j
      x % 2 ^ (A + 1) ∈ residueClasses j A ∧
      ((residueClasses j A).card : ℝ) ≤ (2 : ℝ) ^ ((A : ℝ) * thinConst N) ∧
      (A : ℝ) ≤ j * Real.logb 2 (3 + 1 / N) := by
  obtain ⟨i₀, j₀, h⟩ := divergent_dose_bound hn hdiv N
  refine ⟨i₀, max j₀ 1, le_max_right _ _, fun j hj => ?_⟩
  intro x A
  have hx : x % 2 = 1 := iterate_syracuse_odd hn i₀
  have hj1 : 1 ≤ j := le_trans (le_max_right _ _) hj
  have hjA : j ≤ A := sExpSum_ge hx j
  have hd : (A : ℝ) ≤ j * Real.logb 2 (3 + 1 / N) :=
    thin_dose_le_logb (by omega) (h j (le_trans (le_max_left _ _) hj))
  exact ⟨thin_mod_mem_residueClasses hx j, thin_card_residueClasses_le hN hj1 hjA hd, hd⟩

/-- **Corolario: la fracción.** Bajo las mismas hipótesis, para todo `j ≥ j₀` la fracción de
las `2^A` clases impares mod `2^{A+1}` que son admisibles es `≤ 2^{−(1 − c_N) · A}`, con
`1 − c_N > 0` y `A ≥ j`, así que tiende a cero exponencialmente en `j`. -/
theorem divergent_in_thin_set_fraction {n : ℕ} (hn : n % 2 = 1) (hdiv : SyracuseDivergent n)
    {N : ℕ} (hN : 2 ≤ N) :
    0 < 1 - thinConst N ∧
    ∃ i₀ j₀, ∀ j, j₀ ≤ j →
      let x := syracuse^[i₀] n
      let A := sExpSum x j
      j ≤ A ∧
      x % 2 ^ (A + 1) ∈ residueClasses j A ∧
      ((residueClasses j A).card : ℝ) / 2 ^ A ≤ (2 : ℝ) ^ (-((A : ℝ) * (1 - thinConst N))) := by
  refine ⟨by linarith [thinConst_lt_one hN], ?_⟩
  obtain ⟨i₀, j₀, _, h⟩ := divergent_in_thin_set hn hdiv hN
  refine ⟨i₀, j₀, fun j hj => ?_⟩
  intro x A
  obtain ⟨hmem, hcard, _⟩ := h j hj
  exact ⟨sExpSum_ge (iterate_syracuse_odd hn i₀) j, hmem, thin_fraction_le hcard⟩

end Collatz
