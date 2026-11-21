import Mathlib.Analysis.Complex.ExponentialBounds
import Collatz.Forge.Basic
import Collatz.Forge.Invariants.VerifiedRange
import Collatz.Forge.Invariants.Log23

/-!
# Hercher formalizado: cota inferior explícita para la longitud de un ciclo

Bajo `VerifiedBelow M` (`M = 2^71`), `cycle_sandwich_of_verified` da, para un ciclo no trivial
de Syracuse de `k` pasos con `A` doses en total,

  `3^k < 2^A`   y   `2^A · M^k ≤ (3M + 1)^k`.

Tomando logaritmos: `0 < A·log 2 − k·log 3 ≤ k·log(1 + 1/(3M)) ≤ k/(3M)`. Con
`θ := log 3 / log 2 = log₂ 3`, esto dice que `k·θ` está **por debajo** del entero `A` a
distancia menor que `k/(3M·log 2) ≈ k · 2·10⁻²²`. Como `θ` es irracional y sus convergentes
son sus mejores aproximaciones, eso fuerza `k` enorme.

## Sin teoría de fracciones continuas

No usamos `GenContFract` ni el teorema de Legendre. Basta un lema de álgebra lineal entera:
si `p/q < θ < p'/q'` con `p'q − pq' = 1` (dos convergentes consecutivos, pero el lema no lo
necesita saber), entonces `(q, p)` y `(q', p')` son una base de `ℤ²`, así que todo par `(k, A)`
se escribe `k = aq + bq'`, `A = ap + bp'` con `a, b ∈ ℤ`, y

  `A − kθ = a·(p − qθ) + b·(p' − q'θ) = −a·e + b·e'`,   `e := qθ − p > 0`, `e' := p' − q'θ > 0`.

Para `0 < k < q + q'` los signos de `a, b` no pueden ser ambos `≥ 1` (daría `k ≥ q + q'`) ni
ambos `≤ 0` (daría `k ≤ 0`). Si `a ≥ 1, b ≤ 0` entonces `A − kθ ≤ 0`. Si `a ≤ 0, b ≥ 1`:
`a = 0, b = 1` es `k = q'` con `A − kθ = e'`; `a = 0, b ≥ 2` da `A − kθ ≥ 2e'`; `a ≤ −1` da
`A − kθ ≥ e + e'` (`cf_unimodular_gap`). Es decir: **por debajo de `q + q'`, la única forma
de que `kθ` quede justo debajo de un entero es `k = q'`, y nunca más cerca que `e'`.**

## Los números

Los convergentes 21 y 22 de `θ` (desarrollo `[1; 1, 1, 2, 2, 3, 1, 5, 2, 23, 2, 2, 1, 1, 55, 1,
4, 3, 1, 1, 15, 1, 9, 2, 5, …]`, denominadores `1, 1, 2, 5, 12, 41, 53, 306, 665, 15601, 31867,
79335, 111202, 190537, 10590737, 10781274, 53715833, 171928773, 225644606, 397573379,
6189245291, 6586818670, 65470613321, 137528045312, …`) son

  `p'/q' = 10439860591 / 6586818670 > θ`,   `p/q = 103768467013 / 65470613321 < θ`,

con `p'q − pq' = 1`, `e' ≈ 1.46·10⁻¹¹`, `e ≈ 6.65·10⁻¹²`. Los 25 dígitos de `Log23` certifican
`e' ≥ p' − q'·hi`, `e ≥ q·lo − p`, y con `log 2 > 0.6931471803` (`Real.log_two_gt_d9`) los
tres casos `k = q'`, `≥ 2e'`, `≥ e + e'` contradicen `A·log 2 − k·log 3 ≤ k/(3·2^71)` para
`k < q + q'`. Resultado (`hercher_lower_bound`):

  **todo ciclo no trivial tiene `k ≥ 72 057 431 991 = q + q'` pasos de Syracuse.**

Es exactamente el límite del método: en `k = q + q'` el propio `kθ` queda a `≈ 7.95·10⁻¹²`
debajo de un entero, menos que `k·log(1 + 1/(3·2^71))/log 2 ≈ 1.47·10⁻¹¹`, así que el sándwich
con `M = 2^71` no excluye ese `k`. Para ir más lejos hace falta más verificación (`M` mayor) o
más información sobre el ciclo (por ejemplo, la estructura de Eliahou/Simons–de Weger de los
elementos del ciclo, no solo el mínimo).
-/

namespace Collatz

/-! ## El lema unimodular -/

/-- **Lema unimodular.** Si `p/q < θ < p'/q'` y `p'q − pq' = 1`, entonces para todo entero
`0 < k < q + q'` y todo entero `A`: o bien `A − kθ ≤ 0`, o bien `k = q'` y `A − kθ ≥ p' − q'θ`,
o bien `A − kθ ≥ (qθ − p) + (p' − q'θ)`, o bien `A − kθ ≥ 2(p' − q'θ)`. -/
theorem cf_unimodular_gap {θ : ℝ} {p q p' q' k A : ℤ} (hdet : p' * q - p * q' = 1)
    (hq : 0 < q) (hq' : 0 < q') (he : (p : ℝ) < q * θ) (he' : (q' : ℝ) * θ < p')
    (hk : 0 < k) (hkK : k < q + q') :
    (A : ℝ) - k * θ ≤ 0 ∨
      (k = q' ∧ (p' : ℝ) - q' * θ ≤ A - k * θ) ∨
      ((q : ℝ) * θ - p) + (p' - q' * θ) ≤ A - k * θ ∨
      2 * ((p' : ℝ) - q' * θ) ≤ A - k * θ := by
  set a : ℤ := p' * k - q' * A with ha
  set b : ℤ := q * A - p * k with hb
  have hk' : k = a * q + b * q' := by
    rw [ha, hb]; linear_combination (-k) * hdet
  have hdetR : (p' : ℝ) * q - p * q' = 1 := by exact_mod_cast hdet
  have key : (A : ℝ) - k * θ = a * (p - q * θ) + b * (p' - q' * θ) := by
    rw [ha, hb]; push_cast
    linear_combination (-((A : ℝ) - k * θ)) * hdetR
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq
  have hq'R : (0 : ℝ) < q' := by exact_mod_cast hq'
  rcases le_or_gt a 0 with ha0 | ha1
  · rcases le_or_gt b 0 with hb0 | hb1
    · exfalso
      have : a * q ≤ 0 := mul_nonpos_of_nonpos_of_nonneg ha0 hq.le
      have : b * q' ≤ 0 := mul_nonpos_of_nonpos_of_nonneg hb0 hq'.le
      omega
    · -- `a ≤ 0`, `b ≥ 1`
      have hb1' : (1 : ℝ) ≤ b := by exact_mod_cast hb1
      have ha0' : (a : ℝ) ≤ 0 := by exact_mod_cast ha0
      have hae : 0 ≤ (a : ℝ) * (p - q * θ) :=
        mul_nonneg_of_nonpos_of_nonpos ha0' (by linarith)
      rcases eq_or_lt_of_le ha0 with ha0e | ha0lt
      · -- `a = 0`
        have haR : (a : ℝ) = 0 := by exact_mod_cast ha0e
        have hb1z : 1 ≤ b := by omega
        rcases eq_or_lt_of_le hb1z with hb1e | hb2
        · -- `a = 0`, `b = 1`
          right; left
          refine ⟨by rw [hk', ha0e, ← hb1e]; ring, ?_⟩
          rw [key, haR, ← hb1e]; push_cast; linarith
        · -- `a = 0`, `b ≥ 2`
          right; right; right
          have hb2' : (2 : ℝ) ≤ b := by exact_mod_cast hb2
          rw [key, haR]
          nlinarith
      · -- `a ≤ -1`, `b ≥ 1`
        right; right; left
        have ha1z : a ≤ -1 := by omega
        have ha1' : (a : ℝ) ≤ -1 := by exact_mod_cast ha1z
        rw [key]
        nlinarith
  · rcases le_or_gt b 0 with hb0 | hb1
    · -- `a ≥ 1`, `b ≤ 0`
      left
      have ha1' : (1 : ℝ) ≤ a := by exact_mod_cast ha1
      have hb0' : (b : ℝ) ≤ 0 := by exact_mod_cast hb0
      rw [key]
      nlinarith
    · exfalso
      have : q ≤ a * q := le_mul_of_one_le_left hq.le ha1
      have : q' ≤ b * q' := le_mul_of_one_le_left hq'.le hb1
      omega

/-! ## Del sándwich entero a la desigualdad logarítmica -/

/-- Lectura logarítmica del sándwich: `0 < A·log 2 − k·log 3 ≤ k/(3M)`. -/
theorem cf_cycle_gap {M k A : ℕ} (hM : 0 < M) (h1 : 3 ^ k < 2 ^ A)
    (h2 : 2 ^ A * M ^ k ≤ (3 * M + 1) ^ k) :
    0 < (A : ℝ) * Real.log 2 - k * Real.log 3 ∧
      (A : ℝ) * Real.log 2 - k * Real.log 3 ≤ k / (3 * M) := by
  have hMr : (0 : ℝ) < M := by exact_mod_cast hM
  constructor
  · have h1' : (3 : ℝ) ^ k < 2 ^ A := by exact_mod_cast h1
    have := Real.log_lt_log (by positivity) h1'
    rw [Real.log_pow, Real.log_pow] at this
    linarith
  · have h2' : (2 : ℝ) ^ A * (M : ℝ) ^ k ≤ (3 * M + 1) ^ k := by exact_mod_cast h2
    have hlog := Real.log_le_log (by positivity) h2'
    rw [Real.log_mul (by positivity) (by positivity), Real.log_pow, Real.log_pow,
      Real.log_pow] at hlog
    have hsplit : Real.log (3 * M + 1) = Real.log 3 + Real.log M + Real.log (1 + 1 / (3 * M)) := by
      rw [← Real.log_mul (by norm_num) hMr.ne', ← Real.log_mul (by positivity) (by positivity)]
      congr 1
      field_simp
    have hsmall : Real.log (1 + 1 / (3 * M)) ≤ 1 / (3 * M) := by
      have := Real.log_le_sub_one_of_pos (x := 1 + 1 / (3 * M)) (by positivity)
      linarith
    have hk0 : (0 : ℝ) ≤ k := by positivity
    have : (k : ℝ) * Real.log (1 + 1 / (3 * M)) ≤ k * (1 / (3 * M)) :=
      mul_le_mul_of_nonneg_left hsmall hk0
    rw [hsplit] at hlog
    calc (A : ℝ) * Real.log 2 - k * Real.log 3
        ≤ k * Real.log (1 + 1 / (3 * M)) := by linarith
      _ ≤ k * (1 / (3 * M)) := this
      _ = k / (3 * M) := by ring

/-! ## El teorema -/

/-- **Hercher formalizado.** Bajo `VerifiedBelow (2^71)`, todo ciclo no trivial de Syracuse tiene
al menos `72 057 431 991 = 6586818670 + 65470613321` pasos (suma de los denominadores de los
convergentes 21 y 22 de `log₂ 3`). -/
theorem hercher_lower_bound {n k : ℕ} (hV : VerifiedBelow (2 ^ 71)) (hn : n % 2 = 1)
    (hk : 0 < k) (h : syracuse^[k] n = n) (hne : n ≠ 1) : 72057431991 ≤ k := by
  obtain ⟨h1, h2⟩ := cycle_sandwich_of_verified hV hn hk h hne
  obtain ⟨hpos, hle⟩ := cf_cycle_gap (by positivity) h1 h2
  set A := sExpSum n k with hA
  have hMcast : ((2 ^ 71 : ℕ) : ℝ) = 2 ^ 71 := by norm_num
  rw [hMcast] at hle
  by_contra hlt
  push Not at hlt
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hl2 := Real.log_two_gt_d9
  set θ := Real.log 3 / Real.log 2 with hθ
  have hθlo : (1584962500721156181453738929 : ℝ) / 1000000000000000000000000000 < θ := log2_3_gt
  have hθhi : θ < (1584962500721156181453738949 : ℝ) / 1000000000000000000000000000 := log2_3_lt
  -- `A − kθ = (A log 2 − k log 3) / log 2`
  set D := (A : ℝ) * Real.log 2 - k * Real.log 3 with hD
  have hgap : (A : ℝ) - k * θ = D / Real.log 2 := by
    rw [hD, hθ]; field_simp
  have hkR : (k : ℝ) < 72057431991 := by exact_mod_cast hlt
  have hcases := cf_unimodular_gap (θ := θ) (p := 103768467013) (q := 65470613321)
    (p' := 10439860591) (q' := 6586818670) (k := k) (A := A) (by norm_num) (by norm_num)
    (by norm_num) (by push_cast; linarith) (by push_cast; linarith) (by exact_mod_cast hk)
    (by omega)
  push_cast at hcases
  rw [hgap] at hcases
  -- cotas racionales para `e' = p' − q'θ` y `e = qθ − p`
  have he' : (10439860591 : ℝ) - 6586818670 * θ
      ≥ 10439860591 - 6586818670 * (1584962500721156181453738949 / 1000000000000000000000000000) := by
    linarith
  have he : (65470613321 : ℝ) * θ - 103768467013
      ≥ 65470613321 * (1584962500721156181453738929 / 1000000000000000000000000000) - 103768467013 := by
    linarith
  rcases hcases with hc | ⟨hkq, hc⟩ | hc | hc
  · exact absurd (div_pos hpos hlog2) (not_lt.mpr hc)
  · rw [le_div_iff₀ hlog2] at hc
    have hkq' : (k : ℝ) = 6586818670 := by exact_mod_cast hkq
    rw [hkq'] at hle
    have := mul_le_mul he'.le hl2.le (by norm_num) (by linarith)
    linarith
  · rw [le_div_iff₀ hlog2] at hc
    have := mul_le_mul (add_le_add he.le he'.le) hl2.le (by norm_num) (by linarith)
    have hle' : D < 72057431991 / (3 * 2 ^ 71) := by
      refine hle.trans_lt ?_
      exact div_lt_div_of_pos_right hkR (by positivity)
    linarith
  · rw [le_div_iff₀ hlog2] at hc
    have := mul_le_mul he'.le hl2.le (by norm_num) (by linarith)
    have hle' : D < 72057431991 / (3 * 2 ^ 71) := by
      refine hle.trans_lt ?_
      exact div_lt_div_of_pos_right hkR (by positivity)
    linarith

end Collatz
