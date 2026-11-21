import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Log.Base

/-!
# Cotas racionales certificadas de `log₂ 3`

`log₂ 3 = log 3 / log 2 ≈ 1.5849625007211561814537389…` gobierna la aproximación diofántica
que aparece en los ciclos de Collatz (`3^k < 2^A`, `A = ⌊k log₂ 3⌋ + 1`, ver `CycleDoses`).
Para reproducir cotas del tipo Hercher hacen falta decenas de dígitos certificados por el
kernel, no los 9 de `Real.log_two_gt_d9`.

## Idea

Escribimos todo con la serie de `artanh`, que Mathlib ya acota por ambos lados
(`Real.sum_range_le_log_div`, `Real.log_div_le_sum_range_add`):

  `½ log((1+x)/(1−x)) = Σ_{i≥0} x^{2i+1}/(2i+1)`,   resto tras `n` términos `≤ x^{2n+1}/(1−x²)`.

* `a := ½ log 2 = artanh (1/3)`      (porque `(1+1/3)/(1−1/3) = 2`), razón `1/9` por término.
* `b := ½ log (3/2) = artanh (1/5)`  (porque `(1+1/5)/(1−1/5) = 3/2`), razón `1/25` por término.

Entonces `log 3 = 2a + 2b`, `log 2 = 2a` y `log₂ 3 = 1 + b/a`. Con `a ∈ [A₋, A₊]`,
`b ∈ [B₋, B₊]` racionales explícitos, `1 + B₋/A₊ < log₂ 3 < 1 + B₊/A₋`. Las sumas parciales
se evalúan con `norm_num [Finset.sum_range_succ]` (aritmética racional exacta, verificada
por el kernel); los literales `A±`, `B±` son redondeos decimales de esas sumas, calculados
con `fractions.Fraction` en Python y comprobados aquí.

Con 27 términos para `a` y 19 para `b` el intervalo final tiene ancho `2·10⁻²⁶`
(25 dígitos correctos) y el archivo compila en ~2 s. La misma cadena con 54 y 37 términos
da 50 dígitos en el mismo tiempo: el cuello de botella no es el kernel.
-/

namespace Collatz

open Finset

/-- `½ log 2 = artanh (1/3)`. -/
theorem half_log_two_eq :
    1 / 2 * Real.log ((1 + 1 / 3) / (1 - 1 / 3)) = 1 / 2 * Real.log 2 := by
  rw [show ((1 : ℝ) + 1 / 3) / (1 - 1 / 3) = 2 by norm_num]

/-- `½ log (3/2) = artanh (1/5)`. -/
theorem half_log_three_half_eq :
    1 / 2 * Real.log ((1 + 1 / 5) / (1 - 1 / 5)) = 1 / 2 * (Real.log 3 - Real.log 2) := by
  rw [show ((1 : ℝ) + 1 / 5) / (1 - 1 / 5) = 3 / 2 by norm_num,
    Real.log_div (by norm_num) (by norm_num)]

/-- Cota inferior de `½ log 2`: suma parcial de 27 términos de la serie en `x = 1/3`. -/
theorem half_log_two_ge :
    (17328679513998632735430803 : ℝ) / 50000000000000000000000000 ≤ 1 / 2 * Real.log 2 := by
  rw [← half_log_two_eq]
  refine le_trans ?_ (Real.sum_range_le_log_div (x := 1 / 3) (by norm_num) (by norm_num) 27)
  norm_num [Finset.sum_range_succ]

/-- Cota superior de `½ log 2`: suma parcial más el resto `(1/3)^55 / (1 - 1/9)`. -/
theorem half_log_two_le :
    1 / 2 * Real.log 2 ≤ (86643397569993163677154017 : ℝ) / 250000000000000000000000000 := by
  rw [← half_log_two_eq]
  refine le_trans
    (Real.log_div_le_sum_range_add (x := 1 / 3) (by norm_num) (by norm_num) 27) ?_
  norm_num [Finset.sum_range_succ]

/-- Cota inferior de `½ log (3/2)`: suma parcial de 19 términos de la serie en `x = 1/5`. -/
theorem half_log_three_half_ge :
    (202732554054082190989006557 : ℝ) / 1000000000000000000000000000
      ≤ 1 / 2 * (Real.log 3 - Real.log 2) := by
  rw [← half_log_three_half_eq]
  refine le_trans ?_ (Real.sum_range_le_log_div (x := 1 / 5) (by norm_num) (by norm_num) 19)
  norm_num [Finset.sum_range_succ]

/-- Cota superior de `½ log (3/2)`: suma parcial más el resto `(1/5)^39 / (1 - 1/25)`. -/
theorem half_log_three_half_le :
    1 / 2 * (Real.log 3 - Real.log 2)
      ≤ (202732554054082190989006559 : ℝ) / 1000000000000000000000000000 := by
  rw [← half_log_three_half_eq]
  refine le_trans
    (Real.log_div_le_sum_range_add (x := 1 / 5) (by norm_num) (by norm_num) 19) ?_
  norm_num [Finset.sum_range_succ]

/-- `log₂ 3 > 1.584962500721156181453738929` (25 dígitos correctos). -/
theorem log2_3_gt :
    (1584962500721156181453738929 : ℝ) / 1000000000000000000000000000
      < Real.log 3 / Real.log 2 := by
  have h2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  rw [lt_div_iff₀ h2]
  nlinarith [half_log_two_ge, half_log_two_le, half_log_three_half_ge, half_log_three_half_le]

/-- `log₂ 3 < 1.584962500721156181453738949` (25 dígitos correctos). -/
theorem log2_3_lt :
    Real.log 3 / Real.log 2
      < (1584962500721156181453738949 : ℝ) / 1000000000000000000000000000 := by
  have h2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  rw [div_lt_iff₀ h2]
  nlinarith [half_log_two_ge, half_log_two_le, half_log_three_half_ge, half_log_three_half_le]

/-- Las mismas cotas escritas para `Real.logb 2 3`. -/
theorem logb_two_three_bounds :
    (1584962500721156181453738929 : ℝ) / 1000000000000000000000000000 < Real.logb 2 3 ∧
      Real.logb 2 3 < (1584962500721156181453738949 : ℝ) / 1000000000000000000000000000 := by
  rw [← Real.log_div_log]
  exact ⟨log2_3_gt, log2_3_lt⟩

end Collatz
