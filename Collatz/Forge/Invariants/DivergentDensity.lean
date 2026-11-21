import Collatz.Forge.Basic
import Collatz.Forge.Invariants.OrbitInequality
import Collatz.Forge.Invariants.ParityAperiodic

/-!
# Densidad de doses en órbitas divergentes

Dos pasos:

1. **No acotada ⇒ tiende a infinito** (`syracuse_eventually_ge_of_divergent`). Una órbita
   determinista que vuelve infinitas veces por debajo de `N` repite un valor (pigeonhole
   sobre `Fin N`), luego es periódica desde ahí, luego acotada. Así que "divergente" en el
   sentido débil (`∀ B, ∃ k, B < S^k n`) implica el fuerte (`∀ N, ∃ i₀, ∀ i ≥ i₀, N ≤ S^i n`).

2. **La constraint.** Desde un `i₀` tal que toda la cola es `≥ N`, y como la órbita tiende a
   infinito, para todo `j` grande `S^{i₀+j} n ≥ S^{i₀} n`. Entonces `ascent_bound` da

     `N^j · 2^{A(i₀, j)} ≤ (3N + 1)^j`   para todo `j ≥ j₀`,

   donde `A(i₀, j) = sExpSum (S^{i₀} n) j` son las doses quitadas en los `j` pasos que siguen
   a `i₀`. En logaritmos: para todo `ε > 0` hay una cola donde
   `A(i₀, j) · log 2 ≤ j · (log 3 + ε)` para todo `j ≥ j₀`.

   Lectura: en una órbita divergente, las doses por paso impar no superan `log₂ 3 ≈ 1.585`
   en promedio a largo plazo. Equivalentemente, en el mapa `T` la fracción de pasos impares
   es al menos `log 2 / log 3 ≈ 0.63`. Esto es la heurística estándar (Terras, Lagarias)
   convertida en teorema sobre contraejemplos hipotéticos.
-/

namespace Collatz

open Finset

/-- Dos iterados iguales ⇒ periódico desde el primero. -/
theorem syracuse_periodic_of_iterate_eq {n i j : ℕ} (hij : i < j)
    (h : syracuse^[i] n = syracuse^[j] n) :
    syracuse^[j - i] (syracuse^[i] n) = syracuse^[i] n := by
  rw [← Function.iterate_add_apply, Nat.sub_add_cancel hij.le, h]

/-- **No acotada ⇒ tiende a infinito.** -/
theorem syracuse_eventually_ge_of_divergent {n : ℕ} (hdiv : SyracuseDivergent n) (N : ℕ) :
    ∃ i₀, ∀ i, i₀ ≤ i → N ≤ syracuse^[i] n := by
  by_contra hcon
  push Not at hcon
  -- el conjunto de índices con valor < N es infinito
  set s : Set ℕ := {i | syracuse^[i] n < N} with hs
  have hinf : s.Infinite := by
    apply Set.infinite_of_forall_exists_gt
    intro a
    obtain ⟨i, hi, hlt⟩ := hcon (a + 1)
    exact ⟨i, hlt, by omega⟩
  -- pigeonhole en Fin N
  have hmaps : Set.MapsTo (fun i => syracuse^[i] n) s (Set.Iio N) := fun i hi => hi
  obtain ⟨i, _, j, _, hij, heq⟩ :=
    hinf.exists_ne_map_eq_of_mapsTo hmaps (Set.finite_Iio N)
  rcases Nat.lt_or_gt_of_ne hij with hlt | hlt
  · exact not_syracuseDivergent_of_periodic (Nat.sub_pos_of_lt hlt)
      (syracuse_periodic_of_iterate_eq hlt heq) hdiv
  · exact not_syracuseDivergent_of_periodic (Nat.sub_pos_of_lt hlt)
      (syracuse_periodic_of_iterate_eq hlt heq.symm) hdiv

/-- **Densidad de doses (versión ℕ).** En una órbita divergente, para todo `N` hay una cola
desde `i₀` y un `j₀` tales que `N^j · 2^{A(i₀,j)} ≤ (3N+1)^j` para todo `j ≥ j₀`. -/
theorem divergent_dose_bound {n : ℕ} (hn : n % 2 = 1) (hdiv : SyracuseDivergent n) (N : ℕ) :
    ∃ i₀ j₀, ∀ j, j₀ ≤ j →
      N ^ j * 2 ^ sExpSum (syracuse^[i₀] n) j ≤ (3 * N + 1) ^ j := by
  obtain ⟨i₀, hi₀⟩ := syracuse_eventually_ge_of_divergent hdiv N
  obtain ⟨i₁, hi₁⟩ := syracuse_eventually_ge_of_divergent hdiv (syracuse^[i₀] n)
  refine ⟨i₀, i₁, fun j hj => ?_⟩
  have hx : 0 < syracuse^[i₀] n := by have := iterate_syracuse_odd hn i₀; omega
  apply ascent_bound j hx
  · intro i _
    rw [← Function.iterate_add_apply]
    exact hi₀ _ (by omega)
  · rw [← Function.iterate_add_apply]
    exact hi₁ _ (by omega)

/-- `log (3 + 1/N) ≤ log 3 + 1/(3N)`. -/
theorem log_three_add_inv_le {N : ℕ} (hN : 0 < N) :
    Real.log (3 + 1 / N) ≤ Real.log 3 + 1 / (3 * N) := by
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have h1 : (3 + 1 / N : ℝ) = 3 * (1 + 1 / (3 * N)) := by field_simp
  rw [h1, Real.log_mul (by norm_num) (by positivity)]
  have := Real.log_le_sub_one_of_pos (x := 1 + 1 / (3 * N : ℝ)) (by positivity)
  linarith

/-- **Densidad de doses (versión log).** En una órbita divergente, para todo `ε > 0` hay
una cola desde `i₀` y un `j₀` tales que `A(i₀,j) · log 2 ≤ j · (log 3 + ε)` para `j ≥ j₀`. -/
theorem divergent_dose_density {n : ℕ} (hn : n % 2 = 1) (hdiv : SyracuseDivergent n)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ i₀ j₀, ∀ j, j₀ ≤ j →
      (sExpSum (syracuse^[i₀] n) j : ℝ) * Real.log 2 ≤ j * (Real.log 3 + ε) := by
  obtain ⟨N, hN⟩ := exists_nat_gt (1 / (3 * ε))
  have hNpos : 0 < N := by
    have : (0 : ℝ) < N := lt_of_le_of_lt (by positivity) hN
    exact_mod_cast this
  obtain ⟨i₀, hi₀⟩ := syracuse_eventually_ge_of_divergent hdiv N
  obtain ⟨i₁, hi₁⟩ := syracuse_eventually_ge_of_divergent hdiv (syracuse^[i₀] n)
  refine ⟨i₀, i₁, fun j hj => ?_⟩
  have hx : 0 < syracuse^[i₀] n := by have := iterate_syracuse_odd hn i₀; omega
  have hlog := ascent_bound_log j hNpos hx
    (fun i _ => by rw [← Function.iterate_add_apply]; exact hi₀ _ (by omega))
    (by rw [← Function.iterate_add_apply]; exact hi₁ _ (by omega))
  have hNr : (0 : ℝ) < N := by exact_mod_cast hNpos
  have hε' : 1 / (3 * N : ℝ) ≤ ε := by
    rw [div_le_iff₀ (by positivity)]
    rw [div_lt_iff₀ (by positivity)] at hN
    linarith
  have hj' : (0 : ℝ) ≤ j := by positivity
  calc (sExpSum (syracuse^[i₀] n) j : ℝ) * Real.log 2
      ≤ j * Real.log (3 + 1 / N) := hlog
    _ ≤ j * (Real.log 3 + 1 / (3 * N)) := by gcongr; exact log_three_add_inv_le hNpos
    _ ≤ j * (Real.log 3 + ε) := by gcongr

end Collatz
