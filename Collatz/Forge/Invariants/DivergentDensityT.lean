import Collatz.Forge.Basic
import Collatz.Forge.Invariants.SyracuseCycleEquation
import Collatz.Forge.Invariants.ParityAperiodic
import Collatz.Forge.Invariants.DivergentDensity

/-!
# Densidad de pasos impares en el mapa `T` para órbitas divergentes

`DivergentDensity.lean` prueba que en una órbita divergente de Syracuse las doses por paso
impar no superan `log₂ 3` en promedio: `A(i₀, j) · log 2 ≤ j · (log 3 + ε)` para todo `j`
grande. Aquí traducimos eso a la formulación estándar de la literatura (Terras, Lagarias),
sobre el mapa acelerado `T n = n/2` (par) o `(3n+1)/2` (impar).

## Puente Syracuse ↔ `T`

Un paso de Syracuse desde un impar `x` con exponente `a = sExp x = nu2 (3x+1)` son
exactamente `a` pasos de `T`: el primero es impar (`T x = (3x+1)/2`) y los `a − 1` restantes
son pares (divisiones por `2`), hasta llegar a `syracuse x = (3x+1)/2^a`:

* `T_iterate_sExp_eq_syracuse`: `T^[sExp x] x = syracuse x`.
* `T_iterate_sExpSum_eq_syracuse_iterate`: `T^[sExpSum x j] x = syracuse^[j] x`.

Es decir, `j` pasos de Syracuse con `A = sExpSum x j` doses son `A` pasos de `T`, de los
cuales exactamente `j` son impares (los puntos de partida de cada bloque):

* `oddSteps x m := Σ_{i<m} T^[i] x % 2` cuenta los pasos impares entre los primeros `m`.
* `oddSteps_sExpSum`: `oddSteps x (sExpSum x j) = j`.

## Constraint de densidad en `T`

Combinando con `divergent_dose_density`: si `n` es impar y su órbita de Syracuse diverge,
para todo `ε > 0` hay una cola `y = S^{i₀} n` y un `m₀` tales que

* (`divergent_odd_density_T_exact`) en los `m = sExpSum y j` con `j ≥ j₀`:
  `m · log 2 ≤ oddSteps y m · (log 3 + ε)`;
* (`divergent_odd_density_T`) para **todo** `m ≥ m₀`:
  `m · log 2 ≤ (oddSteps y m + 1) · (log 3 + ε)`.

Lectura: en una órbita divergente, la fracción de pasos impares de `T` es asintóticamente
`≥ log 2 / log 3 ≈ 0.63`. La heurística probabilística dice que "típicamente" es `1/2`, lo
que da tamaño decreciente (`(3/2)^{1/2} · (1/2)^{1/2} < 1`); una órbita divergente tiene
que ser persistentemente atípica.
-/

namespace Collatz

open Finset

/-! ## `T` sobre múltiplos de potencias de 2 -/

/-- `j` pasos de `T` en un múltiplo de `2^j` son `j` divisiones por `2`. -/
theorem T_iterate_of_pow_dvd {x : ℕ} (j : ℕ) (h : 2 ^ j ∣ x) :
    T^[j] x = x / 2 ^ j := by
  induction j with
  | zero => simp
  | succ j ih =>
    have hj : 2 ^ j ∣ x := (pow_dvd_pow 2 (Nat.le_succ j)).trans h
    rw [Function.iterate_succ_apply', ih hj, pow_succ, ← Nat.div_div_eq_div_mul]
    apply T_of_even
    obtain ⟨c, hc⟩ := h
    rw [hc, pow_succ, mul_assoc, Nat.mul_div_cancel_left _ (pow_pos two_pos j)]
    omega

/-- Un paso de Syracuse desde un impar `x` son exactamente `sExp x` pasos de `T`. -/
theorem T_iterate_sExp_eq_syracuse {x : ℕ} (hx : x % 2 = 1) :
    T^[sExp x] x = syracuse x := by
  obtain ⟨b, hb⟩ : ∃ b, sExp x = b + 1 := ⟨sExp x - 1, by have := sExp_pos_of_odd hx; omega⟩
  have hmul := two_pow_sExp_mul_syracuse x
  rw [hb, pow_succ] at hmul
  have hT : T x = 2 ^ b * syracuse x := by
    rw [T_of_odd hx, ← hmul]
    rw [show 2 ^ b * 2 * syracuse x = 2 * (2 ^ b * syracuse x) by ring]
    exact Nat.mul_div_cancel_left _ two_pos
  rw [hb, Function.iterate_succ_apply, hT, T_iterate_of_pow_dvd b (dvd_mul_right _ _),
    Nat.mul_div_cancel_left _ (pow_pos two_pos b)]

/-- `j` pasos de Syracuse desde un impar `x` son exactamente `sExpSum x j` pasos de `T`. -/
theorem T_iterate_sExpSum_eq_syracuse_iterate {x : ℕ} (hx : x % 2 = 1) (j : ℕ) :
    T^[sExpSum x j] x = syracuse^[j] x := by
  induction j with
  | zero => simp [sExpSum_zero]
  | succ j ih =>
    rw [sExpSum_succ, add_comm, Function.iterate_add_apply, ih,
      T_iterate_sExp_eq_syracuse (iterate_syracuse_odd hx j), Function.iterate_succ_apply']

/-! ## Contador de pasos impares -/

/-- Número de pasos impares entre los primeros `m` pasos de `T` desde `x`:
`#{i < m | T^[i] x impar}`, escrito como suma de `T^[i] x % 2`. -/
def oddSteps (x m : ℕ) : ℕ := ∑ i ∈ range m, T^[i] x % 2

theorem oddSteps_zero (x : ℕ) : oddSteps x 0 = 0 := by simp [oddSteps]

theorem oddSteps_succ (x m : ℕ) : oddSteps x (m + 1) = oddSteps x m + T^[m] x % 2 :=
  sum_range_succ _ _

theorem oddSteps_one (x : ℕ) : oddSteps x 1 = x % 2 := by
  rw [oddSteps_succ, oddSteps_zero]; simp

/-- Los pasos impares se acumulan a lo largo de la órbita de `T`. -/
theorem oddSteps_add (x m k : ℕ) :
    oddSteps x (m + k) = oddSteps x m + oddSteps (T^[m] x) k := by
  unfold oddSteps
  rw [sum_range_add]
  congr 1
  refine sum_congr rfl fun i _ => ?_
  rw [← Function.iterate_add_apply, add_comm]

theorem oddSteps_le (x m : ℕ) : oddSteps x m ≤ m := by
  unfold oddSteps
  calc ∑ i ∈ range m, T^[i] x % 2 ≤ ∑ _i ∈ range m, 1 :=
        sum_le_sum fun i _ => by omega
    _ = m := by simp

theorem oddSteps_mono (x : ℕ) {m m' : ℕ} (h : m ≤ m') : oddSteps x m ≤ oddSteps x m' := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le h
  rw [oddSteps_add]
  omega

/-- Desde un múltiplo de `2^b`, los primeros `b` pasos de `T` son todos pares. -/
theorem oddSteps_of_pow_dvd {y b : ℕ} (h : 2 ^ b ∣ y) : oddSteps y b = 0 := by
  unfold oddSteps
  apply sum_eq_zero
  intro i hi
  have hi := mem_range.mp hi
  have hdvd : 2 ^ i ∣ y := (pow_dvd_pow 2 hi.le).trans h
  rw [T_iterate_of_pow_dvd i hdvd]
  obtain ⟨d, hd⟩ : 2 ^ (i + 1) ∣ y := (pow_dvd_pow 2 hi).trans h
  rw [hd, pow_succ, mul_assoc, Nat.mul_div_cancel_left _ (pow_pos two_pos i)]
  omega

/-- Un bloque de Syracuse desde un impar contiene exactamente un paso impar de `T`. -/
theorem oddSteps_sExp {x : ℕ} (hx : x % 2 = 1) : oddSteps x (sExp x) = 1 := by
  obtain ⟨b, hb⟩ : ∃ b, sExp x = b + 1 := ⟨sExp x - 1, by have := sExp_pos_of_odd hx; omega⟩
  have hmul := two_pow_sExp_mul_syracuse x
  rw [hb, pow_succ] at hmul
  have hT : T x = 2 ^ b * syracuse x := by
    rw [T_of_odd hx, ← hmul]
    rw [show 2 ^ b * 2 * syracuse x = 2 * (2 ^ b * syracuse x) by ring]
    exact Nat.mul_div_cancel_left _ two_pos
  rw [hb, add_comm, oddSteps_add, oddSteps_one, hx, Function.iterate_one, hT,
    oddSteps_of_pow_dvd (dvd_mul_right _ _)]

/-- **Conteo exacto.** Los `sExpSum x j` pasos de `T` que cubren `j` pasos de Syracuse
contienen exactamente `j` pasos impares. -/
theorem oddSteps_sExpSum {x : ℕ} (hx : x % 2 = 1) (j : ℕ) :
    oddSteps x (sExpSum x j) = j := by
  induction j with
  | zero => simp [sExpSum_zero, oddSteps_zero]
  | succ j ih =>
    rw [sExpSum_succ, oddSteps_add, ih, T_iterate_sExpSum_eq_syracuse_iterate hx,
      oddSteps_sExp (iterate_syracuse_odd hx j)]

/-- Entre `sExpSum x j` y `sExpSum x (j+1)` hay al menos `j` pasos impares. -/
theorem oddSteps_ge_of_sExpSum_le {x : ℕ} (hx : x % 2 = 1) {j m : ℕ}
    (h : sExpSum x j ≤ m) : j ≤ oddSteps x m := by
  rw [← oddSteps_sExpSum hx j]
  exact oddSteps_mono x h

/-! ## Monotonía de `sExpSum` -/

theorem sExpSum_mono (x : ℕ) {j j' : ℕ} (h : j ≤ j') : sExpSum x j ≤ sExpSum x j' := by
  unfold sExpSum
  exact sum_le_sum_of_subset (range_mono h)

theorem sExpSum_lt_of_lt {x : ℕ} (hx : x % 2 = 1) {j j' : ℕ} (h : j < j') :
    sExpSum x j < sExpSum x j' := by
  calc sExpSum x j < sExpSum x (j + 1) := by
        rw [sExpSum_succ]; have := sExp_pos_of_odd (iterate_syracuse_odd hx j); omega
    _ ≤ sExpSum x j' := sExpSum_mono x h

/-- Todo `m` cae en un bloque: existe `j` con `sExpSum x j ≤ m < sExpSum x (j + 1)`. -/
theorem exists_sExpSum_le_lt {x : ℕ} (hx : x % 2 = 1) (m : ℕ) :
    ∃ j, sExpSum x j ≤ m ∧ m < sExpSum x (j + 1) := by
  have hex : ∃ j, m < sExpSum x j := ⟨m + 1, by have := sExpSum_ge hx (m + 1); omega⟩
  classical
  set j' := Nat.find hex with hj'
  have hspec : m < sExpSum x j' := Nat.find_spec hex
  have hpos : j' ≠ 0 := by
    intro h0
    rw [h0, sExpSum_zero] at hspec
    omega
  refine ⟨j' - 1, ?_, ?_⟩
  · have := Nat.find_min hex (show j' - 1 < j' by omega)
    omega
  · rw [Nat.sub_add_cancel (by omega)]
    exact hspec

/-! ## La constraint de densidad en `T` -/

/-- **Densidad de pasos impares (versión exacta).** Si `n` es impar y diverge en Syracuse,
para todo `ε > 0` hay una cola `y = S^{i₀} n` y un `j₀` tales que, en los instantes
`m = sExpSum y j` (fin del `j`-ésimo bloque) con `j ≥ j₀`,
`m · log 2 ≤ oddSteps y m · (log 3 + ε)`. -/
theorem divergent_odd_density_T_exact {n : ℕ} (hn : n % 2 = 1) (hdiv : SyracuseDivergent n)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ i₀ j₀, ∀ j, j₀ ≤ j →
      (sExpSum (syracuse^[i₀] n) j : ℝ) * Real.log 2 ≤
        (oddSteps (syracuse^[i₀] n) (sExpSum (syracuse^[i₀] n) j) : ℝ) * (Real.log 3 + ε) := by
  obtain ⟨i₀, j₀, h⟩ := divergent_dose_density hn hdiv hε
  refine ⟨i₀, j₀, fun j hj => ?_⟩
  rw [oddSteps_sExpSum (iterate_syracuse_odd hn i₀) j]
  exact h j hj

/-- **Densidad de pasos impares en `T` (formulación estándar).** Si `n` es impar y su órbita
de Syracuse diverge, para todo `ε > 0` hay una cola `y = S^{i₀} n` y un `m₀` tales que para
todo `m ≥ m₀`:

  `m · log 2 ≤ (oddSteps y m + 1) · (log 3 + ε)`.

Es decir, la fracción de pasos impares entre los primeros `m` pasos de `T` es
asintóticamente `≥ log 2 / log 3 ≈ 0.63`. -/
theorem divergent_odd_density_T {n : ℕ} (hn : n % 2 = 1) (hdiv : SyracuseDivergent n)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ i₀ m₀, ∀ m : ℕ, m₀ ≤ m →
      (m : ℝ) * Real.log 2 ≤
        ((oddSteps (syracuse^[i₀] n) m : ℝ) + 1) * (Real.log 3 + ε) := by
  obtain ⟨i₀, j₀, h⟩ := divergent_dose_density hn hdiv hε
  set y := syracuse^[i₀] n with hy
  have hyodd : y % 2 = 1 := iterate_syracuse_odd hn i₀
  refine ⟨i₀, sExpSum y j₀, fun m hm => ?_⟩
  obtain ⟨j, hjle, hjlt⟩ := exists_sExpSum_le_lt hyodd m
  -- `j ≥ j₀`: si no, `sExpSum y (j+1) ≤ sExpSum y j₀ ≤ m`, contra `m < sExpSum y (j+1)`.
  have hj₀ : j₀ ≤ j := by
    by_contra hlt
    have := sExpSum_mono y (show j + 1 ≤ j₀ by omega)
    omega
  have hodd : (j : ℝ) ≤ oddSteps y m := by
    exact_mod_cast oddSteps_ge_of_sExpSum_le hyodd hjle
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlog3 : 0 < Real.log 3 + ε := by
    have := Real.log_pos (show (1 : ℝ) < 3 by norm_num); linarith
  have hm' : (m : ℝ) ≤ sExpSum y (j + 1) := by exact_mod_cast hjlt.le
  calc (m : ℝ) * Real.log 2 ≤ (sExpSum y (j + 1) : ℝ) * Real.log 2 := by gcongr
    _ ≤ ((j + 1 : ℕ) : ℝ) * (Real.log 3 + ε) := h (j + 1) (by omega)
    _ = ((j : ℝ) + 1) * (Real.log 3 + ε) := by push_cast; ring
    _ ≤ ((oddSteps y m : ℝ) + 1) * (Real.log 3 + ε) := by gcongr

end Collatz
