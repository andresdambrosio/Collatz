import Collatz.Forge.Basic
import Collatz.Forge.Invariants.SyracuseCycleEquation

/-!
# La desigualdad de órbita

Un paso de Syracuse es `2^{a} · S n = 3n + 1`. Si `n ≥ N`, entonces `3n + 1 ≤ (3 + 1/N) n`,
o en enteros: `N · 2^{a} · S n ≤ (3N + 1) · n`. Multiplicando `k` pasos, con `A = a₀ + ⋯ + aₖ₋₁`:

  `N^k · 2^A · S^k n ≤ (3N + 1)^k · n`    siempre que `S^i n ≥ N` para `i < k`.

Es una sola identidad, pero da constraints en los dos subproblemas:

* **Ciclos.** Si `S^k n = n`, se cancela `n`: `N^k · 2^A ≤ (3N + 1)^k`, con `N` el mínimo del
  ciclo. Junto con `3^k < 2^A` (`two_pow_gt_three_pow_of_cycle`) queda el *sándwich*
  `3^k < 2^A ≤ (3 + 1/N)^k`: el cociente `2^A / 3^k` está en `(1, (1 + 1/(3N))^k]`.
  Esto es lo que, combinado con la verificación computacional (`N ≥ 2^71`) y con los
  convergentes de `log₂ 3`, produce las cotas de Eliahou/Hercher.

* **Divergencia.** Si la órbita *no baja* de `n` en `k` pasos (`n ≤ S^k n`) y se mantiene
  `≥ N`, entonces la misma cota `N^k · 2^A ≤ (3N + 1)^k`: la órbita no puede quitar más de
  `k · log₂(3 + 1/N)` doses en `k` pasos impares. Para una órbita divergente `N → ∞`, así que
  la densidad de doses por paso impar es a lo sumo `log₂ 3`, o sea la fracción de pasos
  impares (en `T`) es al menos `log 2 / log 3 ≈ 0.63`.

Todo en `ℕ`, sin logaritmos; la versión real con `Real.log` es un corolario.
-/

namespace Collatz

/-- Un paso: si `N ≤ n`, entonces `N · 2^{sExp n} · syracuse n ≤ (3N + 1) · n`. -/
theorem syracuse_step_bound {N n : ℕ} (hN : N ≤ n) :
    N * (2 ^ sExp n * syracuse n) ≤ (3 * N + 1) * n := by
  rw [two_pow_sExp_mul_syracuse]
  nlinarith

/-- `k` pasos: si la órbita se mantiene `≥ N`, entonces
`N^k · 2^{A_k} · S^k n ≤ (3N + 1)^k · n`. -/
theorem syracuse_orbit_bound {N n : ℕ} (k : ℕ) (hN : ∀ i < k, N ≤ syracuse^[i] n) :
    N ^ k * 2 ^ sExpSum n k * syracuse^[k] n ≤ (3 * N + 1) ^ k * n := by
  induction k with
  | zero => simp [sExpSum_zero]
  | succ k ih =>
    have ih := ih fun i hi => hN i (by omega)
    have step := syracuse_step_bound (hN k (by omega))
    rw [sExpSum_succ, pow_succ, pow_succ, pow_add, Function.iterate_succ_apply']
    calc N ^ k * N * (2 ^ sExpSum n k * 2 ^ sExp (syracuse^[k] n)) * syracuse (syracuse^[k] n)
        = (N ^ k * 2 ^ sExpSum n k) *
            (N * (2 ^ sExp (syracuse^[k] n) * syracuse (syracuse^[k] n))) := by ring
      _ ≤ (N ^ k * 2 ^ sExpSum n k) * ((3 * N + 1) * syracuse^[k] n) :=
          Nat.mul_le_mul_left _ step
      _ = (3 * N + 1) * (N ^ k * 2 ^ sExpSum n k * syracuse^[k] n) := by ring
      _ ≤ (3 * N + 1) * ((3 * N + 1) ^ k * n) := Nat.mul_le_mul_left _ ih
      _ = (3 * N + 1) ^ k * (3 * N + 1) * n := by ring

/-- Si la órbita no baja de `n` en `k` pasos y se mantiene `≥ N`, entonces
`N^k · 2^{A_k} ≤ (3N + 1)^k`. Vale tanto para ciclos como para tramos ascendentes. -/
theorem ascent_bound {N n : ℕ} (k : ℕ) (hn : 0 < n) (hN : ∀ i < k, N ≤ syracuse^[i] n)
    (hup : n ≤ syracuse^[k] n) :
    N ^ k * 2 ^ sExpSum n k ≤ (3 * N + 1) ^ k := by
  have h := syracuse_orbit_bound k hN
  have : N ^ k * 2 ^ sExpSum n k * n ≤ (3 * N + 1) ^ k * n :=
    (Nat.mul_le_mul_left _ hup).trans h
  exact Nat.le_of_mul_le_mul_right this hn

/-- **Sándwich del ciclo.** En un ciclo de `k > 0` pasos de Syracuse cuyos elementos son
todos `≥ N`: `3^k < 2^{A_k}` y `2^{A_k} · N^k ≤ (3N + 1)^k`, o sea
`1 < 2^{A_k} / 3^k ≤ (1 + 1/(3N))^k`. -/
theorem cycle_sandwich {N n k : ℕ} (hk : 0 < k) (hn : 0 < n)
    (hN : ∀ i < k, N ≤ syracuse^[i] n) (h : syracuse^[k] n = n) :
    3 ^ k < 2 ^ sExpSum n k ∧ 2 ^ sExpSum n k * N ^ k ≤ (3 * N + 1) ^ k :=
  ⟨two_pow_gt_three_pow_of_cycle hk h, by rw [mul_comm]; exact ascent_bound k hn hN h.ge⟩

/-- Lectura logarítmica: en un tramo que no baja y se mantiene `≥ N`, las doses quitadas por
paso de Syracuse promedian a lo sumo `log₂ (3 + 1/N)`. Para `N → ∞` esto tiende a `log₂ 3`. -/
theorem ascent_bound_log {N n : ℕ} (k : ℕ) (hN0 : 0 < N) (hn : 0 < n)
    (hN : ∀ i < k, N ≤ syracuse^[i] n) (hup : n ≤ syracuse^[k] n) :
    (sExpSum n k : ℝ) * Real.log 2 ≤ k * Real.log (3 + 1 / N) := by
  have h := ascent_bound k hn hN hup
  have hcast : ((N : ℝ) ^ k * 2 ^ sExpSum n k) ≤ (3 * N + 1) ^ k := by exact_mod_cast h
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN0
  have hlog := Real.log_le_log (by positivity) hcast
  rw [Real.log_mul (by positivity) (by positivity), Real.log_pow, Real.log_pow, Real.log_pow] at hlog
  have : (3 + 1 / N : ℝ) = (3 * N + 1) / N := by field_simp
  rw [this, Real.log_div (by positivity) hNr.ne', mul_sub]
  linarith

end Collatz
