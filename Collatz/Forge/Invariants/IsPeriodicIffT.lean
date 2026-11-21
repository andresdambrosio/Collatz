import Collatz.Forge.Basic
import Collatz.Forge.Cycles

/-!
# Ciclos de `collatz` vs. ciclos de `T`

`T` colapsa el paso impar `n ↦ 3n + 1` con la división por `2` que siempre le sigue.
Así, un paso de `T` son uno o dos pasos de `collatz`, y la órbita de `T` es una
subsucesión de la de `collatz` que se saltea exactamente los valores `3x + 1` con `x` impar.

**Contraejemplo al enunciado ingenuo.** `IsPeriodic n ↔ (n es T-periódico)` es falso
para `n = 4`: `4` está en el ciclo `1 → 4 → 2` de `collatz`, pero la órbita de `T` desde
`4` es `2, 1, 2, 1, …` y nunca vuelve a `4` (`not_T_periodic_four`). El motivo es que
`4 = 3·1 + 1` es justamente un valor salteado.

**Enunciado correcto.**
* `isPeriodic_of_T_periodic`: T-periódico ⇒ `IsPeriodic`, para todo `n`.
* `T_periodic_of_isPeriodic_of_odd`: `IsPeriodic` ⇒ T-periódico, para `n` **impar**
  (un impar nunca es de la forma `3x + 1` con `x` impar, así que no se saltea).
* `isPeriodic_iff_T_of_odd`: la equivalencia, para `n` impar.

Idea de la prueba de la dirección difícil: se lleva un invariante
`∃ k, T^[k] n = collatz^[j] n ∨ T^[k] n = collatz^[j+1] n`, con contadores `j ≤ 2k`
para garantizar `k > 0` al final, y con la marca "en el segundo caso `collatz^[j] n` es par"
para descartar ese caso cuando `j = 2m` devuelve `n`, que es impar.
-/

namespace Collatz

/-! ## Un paso de `T` en términos de `collatz` -/

theorem T_eq_collatz_of_even {n : ℕ} (h : n % 2 = 0) : T n = collatz n := by
  simp [T, collatz, h]

theorem collatz_even_of_odd {n : ℕ} (h : n % 2 = 1) : collatz n % 2 = 0 := by
  rw [collatz_of_odd h]; omega

theorem T_eq_collatz_collatz_of_odd {n : ℕ} (h : n % 2 = 1) : T n = collatz (collatz n) := by
  rw [T_of_odd h, collatz_of_odd h, collatz_of_even (by omega)]

/-! ## T-periódico ⇒ collatz-periódico -/

/-- Cada iterado de `T` es algún iterado (al menos tan largo) de `collatz`. -/
theorem exists_iterate_collatz_eq_iterate_T (n k : ℕ) :
    ∃ m, k ≤ m ∧ collatz^[m] n = T^[k] n := by
  induction k with
  | zero => exact ⟨0, le_refl _, rfl⟩
  | succ k ih =>
    obtain ⟨m, hm, h⟩ := ih
    rcases Nat.mod_two_eq_zero_or_one (collatz^[m] n) with he | ho
    · refine ⟨m + 1, by omega, ?_⟩
      rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ← h,
        T_eq_collatz_of_even he]
    · refine ⟨m + 1 + 1, by omega, ?_⟩
      rw [Function.iterate_succ_apply', Function.iterate_succ_apply',
        Function.iterate_succ_apply', ← h, T_eq_collatz_collatz_of_odd ho]

theorem isPeriodic_of_T_periodic {n k : ℕ} (hk : 0 < k) (h : T^[k] n = n) : IsPeriodic n := by
  obtain ⟨m, hm, hmk⟩ := exists_iterate_collatz_eq_iterate_T n k
  exact ⟨m, by omega, by rw [hmk, h]⟩

/-! ## collatz-periódico e impar ⇒ T-periódico -/

/-- Invariante: la órbita de `T` sigue de cerca a la de `collatz`. En el segundo caso
el valor salteado `collatz^[j] n` es par (es un `3x + 1`). -/
theorem T_iterate_track (n j : ℕ) :
    ∃ k, (T^[k] n = collatz^[j] n ∧ j ≤ 2 * k) ∨
      (T^[k] n = collatz^[j + 1] n ∧ j + 1 ≤ 2 * k ∧ collatz^[j] n % 2 = 0) := by
  induction j with
  | zero => exact ⟨0, Or.inl ⟨rfl, le_refl _⟩⟩
  | succ j ih =>
    obtain ⟨k, ⟨hk, hj⟩ | ⟨hk, hj, _⟩⟩ := ih
    · rcases Nat.mod_two_eq_zero_or_one (collatz^[j] n) with he | ho
      · refine ⟨k + 1, Or.inl ⟨?_, by omega⟩⟩
        rw [Function.iterate_succ_apply' (f := T), Function.iterate_succ_apply' (f := collatz),
          hk, T_eq_collatz_of_even he]
      · refine ⟨k + 1, Or.inr ⟨?_, by omega, ?_⟩⟩
        · rw [Function.iterate_succ_apply' (f := T), Function.iterate_succ_apply' (f := collatz),
            Function.iterate_succ_apply' (f := collatz), hk, T_eq_collatz_collatz_of_odd ho]
        · rw [Function.iterate_succ_apply']
          exact collatz_even_of_odd ho
    · exact ⟨k, Or.inl ⟨hk, hj⟩⟩

theorem T_periodic_of_isPeriodic_of_odd {n : ℕ} (hn : n % 2 = 1) (hp : IsPeriodic n) :
    ∃ k, 0 < k ∧ T^[k] n = n := by
  obtain ⟨m, hm, hmn⟩ := hp
  have h2 : collatz^[2 * m] n = n := by
    rw [two_mul, Function.iterate_add_apply, hmn, hmn]
  obtain ⟨k, ⟨hk, hj⟩ | ⟨_, _, he⟩⟩ := T_iterate_track n (2 * m)
  · exact ⟨k, by omega, by rw [hk, h2]⟩
  · rw [h2] at he; omega

theorem isPeriodic_iff_T_of_odd {n : ℕ} (hn : n % 2 = 1) :
    IsPeriodic n ↔ ∃ k, 0 < k ∧ T^[k] n = n :=
  ⟨T_periodic_of_isPeriodic_of_odd hn, fun ⟨_, hk, h⟩ => isPeriodic_of_T_periodic hk h⟩

/-! ## El contraejemplo para pares -/

theorem T_iterate_four (k : ℕ) : T^[k + 1] 4 = 2 ∨ T^[k + 1] 4 = 1 := by
  induction k with
  | zero => left; rfl
  | succ k ih =>
    rw [Function.iterate_succ_apply']
    rcases ih with h | h <;> rw [h] <;> decide

/-- `4` es `collatz`-periódico (`isPeriodic_four`) pero no `T`-periódico. -/
theorem not_T_periodic_four : ¬ ∃ k, 0 < k ∧ T^[k] 4 = 4 := by
  rintro ⟨k, hk, h⟩
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
  rcases T_iterate_four j with h' | h' <;> omega

end Collatz
