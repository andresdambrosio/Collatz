import Collatz.Forge.Basic
import Collatz.Forge.Cycles
import Collatz.Forge.Invariants.VerifiedRange

/-!
# Ciclos de `collatz` ⇔ ciclos de Syracuse sobre impares

Objetivo: enunciar `NoNontrivialCycles` (sobre `collatz`) como una afirmación puramente
sobre `syracuse` en impares, donde vive toda la aritmética de ciclos:

  `NoSyracuseCycles := ∀ n k, n impar → 0 < k → syracuse^[k] n = n → n = 1`.

**Teorema:** `NoNontrivialCycles ↔ NoSyracuseCycles`.

Piezas:
* `oddPart_iterate_collatz`: para `n` impar, la parte impar de cada `collatz^[j] n` es un
  iterado de Syracuse de `n`. Es el invariante que sigue a la órbita de `collatz` y "borra"
  las divisiones por `2`.
* `syracuse_periodic_of_isPeriodic_of_odd`: impar y `collatz`-periódico ⇒ Syracuse-periódico.
  (La otra dirección es `isPeriodic_of_syracuse_periodic`, en `VerifiedRange.lean`.)
* `exists_odd_of_isPeriodic`: todo ciclo positivo de `collatz` contiene un impar (si fuera
  todo par, la órbita bajaría estrictamente).
-/

namespace Collatz

/-- Invariante: la parte impar de la órbita de `collatz` recorre los iterados de Syracuse.
El contador `k` es `≥ 1` en cuanto `j ≥ 1`, porque el primer paso desde un impar ya es
un paso de Syracuse. -/
theorem oddPart_iterate_collatz {n : ℕ} (hn : n % 2 = 1) (j : ℕ) :
    ∃ k, oddPart (collatz^[j] n) = syracuse^[k] n ∧ (1 ≤ j → 1 ≤ k) := by
  induction j with
  | zero => exact ⟨0, by simp [oddPart_of_odd (Nat.odd_iff.mpr hn)], by omega⟩
  | succ j ih =>
    obtain ⟨k, hk, hk1⟩ := ih
    rw [Function.iterate_succ_apply']
    rcases Nat.mod_two_eq_zero_or_one (collatz^[j] n) with he | ho
    · -- paso par: la parte impar no cambia
      refine ⟨k, ?_, fun _ => ?_⟩
      · rw [collatz_of_even he, ← hk]
        conv_rhs => rw [show collatz^[j] n = 2 * (collatz^[j] n / 2) by omega]
        rw [oddPart_two_mul]
        intro h0
        have := iterate_pos (by omega : 0 < n) j
        omega
      · -- si j = 0 el valor es n, impar: contradicción con `he`
        rcases Nat.eq_zero_or_pos j with rfl | hj
        · simp at he; omega
        · exact hk1 hj
    · -- paso impar: un paso de Syracuse
      refine ⟨k + 1, ?_, by omega⟩
      have hodd : oddPart (collatz^[j] n) = collatz^[j] n := oddPart_of_odd (Nat.odd_iff.mpr ho)
      rw [collatz_of_odd ho, Function.iterate_succ_apply', ← hk, hodd]
      rfl

/-- Impar y `collatz`-periódico ⇒ Syracuse-periódico. -/
theorem syracuse_periodic_of_isPeriodic_of_odd {n : ℕ} (hn : n % 2 = 1) (hp : IsPeriodic n) :
    ∃ k, 0 < k ∧ syracuse^[k] n = n := by
  obtain ⟨m, hm, hmn⟩ := hp
  obtain ⟨k, hk, hk1⟩ := oddPart_iterate_collatz hn m
  refine ⟨k, hk1 hm, ?_⟩
  rw [← hk, hmn, oddPart_of_odd (Nat.odd_iff.mpr hn)]

/-- Para `n` impar: `collatz`-periódico ⇔ Syracuse-periódico. -/
theorem isPeriodic_iff_syracuse_of_odd {n : ℕ} (hn : n % 2 = 1) :
    IsPeriodic n ↔ ∃ k, 0 < k ∧ syracuse^[k] n = n :=
  ⟨syracuse_periodic_of_isPeriodic_of_odd hn,
    fun ⟨_, hk, h⟩ => isPeriodic_of_syracuse_periodic hn hk h⟩

/-- Si los primeros `j` valores de la órbita son pares, el `j`-ésimo es `n / 2^j`. -/
theorem iterate_collatz_of_all_even {n : ℕ} (j : ℕ)
    (h : ∀ i < j, collatz^[i] n % 2 = 0) : collatz^[j] n = n / 2 ^ j := by
  induction j with
  | zero => simp
  | succ j ih =>
    rw [Function.iterate_succ_apply', ih (fun i hi => h i (by omega)),
      collatz_of_even (by rw [← ih (fun i hi => h i (by omega))]; exact h j (by omega)),
      pow_succ, Nat.div_div_eq_div_mul]

/-- Todo ciclo positivo de `collatz` contiene un impar. -/
theorem exists_odd_of_isPeriodic {n : ℕ} (hn : 0 < n) (hp : IsPeriodic n) :
    ∃ j, collatz^[j] n % 2 = 1 := by
  by_contra hcon
  push Not at hcon
  obtain ⟨m, hm, hmn⟩ := hp
  have := iterate_collatz_of_all_even (n := n) m (fun i _ => by have := hcon i; omega)
  rw [hmn] at this
  have h2 : 2 ≤ 2 ^ m := by
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ m := Nat.pow_le_pow_right two_pos hm
  have : n / 2 ^ m < n := Nat.div_lt_self hn (by omega)
  omega

/-- **Enunciado de ciclos en Syracuse.** Ningún impar distinto de `1` es Syracuse-periódico. -/
def NoSyracuseCycles : Prop := ∀ n k, n % 2 = 1 → 0 < k → syracuse^[k] n = n → n = 1

/-- **`NoNontrivialCycles ↔ NoSyracuseCycles`.** Ciclos vive enteramente en Syracuse. -/
theorem noNontrivialCycles_iff : NoNontrivialCycles ↔ NoSyracuseCycles := by
  constructor
  · intro hc n k hn hk h
    rcases hc n (by omega) (isPeriodic_of_syracuse_periodic hn hk h) with h1 | h2 | h4 <;> omega
  · intro hs n hn hp
    -- el ciclo contiene un impar m, que es Syracuse-periódico, luego m = 1
    obtain ⟨j, hj⟩ := exists_odd_of_isPeriodic hn hp
    have hpj : IsPeriodic (collatz^[j] n) := by
      obtain ⟨m, hm, hmn⟩ := hp
      exact ⟨m, hm, by rw [← Function.iterate_add_apply, add_comm, Function.iterate_add_apply, hmn]⟩
    obtain ⟨k, hk, hkm⟩ := syracuse_periodic_of_isPeriodic_of_odd hj hpj
    have h1 : collatz^[j] n = 1 := hs _ k hj hk hkm
    -- entonces n llega a 1 y es periódico: está en {1, 4, 2}
    rcases eq_of_isPeriodic_of_reachesOne hp ⟨j, h1⟩ with h | h | h <;> omega

end Collatz
