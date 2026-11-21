import Collatz.Forge.Basic

/-!
# Divergencia

La órbita de `n` es *acotada* si existe `B` con `collatz^[k] n ≤ B` para todo `k`.

**Subproblema abierto:** `NoDivergence`, toda órbita positiva es acotada.
Se enuncia como `Prop` y se usa como hipótesis; no es un axioma.

Lo que sí está probado aquí: una órbita acotada es eventualmente periódica
(pigeonhole sobre `Fin (B + 1)`). Ese es el eslabón que usa `Main.lean`.
-/

namespace Collatz

/-- La órbita de `n` bajo `collatz` es acotada. -/
def OrbitBounded (n : ℕ) : Prop := ∃ B, ∀ k, collatz^[k] n ≤ B

/-- **Abierto.** Ninguna órbita positiva diverge. -/
def NoDivergence : Prop := ∀ n, 0 < n → OrbitBounded n

/-- Una órbita acotada cae en un ciclo: hay `m` con `collatz^[m] n` periódico. -/
theorem exists_isPeriodic_iterate_of_orbitBounded {n : ℕ} (h : OrbitBounded n) :
    ∃ m, ∃ k, 0 < k ∧ collatz^[k] (collatz^[m] n) = collatz^[m] n := by
  obtain ⟨B, hB⟩ := h
  let f : ℕ → Fin (B + 1) := fun k => ⟨collatz^[k] n, Nat.lt_succ_of_le (hB k)⟩
  obtain ⟨i, j, hij, hf⟩ := Finite.exists_ne_map_eq_of_infinite f
  have hf' : collatz^[i] n = collatz^[j] n := by
    simpa [f, Fin.ext_iff] using hf
  rcases Nat.lt_or_gt_of_ne hij with hlt | hlt
  · refine ⟨i, j - i, Nat.sub_pos_of_lt hlt, ?_⟩
    rw [← Function.iterate_add_apply, Nat.sub_add_cancel hlt.le, hf']
  · refine ⟨j, i - j, Nat.sub_pos_of_lt hlt, ?_⟩
    rw [← Function.iterate_add_apply, Nat.sub_add_cancel hlt.le, hf']

end Collatz
