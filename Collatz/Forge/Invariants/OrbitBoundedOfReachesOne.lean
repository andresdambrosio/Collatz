import Collatz.Forge.Basic
import Collatz.Forge.Divergence

/-!
# Si la órbita pasa por 1, es acotada

Recíproco fácil de la dirección "acotada ⇒ periódica". Si `collatz^[k] n = 1`,
la órbita se parte en dos tramos:

* antes de `k`: finitos valores, acotados por su máximo (`Finset.sup` sobre `range k`);
* desde `k`: es la órbita de `1`, que vive en `{1, 4, 2}` y por tanto es `≤ 4`.

La cota final es `max (sup de los primeros k valores) 4`.
-/

namespace Collatz

/-- La órbita de `1` se queda en el ciclo `1 → 4 → 2`. -/
theorem iterate_one_mem (j : ℕ) :
    collatz^[j] 1 = 1 ∨ collatz^[j] 1 = 4 ∨ collatz^[j] 1 = 2 := by
  induction j with
  | zero => simp
  | succ j ih =>
    rw [Function.iterate_succ_apply']
    rcases ih with h | h | h <;> rw [h] <;> decide

theorem iterate_one_le (j : ℕ) : collatz^[j] 1 ≤ 4 := by
  rcases iterate_one_mem j with h | h | h <;> omega

/-- Si `n` llega a `1`, su órbita es acotada. -/
theorem orbitBounded_of_reachesOne {n : ℕ} (h : ReachesOne n) : OrbitBounded n := by
  obtain ⟨k, hk⟩ := h
  refine ⟨max ((Finset.range k).sup fun j => collatz^[j] n) 4, fun j => ?_⟩
  rcases lt_or_ge j k with hj | hj
  · exact le_max_of_le_left
      (Finset.le_sup (f := fun j => collatz^[j] n) (Finset.mem_range.mpr hj))
  · have : collatz^[j] n = collatz^[j - k] 1 := by
      rw [← hk, ← Function.iterate_add_apply, Nat.sub_add_cancel hj]
    rw [this]
    exact le_max_of_le_right (iterate_one_le _)

end Collatz
