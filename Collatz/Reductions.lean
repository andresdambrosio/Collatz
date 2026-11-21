import Mathlib
import Collatz.Basic

/-!
# Reducción: Collatz ⟺ (no hay ciclos no triviales) ∧ (no hay órbitas divergentes)

Una órbita que no llega a 1 o bien entra en un ciclo distinto de 1 → 4 → 2 → 1,
o bien no está acotada. Este archivo lo demuestra y separa el problema en dos frentes.
-/

/-! ## Lemas básicos sobre `iter` -/

theorem iter_succ' (k n : Nat) : iter (k + 1) n = T (iter k n) := by
  rw [iter_add]; rfl

theorem T_pos {n : Nat} (h : n ≥ 1) : T n ≥ 1 := by
  unfold T; split <;> omega

theorem iter_pos (k : Nat) {n : Nat} (h : n ≥ 1) : iter k n ≥ 1 := by
  induction k with
  | zero => simpa [iter]
  | succ k ih => rw [iter_succ']; exact T_pos ih

theorem iter_mul_of_periodic {p m : Nat} (h : iter p m = m) (t : Nat) :
    iter (p * t) m = m := by
  induction t with
  | zero => simp [iter]
  | succ t ih => rw [Nat.mul_succ, iter_add, ih, h]

/-! ## El ciclo trivial {1, 2, 4} -/

def InTrivialCycle (m : Nat) : Prop := m = 1 ∨ m = 2 ∨ m = 4

theorem trivialCycle_closed {m : Nat} (h : InTrivialCycle m) : InTrivialCycle (T m) := by
  rcases h with rfl | rfl | rfl <;> (unfold InTrivialCycle T; decide)

theorem iter_trivialCycle (k : Nat) {m : Nat} (h : InTrivialCycle m) :
    InTrivialCycle (iter k m) := by
  induction k with
  | zero => simpa [iter]
  | succ k ih => rw [iter_succ']; exact trivialCycle_closed ih

theorem trivialCycle_reaches_one {m : Nat} (h : InTrivialCycle m) : ∃ k, iter k m = 1 := by
  rcases h with rfl | rfl | rfl
  · exact ⟨0, by decide⟩
  · exact ⟨1, by decide⟩
  · exact ⟨2, by decide⟩

/-! ## Los dos frentes -/

/-- Todo punto periódico (n ≥ 1) está en el ciclo trivial. -/
def NoNontrivialCycles : Prop :=
  ∀ n p, n ≥ 1 → p ≥ 1 → iter p n = n → InTrivialCycle n

/-- Toda órbita que empieza en n ≥ 1 está acotada. -/
def NoDivergentOrbits : Prop :=
  ∀ n, n ≥ 1 → ∃ B, ∀ k, iter k n ≤ B

/-- Palomar: una órbita acotada termina siendo periódica. -/
theorem exists_periodic_of_bounded {n B : Nat} (hB : ∀ k, iter k n ≤ B) :
    ∃ i p, p ≥ 1 ∧ iter p (iter i n) = iter i n := by
  obtain ⟨x, -, y, -, hxy, hf⟩ := Finset.exists_ne_map_eq_of_card_lt_of_maps_to
    (s := Finset.range (B + 2)) (t := Finset.range (B + 1)) (f := fun k => iter k n)
    (by simp)
    (by
      intro k _
      simp only [Finset.coe_range, Set.mem_Iio]
      have := hB k; omega)
  rcases Nat.lt_or_gt_of_ne hxy with h | h
  · refine ⟨x, y - x, by omega, ?_⟩
    rw [← iter_add, Nat.add_sub_cancel' h.le]; exact hf.symm
  · refine ⟨y, x - y, by omega, ?_⟩
    rw [← iter_add, Nat.add_sub_cancel' h.le]; exact hf

theorem collatz_of_noCycles_noDivergence (hc : NoNontrivialCycles) (hd : NoDivergentOrbits) :
    Collatz := by
  intro n hn
  obtain ⟨B, hB⟩ := hd n hn
  obtain ⟨i, p, hp, hper⟩ := exists_periodic_of_bounded hB
  obtain ⟨j, hj⟩ := trivialCycle_reaches_one (hc _ p (iter_pos i hn) hp hper)
  exact ⟨i + j, by rw [iter_add]; exact hj⟩

theorem noCycles_of_collatz (h : Collatz) : NoNontrivialCycles := by
  intro n p hn hp hper
  obtain ⟨k, hk⟩ := h n hn
  have e : iter (p * k) n = n := iter_mul_of_periodic hper k
  have hle : k ≤ p * k := by nlinarith
  rw [← Nat.add_sub_cancel' hle, iter_add, hk] at e
  rw [← e]
  exact iter_trivialCycle _ (Or.inl rfl)

theorem noDivergence_of_collatz (h : Collatz) : NoDivergentOrbits := by
  intro n hn
  obtain ⟨k, hk⟩ := h n hn
  refine ⟨(∑ i ∈ Finset.range k, iter i n) + 4, fun j => ?_⟩
  rcases Nat.lt_or_ge j k with hj | hj
  · have := Finset.single_le_sum (f := fun i => iter i n) (fun _ _ => Nat.zero_le _)
      (Finset.mem_range.mpr hj)
    omega
  · have e : iter j n = iter (j - k) 1 := by
      conv_lhs => rw [← Nat.add_sub_cancel' hj]
      rw [iter_add, hk]
    rcases iter_trivialCycle (j - k) (m := 1) (Or.inl rfl) with h1 | h1 | h1 <;> omega

/-- **Reducción principal.** -/
theorem collatz_iff : Collatz ↔ NoNontrivialCycles ∧ NoDivergentOrbits :=
  ⟨fun h => ⟨noCycles_of_collatz h, noDivergence_of_collatz h⟩,
   fun ⟨hc, hd⟩ => collatz_of_noCycles_noDivergence hc hd⟩
