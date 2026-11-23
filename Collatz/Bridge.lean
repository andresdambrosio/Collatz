import Collatz.Reductions
import Collatz.Forge

/-!
# Puente entre este proyecto y la librería `Collatz.Forge`

Este proyecto usa `T` (el mapa clásico, `n/2` o `3n+1`), `iter` y `Collatz`. La librería
importada de CollatzForge usa `Collatz.collatz` (el mismo mapa), `Nat.iterate`
y `Collatz.CollatzConjecture`, y además el mapa acelerado `Collatz.T` y `Collatz.syracuse`.

Probamos que las definiciones coinciden y traducimos los resultados principales:

* `collatz_iff_forge`, `noNontrivialCycles_iff_forge`, `noDivergentOrbits_iff_forge`:
  los enunciados de los dos proyectos son equivalentes.
* `cycle_period_ge`: todo ciclo no trivial de `T` tiene período `≥ 2301`. Es **incondicional**:
  `k12_syracuse_cycle_length_ge` comprueba en el kernel que todo `n < 600001` llega a 1.
  Es más débil que lo que dice Forge: hay al menos 2301 pasos **impares**.
-/

/-! ## Las definiciones coinciden -/

theorem T_eq_collatz : T = Collatz.collatz := rfl

theorem iter_eq_iterate (k n : ℕ) : iter k n = Collatz.collatz^[k] n := by
  induction k generalizing n with
  | zero => rfl
  | succ k ih => rw [Function.iterate_succ_apply, ← ih]; rfl

theorem collatz_iff_forge : Collatz ↔ Collatz.CollatzConjecture := by
  simp only [Collatz, Collatz.CollatzConjecture, Collatz.ReachesOne, iter_eq_iterate]
  exact forall_congr' fun n => by rw [ge_iff_le, Nat.one_le_iff_ne_zero, Nat.pos_iff_ne_zero]

theorem noNontrivialCycles_iff_forge : NoNontrivialCycles ↔ Collatz.NoNontrivialCycles := by
  constructor
  · rintro h n hn ⟨p, hp, hper⟩
    exact h n p hn hp (by rw [iter_eq_iterate]; exact hper)
  · intro h n p hn hp hper
    exact h n hn ⟨p, hp, by rw [← iter_eq_iterate]; exact hper⟩

theorem noDivergentOrbits_iff_forge : NoDivergentOrbits ↔ Collatz.NoDivergence := by
  simp only [NoDivergentOrbits, Collatz.NoDivergence, Collatz.OrbitBounded, iter_eq_iterate]
  exact forall_congr' fun n => by rw [ge_iff_le, Nat.one_le_iff_ne_zero, Nat.pos_iff_ne_zero]

/-! ## Ciclos: período `≥ 2301`, incondicional -/

/-- Variante de `Collatz.oddPart_iterate_collatz` que además acota el número `k` de pasos
de Syracuse por el número `j` de pasos de `collatz`. -/
theorem oddPart_iterate_collatz_le {n : ℕ} (hn : n % 2 = 1) (j : ℕ) :
    ∃ k, Collatz.oddPart (Collatz.collatz^[j] n) = Collatz.syracuse^[k] n ∧
      (1 ≤ j → 1 ≤ k) ∧ k ≤ j := by
  induction j with
  | zero => exact ⟨0, by simp [Collatz.oddPart_of_odd (Nat.odd_iff.mpr hn)], by omega, le_rfl⟩
  | succ j ih =>
    obtain ⟨k, hk, hk1, hkj⟩ := ih
    rw [Function.iterate_succ_apply']
    rcases Nat.mod_two_eq_zero_or_one (Collatz.collatz^[j] n) with he | ho
    · refine ⟨k, ?_, fun _ => ?_, by omega⟩
      · rw [Collatz.collatz_of_even he, ← hk]
        conv_rhs => rw [show Collatz.collatz^[j] n = 2 * (Collatz.collatz^[j] n / 2) by omega]
        rw [Collatz.oddPart_two_mul]
        intro h0
        have := Collatz.iterate_pos (by omega : 0 < n) j
        omega
      · rcases Nat.eq_zero_or_pos j with rfl | hj
        · simp at he; omega
        · exact hk1 hj
    · refine ⟨k + 1, ?_, by omega, by omega⟩
      have hodd : Collatz.oddPart (Collatz.collatz^[j] n) = Collatz.collatz^[j] n :=
        Collatz.oddPart_of_odd (Nat.odd_iff.mpr ho)
      rw [Collatz.collatz_of_odd ho, Function.iterate_succ_apply', ← hk, hodd]
      rfl

/-- Una cota `B` para los ciclos no triviales de Syracuse (en pasos impares) da la misma cota
para el período de los ciclos no triviales de `T`. -/
theorem cycle_period_ge_of {B : ℕ}
    (hB : ∀ {m k : ℕ}, m % 2 = 1 → 0 < k → Collatz.syracuse^[k] m = m → m ≠ 1 → B ≤ k)
    {n p : ℕ} (hn : n ≥ 1) (hp : p ≥ 1) (h : iter p n = n)
    (hnt : ¬ InTrivialCycle n) : B ≤ p := by
  rw [iter_eq_iterate] at h
  -- el ciclo contiene un impar `m = collatz^[j] n`
  obtain ⟨j, hj⟩ := Collatz.exists_odd_of_isPeriodic (by omega) ⟨p, hp, h⟩
  set m := Collatz.collatz^[j] n with hm
  have hper : ∀ t, Collatz.collatz^[p * t] n = n := by
    intro t
    induction t with
    | zero => simp
    | succ t ih => rw [Nat.mul_succ, Function.iterate_add_apply, h, ih]
  have hmp : Collatz.collatz^[p] m = m := by
    rw [hm, ← Function.iterate_add_apply, add_comm, Function.iterate_add_apply, h]
  -- `n` está en la órbita de `m`
  have hle : j ≤ p * (j + 1) := by nlinarith
  have hnm : Collatz.collatz^[p * (j + 1) - j] m = n := by
    rw [hm, ← Function.iterate_add_apply, Nat.sub_add_cancel hle, hper]
  have hm1 : m ≠ 1 := by
    intro h1
    apply hnt
    have := iter_trivialCycle (p * (j + 1) - j) (m := 1) (Or.inl rfl)
    rw [h1] at hnm
    rwa [iter_eq_iterate, hnm] at this
  -- `m` es Syracuse-periódico con a lo sumo `p` pasos
  obtain ⟨k, hk, hk1, hkp⟩ := oddPart_iterate_collatz_le hj p
  rw [hmp, Collatz.oddPart_of_odd (Nat.odd_iff.mpr hj)] at hk
  have := hB hj (hk1 hp) hk.symm hm1
  omega

/-- **Todo ciclo no trivial de `T` tiene período al menos 2301.** Incondicional. -/
theorem cycle_period_ge {n p : ℕ} (hn : n ≥ 1) (hp : p ≥ 1) (h : iter p n = n)
    (hnt : ¬ InTrivialCycle n) : 2301 ≤ p :=
  cycle_period_ge_of (fun hm hk h' hne => Collatz.k12_syracuse_cycle_length_ge hm hk h' hne)
    hn hp h hnt
