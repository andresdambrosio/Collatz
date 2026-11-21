import Collatz.Bridge

/-!
# Objetivos abiertos

La conjetura queda reducida (sin `sorry`) a los dos frentes de `Collatz.Reductions`.
Los dos `sorry` de abajo son exactamente lo que falta.
-/

/-- Frente 1 (abierto): no hay ciclos distintos de 1 → 4 → 2 → 1. -/
theorem no_nontrivial_cycles : NoNontrivialCycles := by
  sorry

/-- Frente 2 (abierto): ninguna órbita se va a infinito. -/
theorem no_divergent_orbits : NoDivergentOrbits := by
  sorry

theorem collatz_conjecture : Collatz :=
  collatz_iff.mpr ⟨no_nontrivial_cycles, no_divergent_orbits⟩
