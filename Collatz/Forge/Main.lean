import Collatz.Forge.Basic
import Collatz.Forge.Cycles
import Collatz.Forge.Divergence

/-!
# Teorema objetivo

`CollatzConjecture` se reduce a dos subproblemas independientes:

* `NoNontrivialCycles` (`Cycles.lean`): el único ciclo positivo es `1 → 4 → 2`.
* `NoDivergence` (`Divergence.lean`): toda órbita positiva es acotada.

La reducción es elemental: una órbita acotada cae en un ciclo (pigeonhole), el
ciclo es el trivial (por hipótesis), luego la órbita pasa por `1`.

Este archivo **no** contiene la conjetura como teorema incondicional. El día
que `NoNontrivialCycles` y `NoDivergence` estén probados sin hipótesis,
`collatz_conjecture` se cierra aplicando `collatz_of_noCycles_noDivergence`.
-/

namespace Collatz

/-- Si algún iterado de `n` llega a `1`, `n` llega a `1`. -/
theorem reachesOne_of_iterate {n m : ℕ} (h : ReachesOne (collatz^[m] n)) : ReachesOne n := by
  obtain ⟨k, hk⟩ := h
  exact ⟨k + m, by rw [Function.iterate_add_apply]; exact hk⟩

/-- **Reducción.** Sin ciclos no triviales y sin divergencia, la conjetura vale. -/
theorem collatz_of_noCycles_noDivergence (hc : NoNontrivialCycles) (hd : NoDivergence) :
    CollatzConjecture := by
  intro n hn
  obtain ⟨m, hm⟩ := exists_isPeriodic_iterate_of_orbitBounded (hd n hn)
  exact reachesOne_of_iterate (reachesOne_of_isPeriodic hc (iterate_pos hn m) hm)

end Collatz
