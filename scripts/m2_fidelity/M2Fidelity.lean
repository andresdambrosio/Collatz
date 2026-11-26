/-
Chequeo de fidelidad de `M2.Statement` (`Collatz/Density.lean`) contra el M2 de ProofAtlas.
NO es parte de `lake build`: se corre dentro de un clon compilado de github.com/neljaouh/ConjectureA
(Lean v4.30.0-rc2), que vendoriza M2:

    cd <clon de ConjectureA> && lake env lean <este repo>/scripts/m2_fidelity/M2Fidelity.lean

Las definiciones de abajo son copia literal de las de `Collatz/Density.lean`. Resultado (2026-11-26):
`M2.statement_holds` compila y depende sólo de [propext, Classical.choice, Quot.sound]; con `1 < c` en vez de
`0 < c` falla (prueba de mutación).
-/
import Erdos1135.ND.PositiveDensity.GeneralTargetPositiveDensity

namespace M2
def collatzStep (n : ℕ) : ℕ := if Even n then n / 2 else 3 * n + 1

/-- `Erdos1135.Reaches`. -/
def Reaches (a b : ℕ) : Prop := ∃ m, collatzStep^[m] a = b

/-- `Erdos1135.ND.PositiveDensity.ordinaryPredecessorSet`. -/
def ordinaryPredecessorSet (a : ℕ) : Set ℕ := {n | 0 < n ∧ Reaches n a}

/-- `Erdos1135.Terras.natCount`. -/
noncomputable def natCount (s : Set ℕ) (N : ℕ) : ℕ :=
  @Nat.count (fun n => n ∈ s) (fun n => Classical.propDecidable (n ∈ s)) N

/-- El enunciado de `generalTarget_predecessors_positive_lower_density` (M2), cuantificado en `a`. -/
def Statement : Prop :=
  ∀ {a : ℕ}, 0 < a → ¬ 3 ∣ a →
    ∃ c : ℝ, 0 < c ∧ ∃ X0 : ℕ, ∀ X : ℕ, X0 ≤ X →
      c * (X : ℝ) ≤ (natCount (ordinaryPredecessorSet a) X : ℝ)

/-- El teorema M2 de ProofAtlas prueba exactamente nuestro `Statement` (igualdad por definición). -/
theorem statement_holds : Statement :=
  fun ha h3 => Erdos1135.ND.PositiveDensity.generalTarget_predecessors_positive_lower_density ha h3

end M2
#print axioms M2.statement_holds
