import Collatz.Forge.Basic

/-!
# Ciclos

Un entero `n` es *periódico* si la órbita de `n` bajo `collatz` vuelve a `n` en
un número positivo de pasos. El único ciclo conocido sobre los positivos es
`1 → 4 → 2 → 1`.

**Subproblema abierto:** `NoNontrivialCycles`, todo periódico positivo está en
`{1, 2, 4}`. Se enuncia como `Prop` y se usa como hipótesis; no es un axioma.

Lo que sí está probado aquí: si se asume `NoNontrivialCycles`, todo punto
periódico positivo alcanza `1`. Ese es el eslabón que usa `Main.lean`.
-/

namespace Collatz

/-- `n` está en un ciclo de `collatz`. -/
def IsPeriodic (n : ℕ) : Prop := ∃ k, 0 < k ∧ collatz^[k] n = n

theorem isPeriodic_one : IsPeriodic 1 := ⟨3, by decide, rfl⟩
theorem isPeriodic_two : IsPeriodic 2 := ⟨3, by decide, rfl⟩
theorem isPeriodic_four : IsPeriodic 4 := ⟨3, by decide, rfl⟩

/-- **Abierto.** Ningún ciclo positivo fuera del trivial `1 → 4 → 2 → 1`. -/
def NoNontrivialCycles : Prop := ∀ n, 0 < n → IsPeriodic n → n = 1 ∨ n = 2 ∨ n = 4

/-- Bajo `NoNontrivialCycles`, todo punto periódico positivo llega a `1`. -/
theorem reachesOne_of_isPeriodic (hc : NoNontrivialCycles) {n : ℕ} (hn : 0 < n)
    (hp : IsPeriodic n) : ReachesOne n := by
  rcases hc n hn hp with rfl | rfl | rfl
  · exact reachesOne_one
  · exact reachesOne_two
  · exact reachesOne_four

end Collatz
