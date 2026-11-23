-- Generado por scripts/gen_cycle_blocks.py. No editar a mano.
import Collatz.CycleBound.Res14
import Collatz.CycleBound.Res15
import Collatz.CycleBound.Table

/-!
# Fase 3b: todo ciclo no trivial tiene al menos 15601 pasos impares

Incondicional, chequeado en el kernel. `M = 2^20 · 78 = 81788928`: todo impar `1 < n < M`
desciende bajo `T` (criba de Terras mod `2^20` + chequeo numérico de los sobrevivientes,
`Res00`–`Res15`); por lo tanto ningún elemento de un ciclo no trivial es `< M`
(`syracuse_cycle_ge_of_descends`), y el sándwich no deja ningún `A` para `1 ≤ k ≤ 15600` (`Table`).
-/

namespace Collatz

theorem cb_blocks (b : ℕ) (hb : b < 2048) : blockOK 20 78 500 (1 + 512 * b) 256 = true := by
  obtain ⟨f, i, hi, rfl⟩ : ∃ f i, i < 128 ∧ b = 128 * f + i :=
    ⟨b / 128, b % 128, Nat.mod_lt _ (by norm_num), (Nat.div_add_mod b 128).symm⟩
  have hf : f < 16 := by omega
  interval_cases f
  exacts [cb_file_0 i hi, cb_file_1 i hi, cb_file_2 i hi, cb_file_3 i hi, cb_file_4 i hi, cb_file_5 i hi, cb_file_6 i hi, cb_file_7 i hi, cb_file_8 i hi, cb_file_9 i hi, cb_file_10 i hi, cb_file_11 i hi, cb_file_12 i hi, cb_file_13 i hi, cb_file_14 i hi, cb_file_15 i hi]

theorem cb_residues : ∀ r, r < 2 ^ 20 → r % 2 = 1 → residueOK 20 78 500 r = true := by
  intro r hr hodd
  exact blockOK_mem (cb_blocks (r / 512) (by omega)) (by omega) (by omega) (by omega)

theorem cb_descendsBelow : DescendsBelow (2 ^ 20 * 78) :=
  descendsBelow_of_T (descendsT_of_residueOK (by norm_num) cb_residues)

/-- **Todo ciclo no trivial de Syracuse tiene al menos 15601 pasos.** Incondicional
(antes: 2301, `k12_syracuse_cycle_length_ge`). -/
theorem syracuse_cycle_length_ge_15601 {n k : ℕ} (hn : n % 2 = 1) (hk : 0 < k)
    (h : syracuse^[k] n = n) (hne : n ≠ 1) : 15601 ≤ k := by
  by_contra hlt
  push Not at hlt
  obtain ⟨h1, h2⟩ := cycle_sandwich_of_descends cb_descendsBelow hn hk h hne
  exact k12_no_A_of_sandwichFree (cb_table hk (by omega)) _ h1 h2

end Collatz

/-- **Todo ciclo no trivial de `T` tiene período al menos 15601.** Incondicional. -/
theorem cycle_period_ge_15601 {n p : ℕ} (hn : n ≥ 1) (hp : p ≥ 1) (h : iter p n = n)
    (hnt : ¬ InTrivialCycle n) : 15601 ≤ p :=
  cycle_period_ge_of (fun hm hk h' hne => Collatz.syracuse_cycle_length_ge_15601 hm hk h' hne)
    hn hp h hnt
