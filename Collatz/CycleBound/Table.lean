-- Generado por scripts/gen_cycle_blocks.py. No editar a mano.
import Collatz.CycleBound

namespace Collatz

set_option maxHeartbeats 0 in
theorem cb_tab_0 :
    (List.range' 1 975).all (k12_sandwichFree (2 ^ 20 * 78)) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem cb_tab_1 :
    (List.range' 976 975).all (k12_sandwichFree (2 ^ 20 * 78)) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem cb_tab_2 :
    (List.range' 1951 975).all (k12_sandwichFree (2 ^ 20 * 78)) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem cb_tab_3 :
    (List.range' 2926 975).all (k12_sandwichFree (2 ^ 20 * 78)) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem cb_tab_4 :
    (List.range' 3901 975).all (k12_sandwichFree (2 ^ 20 * 78)) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem cb_tab_5 :
    (List.range' 4876 975).all (k12_sandwichFree (2 ^ 20 * 78)) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem cb_tab_6 :
    (List.range' 5851 975).all (k12_sandwichFree (2 ^ 20 * 78)) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem cb_tab_7 :
    (List.range' 6826 975).all (k12_sandwichFree (2 ^ 20 * 78)) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem cb_tab_8 :
    (List.range' 7801 975).all (k12_sandwichFree (2 ^ 20 * 78)) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem cb_tab_9 :
    (List.range' 8776 975).all (k12_sandwichFree (2 ^ 20 * 78)) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem cb_tab_10 :
    (List.range' 9751 975).all (k12_sandwichFree (2 ^ 20 * 78)) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem cb_tab_11 :
    (List.range' 10726 975).all (k12_sandwichFree (2 ^ 20 * 78)) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem cb_tab_12 :
    (List.range' 11701 975).all (k12_sandwichFree (2 ^ 20 * 78)) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem cb_tab_13 :
    (List.range' 12676 975).all (k12_sandwichFree (2 ^ 20 * 78)) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem cb_tab_14 :
    (List.range' 13651 975).all (k12_sandwichFree (2 ^ 20 * 78)) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem cb_tab_15 :
    (List.range' 14626 975).all (k12_sandwichFree (2 ^ 20 * 78)) = true := by
  decide +kernel

theorem cb_chunks (c : ℕ) (hc : c < 16) :
    (List.range' (1 + 975 * c) 975).all (k12_sandwichFree (2 ^ 20 * 78)) = true := by
  interval_cases c
  exacts [cb_tab_0, cb_tab_1, cb_tab_2, cb_tab_3, cb_tab_4, cb_tab_5, cb_tab_6, cb_tab_7, cb_tab_8, cb_tab_9, cb_tab_10, cb_tab_11, cb_tab_12, cb_tab_13, cb_tab_14, cb_tab_15]

theorem cb_table {k : ℕ} (hk : 0 < k) (hkK : k ≤ 15600) :
    k12_sandwichFree (2 ^ 20 * 78) k = true := by
  have h := cb_chunks ((k - 1) / 975) (by omega)
  simp only [List.all_eq_true, List.mem_range'] at h
  exact h k ⟨k - 1 - 975 * ((k - 1) / 975), by omega, by omega⟩

end Collatz
