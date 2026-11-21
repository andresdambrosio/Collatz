import Collatz.Forge.Basic
import Collatz.Forge.Cycles
import Collatz.Forge.Invariants.OrbitBoundedOfReachesOne
import Collatz.Forge.Invariants.SyracuseCycleEquation
import Collatz.Forge.Invariants.OrbitInequality

/-!
# Verificación computacional como hipótesis

La conjetura está verificada por computadora hasta `2^71` (Barina, 2025). Eso **no** entra
al kernel: lo enunciamos como `VerifiedBelow M := ∀ n, 0 < n → n < M → ReachesOne n` y lo
usamos como hipótesis explícita, igual que los subproblemas abiertos.

Lo que sí probamos, incondicionalmente:

* `iterate_collatz_eq_iterate_syracuse`: para `n` impar, cada iterado de Syracuse es un
  iterado de `collatz` (`collatz^[a + 1] n = syracuse n` con `a = nu2 (3n+1)`).
* `eq_of_isPeriodic_of_reachesOne`: un punto periódico que llega a `1` está en `{1, 4, 2}`.
* `syracuse_cycle_ge_of_verified`: bajo `VerifiedBelow M`, todo elemento de un ciclo de
  Syracuse distinto del trivial `{1}` es `≥ M`.
* `cycle_sandwich_of_verified`: la combinación. Bajo `VerifiedBelow M`, todo ciclo no
  trivial de `k` pasos satisface `3^k < 2^{A_k}` y `2^{A_k} · M^k ≤ (3M + 1)^k`.

Con `M = 2^71`, la segunda desigualdad dice que `2^{A_k}/3^k` está a menos de
`(1 + 1/(3·2^71))^k` de `1`: `A_k / k` aproxima `log₂ 3` con error `~ 1/(2^71 · log 8)`.
La teoría de fracciones continuas de `log₂ 3` convierte eso en `k ≥ 10^11` (Hercher).
Esa última pieza todavía no está en el repo.
-/

namespace Collatz

/-! ## Syracuse dentro de la órbita de collatz -/

theorem iterate_collatz_of_pow_dvd {x : ℕ} (j : ℕ) (h : 2 ^ j ∣ x) :
    collatz^[j] x = x / 2 ^ j := by
  induction j with
  | zero => simp
  | succ j ih =>
    have hj : 2 ^ j ∣ x := (pow_dvd_pow 2 (Nat.le_succ j)).trans h
    rw [Function.iterate_succ_apply', ih hj, pow_succ, ← Nat.div_div_eq_div_mul]
    apply collatz_of_even
    obtain ⟨c, hc⟩ := h
    rw [hc, pow_succ, mul_assoc, Nat.mul_div_cancel_left _ (pow_pos two_pos j)]
    omega

theorem syracuse_eq_iterate_collatz {n : ℕ} (hn : n % 2 = 1) :
    collatz^[sExp n + 1] n = syracuse n := by
  rw [Function.iterate_add_apply, Function.iterate_one, collatz_of_odd hn]
  unfold sExp
  rw [iterate_collatz_of_pow_dvd _ pow_padicValNat_dvd]
  rfl

/-- Para `n` impar, cada iterado de Syracuse es un iterado (al menos tan largo) de `collatz`. -/
theorem exists_iterate_collatz_eq_iterate_syracuse {n : ℕ} (hn : n % 2 = 1) (k : ℕ) :
    ∃ m, k ≤ m ∧ collatz^[m] n = syracuse^[k] n := by
  induction k with
  | zero => exact ⟨0, le_refl _, rfl⟩
  | succ k ih =>
    obtain ⟨m, hm, h⟩ := ih
    refine ⟨(sExp (syracuse^[k] n) + 1) + m, by omega, ?_⟩
    rw [Function.iterate_add_apply, h, syracuse_eq_iterate_collatz (iterate_syracuse_odd hn k),
      Function.iterate_succ_apply']

theorem isPeriodic_of_syracuse_periodic {n k : ℕ} (hn : n % 2 = 1) (hk : 0 < k)
    (h : syracuse^[k] n = n) : IsPeriodic n := by
  obtain ⟨m, hm, hmk⟩ := exists_iterate_collatz_eq_iterate_syracuse hn k
  exact ⟨m, by omega, by rw [hmk, h]⟩

/-! ## Periódico y llega a 1 ⇒ ciclo trivial -/

theorem eq_of_isPeriodic_of_reachesOne {n : ℕ} (hp : IsPeriodic n) (hr : ReachesOne n) :
    n = 1 ∨ n = 4 ∨ n = 2 := by
  obtain ⟨m, hm, hmn⟩ := hp
  obtain ⟨j, hj⟩ := hr
  have hfix : collatz^[m * j] n = n := by
    rw [Function.iterate_mul]
    exact Function.iterate_fixed hmn j
  have hsplit : collatz^[m * j] n = collatz^[m * j - j] 1 := by
    rw [← hj, ← Function.iterate_add_apply, Nat.sub_add_cancel (Nat.le_mul_of_pos_left j hm)]
  rw [← hfix, hsplit]
  exact iterate_one_mem _

theorem syracuse_one : syracuse 1 = 1 := by
  show oddPart 4 = 1
  rw [show (4 : ℕ) = 2 * 2 by norm_num, oddPart_two_mul two_ne_zero,
    show (2 : ℕ) = 2 * 1 by norm_num, oddPart_two_mul one_ne_zero, oddPart_of_odd odd_one]

/-! ## La hipótesis computacional -/

/-- **Hipótesis.** La conjetura vale por debajo de `M`. Verificado por computadora para
`M = 2^71` (Barina 2025), pero no reproducible en el kernel. -/
def VerifiedBelow (M : ℕ) : Prop := ∀ n, 0 < n → n < M → ReachesOne n

/-- Bajo `VerifiedBelow M`, un impar en un ciclo de Syracuse es `1` o es `≥ M`. -/
theorem syracuse_cycle_ge_of_verified {M n k : ℕ} (hV : VerifiedBelow M) (hn : n % 2 = 1)
    (hk : 0 < k) (h : syracuse^[k] n = n) (hne : n ≠ 1) : M ≤ n := by
  by_contra hlt
  have hr := hV n (by omega) (by omega)
  rcases eq_of_isPeriodic_of_reachesOne (isPeriodic_of_syracuse_periodic hn hk h) hr
    with h1 | h4 | h2 <;> omega

/-- Todo elemento de un ciclo de Syracuse está en el mismo ciclo. -/
theorem iterate_syracuse_periodic {n k : ℕ} (h : syracuse^[k] n = n) (i : ℕ) :
    syracuse^[k] (syracuse^[i] n) = syracuse^[i] n := by
  rw [← Function.iterate_add_apply, add_comm, Function.iterate_add_apply, h]

/-- Si un ciclo de Syracuse pasa por `1`, es el ciclo trivial. -/
theorem eq_one_of_iterate_syracuse_eq_one {n k i : ℕ} (h : syracuse^[k] n = n) (hik : i ≤ k)
    (h1 : syracuse^[i] n = 1) : n = 1 := by
  rw [← h, ← Nat.sub_add_cancel hik, Function.iterate_add_apply, h1]
  exact Function.iterate_fixed syracuse_one _

/-- **Combinación.** Bajo `VerifiedBelow M`, todo ciclo no trivial de Syracuse de `k` pasos
cumple `3^k < 2^{A_k}` y `2^{A_k} · M^k ≤ (3M + 1)^k`. -/
theorem cycle_sandwich_of_verified {M n k : ℕ} (hV : VerifiedBelow M) (hn : n % 2 = 1)
    (hk : 0 < k) (h : syracuse^[k] n = n) (hne : n ≠ 1) :
    3 ^ k < 2 ^ sExpSum n k ∧ 2 ^ sExpSum n k * M ^ k ≤ (3 * M + 1) ^ k := by
  refine cycle_sandwich hk (by omega) (fun i hi => ?_) h
  apply syracuse_cycle_ge_of_verified hV (iterate_syracuse_odd hn i) hk
    (iterate_syracuse_periodic h i)
  intro h1
  exact hne (eq_one_of_iterate_syracuse_eq_one h hi.le h1)

end Collatz
