import Collatz.Forge.Basic
import Collatz.Forge.Invariants.SyracuseCycleEquation

/-!
# Paridad periódica ⇒ ciclo

Sea `xᵢ = S^i n` la órbita de Syracuse de un impar `n`, y `aᵢ = sExp xᵢ = nu2 (3xᵢ + 1)` el
"vector de exponentes" (equivalente al vector de paridad del mapa `T`). Probamos:

> Si `aᵢ` es eventualmente periódica (período `p > 0` desde `i₀`), entonces la órbita es
> un ciclo desde `i₀`: `S^p (S^{i₀} n) = S^{i₀} n`.

Corolario: **una órbita divergente tiene vector de exponentes aperiódico**.

## Idea de la prueba (Lagarias 1985, sin 2-ádicos)

Entre bloques de `p` pasos el patrón de exponentes se repite, así que con `yₘ = S^{i₀ + mp} n`
la ecuación de órbita (`syracuse_iterate_mul_two_pow`) tiene los *mismos* `A` y `c` en cada
bloque:

  `yₘ₊₁ · 2^A = 3^p · yₘ + c`,   `A = a₀ + ⋯ + aₚ₋₁ ≥ 1`,   `c = Σ_{i<p} 3^{p-1-i} 2^{Aᵢ} > 0`.

Sea `wₘ = (2^A − 3^p) · yₘ − c ∈ ℤ`. Un cálculo directo da `2^A · wₘ₊₁ = 3^p · wₘ`, luego
`2^{Am} · wₘ = 3^{pm} · w₀`. Como `2 ⊥ 3`, `2^{Am} ∣ w₀` para todo `m`, así que `w₀ = 0`.
Entonces `(2^A − 3^p) y₀ = c` y `y₁ · 2^A = 3^p y₀ + c = 2^A y₀`, es decir `y₁ = y₀`.

Nótese que el argumento *no* distingue `2^A > 3^p` de `2^A < 3^p`: el caso expansivo se
descarta solo, porque `w₀ = 0` con `c > 0`, `y₀ > 0` fuerza `2^A > 3^p`.
-/

namespace Collatz

open Finset

/-! ## El lema afín en ℤ -/

/-- Telescoping finito. Si `y (m+1) · 2^A = 3^p · y m + c` para `m < M`, entonces
`2^{AM}` divide a `w₀ = (2^A − 3^p) · y 0 − c`. -/
theorem affine_orbit_dvd {A p : ℕ} (y : ℕ → ℕ) (c M : ℕ)
    (h : ∀ m < M, y (m + 1) * 2 ^ A = 3 ^ p * y m + c) :
    (2 : ℤ) ^ (A * M) ∣ ((2 : ℤ) ^ A - 3 ^ p) * y 0 - c := by
  set w : ℕ → ℤ := fun m => ((2 : ℤ) ^ A - 3 ^ p) * y m - c with hw
  have hstep : ∀ m < M, 2 ^ A * w (m + 1) = 3 ^ p * w m := by
    intro m hm
    have hz : ((y (m + 1) : ℤ)) * 2 ^ A = 3 ^ p * y m + c := by exact_mod_cast h m hm
    simp only [hw]
    linear_combination ((2 : ℤ) ^ A - 3 ^ p) * hz
  have htel : ∀ m ≤ M, 2 ^ (A * m) * w m = 3 ^ (p * m) * w 0 := by
    intro m
    induction m with
    | zero => intro _; simp
    | succ m ih =>
      intro hm
      have ih := ih (by omega)
      rw [Nat.mul_succ, Nat.mul_succ, pow_add, pow_add]
      calc 2 ^ (A * m) * 2 ^ A * w (m + 1) = 2 ^ (A * m) * (2 ^ A * w (m + 1)) := by ring
        _ = 2 ^ (A * m) * (3 ^ p * w m) := by rw [hstep m (by omega)]
        _ = 3 ^ p * (2 ^ (A * m) * w m) := by ring
        _ = 3 ^ p * (3 ^ (p * m) * w 0) := by rw [ih]
        _ = 3 ^ (p * m) * 3 ^ p * w 0 := by ring
  have h1 : (2 : ℤ) ^ (A * M) ∣ 3 ^ (p * M) * w 0 := ⟨w M, (htel M le_rfl).symm⟩
  have hcop : IsCoprime ((2 : ℤ) ^ (A * M)) (3 ^ (p * M)) :=
    IsCoprime.pow (Int.isCoprime_iff_gcd_eq_one.mpr (by decide))
  exact hcop.dvd_of_dvd_mul_left h1

/-- **Versión cuantitativa.** Tras `M` bloques afines, o `w₀ = 0` o `|w₀| ≥ 2^{AM}`. -/
theorem affine_orbit_zero_or_large {A p : ℕ} (y : ℕ → ℕ) (c M : ℕ)
    (h : ∀ m < M, y (m + 1) * 2 ^ A = 3 ^ p * y m + c) :
    ((2 : ℤ) ^ A - 3 ^ p) * y 0 - c = 0 ∨
      (2 : ℤ) ^ (A * M) ≤ |((2 : ℤ) ^ A - 3 ^ p) * y 0 - c| := by
  rcases eq_or_ne (((2 : ℤ) ^ A - 3 ^ p) * y 0 - c) 0 with h0 | h0
  · exact Or.inl h0
  · exact Or.inr (Int.le_of_dvd (abs_pos.mpr h0) ((dvd_abs _ _).mpr (affine_orbit_dvd y c M h)))

/-- Si `w₀ = 0` y hay al menos un bloque, `y 1 = y 0`. -/
theorem affine_orbit_fixed_of_zero {A p : ℕ} (y : ℕ → ℕ) (c : ℕ)
    (h0 : y 1 * 2 ^ A = 3 ^ p * y 0 + c)
    (hw : ((2 : ℤ) ^ A - 3 ^ p) * y 0 - c = 0) : y 1 = y 0 := by
  have hz : ((y 1 : ℤ)) * 2 ^ A = 3 ^ p * y 0 + c := by exact_mod_cast h0
  have hy : ((y 1 : ℤ)) * 2 ^ A = (y 0 : ℤ) * 2 ^ A := by linear_combination hz - hw
  have h2 : (0 : ℤ) < 2 ^ A := by positivity
  exact_mod_cast mul_right_cancel₀ h2.ne' hy

/-- Una sucesión de naturales que satisface `y (m+1) · 2^A = 3^p · y m + c` para todo `m`,
con `A ≥ 1`, es constante desde el principio: `y 1 = y 0`. -/
theorem affine_orbit_fixed {A p : ℕ} (hA : 0 < A) (y : ℕ → ℕ) (c : ℕ)
    (h : ∀ m, y (m + 1) * 2 ^ A = 3 ^ p * y m + c) : y 1 = y 0 := by
  set w0 : ℤ := ((2 : ℤ) ^ A - 3 ^ p) * y 0 - c with hw0
  have hw : w0 = 0 := by
    by_contra hne
    set N := w0.natAbs with hN
    have hlt : |w0| < (2 : ℤ) ^ (A * (N + 1)) := by
      rw [Int.abs_eq_natAbs, ← hN]
      have h1 : N < 2 ^ N := Nat.lt_two_pow_self
      have h2 : 2 ^ N ≤ 2 ^ (A * (N + 1)) :=
        Nat.pow_le_pow_right two_pos (by nlinarith)
      exact_mod_cast h1.trans_le h2
    exact hne (Int.eq_zero_of_abs_lt_dvd (affine_orbit_dvd y c (N + 1) fun m _ => h m) hlt)
  exact affine_orbit_fixed_of_zero y c (h 0) hw

/-! ## Exponentes a lo largo de la órbita -/

theorem sExp_pos_of_odd {x : ℕ} (hx : x % 2 = 1) : 0 < sExp x :=
  one_le_padicValNat_of_dvd (by omega) (by omega)

/-- El término constante de la ecuación de órbita en `p` pasos. -/
def cSum (y p : ℕ) : ℕ := ∑ i ∈ range p, 3 ^ (p - 1 - i) * 2 ^ sExpSum y i

/-- Si el patrón de exponentes de largo `p` se repite `M` veces consecutivas desde `i₀`,
los exponentes del bloque `m ≤ M` coinciden con los del bloque `0`. -/
theorem sExp_periodic_iterate {n i₀ p M : ℕ}
    (hper : ∀ i, i₀ ≤ i → i < i₀ + M * p → sExp (syracuse^[i + p] n) = sExp (syracuse^[i] n)) :
    ∀ m ≤ M, ∀ j < p, sExp (syracuse^[(i₀ + j) + m * p] n) = sExp (syracuse^[i₀ + j] n) := by
  intro m
  induction m with
  | zero => intro _ j _; simp
  | succ m ih =>
    intro hm j hj
    rw [Nat.succ_mul, ← add_assoc, hper (i₀ + j + m * p) (by omega) (by nlinarith), ih (by omega) j hj]

/-- Los bloques `y m = S^{i₀ + mp} n` satisfacen la recurrencia afín con `A`, `c` fijos
mientras el patrón se repita. -/
theorem syracuse_block_recurrence {n i₀ p M : ℕ}
    (hper : ∀ i, i₀ ≤ i → i < i₀ + M * p → sExp (syracuse^[i + p] n) = sExp (syracuse^[i] n)) :
    ∀ m < M, syracuse^[i₀ + (m + 1) * p] n * 2 ^ sExpSum (syracuse^[i₀] n) p =
      3 ^ p * syracuse^[i₀ + m * p] n + cSum (syracuse^[i₀] n) p := by
  intro m hm
  have hexp : ∀ j < p, sExp (syracuse^[j] (syracuse^[i₀ + m * p] n)) =
      sExp (syracuse^[j] (syracuse^[i₀] n)) := by
    intro j hj
    rw [← Function.iterate_add_apply, ← Function.iterate_add_apply,
      show j + (i₀ + m * p) = (i₀ + j) + m * p by ring,
      sExp_periodic_iterate hper m hm.le j hj, add_comm]
  have hsum : ∀ j ≤ p, sExpSum (syracuse^[i₀ + m * p] n) j = sExpSum (syracuse^[i₀] n) j := by
    intro j hj
    unfold sExpSum
    exact sum_congr rfl fun i hi => hexp i (by have := mem_range.mp hi; omega)
  have hc : cSum (syracuse^[i₀ + m * p] n) p = cSum (syracuse^[i₀] n) p := by
    unfold cSum
    exact sum_congr rfl fun i hi => by rw [hsum i (mem_range.mp hi).le]
  rw [← hsum p le_rfl, ← hc, show i₀ + (m + 1) * p = p + (i₀ + m * p) by ring,
    Function.iterate_add_apply]
  exact syracuse_iterate_mul_two_pow _ p

theorem sExpSum_pos_of_odd {n : ℕ} (hn : n % 2 = 1) {p : ℕ} (hp : 0 < p) :
    0 < sExpSum n p := by
  unfold sExpSum
  apply sum_pos
  · intro i _
    exact sExp_pos_of_odd (iterate_syracuse_odd hn i)
  · exact nonempty_range_iff.mpr hp.ne'

/-- Cada paso de Syracuse desde un impar quita al menos una dos: `k ≤ A_k`. -/
theorem sExpSum_ge {n : ℕ} (hn : n % 2 = 1) (k : ℕ) : k ≤ sExpSum n k := by
  induction k with
  | zero => simp [sExpSum_zero]
  | succ k ih =>
    rw [sExpSum_succ]
    have := sExp_pos_of_odd (iterate_syracuse_odd hn k)
    omega

/-- **Cota de repeticiones.** Si el patrón de exponentes de largo `p` se repite `M ≥ 1` veces
consecutivas desde `x = S^{i₀} n`, entonces o `x` es `p`-periódico, o
`2^{AM} ≤ (2^A + 3^p) · x + c`. A altura `x`, ningún bloque se repite más de
`~ log₂ x / A` veces seguidas. -/
theorem syracuse_repeat_bound {n i₀ p M : ℕ} (hM : 0 < M)
    (hper : ∀ i, i₀ ≤ i → i < i₀ + M * p → sExp (syracuse^[i + p] n) = sExp (syracuse^[i] n)) :
    syracuse^[p] (syracuse^[i₀] n) = syracuse^[i₀] n ∨
      2 ^ (sExpSum (syracuse^[i₀] n) p * M) ≤
        (2 ^ sExpSum (syracuse^[i₀] n) p + 3 ^ p) * syracuse^[i₀] n
          + cSum (syracuse^[i₀] n) p := by
  set y : ℕ → ℕ := fun m => syracuse^[i₀ + m * p] n with hy
  have hrec : ∀ m < M, y (m + 1) * 2 ^ sExpSum (syracuse^[i₀] n) p =
      3 ^ p * y m + cSum (syracuse^[i₀] n) p := syracuse_block_recurrence hper
  have hy0 : y 0 = syracuse^[i₀] n := by simp [hy]
  have hy1 : y 1 = syracuse^[p] (syracuse^[i₀] n) := by
    simp only [hy, one_mul]
    rw [add_comm, Function.iterate_add_apply]
  rcases affine_orbit_zero_or_large y _ M hrec with h0 | hlarge
  · left
    rw [← hy1, ← hy0]
    exact affine_orbit_fixed_of_zero y _ (hrec 0 hM) h0
  · right
    rw [hy0] at hlarge
    set A := sExpSum (syracuse^[i₀] n) p
    set x := syracuse^[i₀] n
    set c := cSum x p
    have habs : |((2 : ℤ) ^ A - 3 ^ p) * x - c| ≤ (2 ^ A + 3 ^ p) * x + c := by
      have hx : (0 : ℤ) ≤ x := by positivity
      have hc : (0 : ℤ) ≤ c := by positivity
      have h2 : (0 : ℤ) ≤ 2 ^ A := by positivity
      have h3 : (0 : ℤ) ≤ 3 ^ p := by positivity
      rw [abs_le]
      constructor <;> nlinarith
    have := hlarge.trans habs
    exact_mod_cast this

/-- Si los exponentes son periódicos desde `i₀`, la órbita es un ciclo desde `i₀`. -/
theorem syracuse_periodic_of_sExp_periodic {n i₀ p : ℕ} (hn : n % 2 = 1) (hp : 0 < p)
    (hper : ∀ i, i₀ ≤ i → sExp (syracuse^[i + p] n) = sExp (syracuse^[i] n)) :
    syracuse^[p] (syracuse^[i₀] n) = syracuse^[i₀] n := by
  set y : ℕ → ℕ := fun m => syracuse^[i₀ + m * p] n with hy
  have hrec : ∀ m, y (m + 1) * 2 ^ sExpSum (syracuse^[i₀] n) p =
      3 ^ p * y m + cSum (syracuse^[i₀] n) p := fun m =>
    syracuse_block_recurrence (M := m + 1) (fun i hi _ => hper i hi) m (by omega)
  have hA : 0 < sExpSum (syracuse^[i₀] n) p :=
    sExpSum_pos_of_odd (iterate_syracuse_odd hn i₀) hp
  have := affine_orbit_fixed hA y _ hrec
  simp only [hy, one_mul, zero_mul, add_zero] at this
  rw [add_comm, Function.iterate_add_apply] at this
  exact this

/-! ## Corolario: divergente ⇒ aperiódica -/

/-- La órbita de Syracuse de `n` diverge. -/
def SyracuseDivergent (n : ℕ) : Prop := ∀ B, ∃ k, B < syracuse^[k] n

/-- Una órbita que entra en un ciclo es acotada. -/
theorem not_syracuseDivergent_of_periodic {n i₀ p : ℕ} (hp : 0 < p)
    (h : syracuse^[p] (syracuse^[i₀] n) = syracuse^[i₀] n) : ¬ SyracuseDivergent n := by
  intro hdiv
  -- cota: los primeros i₀ + p valores
  obtain ⟨k, hk⟩ := hdiv ((range (i₀ + p)).sup fun j => syracuse^[j] n)
  -- todo iterado k ≥ i₀ es igual a uno con índice en [i₀, i₀ + p)
  have hmod : ∀ k, i₀ ≤ k → syracuse^[k] n = syracuse^[i₀ + (k - i₀) % p] n := by
    intro k hk
    have hfix : ∀ q, syracuse^[i₀ + p * q] n = syracuse^[i₀] n := by
      intro q
      rw [add_comm, Function.iterate_add_apply, Function.iterate_mul]
      exact Function.iterate_fixed h q
    conv_lhs => rw [show k = (k - i₀) % p + (i₀ + p * ((k - i₀) / p)) by
      have := Nat.mod_add_div (k - i₀) p; omega]
    rw [Function.iterate_add_apply, hfix, ← Function.iterate_add_apply, add_comm]
  rcases lt_or_ge k i₀ with hki | hki
  · exact absurd hk (not_lt.mpr (le_sup (f := fun j => syracuse^[j] n) (mem_range.mpr (by omega))))
  · rw [hmod k hki] at hk
    have : i₀ + (k - i₀) % p < i₀ + p := by have := Nat.mod_lt (k - i₀) hp; omega
    exact absurd hk (not_lt.mpr (le_sup (f := fun j => syracuse^[j] n) (mem_range.mpr this)))

/-- **Cota de repeticiones en órbitas divergentes.** Si `n` diverge, ningún patrón de
exponentes de largo `p` se repite `M` veces seguidas desde `x = S^{i₀} n` salvo que
`2^{AM} ≤ (2^A + 3^p) x + c`. -/
theorem divergent_repeat_bound {n i₀ p M : ℕ} (hdiv : SyracuseDivergent n) (hp : 0 < p)
    (hM : 0 < M)
    (hper : ∀ i, i₀ ≤ i → i < i₀ + M * p → sExp (syracuse^[i + p] n) = sExp (syracuse^[i] n)) :
    2 ^ (sExpSum (syracuse^[i₀] n) p * M) ≤
      (2 ^ sExpSum (syracuse^[i₀] n) p + 3 ^ p) * syracuse^[i₀] n
        + cSum (syracuse^[i₀] n) p := by
  rcases syracuse_repeat_bound hM hper with h | h
  · exact absurd hdiv (not_syracuseDivergent_of_periodic hp h)
  · exact h

/-- **Toda órbita divergente tiene vector de exponentes aperiódico.** -/
theorem sExp_not_periodic_of_divergent {n : ℕ} (hn : n % 2 = 1) (hdiv : SyracuseDivergent n) :
    ¬ ∃ i₀ p, 0 < p ∧ ∀ i, i₀ ≤ i → sExp (syracuse^[i + p] n) = sExp (syracuse^[i] n) := by
  rintro ⟨i₀, p, hp, hper⟩
  exact not_syracuseDivergent_of_periodic hp (syracuse_periodic_of_sExp_periodic hn hp hper) hdiv

end Collatz
