import Collatz.Forge.Basic
import Collatz.Forge.Invariants.SyracuseCycleEquation
import Collatz.Forge.Invariants.ParityAperiodic

/-!
# Terras en Syracuse: el patrón de exponentes es la clase residual

Terras (1976) probó que el vector de paridad de los primeros `k` pasos de `T` es una
biyección entre `ℤ/2^k` y `{0,1}^k`. En Syracuse el enunciado exacto es:

> Para `x, x'` impares, con `A = a₀ + ⋯ + aⱼ₋₁` las doses de los primeros `j` pasos de `x`:
> **los patrones de exponentes de `x` y `x'` coinciden en `j` pasos ⇔ `x ≡ x' (mod 2^{A+1})`.**

El `+1` es real. La ecuación de órbita dice `S^j x · 2^A = 3^j x + c` y `S^j x` es **impar**,
así que `3^j x + c ≡ 2^A (mod 2^{A+1})`, no solo `≡ 0 (mod 2^A)`. Dos `x` con el mismo patrón
(luego mismos `A`, `c`) cumplen `3^j (x − x') ≡ 0 (mod 2^{A+1})`, y `3 ⊥ 2`.

Recíproco por inducción: `x ≡ x' (mod 2^{a₀+1})` fija `nu2 (3x+1)`; dividir por `2^{a₀}`
baja el módulo a `2^{A'+1}` para el resto.

## Por qué importa

Convierte "patrones de exponentes" en "clases residuales mod potencias de 2": cada patrón de
`j` pasos con suma `A` ocupa **exactamente una** clase mod `2^{A+1}`. Es la pieza que habilita
argumentos de conteo: los patrones con densidad baja (`A ≤ j log₂3`) son pocos, luego las
clases residuales donde una órbita divergente puede vivir son pocas (`divergent_dose_density`).
-/

namespace Collatz

open Finset

/-! ## `nu2` depende solo de la clase mod `2^{nu2 + 1}` -/

theorem nu2_eq_of_modEq {m m' : ℕ} (hm : m ≠ 0) (hm' : m' ≠ 0)
    (h : m ≡ m' [MOD 2 ^ (nu2 m + 1)]) : nu2 m' = nu2 m := by
  have h1 : 2 ^ nu2 m ∣ m' := by
    have hlow : m ≡ m' [MOD 2 ^ nu2 m] := h.of_dvd (pow_dvd_pow 2 (Nat.le_succ _))
    exact Nat.modEq_zero_iff_dvd.mp
      (hlow.symm.trans (Nat.modEq_zero_iff_dvd.mpr pow_padicValNat_dvd))
  have h2 : ¬ 2 ^ (nu2 m + 1) ∣ m' := by
    intro hd
    exact pow_succ_padicValNat_not_dvd (p := 2) hm
      (Nat.modEq_zero_iff_dvd.mp (h.trans (Nat.modEq_zero_iff_dvd.mpr hd)))
  have hle : nu2 m ≤ nu2 m' := (padicValNat_dvd_iff_le (p := 2) hm').mp h1
  have hlt : ¬ nu2 m + 1 ≤ nu2 m' := fun hle' =>
    h2 ((padicValNat_dvd_iff_le (p := 2) hm').mpr hle')
  omega

/-- `sExp` depende solo de la clase mod `2^{sExp + 1}`. -/
theorem sExp_eq_of_modEq {x x' : ℕ} (h : x ≡ x' [MOD 2 ^ (sExp x + 1)]) : sExp x' = sExp x :=
  nu2_eq_of_modEq (by omega) (by omega) ((h.mul_left 3).add_right 1)

/-- Desplazamiento de la suma de exponentes: `A(x, j+1) = a₀ + A(S x, j)`. -/
theorem sExpSum_succ' (x j : ℕ) : sExpSum x (j + 1) = sExp x + sExpSum (syracuse x) j := by
  unfold sExpSum
  rw [sum_range_succ', add_comm]
  simp [Function.iterate_succ_apply]

/-! ## Mismo patrón ⇒ misma clase mod `2^{A+1}` -/

theorem sExpSum_eq_of_pattern {x x' : ℕ} (j : ℕ)
    (h : ∀ i < j, sExp (syracuse^[i] x) = sExp (syracuse^[i] x')) :
    sExpSum x j = sExpSum x' j := by
  unfold sExpSum
  exact sum_congr rfl fun i hi => h i (mem_range.mp hi)

theorem cSum_eq_of_pattern {x x' : ℕ} (j : ℕ)
    (h : ∀ i < j, sExp (syracuse^[i] x) = sExp (syracuse^[i] x')) :
    cSum x j = cSum x' j := by
  unfold cSum
  refine sum_congr rfl fun i hi => ?_
  rw [sExpSum_eq_of_pattern i fun l hl => h l (by have := mem_range.mp hi; omega)]

/-- **Terras, ida.** Mismo patrón de `j` pasos ⇒ `x ≡ x' (mod 2^{A+1})`. -/
theorem modEq_of_pattern {x x' : ℕ} (hx : x % 2 = 1) (hx' : x' % 2 = 1) (j : ℕ)
    (h : ∀ i < j, sExp (syracuse^[i] x) = sExp (syracuse^[i] x')) :
    x ≡ x' [MOD 2 ^ (sExpSum x j + 1)] := by
  have hA := sExpSum_eq_of_pattern j h
  have hc := cSum_eq_of_pattern j h
  have e1 : syracuse^[j] x * 2 ^ sExpSum x j = 3 ^ j * x + cSum x j :=
    syracuse_iterate_mul_two_pow x j
  have e2 : syracuse^[j] x' * 2 ^ sExpSum x' j = 3 ^ j * x' + cSum x' j :=
    syracuse_iterate_mul_two_pow x' j
  rw [← hA, ← hc] at e2
  -- los cocientes son impares
  obtain ⟨m, hm⟩ : ∃ m, syracuse^[j] x = 2 * m + 1 :=
    ⟨syracuse^[j] x / 2, by have := iterate_syracuse_odd hx j; omega⟩
  obtain ⟨m', hm'⟩ : ∃ m', syracuse^[j] x' = 2 * m' + 1 :=
    ⟨syracuse^[j] x' / 2, by have := iterate_syracuse_odd hx' j; omega⟩
  rw [hm] at e1
  rw [hm'] at e2
  -- en ℤ: 3^j (x' − x) = 2^{A+1} (m' − m)
  rw [Nat.modEq_iff_dvd]
  have hz1 : ((2 * m + 1 : ℕ) : ℤ) * 2 ^ sExpSum x j = 3 ^ j * x + cSum x j := by
    exact_mod_cast e1
  have hz2 : ((2 * m' + 1 : ℕ) : ℤ) * 2 ^ sExpSum x j = 3 ^ j * x' + cSum x j := by
    exact_mod_cast e2
  have key : (3 : ℤ) ^ j * ((x' : ℤ) - x) = 2 ^ (sExpSum x j + 1) * ((m' : ℤ) - m) := by
    push_cast at hz1 hz2
    rw [pow_succ]
    linear_combination hz1 - hz2
  have hdvd : (2 : ℤ) ^ (sExpSum x j + 1) ∣ 3 ^ j * ((x' : ℤ) - x) := ⟨_, key⟩
  have hcop : IsCoprime ((2 : ℤ) ^ (sExpSum x j + 1)) (3 ^ j) :=
    IsCoprime.pow (Int.isCoprime_iff_gcd_eq_one.mpr (by decide))
  exact hcop.dvd_of_dvd_mul_left hdvd

/-! ## Misma clase mod `2^{A+1}` ⇒ mismo patrón -/

/-- **Terras, vuelta.** `x ≡ x' (mod 2^{A+1})` ⇒ mismo patrón de `j` pasos. -/
theorem pattern_of_modEq (j : ℕ) : ∀ {x x' : ℕ}, x % 2 = 1 → x' % 2 = 1 →
    x ≡ x' [MOD 2 ^ (sExpSum x j + 1)] →
    ∀ i < j, sExp (syracuse^[i] x) = sExp (syracuse^[i] x') := by
  induction j with
  | zero => intro x x' _ _ _ i hi; omega
  | succ j ih =>
    intro x x' hx hx' h i hi
    rw [sExpSum_succ'] at h
    -- a₀ coincide
    have h0 : x ≡ x' [MOD 2 ^ (sExp x + 1)] :=
      h.of_dvd (pow_dvd_pow 2 (by omega))
    have ha : sExp x' = sExp x := sExp_eq_of_modEq h0
    -- S x ≡ S x' mod 2^{A' + 1}
    have hS : syracuse x ≡ syracuse x' [MOD 2 ^ (sExpSum (syracuse x) j + 1)] := by
      have e1 := two_pow_sExp_mul_syracuse x
      have e2 := two_pow_sExp_mul_syracuse x'
      rw [ha] at e2
      rw [Nat.modEq_iff_dvd] at h ⊢
      have hz1 : ((2 : ℤ) ^ sExp x) * syracuse x = 3 * x + 1 := by exact_mod_cast e1
      have hz2 : ((2 : ℤ) ^ sExp x) * syracuse x' = 3 * x' + 1 := by exact_mod_cast e2
      obtain ⟨t, ht⟩ := h
      -- 2^{a₀} (S x' − S x) = 3 (x' − x) = 3 · 2^{a₀ + A' + 1} t
      have key : (2 : ℤ) ^ sExp x * ((syracuse x' : ℤ) - syracuse x) =
          2 ^ sExp x * (2 ^ (sExpSum (syracuse x) j + 1) * (3 * t)) := by
        rw [show (sExp x + sExpSum (syracuse x) j + 1) = sExp x + (sExpSum (syracuse x) j + 1)
          by ring, pow_add] at ht
        push_cast at ht
        linear_combination hz2 - hz1 + 3 * ht
      have h2 : (0 : ℤ) < 2 ^ sExp x := by positivity
      exact ⟨3 * t, mul_left_cancel₀ h2.ne' key⟩
    have hSx : syracuse x % 2 = 1 := Nat.odd_iff.mp (syracuse_odd x)
    have hSx' : syracuse x' % 2 = 1 := Nat.odd_iff.mp (syracuse_odd x')
    have ih' := ih hSx hSx' hS
    rcases i with _ | i
    · simpa using ha.symm
    · rw [Function.iterate_succ_apply, Function.iterate_succ_apply]
      exact ih' i (by omega)

/-- **Terras en Syracuse.** Para `x, x'` impares: mismo patrón de exponentes en `j` pasos
⇔ `x ≡ x' (mod 2^{A(x,j)+1})`. -/
theorem pattern_iff_modEq {x x' : ℕ} (hx : x % 2 = 1) (hx' : x' % 2 = 1) (j : ℕ) :
    (∀ i < j, sExp (syracuse^[i] x) = sExp (syracuse^[i] x')) ↔
      x ≡ x' [MOD 2 ^ (sExpSum x j + 1)] :=
  ⟨modEq_of_pattern hx hx' j, pattern_of_modEq j hx hx'⟩

/-! ## Conteo: clases residuales con `j` pasos y `A` doses -/

theorem sExpSum_add (r i l : ℕ) :
    sExpSum r (i + l) = sExpSum r i + sExpSum (syracuse^[i] r) l := by
  unfold sExpSum
  rw [sum_range_add]
  congr 1
  refine sum_congr rfl fun x _ => ?_
  rw [← Function.iterate_add_apply, add_comm]

theorem sExpSum_strictMono {r : ℕ} (hr : r % 2 = 1) : StrictMono (sExpSum r) := by
  intro i i' hii'
  obtain ⟨l, rfl⟩ : ∃ l, i' = i + (l + 1) := ⟨i' - i - 1, by omega⟩
  rw [sExpSum_add]
  have := sExpSum_ge (iterate_syracuse_odd hr i) (l + 1)
  omega

/-- Los patrones de `j` pasos coinciden si coinciden todas las sumas parciales hasta `j`. -/
theorem pattern_of_partialSums {r r' j : ℕ} (h : ∀ i ≤ j, sExpSum r i = sExpSum r' i) :
    ∀ i < j, sExp (syracuse^[i] r) = sExp (syracuse^[i] r') := by
  intro i hi
  have h1 := h i hi.le
  have h2 := h (i + 1) hi
  rw [sExpSum_succ, sExpSum_succ] at h2
  omega

/-- Las sumas parciales intermedias `A(r, 1), …, A(r, j−1)`, como función de `Fin (j - 1)`. -/
def partialSums (r j : ℕ) : Fin (j - 1) → ℕ := fun i => sExpSum r (i.val + 1)

theorem partialSums_strictMono {r : ℕ} (hr : r % 2 = 1) (j : ℕ) :
    StrictMono (partialSums r j) := fun _ _ h =>
  sExpSum_strictMono hr (Nat.succ_lt_succ (Fin.lt_def.mp h))

/-- El conjunto de residuos impares mod `2^{A+1}` cuyos primeros `j` pasos quitan
exactamente `A` doses. -/
def residueClasses (j A : ℕ) : Finset ℕ :=
  (range (2 ^ (A + 1))).filter fun r => r % 2 = 1 ∧ sExpSum r j = A

/-- La imagen de las sumas parciales: un subconjunto de `[1, A)` de tamaño `j - 1`. -/
def sumsImage (r j : ℕ) : Finset ℕ := univ.image (partialSums r j)

theorem sumsImage_mem {r j A : ℕ} (hr : r % 2 = 1) (hj : 1 ≤ j) (hA : sExpSum r j = A) :
    sumsImage r j ∈ powersetCard (j - 1) (Ico 1 A) := by
  rw [mem_powersetCard]
  constructor
  · intro y hy
    obtain ⟨i, _, rfl⟩ := mem_image.mp hy
    rw [mem_Ico]
    have hlo := sExpSum_ge hr (i.val + 1)
    have hhi : sExpSum r (i.val + 1) < sExpSum r j :=
      sExpSum_strictMono hr (by have := i.isLt; omega)
    unfold partialSums
    omega
  · unfold sumsImage
    rw [card_image_of_injective _ (partialSums_strictMono hr j).injective, card_univ,
      Fintype.card_fin]

theorem mem_residueClasses {j A r : ℕ} :
    r ∈ residueClasses j A ↔ r < 2 ^ (A + 1) ∧ r % 2 = 1 ∧ sExpSum r j = A := by
  unfold residueClasses
  rw [mem_filter, mem_range]

theorem sumsImage_injOn (j : ℕ) (hj : 1 ≤ j) (A : ℕ) :
    Set.InjOn (fun r => sumsImage r j) (residueClasses j A) := by
  intro r hr r' hr' heq
  rw [mem_coe, mem_residueClasses] at hr hr'
  obtain ⟨hrlt, hrodd, hrA⟩ := hr
  obtain ⟨hrlt', hrodd', hrA'⟩ := hr'
  -- mismas sumas parciales
  have hcard : (sumsImage r j).card = j - 1 := by
    unfold sumsImage
    rw [card_image_of_injective _ (partialSums_strictMono hrodd j).injective, card_univ,
      Fintype.card_fin]
  have hf := orderEmbOfFin_unique hcard (f := partialSums r j)
    (fun i => mem_image_of_mem _ (mem_univ i)) (partialSums_strictMono hrodd j)
  have hf' := orderEmbOfFin_unique (s := sumsImage r j) hcard (f := partialSums r' j)
    (fun i => by rw [show sumsImage r j = sumsImage r' j from heq]; exact mem_image_of_mem _ (mem_univ i))
    (partialSums_strictMono hrodd' j)
  have hps : partialSums r j = partialSums r' j := hf.trans hf'.symm
  -- luego mismo patrón, luego misma clase, luego iguales
  have hsums : ∀ i ≤ j, sExpSum r i = sExpSum r' i := by
    intro i hi
    rcases Nat.eq_zero_or_pos i with rfl | hi0
    · simp [sExpSum_zero]
    rcases eq_or_ne i j with rfl | hij
    · rw [hrA, hrA']
    · have := congrFun hps ⟨i - 1, by omega⟩
      unfold partialSums at this
      simpa [Nat.sub_add_cancel hi0] using this
  have hpat := pattern_of_partialSums hsums
  have hmod := modEq_of_pattern hrodd hrodd' j hpat
  rw [hrA] at hmod
  exact ((Nat.ModEq.eq_of_lt_of_lt hmod hrlt hrlt'))

/-- **Conteo.** Hay a lo sumo `C(A−1, j−1)` clases residuales impares mod `2^{A+1}` cuyos
primeros `j` pasos de Syracuse quitan exactamente `A` doses. -/
theorem card_residueClasses_le {j : ℕ} (hj : 1 ≤ j) (A : ℕ) :
    (residueClasses j A).card ≤ (A - 1).choose (j - 1) := by
  have := card_le_card_of_injOn (fun r => sumsImage r j) (t := powersetCard (j - 1) (Ico 1 A))
    (fun r hr => by
      rw [mem_coe, mem_residueClasses] at hr
      rw [mem_coe]
      exact sumsImage_mem hr.2.1 hj hr.2.2)
    (sumsImage_injOn j hj A)
  rwa [card_powersetCard, Nat.card_Ico] at this

end Collatz
