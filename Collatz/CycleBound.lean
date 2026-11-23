import Collatz.Bridge

/-!
# Fase 3b: cota de ciclos a partir de descenso (no de convergencia)

Para acotar el largo de un ciclo de Syracuse con el sándwich de Forge sólo hace falta que
ningún elemento del ciclo sea `< M`. Eso se deduce de una hipótesis más débil y mucho más
barata de verificar que `VerifiedBelow M`: que todo impar `1 < n < M` **descienda**, es decir,
que algún iterado de Syracuse sea menor que `n`. El mínimo de un ciclo no puede descender.
-/

namespace Collatz

/-- Todo impar `1 < n < M` tiene un iterado de Syracuse menor que él. -/
def DescendsBelow (M : ℕ) : Prop :=
  ∀ n, n % 2 = 1 → 1 < n → n < M → ∃ i, syracuse^[i] n < n

theorem DescendsBelow.mono {M M' : ℕ} (h : DescendsBelow M) (hM : M' ≤ M) : DescendsBelow M' :=
  fun n hn h1 hlt => h n hn h1 (lt_of_lt_of_le hlt hM)

/-- Bajo `DescendsBelow M`, un elemento de un ciclo no trivial de Syracuse es `≥ M`. -/
theorem syracuse_cycle_ge_of_descends {M n k : ℕ} (hD : DescendsBelow M) (hn : n % 2 = 1)
    (hk : 0 < k) (h : syracuse^[k] n = n) (hne : n ≠ 1) : M ≤ n := by
  have hP : Function.IsPeriodicPt syracuse k n := h
  -- el mínimo del ciclo
  have hne' : ((Finset.range k).image fun i => syracuse^[i] n).Nonempty :=
    ⟨n, Finset.mem_image.mpr ⟨0, Finset.mem_range.mpr hk, rfl⟩⟩
  set m := ((Finset.range k).image fun i => syracuse^[i] n).min' hne' with hm
  obtain ⟨j, hj, hjm⟩ := Finset.mem_image.mp (Finset.min'_mem _ hne')
  rw [← hm] at hjm
  have hmin : ∀ i, m ≤ syracuse^[i] n := fun i => by
    rw [← hP.iterate_mod_apply i]
    exact Finset.min'_le _ _ (Finset.mem_image.mpr
      ⟨i % k, Finset.mem_range.mpr (Nat.mod_lt _ hk), rfl⟩)
  have hmn : m ≤ n := hmin 0
  by_contra hlt
  push Not at hlt
  have hmodd : m % 2 = 1 := hjm ▸ iterate_syracuse_odd hn j
  have hm1 : m ≠ 1 := fun h1 =>
    hne (eq_one_of_iterate_syracuse_eq_one h (Finset.mem_range.mp hj).le (hjm.trans h1))
  obtain ⟨i, hi⟩ := hD m hmodd (by omega) (by omega)
  have := hmin (i + j)
  rw [Function.iterate_add_apply, hjm] at this
  omega

/-- **Sándwich bajo descenso.** Bajo `DescendsBelow M`, todo ciclo no trivial de Syracuse de
`k` pasos cumple `3^k < 2^{A_k}` y `2^{A_k} · M^k ≤ (3M + 1)^k`. -/
theorem cycle_sandwich_of_descends {M n k : ℕ} (hD : DescendsBelow M) (hn : n % 2 = 1)
    (hk : 0 < k) (h : syracuse^[k] n = n) (hne : n ≠ 1) :
    3 ^ k < 2 ^ sExpSum n k ∧ 2 ^ sExpSum n k * M ^ k ≤ (3 * M + 1) ^ k := by
  refine cycle_sandwich hk (by omega) (fun i hi => ?_) h
  apply syracuse_cycle_ge_of_descends hD (iterate_syracuse_odd hn i) hk
    (iterate_syracuse_periodic h i)
  intro h1
  exact hne (eq_one_of_iterate_syracuse_eq_one h hi.le h1)


/-! ## De descenso bajo `T` a descenso bajo Syracuse -/

theorem oddPart_half {x : ℕ} (hx : x % 2 = 0) (hpos : 0 < x) : oddPart (x / 2) = oddPart x := by
  obtain ⟨y, rfl⟩ : ∃ y, x = 2 * y := ⟨x / 2, by omega⟩
  rw [show 2 * y / 2 = y by omega, oddPart_two_mul (by omega)]

/-- Para `n` impar, la parte impar de todo iterado de `T` es un iterado de Syracuse. -/
theorem exists_syracuse_eq_oddPart_T {n : ℕ} (hn : n % 2 = 1) :
    ∀ s, ∃ i, syracuse^[i] n = oddPart (T^[s] n) := by
  intro s
  induction s with
  | zero => exact ⟨0, by simp [oddPart_of_odd (Nat.odd_iff.mpr hn)]⟩
  | succ s ih =>
    obtain ⟨i, hi⟩ := ih
    have hpos : 0 < T^[s] n := by
      clear hi
      induction s with
      | zero => simp; omega
      | succ s ih => rw [Function.iterate_succ_apply']; exact T_pos ih
    rw [Function.iterate_succ_apply']
    rcases Nat.mod_two_eq_zero_or_one (T^[s] n) with he | ho
    · rw [T_of_even he, oddPart_half he hpos]; exact ⟨i, hi⟩
    · refine ⟨i + 1, ?_⟩
      rw [T_of_odd ho, Function.iterate_succ_apply', hi,
        oddPart_of_odd (Nat.odd_iff.mpr ho)]
      have h2 : (3 * T^[s] n + 1) % 2 = 0 := by omega
      rw [oddPart_half h2 (by omega)]
      rfl

/-- Todo impar `1 < n < M` tiene un iterado de `T` menor que él. -/
def DescendsT (M : ℕ) : Prop := ∀ n, n % 2 = 1 → 1 < n → n < M → ∃ s, T^[s] n < n

theorem descendsBelow_of_T {M : ℕ} (h : DescendsT M) : DescendsBelow M := by
  intro n hn h1 hM
  obtain ⟨s, hs⟩ := h n hn h1 hM
  obtain ⟨i, hi⟩ := exists_syracuse_eq_oddPart_T hn s
  exact ⟨i, by rw [hi]; exact lt_of_le_of_lt (oddPart_le _) hs⟩

/-! ## Criba de Terras simbólica

El estado `(K, c)` representa `T^[i] (K₀ q + r) = K q + c` para todo `q`. Mientras `K` es par,
la paridad del valor es la de `c`, así que `T (K q + c)` es `(K/2) q + c/2` o
`(3K/2) q + (3c+1)/2`. Si en algún momento `K < K₀` y `c < r`, la clase entera desciende. -/

def symDesc (K₀ r : ℕ) : ℕ → ℕ → ℕ → Bool
  | _, _, 0 => false
  | K, c, fuel + 1 =>
    if K < K₀ ∧ c < r then true
    else if K % 2 = 1 then false
    else if c % 2 = 0 then symDesc K₀ r (K / 2) (c / 2) fuel
    else symDesc K₀ r (3 * K / 2) ((3 * c + 1) / 2) fuel

theorem T_lin_even {K c q : ℕ} (hK : K % 2 = 0) (hc : c % 2 = 0) :
    T (K * q + c) = K / 2 * q + c / 2 := by
  obtain ⟨K', rfl⟩ : ∃ K', K = 2 * K' := ⟨K / 2, by omega⟩
  obtain ⟨c', rfl⟩ : ∃ c', c = 2 * c' := ⟨c / 2, by omega⟩
  rw [T_of_even (by rw [Nat.add_mod, Nat.mul_mod]; simp)]
  simp only [Nat.mul_div_cancel_left _ (by norm_num : 0 < 2)]
  rw [show 2 * K' * q + 2 * c' = 2 * (K' * q + c') by ring]; omega

theorem T_lin_odd {K c q : ℕ} (hK : K % 2 = 0) (hc : c % 2 = 1) :
    T (K * q + c) = 3 * K / 2 * q + (3 * c + 1) / 2 := by
  obtain ⟨K', rfl⟩ : ∃ K', K = 2 * K' := ⟨K / 2, by omega⟩
  obtain ⟨c', rfl⟩ : ∃ c', c = 2 * c' + 1 := ⟨c / 2, by omega⟩
  rw [T_of_odd (by rw [Nat.add_mod, Nat.mul_mod]; simp)]
  rw [show 3 * (2 * K') / 2 = 3 * K' by omega, show (3 * (2 * c' + 1) + 1) / 2 = 3 * c' + 2 by omega,
    show 3 * (2 * K' * q + (2 * c' + 1)) + 1 = 2 * (3 * K' * q + (3 * c' + 2)) by ring]
  omega

theorem symDesc_sound {K₀ r : ℕ} : ∀ {K c fuel : ℕ}, symDesc K₀ r K c fuel = true →
    ∀ q, ∃ s, T^[s] (K * q + c) < K₀ * q + r := by
  intro K c fuel
  induction fuel generalizing K c with
  | zero => intro h; simp [symDesc] at h
  | succ fuel ih =>
    intro h q
    unfold symDesc at h
    split at h
    · rename_i hlt
      refine ⟨0, ?_⟩
      simp only [Function.iterate_zero, id]
      have := Nat.mul_le_mul_right q hlt.1.le
      omega
    · split at h
      · simp at h
      · rename_i _ hK
        have hK' : K % 2 = 0 := by omega
        split at h
        · rename_i hc
          obtain ⟨s, hs⟩ := ih h q
          exact ⟨s + 1, by rw [Function.iterate_succ_apply, T_lin_even hK' hc]; exact hs⟩
        · rename_i hc
          obtain ⟨s, hs⟩ := ih h q
          exact ⟨s + 1, by rw [Function.iterate_succ_apply, T_lin_odd hK' (by omega)]; exact hs⟩

/-! ## Chequeo por bloques de residuos

Versión con operaciones que el kernel acelera (`Nat.beq`, `Nat.blt`, `Nat.ble`, `cond`):
~1.7 veces más rápida que iterar `T` con `if`. -/

def stepB (x : ℕ) : ℕ := cond (Nat.beq (x % 2) 0) (x / 2) ((3 * x + 1) / 2)

theorem stepB_eq (x : ℕ) : stepB x = T x := by
  unfold stepB T
  by_cases h : x % 2 = 0
  · simp [h]
  · have h1 : x % 2 = 1 := by omega
    have : Nat.beq (x % 2) 0 = false := by rw [h1]; rfl
    simp [h, this]

/-- `dropsB m x fuel = true` sii la órbita de `T` desde `x` baja de `m` en `≤ fuel` pasos. -/
def dropsB (m : ℕ) : ℕ → ℕ → Bool
  | _, 0 => false
  | x, fuel + 1 => cond (Nat.blt x m) true (dropsB m (stepB x) fuel)

theorem dropsB_sound {m : ℕ} : ∀ {x fuel : ℕ}, dropsB m x fuel = true → ∃ j, T^[j] x < m := by
  intro x fuel
  induction fuel generalizing x with
  | zero => intro h; simp [dropsB] at h
  | succ fuel ih =>
    intro h
    unfold dropsB at h
    cases hb : Nat.blt x m
    · rw [hb, cond_false] at h
      obtain ⟨j, hj⟩ := ih h
      exact ⟨j + 1, by rw [Function.iterate_succ_apply, ← stepB_eq]; exact hj⟩
    · exact ⟨0, by simpa using hb⟩

/-- Para el residuo `r` mod `2^j`: o la clase desciende simbólicamente, o se comprueba
numéricamente cada `n = 2^j q + r` con `q < Q` (salvo `n ≤ 1`). -/
def residueOK (j Q fuel r : ℕ) : Bool :=
  symDesc (2 ^ j) r (2 ^ j) r (j + 1) ||
    (List.range Q).all fun q =>
      Nat.ble (2 ^ j * q + r) 1 || dropsB (2 ^ j * q + r) (stepB (2 ^ j * q + r)) fuel

/-- Los residuos impares `lo, lo + 2, …` (`cnt` de ellos). -/
def blockOK (j Q fuel lo cnt : ℕ) : Bool := (List.range' lo cnt 2).all (residueOK j Q fuel)

theorem blockOK_mem {j Q fuel lo cnt r : ℕ} (h : blockOK j Q fuel lo cnt = true)
    (h1 : lo ≤ r) (h2 : r < lo + 2 * cnt) (hpar : r % 2 = lo % 2) : residueOK j Q fuel r = true := by
  simp only [blockOK, List.all_eq_true, List.mem_range'] at h
  have := h (lo + 2 * ((r - lo) / 2)) ⟨(r - lo) / 2, by omega, rfl⟩
  rwa [show lo + 2 * ((r - lo) / 2) = r by omega] at this

theorem descendsT_of_residueOK {j Q fuel : ℕ} (hj0 : 0 < j)
    (h : ∀ r, r < 2 ^ j → r % 2 = 1 → residueOK j Q fuel r = true) : DescendsT (2 ^ j * Q) := by
  intro n hn h1 hM
  have hj : 0 < 2 ^ j := by positivity
  set r := n % 2 ^ j
  set q := n / 2 ^ j
  have hnq : n = 2 ^ j * q + r := (Nat.div_add_mod n (2 ^ j)).symm
  have hr : r < 2 ^ j := Nat.mod_lt _ hj
  have hrodd : r % 2 = 1 := by
    have : 2 ∣ 2 ^ j := dvd_pow_self 2 (by omega)
    rw [show r % 2 = n % 2 by simp only [r]; exact Nat.mod_mod_of_dvd n this]; exact hn
  have hq : q < Q := by
    by_contra hc; push Not at hc
    have := Nat.mul_le_mul_left (2 ^ j) hc
    omega
  have hok := h r hr hrodd
  simp only [residueOK, Bool.or_eq_true, List.all_eq_true, List.mem_range] at hok
  rcases hok with hs | hnum
  · obtain ⟨s, hs⟩ := symDesc_sound hs q
    exact ⟨s, by rw [hnq]; exact hs⟩
  · rcases hnum q hq with hle | hd
    · simp [Nat.ble_eq] at hle; omega
    · obtain ⟨s, hs⟩ := dropsB_sound hd
      refine ⟨s + 1, ?_⟩
      rw [Function.iterate_succ_apply, ← stepB_eq, hnq]; exact hs

end Collatz
