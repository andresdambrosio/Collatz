/-! Collatz: definiciones y resultados parciales demostrados (sin Mathlib). -/

def T (n : Nat) : Nat := if n % 2 = 0 then n / 2 else 3 * n + 1

def iter : Nat → Nat → Nat
  | 0,     n => n
  | k + 1, n => iter k (T n)

/-- La conjetura (NO demostrada): todo n ≥ 1 llega a 1. -/
def Collatz : Prop := ∀ n, n ≥ 1 → ∃ k, iter k n = 1

theorem iter_add (a b n : Nat) : iter (a + b) n = iter b (iter a n) := by
  induction a generalizing n with
  | zero => simp [iter]
  | succ a ih => rw [Nat.succ_add]; simp [iter, ih]

/-- Las potencias de 2 llegan a 1. -/
theorem pow_two_reaches (m : Nat) : iter m (2 ^ m) = 1 := by
  induction m with
  | zero => rfl
  | succ m ih =>
    have h : T (2 ^ (m+1)) = 2 ^ m := by
      unfold T; rw [Nat.pow_succ]; simp [Nat.mul_mod_left]
    simp [iter, h, ih]

/-- Los pares descienden en un paso. -/
theorem even_descends (n : Nat) (h : n % 2 = 0) (hn : n ≥ 2) : iter 1 n < n := by
  simp [iter, T, h]; omega

/-- Los n ≡ 1 (mod 4), n > 1, descienden en tres pasos: 4k+1 → 12k+4 → 6k+2 → 3k+1. -/
theorem one_mod_four_descends (n : Nat) (h : n % 4 = 1) (hn : n > 1) : iter 3 n < n := by
  have h2 : n % 2 = 1 := by omega
  have e1 : (3*n+1) % 2 = 0 := by omega
  have e2 : ((3*n+1)/2) % 2 = 0 := by omega
  simp [iter, T, h2, e1, e2]; omega

/-- Reducción clave: basta probar que todo n > 1 alcanza algún valor menor (y ≥ 1). -/
theorem collatz_of_descent
    (H : ∀ n, n > 1 → ∃ k, iter k n < n ∧ iter k n ≥ 1) : Collatz := by
  intro n hn
  induction n using Nat.strongRecOn with
  | _ n ih =>
    by_cases h1 : n = 1
    · exact ⟨0, h1⟩
    · obtain ⟨k, hk, hk1⟩ := H n (by omega)
      obtain ⟨j, hj⟩ := ih _ hk hk1
      exact ⟨k + j, by rw [iter_add]; exact hj⟩

/-- Comprobador con combustible. -/
def reachesWithin : Nat → Nat → Bool
  | 0,     n => n == 1
  | f + 1, n => n == 1 || reachesWithin f (T n)

theorem reachesWithin_sound (f n : Nat) (h : reachesWithin f n = true) : ∃ k, iter k n = 1 := by
  induction f generalizing n with
  | zero => exact ⟨0, by simpa [reachesWithin, iter] using h⟩
  | succ f ih =>
    simp [reachesWithin] at h
    rcases h with h | h
    · exact ⟨0, h⟩
    · obtain ⟨k, hk⟩ := ih _ h; exact ⟨k+1, hk⟩

/-- Verificación para 1 ≤ n ≤ 1000 (cada uno llega a 1 en ≤ 200 pasos). -/
theorem collatz_upto_1000 : ∀ n, 1 ≤ n → n ≤ 1000 → ∃ k, iter k n = 1 := by
  have hall : (List.range 1000).all (fun i => reachesWithin 200 (i+1)) = true := by native_decide
  intro n h1 h2
  apply reachesWithin_sound 200
  have := List.all_eq_true.mp hall (n-1) (List.mem_range.mpr (by omega))
  simpa [show n - 1 + 1 = n by omega] using this
