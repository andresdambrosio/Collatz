import Collatz.Forge.Invariants.IsPeriodicIffT

/-!
# El "algoritmo de aniquilación" de Opfer (2011) es el mapa de Collatz

G. Opfer, *An analytic approach to the Collatz 3n + 1 problem*, Hamburger Beiträge zur Angewandten
Mathematik 2011-09, anunció una prueba de la conjetura vía las ecuaciones funcionales de Berg–Meinardus.
El paso clave (Teorema 4.17) dice que su *algoritmo de aniquilación* (Algoritmo 4.10), aplicado a
cualquier par `2ℓ > 8`, termina en `8`. El propio autor retiró la afirmación (nota del 17/06/2011).

Acá formalizamos el algoritmo tal como está escrito (algoritmos "forward" 3.1 y "backward" 3.4) y
probamos que **su Teorema 4.17 es equivalente a la conjetura de Collatz**: un paso de aniquilación es
`2x ↦ 2·T^[t+1] x`, o sea recorrer la órbita de `x` bajo el mapa acelerado `T` hasta el primer valor par y
dividirlo por 2. Así que el argumento del "árbol de aniquilación" de la p. 11 supone lo que quiere probar.

* `fwd j`: Algoritmo 3.1. Mientras `j` es impar, `j := (3j+1)/2`; devuelve el primer valor par.
* `bwd m`: Algoritmo 3.4. Mientras `m ≥ 5` y `3 ∣ m + 1`, `m := (2m−1)/3`.
* `annih v = fwd (bwd (v/2))`: un paso del Algoritmo 4.10 sobre la columna `2ℓ`.

Lectura del Teorema 4.17: "para todo par `v ≥ 6`, alguna iteración de `annih` vale `8`". (El 6 entra porque
la tabla de Opfer tiene la fila `6, 6, 3` que lleva a `8`: `annih 6 = 8`.)
-/

namespace Collatz.Opfer

open Collatz

/-- Algoritmo 3.1 (forward): avanzar con `(3j+1)/2` mientras `j` sea impar. Termina porque cada paso
baja en 1 la valuación 2-ádica de `j + 1`. -/
def fwd (j : ℕ) : ℕ :=
  if h : j % 2 = 1 then fwd ((3 * j + 1) / 2) else j
termination_by padicValNat 2 (j + 1)
decreasing_by
  have h2 : 2 ∣ j + 1 := by omega
  have hpos : (j + 1) / 2 ≠ 0 := by omega
  have e : (3 * j + 1) / 2 + 1 = 3 * ((j + 1) / 2) := by omega
  rw [e, padicValNat.mul (by norm_num) hpos, padicValNat.div h2]
  have h3 : padicValNat 2 3 = 0 := padicValNat.eq_zero_of_not_dvd (by norm_num)
  have h1 : 1 ≤ padicValNat 2 (j + 1) := one_le_padicValNat_of_dvd (by omega) h2
  omega

/-- Algoritmo 3.4 (backward): retroceder con `(2m−1)/3` mientras `m ≥ 5` y `3 ∣ m + 1`. -/
def bwd (m : ℕ) : ℕ :=
  if h : 5 ≤ m ∧ (m + 1) % 3 = 0 then bwd ((2 * m - 1) / 3) else m
termination_by m
decreasing_by omega

/-- Un paso del algoritmo de aniquilación (Algoritmo 4.10) sobre la columna `2ℓ`. -/
def annih (v : ℕ) : ℕ := fwd (bwd (v / 2))

theorem fwd_of_even {j : ℕ} (h : j % 2 = 0) : fwd j = j := by
  rw [fwd]; simp [show ¬ j % 2 = 1 by omega]

theorem fwd_of_odd {j : ℕ} (h : j % 2 = 1) : fwd j = fwd (T j) := by
  rw [fwd]; simp [h, T_of_odd h]

/-- `fwd j` es un iterado de `T` y es par. -/
theorem fwd_spec (j : ℕ) : ∃ t, fwd j = T^[t] j ∧ fwd j % 2 = 0 := by
  induction h : padicValNat 2 (j + 1) using Nat.strong_induction_on generalizing j with
  | _ n ih =>
    rcases Nat.mod_two_eq_zero_or_one j with he | ho
    · exact ⟨0, by simp [fwd_of_even he], by rw [fwd_of_even he]; exact he⟩
    · have h2 : 2 ∣ j + 1 := by omega
      have hpos : (j + 1) / 2 ≠ 0 := by omega
      have e : T j + 1 = 3 * ((j + 1) / 2) := by rw [T_of_odd ho]; omega
      have hlt : padicValNat 2 (T j + 1) < n := by
        rw [e, padicValNat.mul (by norm_num) hpos, padicValNat.div h2, ← h]
        have h3 : padicValNat 2 3 = 0 := padicValNat.eq_zero_of_not_dvd (by norm_num)
        have h1 : 1 ≤ padicValNat 2 (j + 1) := one_le_padicValNat_of_dvd (by omega) h2
        omega
      obtain ⟨t, ht, hev⟩ := ih _ hlt (T j) rfl
      refine ⟨t + 1, ?_, ?_⟩
      · rw [fwd_of_odd ho, ht, Function.iterate_succ_apply]
      · rw [fwd_of_odd ho]; exact hev

/-- El algoritmo backward no cambia el resultado del forward: `bwd m` está en la misma corrida impar. -/
theorem fwd_bwd (m : ℕ) : fwd (bwd m) = fwd m := by
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    by_cases hc : 5 ≤ m ∧ (m + 1) % 3 = 0
    · have hb : bwd m = bwd ((2 * m - 1) / 3) := by rw [bwd]; simp [hc]
      have hlt : (2 * m - 1) / 3 < m := by omega
      have hodd : ((2 * m - 1) / 3) % 2 = 1 := by omega
      have hT : T ((2 * m - 1) / 3) = m := by rw [T_of_odd hodd]; omega
      rw [hb, ih _ hlt, fwd_of_odd hodd, hT]
    · have hb : bwd m = m := by rw [bwd]; simp [hc]
      rw [hb]

theorem annih_double (x : ℕ) : annih (2 * x) = fwd x := by
  simp [annih, fwd_bwd]

/-- Un paso de aniquilación: `2x ↦ 2·T^[t+1] x`. -/
theorem annih_double_eq (x : ℕ) : ∃ t, annih (2 * x) = 2 * T^[t + 1] x := by
  obtain ⟨t, ht, hev⟩ := fwd_spec x
  refine ⟨t, ?_⟩
  rw [annih_double, Function.iterate_succ_apply', ← ht, T_of_even hev]
  omega

/-- Toda la columna `2ℓ` de una tabla de aniquilación es `2·(órbita de T)`. -/
theorem annih_iterate (x i : ℕ) : ∃ s, annih^[i] (2 * x) = 2 * T^[s] x := by
  induction i with
  | zero => exact ⟨0, by simp⟩
  | succ i ih =>
    obtain ⟨s, hs⟩ := ih
    obtain ⟨t, ht⟩ := annih_double_eq (T^[s] x)
    refine ⟨t + 1 + s, ?_⟩
    rw [Function.iterate_succ_apply', hs, ht, Function.iterate_add_apply T (t + 1) s x]

/-- El Teorema 4.17 de Opfer, tal como lo usa su prueba. -/
def Theorem_4_17 : Prop := ∀ v, 6 ≤ v → v % 2 = 0 → ∃ i, annih^[i] v = 8

/-- **El Teorema 4.17 de Opfer implica la conjetura de Collatz.** -/
theorem collatz_of_theorem_4_17 (h : Theorem_4_17) : CollatzConjecture := by
  intro n hn
  have hT : ∃ s, T^[s] n = 1 := by
    rcases (show n = 1 ∨ n = 2 ∨ 3 ≤ n by omega) with h1 | h2 | h3
    · exact ⟨0, by simp [h1]⟩
    · exact ⟨1, by simp [h2, T]⟩
    · obtain ⟨i, hi⟩ := h (2 * n) (by omega) (by omega)
      obtain ⟨s, hs⟩ := annih_iterate n i
      have h4 : T^[s] n = 4 := by omega
      refine ⟨s + 2, ?_⟩
      rw [show s + 2 = 2 + s by omega, Function.iterate_add_apply, h4]
      rfl
  obtain ⟨s, hs⟩ := hT
  obtain ⟨m, -, hm⟩ := exists_iterate_collatz_eq_iterate_T n s
  exact ⟨m, hm.trans hs⟩

/-- Si la órbita clásica de `n > 0` llega a 1, también la de `T`. -/
theorem T_reaches_of_collatz (k : ℕ) : ∀ n, 0 < n → collatz^[k] n = 1 → ∃ s, T^[s] n = 1 := by
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    intro n hn hk
    by_cases h1 : n = 1
    · exact ⟨0, by simp [h1]⟩
    rcases Nat.mod_two_eq_zero_or_one n with he | ho
    · obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by
        rcases k with _ | k
        · simp at hk; omega
        · omega⟩
      rw [Function.iterate_succ_apply, collatz_of_even he] at hk
      obtain ⟨s, hs⟩ := ih k' (by omega) (n / 2) (by omega) hk
      exact ⟨s + 1, by rw [Function.iterate_succ_apply, T_of_even he]; exact hs⟩
    · obtain ⟨k', rfl⟩ : ∃ k', k = k' + 2 := ⟨k - 2, by
        rcases k with _ | _ | k
        · simp at hk; omega
        · simp [collatz_of_odd ho] at hk; omega
        · omega⟩
      have hev : (3 * n + 1) % 2 = 0 := by omega
      rw [show k' + 2 = k' + 1 + 1 by rfl, Function.iterate_succ_apply, Function.iterate_succ_apply,
        collatz_of_odd ho, collatz_of_even hev] at hk
      obtain ⟨s, hs⟩ := ih k' (by omega) ((3 * n + 1) / 2) (by omega) hk
      exact ⟨s + 1, by rw [Function.iterate_succ_apply, T_of_odd ho]; exact hs⟩

/-- Si la órbita de `x ≥ 3` bajo `T` llega a 1, la columna de aniquilación que empieza en `2x` llega a 8. -/
theorem annih_reaches_eight (s : ℕ) : ∀ x, 3 ≤ x → T^[s] x = 1 → ∃ i, annih^[i] (2 * x) = 8 := by
  induction s with
  | zero => intro x hx hs; simp at hs; omega
  | succ s ih =>
    intro x hx hs
    rw [Function.iterate_succ_apply] at hs
    by_cases h4 : x = 4
    · exact ⟨0, by simp [h4]⟩
    rcases Nat.mod_two_eq_zero_or_one x with he | ho
    · -- par ≠ 4: el paso es `2x ↦ x = 2·(x/2)`
      have hTx : T x = x / 2 := T_of_even he
      obtain ⟨i, hi⟩ := ih (T x) (by omega) hs
      refine ⟨i + 1, ?_⟩
      rw [Function.iterate_succ_apply, annih_double, fwd_of_even he]
      rw [hTx] at hi
      rwa [show x = 2 * (x / 2) by omega]
    · -- impar: `annih (2x) = fwd x = fwd (T x) = annih (2·T x)`
      have hTx : T x = (3 * x + 1) / 2 := T_of_odd ho
      obtain ⟨i, hi⟩ := ih (T x) (by omega) hs
      have hstep : annih (2 * x) = annih (2 * T x) := by
        rw [annih_double, annih_double, fwd_of_odd ho]
      rcases i with _ | i
      · simp at hi; omega
      · refine ⟨i + 1, ?_⟩
        rw [Function.iterate_succ_apply, hstep, ← Function.iterate_succ_apply]
        exact hi

/-- **El Teorema 4.17 de Opfer es equivalente a la conjetura de Collatz.** -/
theorem theorem_4_17_iff_collatz : Theorem_4_17 ↔ CollatzConjecture := by
  refine ⟨collatz_of_theorem_4_17, fun hC v hv hev => ?_⟩
  obtain ⟨k, hk⟩ := hC (v / 2) (by omega)
  obtain ⟨s, hs⟩ := T_reaches_of_collatz k (v / 2) (by omega) hk
  have := annih_reaches_eight s (v / 2) (by omega) hs
  rwa [show 2 * (v / 2) = v by omega] at this

end Collatz.Opfer
