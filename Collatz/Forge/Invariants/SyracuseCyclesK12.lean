import Collatz.Forge.Basic
import Collatz.Forge.Invariants.SyracuseCycleEquation
import Collatz.Forge.Invariants.ParityAperiodic
import Collatz.Forge.Invariants.SyracuseSmallCycles
import Collatz.Forge.Invariants.SyracuseCyclesK5K6
import Collatz.Forge.Invariants.VerifiedRange
import Collatz.Forge.Invariants.Terras
import Collatz.Forge.Invariants.IsPeriodicIffT

/-!
# Ciclos de Syracuse de longitud `k ≥ 12`

Dos herramientas para extender `SyracuseCyclesK5K6.lean` más allá de `k = 11`.

**(1) Enumerador podado.** `compCheck k A f` recorre `a₀ ∈ [1, A]` aunque queden `k − 1`
partes que necesitan al menos una dosis cada una. `k12_compCheck` recorta a
`a₀ ∈ [1, A − (k − 1)]`. Es válido sobre la órbita real porque cada `sExp ≥ 1`
(`sExpSum_ge`: `sExpSum x k ≥ k` para `x` impar). Reduce ~3× los nodos visitados
(para `k = 12`, `A = 20`: 294k nodos frente a 911k) y cierra `k = 12` en ~25 s de kernel
(`k12_no_syracuse_twelve_cycle`). `k12_scan` es la variante que acumula el resto módulo `d`
sin clausuras; está probada (`k12_no_cycle_of_scan`) pero no es más rápida (~26 s en
`k = 12`): el costo es el número de nodos, no el tamaño de los números. Para `k = 13` harían
falta ~140 s (`A ∈ {21, 22}`, 1.6M nodos) y por eso no se incluye.

**(2) Subir `N` en el sándwich.** `cycle_sandwich_of_verified` da, bajo `VerifiedBelow M`,
`3^k < 2^A` y `2^A · M^k ≤ (3M + 1)^k`, es decir `2^A / 3^k ∈ (1, (1 + 1/(3M))^k]`. Cuanto
mayor `M`, más estrecha la ventana, y para la mayoría de los `k` no queda ninguna `A`: el
ciclo se descarta sin enumerar composiciones. Aquí `VerifiedBelow M` **se demuestra** en el
kernel para `M = 600001`: basta ver que todo impar `3 ≤ n ≤ 600000` baja por debajo de sí
mismo bajo `T` (`k12_dropsT`, 24 bloques de `decide +kernel`), y una inducción fuerte da
`ReachesOne n` (`k12_verifiedBelow_600001`). Con ese `N`, `k12_sandwichFree` certifica para
cada `1 ≤ k ≤ 2300` que no hay `A` admisible (`k12_sandwich_table_600001`), de donde
**todo ciclo no trivial de Syracuse tiene `k ≥ 2301`** (`k12_syracuse_cycle_length_ge`),
incondicionalmente. Tiempo total del archivo: ~3 min (25 s el enumerador, 24 × 5.6 s los
bloques, ~2 s la tabla).
-/

namespace Collatz

open Finset

/-! ## (1) Enumerador podado -/

/-- Como `compCheck`, pero la primera parte solo recorre `a₀ ∈ [1, A − k]` cuando quedan
`k` partes más (cada una necesita `≥ 1`). -/
def k12_compCheck : ℕ → ℕ → (ℕ → Bool) → Bool
  | 0, A, f => if A = 0 then f 0 else true
  | k + 1, A, f =>
      (List.range' 1 (A - k)).all fun a => k12_compCheck k (A - a) fun r => f (3 ^ k + 2 ^ a * r)

/-- **Puente podado.** Si `k12_compCheck` acepta el total de doses de la órbita de un impar `n`,
entonces `f` vale en el lado derecho de la ecuación de órbita de `n`. La poda es legítima
porque `sExpSum (syracuse n) k ≥ k`. -/
theorem k12_compCheck_orbit (k : ℕ) :
    ∀ (f : ℕ → Bool) (n : ℕ), n % 2 = 1 → k12_compCheck k (sExpSum n k) f = true →
      f (∑ i ∈ range k, 3 ^ (k - 1 - i) * 2 ^ sExpSum n i) = true := by
  induction k with
  | zero =>
    intro f n _ h
    simpa [k12_compCheck, sExpSum_zero] using h
  | succ k ih =>
    intro f n hn h
    rw [orbit_rhs_succ]
    simp only [k12_compCheck, List.all_eq_true, List.mem_range'_1] at h
    have ha : 1 ≤ sExp n := sExp_pos_of_odd hn
    have hA := sExpSum_succ' n k
    have hodd : syracuse n % 2 = 1 := Nat.odd_iff.mp (syracuse_odd n)
    have hge := sExpSum_ge hodd k
    have hmem : 1 ≤ sExp n ∧ sExp n < 1 + (sExpSum n (k + 1) - k) := ⟨ha, by omega⟩
    have h' := h (sExp n) hmem
    have hsub : sExpSum n (k + 1) - sExp n = sExpSum (syracuse n) k := by omega
    rw [hsub] at h'
    exact ih _ (syracuse n) hodd h'

/-- **Cierre podado.** Igual que `no_cycle_of_compCheck` con el enumerador podado. -/
theorem k12_no_cycle_of_compCheck {n k A d : ℕ} (hn : n % 2 = 1) (h : syracuse^[k] n = n)
    (hA : sExpSum n k = A) (hd : 2 ^ A = 3 ^ k + d)
    (hck : k12_compCheck k A (fun r => r % d != 0) = true) : False := by
  rw [← hA] at hck hd
  have hR := k12_compCheck_orbit k _ n hn hck
  simp only [bne_iff_ne, ne_eq] at hR
  have hid := syracuse_iterate_mul_two_pow n k
  rw [h, hd] at hid
  have : (∑ i ∈ range k, 3 ^ (k - 1 - i) * 2 ^ sExpSum n i) = n * d := by
    have := hid
    rw [mul_add, mul_comm n (3 ^ k)] at this
    omega
  rw [this, Nat.mul_mod_left] at hR
  exact hR rfl

/-- Variante sin clausuras que acumula módulo `d`. Estado: `k` partes restantes, `A` doses
restantes, `r = R mod d` (recurrencia hacia adelante `R ← 3R + 2^s`) y `p = 2^s mod d`. -/
def k12_scan (d : ℕ) : ℕ → ℕ → ℕ → ℕ → Bool
  | 0, A, r, _ => if A = 0 then r != 0 else true
  | k + 1, A, r, p =>
      (List.range' 1 (A - k)).all fun a => k12_scan d k (A - a) ((3 * r + p) % d) (p * 2 ^ a % d)

/-- Recurrencia hacia adelante del término constante: `C_{j+1} = 3 C_j + 2^{s_j}`. -/
theorem k12_cSum_succ (n j : ℕ) : cSum n (j + 1) = 3 * cSum n j + 2 ^ sExpSum n j := by
  unfold cSum
  rw [sum_range_succ, mul_sum]
  congr 1
  · apply sum_congr rfl
    intro i hi
    have := mem_range.mp hi
    rw [show j + 1 - 1 - i = (j - 1 - i) + 1 by omega, pow_succ]
    ring
  · simp

/-- **Puente de `k12_scan`.** Si el barrido acepta desde el punto `syracuse^[j] n` con el estado
real (`C_j mod d`, `2^{s_j} mod d`), entonces `d ∤ C_{j+k}`. -/
theorem k12_scan_orbit (d : ℕ) (n : ℕ) (hn : n % 2 = 1) (k : ℕ) :
    ∀ j, k12_scan d k (sExpSum (syracuse^[j] n) k) (cSum n j % d) (2 ^ sExpSum n j % d) = true →
      cSum n (j + k) % d ≠ 0 := by
  induction k with
  | zero =>
    intro j h
    simp only [k12_scan, sExpSum_zero, if_true, bne_iff_ne, ne_eq] at h
    simpa using h
  | succ k ih =>
    intro j h
    simp only [k12_scan, List.all_eq_true, List.mem_range'_1] at h
    set x := syracuse^[j] n with hx
    have hxodd : x % 2 = 1 := iterate_syracuse_odd hn j
    have hodd : syracuse x % 2 = 1 := Nat.odd_iff.mp (syracuse_odd x)
    have ha : 1 ≤ sExp x := sExp_pos_of_odd hxodd
    have hA := sExpSum_succ' x k
    have hge := sExpSum_ge hodd k
    have h' := h (sExp x) ⟨ha, by omega⟩
    have hsub : sExpSum x (k + 1) - sExp x = sExpSum (syracuse x) k := by omega
    have hsx : syracuse x = syracuse^[j + 1] n := by rw [hx, Function.iterate_succ_apply']
    have hr : (3 * (cSum n j % d) + 2 ^ sExpSum n j % d) % d = cSum n (j + 1) % d := by
      rw [k12_cSum_succ]
      exact ((Nat.mod_modEq _ _).mul_left 3).add (Nat.mod_modEq _ _)
    have hp : 2 ^ sExpSum n j % d * 2 ^ sExp x % d = 2 ^ sExpSum n (j + 1) % d := by
      rw [sExpSum_succ, pow_add]
      exact (Nat.mod_modEq _ _).mul_right _
    rw [hsub, hr, hp, hsx] at h'
    have := ih (j + 1) h'
    rwa [show j + 1 + k = j + (k + 1) by omega] at this

/-- **Cierre de `k12_scan`.** Como `k12_no_cycle_of_compCheck`, con el barrido módulo `d`. -/
theorem k12_no_cycle_of_scan {n k A d : ℕ} (hn : n % 2 = 1) (h : syracuse^[k] n = n)
    (hA : sExpSum n k = A) (hd : 2 ^ A = 3 ^ k + d)
    (hck : k12_scan d k A 0 (1 % d) = true) : False := by
  rw [← hA] at hck hd
  have hR := k12_scan_orbit d n hn k 0 (by simpa [cSum, sExpSum_zero] using hck)
  rw [zero_add] at hR
  have hid := syracuse_iterate_mul_two_pow n k
  rw [h, hd] at hid
  have : cSum n k = n * d := by
    unfold cSum
    rw [mul_add, mul_comm n (3 ^ k)] at hid
    omega
  rw [this, Nat.mul_mod_left] at hR
  exact hR rfl

set_option maxHeartbeats 2000000 in
/-- **`k = 12`, por enumeración.** `A = 20` está forzado por el sándwich con `N = 3` y ninguna
de las 75582 composiciones de `20` en doce partes da `517135 ∣ R_12`. -/
theorem k12_no_syracuse_twelve_cycle {n : ℕ} (hn : n % 2 = 1) (h : syracuse^[12] n = n) :
    n = 1 := by
  by_contra hne
  obtain ⟨h1, h2⟩ := cycle_sandwich_three hn (by norm_num) h hne
  obtain ⟨hlo, hhi⟩ := sExpSum_bounds (n := n) (k := 12) (lo := 19) (hi := 21) (by omega) (by omega)
  exact k12_no_cycle_of_compCheck hn h (by omega : sExpSum n 12 = 20) (d := 517135) (by norm_num)
    (by decide +kernel)

/-! ## (2) `VerifiedBelow M` demostrado en el kernel

Para `M` concreto, `VerifiedBelow M` sale de una comprobación finita: basta que todo impar
`3 ≤ n < M` baje por debajo de sí mismo (los pares bajan en un paso), y una inducción fuerte
da `ReachesOne n`. Se itera `T` en vez de `collatz` (la mitad de pasos en los impares;
`exists_iterate_collatz_eq_iterate_T` traduce) y se comprueban solo los impares. Cada bloque
de `12 500` impares es un `decide +kernel` independiente de ~5.6 s; un solo `decide` grande
se vuelve superlineal y se queda sin memoria (el kernel no libera su caché hasta terminar la
declaración). -/

/-- `k12_dropsT m x fuel = true` sii la órbita de `T` desde `x` baja por debajo de `m` en a lo
sumo `fuel` pasos. -/
def k12_dropsT (m : ℕ) : ℕ → ℕ → Bool
  | _, 0 => false
  | x, fuel + 1 => if x < m then true else k12_dropsT m (T x) fuel

theorem k12_dropsT_sound {m : ℕ} :
    ∀ {x fuel : ℕ}, k12_dropsT m x fuel = true → ∃ j, T^[j] x < m := by
  intro x fuel
  induction fuel generalizing x with
  | zero => intro h; simp [k12_dropsT] at h
  | succ fuel ih =>
    intro h
    unfold k12_dropsT at h
    split at h
    · exact ⟨0, by simpa⟩
    · obtain ⟨j, hj⟩ := ih h
      exact ⟨j + 1, by rw [Function.iterate_succ_apply]; exact hj⟩

/-- Los `cnt` números `lo, lo + 2, …` bajan por debajo de sí mismos bajo `T`. -/
def k12_dropsOdd (lo cnt fuel : ℕ) : Bool :=
  (List.range' lo cnt 2).all fun n => k12_dropsT n (T n) fuel

theorem k12_dropsOdd_spec {lo cnt fuel : ℕ} (h : k12_dropsOdd lo cnt fuel = true) :
    ∀ i < cnt, k12_dropsT (lo + 2 * i) (T (lo + 2 * i)) fuel = true := by
  simp only [k12_dropsOdd, List.all_eq_true, List.mem_range'] at h
  exact fun i hi => h _ ⟨i, hi, rfl⟩

theorem k12_dropsOdd_mem {lo cnt fuel n : ℕ} (h : k12_dropsOdd lo cnt fuel = true)
    (h1 : lo ≤ n) (h2 : n < lo + 2 * cnt) (hpar : n % 2 = lo % 2) :
    k12_dropsT n (T n) fuel = true := by
  have := k12_dropsOdd_spec h ((n - lo) / 2) (by omega)
  rwa [show lo + 2 * ((n - lo) / 2) = n by omega] at this

theorem k12_reachesOne_of_iterate {n m : ℕ} (hm : ReachesOne m) (j : ℕ)
    (h : collatz^[j] n = m) : ReachesOne n := by
  obtain ⟨i, hi⟩ := hm
  exact ⟨i + j, by rw [Function.iterate_add_apply, h, hi]⟩

/-- **Puente.** Si todo impar `3 ≤ n ≤ M` baja por debajo de sí mismo bajo `T`, entonces
`VerifiedBelow (M + 1)`: inducción fuerte; los pares bajan en un paso de `collatz`. -/
theorem k12_verifiedBelow_of_dropsT {M fuel : ℕ}
    (h : ∀ n, 3 ≤ n → n ≤ M → n % 2 = 1 → k12_dropsT n (T n) fuel = true) :
    VerifiedBelow (M + 1) := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro hn hM
    rcases Nat.lt_or_ge n 2 with h1 | h2
    · have : n = 1 := by omega
      subst this; exact reachesOne_one
    rcases Nat.mod_two_eq_zero_or_one n with he | ho
    · have hlt : collatz n < n := by rw [collatz_of_even he]; omega
      exact k12_reachesOne_of_iterate (ih _ hlt (collatz_pos (by omega)) (by omega)) 1 rfl
    · obtain ⟨j, hj⟩ := k12_dropsT_sound (h n (by omega) (by omega) ho)
      have hj' : T^[j + 1] n < n := by rw [Function.iterate_succ_apply]; exact hj
      obtain ⟨m, _, hm⟩ := exists_iterate_collatz_eq_iterate_T n (j + 1)
      rw [← hm] at hj'
      have hpos := iterate_pos (by omega : 0 < n) m
      exact k12_reachesOne_of_iterate (ih _ hj' hpos (by omega)) m rfl

/-! Veinticuatro bloques de `12 500` impares: `[3, 25003)`, `[25003, 50003)`, …,
`[575003, 600003)`. Bloques de `25 000` ya muestran comportamiento superlineal en el kernel
(uno tardó `36 s` en vez de `12 s`); los de `12 500` tardan `~5.6 s` cada uno. -/

set_option maxHeartbeats 4000000 in
theorem k12_dropsOdd_block1 : k12_dropsOdd 3 12500 1000 = true := by decide +kernel

set_option maxHeartbeats 4000000 in
theorem k12_dropsOdd_block2 : k12_dropsOdd 25003 12500 1000 = true := by decide +kernel

set_option maxHeartbeats 4000000 in
theorem k12_dropsOdd_block3 : k12_dropsOdd 50003 12500 1000 = true := by decide +kernel

set_option maxHeartbeats 4000000 in
theorem k12_dropsOdd_block4 : k12_dropsOdd 75003 12500 1000 = true := by decide +kernel

set_option maxHeartbeats 4000000 in
theorem k12_dropsOdd_block5 : k12_dropsOdd 100003 12500 1000 = true := by decide +kernel

set_option maxHeartbeats 4000000 in
theorem k12_dropsOdd_block6 : k12_dropsOdd 125003 12500 1000 = true := by decide +kernel

set_option maxHeartbeats 4000000 in
theorem k12_dropsOdd_block7 : k12_dropsOdd 150003 12500 1000 = true := by decide +kernel

set_option maxHeartbeats 4000000 in
theorem k12_dropsOdd_block8 : k12_dropsOdd 175003 12500 1000 = true := by decide +kernel

set_option maxHeartbeats 4000000 in
theorem k12_dropsOdd_block9 : k12_dropsOdd 200003 12500 1000 = true := by decide +kernel

set_option maxHeartbeats 4000000 in
theorem k12_dropsOdd_block10 : k12_dropsOdd 225003 12500 1000 = true := by decide +kernel

set_option maxHeartbeats 4000000 in
theorem k12_dropsOdd_block11 : k12_dropsOdd 250003 12500 1000 = true := by decide +kernel

set_option maxHeartbeats 4000000 in
theorem k12_dropsOdd_block12 : k12_dropsOdd 275003 12500 1000 = true := by decide +kernel

set_option maxHeartbeats 4000000 in
theorem k12_dropsOdd_block13 : k12_dropsOdd 300003 12500 1000 = true := by decide +kernel

set_option maxHeartbeats 4000000 in
theorem k12_dropsOdd_block14 : k12_dropsOdd 325003 12500 1000 = true := by decide +kernel

set_option maxHeartbeats 4000000 in
theorem k12_dropsOdd_block15 : k12_dropsOdd 350003 12500 1000 = true := by decide +kernel

set_option maxHeartbeats 4000000 in
theorem k12_dropsOdd_block16 : k12_dropsOdd 375003 12500 1000 = true := by decide +kernel

set_option maxHeartbeats 4000000 in
theorem k12_dropsOdd_block17 : k12_dropsOdd 400003 12500 1000 = true := by decide +kernel

set_option maxHeartbeats 4000000 in
theorem k12_dropsOdd_block18 : k12_dropsOdd 425003 12500 1000 = true := by decide +kernel

set_option maxHeartbeats 4000000 in
theorem k12_dropsOdd_block19 : k12_dropsOdd 450003 12500 1000 = true := by decide +kernel

set_option maxHeartbeats 4000000 in
theorem k12_dropsOdd_block20 : k12_dropsOdd 475003 12500 1000 = true := by decide +kernel

set_option maxHeartbeats 4000000 in
theorem k12_dropsOdd_block21 : k12_dropsOdd 500003 12500 1000 = true := by decide +kernel

set_option maxHeartbeats 4000000 in
theorem k12_dropsOdd_block22 : k12_dropsOdd 525003 12500 1000 = true := by decide +kernel

set_option maxHeartbeats 4000000 in
theorem k12_dropsOdd_block23 : k12_dropsOdd 550003 12500 1000 = true := by decide +kernel

set_option maxHeartbeats 4000000 in
theorem k12_dropsOdd_block24 : k12_dropsOdd 575003 12500 1000 = true := by decide +kernel

/-- **`VerifiedBelow 600001`**, demostrado en el kernel: todo `0 < n ≤ 600000` llega a `1`. -/
theorem k12_verifiedBelow_600001 : VerifiedBelow 600001 := by
  apply k12_verifiedBelow_of_dropsT (fuel := 1000)
  intro n h3 hM ho
  rcases Nat.lt_or_ge n 25003 with c1 | c1
  · exact k12_dropsOdd_mem k12_dropsOdd_block1 (by omega) c1 (by omega)
  rcases Nat.lt_or_ge n 50003 with c2 | c2
  · exact k12_dropsOdd_mem k12_dropsOdd_block2 (by omega) c2 (by omega)
  rcases Nat.lt_or_ge n 75003 with c3 | c3
  · exact k12_dropsOdd_mem k12_dropsOdd_block3 (by omega) c3 (by omega)
  rcases Nat.lt_or_ge n 100003 with c4 | c4
  · exact k12_dropsOdd_mem k12_dropsOdd_block4 (by omega) c4 (by omega)
  rcases Nat.lt_or_ge n 125003 with c5 | c5
  · exact k12_dropsOdd_mem k12_dropsOdd_block5 (by omega) c5 (by omega)
  rcases Nat.lt_or_ge n 150003 with c6 | c6
  · exact k12_dropsOdd_mem k12_dropsOdd_block6 (by omega) c6 (by omega)
  rcases Nat.lt_or_ge n 175003 with c7 | c7
  · exact k12_dropsOdd_mem k12_dropsOdd_block7 (by omega) c7 (by omega)
  rcases Nat.lt_or_ge n 200003 with c8 | c8
  · exact k12_dropsOdd_mem k12_dropsOdd_block8 (by omega) c8 (by omega)
  rcases Nat.lt_or_ge n 225003 with c9 | c9
  · exact k12_dropsOdd_mem k12_dropsOdd_block9 (by omega) c9 (by omega)
  rcases Nat.lt_or_ge n 250003 with c10 | c10
  · exact k12_dropsOdd_mem k12_dropsOdd_block10 (by omega) c10 (by omega)
  rcases Nat.lt_or_ge n 275003 with c11 | c11
  · exact k12_dropsOdd_mem k12_dropsOdd_block11 (by omega) c11 (by omega)
  rcases Nat.lt_or_ge n 300003 with c12 | c12
  · exact k12_dropsOdd_mem k12_dropsOdd_block12 (by omega) c12 (by omega)
  rcases Nat.lt_or_ge n 325003 with c13 | c13
  · exact k12_dropsOdd_mem k12_dropsOdd_block13 (by omega) c13 (by omega)
  rcases Nat.lt_or_ge n 350003 with c14 | c14
  · exact k12_dropsOdd_mem k12_dropsOdd_block14 (by omega) c14 (by omega)
  rcases Nat.lt_or_ge n 375003 with c15 | c15
  · exact k12_dropsOdd_mem k12_dropsOdd_block15 (by omega) c15 (by omega)
  rcases Nat.lt_or_ge n 400003 with c16 | c16
  · exact k12_dropsOdd_mem k12_dropsOdd_block16 (by omega) c16 (by omega)
  rcases Nat.lt_or_ge n 425003 with c17 | c17
  · exact k12_dropsOdd_mem k12_dropsOdd_block17 (by omega) c17 (by omega)
  rcases Nat.lt_or_ge n 450003 with c18 | c18
  · exact k12_dropsOdd_mem k12_dropsOdd_block18 (by omega) c18 (by omega)
  rcases Nat.lt_or_ge n 475003 with c19 | c19
  · exact k12_dropsOdd_mem k12_dropsOdd_block19 (by omega) c19 (by omega)
  rcases Nat.lt_or_ge n 500003 with c20 | c20
  · exact k12_dropsOdd_mem k12_dropsOdd_block20 (by omega) c20 (by omega)
  rcases Nat.lt_or_ge n 525003 with c21 | c21
  · exact k12_dropsOdd_mem k12_dropsOdd_block21 (by omega) c21 (by omega)
  rcases Nat.lt_or_ge n 550003 with c22 | c22
  · exact k12_dropsOdd_mem k12_dropsOdd_block22 (by omega) c22 (by omega)
  rcases Nat.lt_or_ge n 575003 with c23 | c23
  · exact k12_dropsOdd_mem k12_dropsOdd_block23 (by omega) c23 (by omega)
  exact k12_dropsOdd_mem k12_dropsOdd_block24 c23 (by omega) (by omega)

/-- Sándwich con `N = 600001`, incondicional (la hipótesis computacional ya está probada). -/
theorem k12_cycle_sandwich_600001 {n k : ℕ} (hn : n % 2 = 1) (hk : 0 < k)
    (h : syracuse^[k] n = n) (hne : n ≠ 1) :
    3 ^ k < 2 ^ sExpSum n k ∧ 2 ^ sExpSum n k * 600001 ^ k ≤ (3 * 600001 + 1) ^ k :=
  cycle_sandwich_of_verified k12_verifiedBelow_600001 hn hk h hne

/-! ## (3) `k` eliminados por el sándwich solo

Para `k` dado, no existe `A` con `3^k < 2^A` y `2^A N^k ≤ (3N+1)^k` sii, con
`A₀ = ⌊log₂ 3^k⌋`, se tiene `(3N+1)^k < 2^{A₀+1} N^k`: toda `A` admisible es `≥ A₀ + 1` y
ya la primera se pasa. `k12_sandwichFree` calcula `A₀` (aproximación + barrido corto) y comprueba las dos
desigualdades; el puente `k12_no_A_of_sandwichFree` solo usa monotonía de `2^·`. -/

/-- Barrido corto: el mayor `A' ∈ [A, A + fuel]` con `2^{A'} ≤ x` (si `2^A ≤ x`). -/
def k12_floorLog2 (x : ℕ) : ℕ → ℕ → ℕ
  | A, 0 => A
  | A, fuel + 1 => if 2 ^ (A + 1) ≤ x then k12_floorLog2 x (A + 1) fuel else A

/-- Certificado de que ninguna `A` satisface el sándwich con `N` en `k` pasos. `A₀` se calcula
partiendo de la aproximación `k · 1054/665 − 1` (convergente de `log₂ 3`, exacta a `±1` para
`k ≤ 5000`) y ajustando con un barrido de `3` pasos; `Nat.log2` no está acelerado en el kernel
(~17 ms por `k`), `Nat.pow` y las comparaciones sí. La corrección no depende de que `A₀`
sea exacto: solo se usan las dos desigualdades comprobadas. -/
def k12_sandwichFree (N k : ℕ) : Bool :=
  let A₀ := k12_floorLog2 (3 ^ k) (k * 1054 / 665 - 1) 3
  decide (2 ^ A₀ ≤ 3 ^ k) && decide ((3 * N + 1) ^ k < 2 ^ (A₀ + 1) * N ^ k)

theorem k12_no_A_of_sandwichFree {N k : ℕ} (h : k12_sandwichFree N k = true) (A : ℕ)
    (h1 : 3 ^ k < 2 ^ A) (h2 : 2 ^ A * N ^ k ≤ (3 * N + 1) ^ k) : False := by
  simp only [k12_sandwichFree, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨hA0, hA1⟩ := h
  set A₀ := k12_floorLog2 (3 ^ k) (k * 1054 / 665 - 1) 3
  have hlt : A₀ < A := by
    by_contra hc
    push Not at hc
    have := Nat.pow_le_pow_right (show 0 < 2 by norm_num) hc
    omega
  have h3 : 2 ^ (A₀ + 1) ≤ 2 ^ A := Nat.pow_le_pow_right (by norm_num) hlt
  have h4 := Nat.mul_le_mul_right (N ^ k) h3
  exact absurd (lt_of_lt_of_le hA1 (h4.trans h2)) (lt_irrefl _)

/-- **Cierre por sándwich.** Bajo `VerifiedBelow M`, si `k12_sandwichFree M k`, no hay
`k`-ciclo no trivial. -/
theorem k12_no_cycle_of_sandwich {M n k : ℕ} (hV : VerifiedBelow M) (hk : 0 < k)
    (hfree : k12_sandwichFree M k = true) (hn : n % 2 = 1) (h : syracuse^[k] n = n) : n = 1 := by
  by_contra hne
  obtain ⟨h1, h2⟩ := cycle_sandwich_of_verified hV hn hk h hne
  exact k12_no_A_of_sandwichFree hfree _ h1 h2

set_option maxHeartbeats 4000000 in
/-- **Tabla.** Con `N = 600001`, el sándwich no deja ninguna `A` para `1 ≤ k ≤ 2300`
(el primer `k` que sobrevive es `2301`, con `A = 3647`; con `N = 100001` sería `971` y con
`N = 400001`, `1636`). -/
theorem k12_sandwich_table_600001 :
    (List.range' 1 2300).all (k12_sandwichFree 600001) = true := by decide +kernel

/-- **Todo ciclo no trivial de Syracuse tiene al menos `2301` pasos.** Incondicional: la
verificación hasta `6·10^5` está en el kernel y el sándwich descarta `1 ≤ k ≤ 2300`. -/
theorem k12_syracuse_cycle_length_ge {n k : ℕ} (hn : n % 2 = 1) (hk : 0 < k)
    (h : syracuse^[k] n = n) (hne : n ≠ 1) : 2301 ≤ k := by
  by_contra hlt
  push Not at hlt
  have htab := k12_sandwich_table_600001
  simp only [List.all_eq_true, List.mem_range'_1] at htab
  exact hne (k12_no_cycle_of_sandwich k12_verifiedBelow_600001 hk
    (htab k ⟨hk, by omega⟩) hn h)

end Collatz
