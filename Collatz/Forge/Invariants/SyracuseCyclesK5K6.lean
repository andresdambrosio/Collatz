import Collatz.Forge.Basic
import Collatz.Forge.Invariants.SyracuseCycleEquation
import Collatz.Forge.Invariants.ParityAperiodic
import Collatz.Forge.Invariants.SyracuseSmallCycles
import Collatz.Forge.Invariants.Terras

/-!
# Ciclos de Syracuse de longitud 5 a 11

Continuación de `SyracuseSmallCycles.lean` (donde están `k = 1, 2, 3, 4`). La idea es la
misma que en `k = 3`, pero con un enumerador de composiciones evaluado por el kernel en
lugar de `interval_cases` anidado, que no escala.

**Matemática.** En un ciclo no trivial de `k` pasos con `A` doses en total, el sándwich
incondicional `cycle_sandwich_three` da `3^k < 2^A` y `2^A · 3^k ≤ 10^k`, lo que fija `A`:

| `k` | `A` | `d = 2^A − 3^k` |
|-----|-----|-----------------|
| 5   | 8   | 13              |
| 6   | 10  | 295             |
| 7   | 12  | 1909            |
| 8   | 13  | 1631            |
| 9   | 15  | 13085           |
| 10  | 16, 17 | 6487, 72023  |
| 11  | 18, 19 | 84997, 347141 |

La ecuación de órbita (`syracuse_iterate_mul_two_pow`) con `S^k n = n` se lee

  `n · d = R_k(a) := Σ_{i<k} 3^{k-1-i} · 2^{a₀+⋯+a_{i-1}}`,

donde `aᵢ = sExp (S^i n) ≥ 1` (impares) y `Σ aᵢ = A`. Luego `d ∣ R_k(a)` para la composición
`a` de `A` en `k` partes realizada por la órbita. Basta comprobar que **ninguna** composición
de `A` en `k` partes `≥ 1` hace `R_k` divisible por `d`; son 35, 126, 462, 792, 3003,
5005 + 11440 y 19448 + 43758 composiciones respectivamente, y ninguna lo hace (verificado
numéricamente antes de formalizar, sin candidato alguno; tampoco lo hay para `k = 12`,
`A = 20`, pero ahí el kernel ya no termina en tiempo razonable).

**Formalización.** `compCheck k A f` recorre las composiciones de `A` en `k` partes `≥ 1`
por recursión estructural en `k` (la parte `a₀` recorre `1..A` y la recursión continúa con
`A − a₀`), acumulando `R` con la recurrencia `R_{k+1}(a₀, a') = 3^k + 2^{a₀} · R_k(a')`, y
devuelve `true` sii `f R = true` en todas ellas. Se evalúa con `decide +kernel` (reducción
en el kernel, sin `native_decide` ni axiomas extra; el `whnf` del elaborador se ahoga a
partir de `k = 10`). El puente `compCheck_orbit` dice, por inducción en `k` y para todo `n`
impar, que si `compCheck k (sExpSum n k) f = true` entonces `f` vale en el lado derecho de la
ecuación de órbita de `n`. `no_cycle_of_compCheck` empaqueta el final: `compCheck` con
`f r := (r % d != 0)` ⇒ `d ∤ R`; ecuación de órbita ⇒ `R = d · n`; contradicción. Los teoremas
concretos solo combinan sándwich ⇒ `A` (uno o dos valores) y `decide +kernel`.

Tiempos de compilación aproximados (`decide +kernel`): `k ≤ 8` < 1 s cada uno; `k = 9` ~3 s;
`k = 10` ~10 s; `k = 11` ~50 s.
-/

namespace Collatz

open Finset

/-- `compCheck k A f = true` sii `f (R_k a) = true` para toda composición `a` de `A` en `k`
partes `≥ 1`, donde `R_k a = Σ_{i<k} 3^{k-1-i} 2^{a₀+⋯+a_{i-1}}`. Recursión estructural en
`k` para que el kernel la reduzca con `decide`. -/
def compCheck : ℕ → ℕ → (ℕ → Bool) → Bool
  | 0, A, f => if A = 0 then f 0 else true
  | k + 1, A, f =>
      (List.range' 1 A).all fun a => compCheck k (A - a) fun r => f (3 ^ k + 2 ^ a * r)

/-- El lado derecho de la ecuación de órbita satisface `R_{k+1}(n) = 3^k + 2^{a₀} R_k (S n)`. -/
theorem orbit_rhs_succ (n k : ℕ) :
    ∑ i ∈ range (k + 1), 3 ^ (k + 1 - 1 - i) * 2 ^ sExpSum n i =
      3 ^ k + 2 ^ sExp n * ∑ i ∈ range k, 3 ^ (k - 1 - i) * 2 ^ sExpSum (syracuse n) i := by
  rw [sum_range_succ', mul_sum]
  have h1 : ∀ i ∈ range k,
      3 ^ (k + 1 - 1 - (i + 1)) * 2 ^ sExpSum n (i + 1) =
        2 ^ sExp n * (3 ^ (k - 1 - i) * 2 ^ sExpSum (syracuse n) i) := by
    intro i hi
    have hk : k + 1 - 1 - (i + 1) = k - 1 - i := by
      have := mem_range.mp hi
      omega
    rw [hk, sExpSum_succ', pow_add]
    ring
  rw [sum_congr rfl h1]
  simp only [sExpSum_zero, pow_zero, mul_one, Nat.add_sub_cancel, Nat.sub_zero]
  ring

/-- **Puente.** Si `compCheck` acepta el total de doses de la órbita de un impar `n`, entonces
`f` vale en el lado derecho de la ecuación de órbita de `n`. -/
theorem compCheck_orbit (k : ℕ) :
    ∀ (f : ℕ → Bool) (n : ℕ), n % 2 = 1 → compCheck k (sExpSum n k) f = true →
      f (∑ i ∈ range k, 3 ^ (k - 1 - i) * 2 ^ sExpSum n i) = true := by
  induction k with
  | zero =>
    intro f n _ h
    simpa [compCheck, sExpSum_zero] using h
  | succ k ih =>
    intro f n hn h
    rw [orbit_rhs_succ]
    simp only [compCheck, List.all_eq_true, List.mem_range'_1] at h
    have ha : 1 ≤ sExp n := sExp_pos_of_odd hn
    have hA := sExpSum_succ' n k
    have hmem : 1 ≤ sExp n ∧ sExp n < 1 + sExpSum n (k + 1) := ⟨ha, by omega⟩
    have h' := h (sExp n) hmem
    have hsub : sExpSum n (k + 1) - sExp n = sExpSum (syracuse n) k := by omega
    rw [hsub] at h'
    exact ih _ (syracuse n) (Nat.odd_iff.mp (syracuse_odd n)) h'

/-- **Cierre.** Si `A` es el total de doses del ciclo, `2^A = 3^k + d`, y `compCheck` certifica
que ninguna composición hace `d ∣ R_k`, no hay ciclo. -/
theorem no_cycle_of_compCheck {n k A d : ℕ} (hn : n % 2 = 1) (h : syracuse^[k] n = n)
    (hA : sExpSum n k = A) (hd : 2 ^ A = 3 ^ k + d)
    (hck : compCheck k A (fun r => r % d != 0) = true) : False := by
  rw [← hA] at hck hd
  have hR := compCheck_orbit k _ n hn hck
  simp only [bne_iff_ne, ne_eq] at hR
  have hid := syracuse_iterate_mul_two_pow n k
  rw [h, hd] at hid
  have : (∑ i ∈ range k, 3 ^ (k - 1 - i) * 2 ^ sExpSum n i) = n * d := by
    have := hid
    rw [mul_add, mul_comm n (3 ^ k)] at this
    omega
  rw [this, Nat.mul_mod_left] at hR
  exact hR rfl

/-- Del sándwich `3^k < 2^A ≤ 10^k / 3^k` a cotas enteras sobre `A`. -/
theorem sExpSum_bounds {n k lo hi : ℕ} (h1 : 2 ^ lo < 2 ^ sExpSum n k)
    (h2 : 2 ^ sExpSum n k < 2 ^ hi) : lo < sExpSum n k ∧ sExpSum n k < hi :=
  ⟨(Nat.pow_lt_pow_iff_right (by norm_num)).mp h1,
   (Nat.pow_lt_pow_iff_right (by norm_num)).mp h2⟩

/-- **`k = 5`.** No hay 5-ciclos de Syracuse: `A = 8` está forzado y ninguna de las 35
composiciones de `8` en cinco partes da `13 ∣ R_5`. -/
theorem no_syracuse_five_cycle {n : ℕ} (hn : n % 2 = 1) (h : syracuse^[5] n = n) : n = 1 := by
  by_contra hne
  obtain ⟨h1, h2⟩ := cycle_sandwich_three hn (by norm_num) h hne
  obtain ⟨hlo, hhi⟩ := sExpSum_bounds (n := n) (k := 5) (lo := 7) (hi := 9) (by omega) (by omega)
  exact no_cycle_of_compCheck hn h (by omega : sExpSum n 5 = 8) (d := 13) (by norm_num) (by decide +kernel)

/-- **`k = 6`.** No hay 6-ciclos de Syracuse: `A = 10` está forzado y ninguna de las 126
composiciones de `10` en seis partes da `295 ∣ R_6`. -/
theorem no_syracuse_six_cycle {n : ℕ} (hn : n % 2 = 1) (h : syracuse^[6] n = n) : n = 1 := by
  by_contra hne
  obtain ⟨h1, h2⟩ := cycle_sandwich_three hn (by norm_num) h hne
  obtain ⟨hlo, hhi⟩ := sExpSum_bounds (n := n) (k := 6) (lo := 9) (hi := 11) (by omega) (by omega)
  exact no_cycle_of_compCheck hn h (by omega : sExpSum n 6 = 10) (d := 295) (by norm_num) (by decide +kernel)

/-- **`k = 7`.** No hay 7-ciclos de Syracuse: `A = 12` está forzado y ninguna de las 462
composiciones de `12` en siete partes da `1909 ∣ R_7`. -/
theorem no_syracuse_seven_cycle {n : ℕ} (hn : n % 2 = 1) (h : syracuse^[7] n = n) : n = 1 := by
  by_contra hne
  obtain ⟨h1, h2⟩ := cycle_sandwich_three hn (by norm_num) h hne
  obtain ⟨hlo, hhi⟩ := sExpSum_bounds (n := n) (k := 7) (lo := 11) (hi := 13) (by omega) (by omega)
  exact no_cycle_of_compCheck hn h (by omega : sExpSum n 7 = 12) (d := 1909) (by norm_num) (by decide +kernel)

/-- **`k = 8`.** No hay 8-ciclos de Syracuse: `A = 13` está forzado y ninguna de las 792
composiciones de `13` en ocho partes da `1631 ∣ R_8`. -/
theorem no_syracuse_eight_cycle {n : ℕ} (hn : n % 2 = 1) (h : syracuse^[8] n = n) : n = 1 := by
  by_contra hne
  obtain ⟨h1, h2⟩ := cycle_sandwich_three hn (by norm_num) h hne
  obtain ⟨hlo, hhi⟩ := sExpSum_bounds (n := n) (k := 8) (lo := 12) (hi := 14) (by omega) (by omega)
  exact no_cycle_of_compCheck hn h (by omega : sExpSum n 8 = 13) (d := 1631) (by norm_num) (by decide +kernel)

/-- **`k = 9`.** No hay 9-ciclos de Syracuse: `A = 15` está forzado y ninguna de las 3003
composiciones de `15` en nueve partes da `13085 ∣ R_9`. -/
theorem no_syracuse_nine_cycle {n : ℕ} (hn : n % 2 = 1) (h : syracuse^[9] n = n) : n = 1 := by
  by_contra hne
  obtain ⟨h1, h2⟩ := cycle_sandwich_three hn (by norm_num) h hne
  obtain ⟨hlo, hhi⟩ := sExpSum_bounds (n := n) (k := 9) (lo := 14) (hi := 16) (by omega) (by omega)
  exact no_cycle_of_compCheck hn h (by omega : sExpSum n 9 = 15) (d := 13085) (by norm_num) (by decide +kernel)

/-- **`k = 10`.** No hay 10-ciclos de Syracuse: `A ∈ {16, 17}` y ninguna composición da
`6487 ∣ R_10` (5005 casos) ni `72023 ∣ R_10` (11440 casos). -/
theorem no_syracuse_ten_cycle {n : ℕ} (hn : n % 2 = 1) (h : syracuse^[10] n = n) : n = 1 := by
  by_contra hne
  obtain ⟨h1, h2⟩ := cycle_sandwich_three hn (by norm_num) h hne
  obtain ⟨hlo, hhi⟩ := sExpSum_bounds (n := n) (k := 10) (lo := 15) (hi := 18) (by omega) (by omega)
  rcases (by omega : sExpSum n 10 = 16 ∨ sExpSum n 10 = 17) with hA | hA
  · exact no_cycle_of_compCheck hn h hA (d := 6487) (by norm_num) (by decide +kernel)
  · exact no_cycle_of_compCheck hn h hA (d := 72023) (by norm_num) (by decide +kernel)

set_option maxHeartbeats 1000000 in
/-- **`k = 11`.** No hay 11-ciclos de Syracuse: `A ∈ {18, 19}` y ninguna composición da
`84997 ∣ R_11` (19448 casos) ni `347141 ∣ R_11` (43758 casos). El caso `A = 19` supera los
200k heartbeats por defecto (~40 s de kernel); se le da margen. -/
theorem no_syracuse_eleven_cycle {n : ℕ} (hn : n % 2 = 1) (h : syracuse^[11] n = n) :
    n = 1 := by
  by_contra hne
  obtain ⟨h1, h2⟩ := cycle_sandwich_three hn (by norm_num) h hne
  obtain ⟨hlo, hhi⟩ := sExpSum_bounds (n := n) (k := 11) (lo := 17) (hi := 20) (by omega) (by omega)
  rcases (by omega : sExpSum n 11 = 18 ∨ sExpSum n 11 = 19) with hA | hA
  · exact no_cycle_of_compCheck hn h hA (d := 84997) (by norm_num) (by decide +kernel)
  · exact no_cycle_of_compCheck hn h hA (d := 347141) (by norm_num) (by decide +kernel)

end Collatz
