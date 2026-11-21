import Collatz.Forge.Basic
import Collatz.Forge.Invariants.SyracuseCycleEquation
import Collatz.Forge.Invariants.ParityAperiodic
import Collatz.Forge.Invariants.DivergentDensity
import Collatz.Forge.Invariants.Terras

/-!
# Órbitas divergentes con exponentes acotados

Hipótesis de trabajo: `n` impar diverge bajo Syracuse y sus exponentes están **acotados**,
`sExp (S^i n) ≤ L` para todo `i` (`BoundedExponents n L`). Es una hipótesis fuerte y no hay
razón para creerla cierta de una órbita divergente hipotética; el interés es que bajo ella
todo lo cuantitativo de `ParityAperiodic` se vuelve explícito.

## Qué se prueba

* **(a) Cotas triviales.** `p ≤ A_p ≤ p·L` y `c_p ≤ 3^p · 2^{pL}`, donde `A_p = sExpSum x p`
  y `c_p = cSum x p` son los coeficientes de la ecuación de órbita en `p` pasos.

* **(b) Cota de repeticiones explícita.** Si el patrón de largo `p` se repite `M ≥ 1` veces
  seguidas desde `x = S^{i₀} n`, entonces `2^{pM} ≤ (2^{pL} + 3^p)·x + 3^p·2^{pL}`, es decir
  `M ≤ log₂((2^{pL} + 3^p)·x + 3^p·2^{pL}) / p`. Es `divergent_repeat_bound` con las cotas
  de (a). Contrapositivo: en todo tramo de `M` bloques con `2^{pM}` mayor que ese número, el
  patrón **cambia** en algún bloque.

* **(c) Conteo de cambios.** Con exponentes en `[1, L]` hay a lo sumo `L^p` patrones de
  largo `p`, y por pigeonhole en `m` bloques alguno aparece `≥ m / L^p` veces — pero no
  necesariamente seguidas, así que (b) no se aplica directo. Lo que sí sale de (b) es un
  conteo de *cambios de patrón*: si `B` acota las alturas `S^{i₀+kp} n` de los bloques
  considerados y `2^{pM} > (2^{pL} + 3^p)·B + 3^p·2^{pL}`, entonces cada ventana de `M`
  bloques consecutivos contiene un cambio (`divergent_bounded_exists_change`). Honestamente: es una restricción cuantitativa sobre cómo puede ser
  una órbita divergente, no una contradicción. Como la órbita tiende a infinito, `B` crece
  y la ventana `M ~ log₂ B / p` se ensancha; la constraint dice que la sucesión de patrones
  tiene "entropía" al menos `1 / (M + 1)` por bloque en cada escala.

* **(d) Residuos mod `2^{L+1}`.** Por Terras (`sExp_eq_of_modEq`), `sExp x` depende solo de
  `x mod 2^{sExp x + 1}`; con `sExp x ≤ L`, depende solo de `x mod 2^{L+1}`. Luego si la
  sucesión de residuos `S^i n mod 2^{L+1}` fuera eventualmente periódica, los exponentes lo
  serían, y `sExp_not_periodic_of_divergent` da que la órbita no diverge. Conclusión:
  **si `n` diverge con exponentes `≤ L`, la sucesión `(S^i n mod 2^{L+1})_i`, que vive en
  un conjunto de `2^L` residuos impares, no es eventualmente periódica.** Esta sí es una
  restricción nueva y limpia (aunque sucesiones así existen de sobra en alfabetos finitos).
-/

namespace Collatz

open Finset

/-- Exponentes de la órbita de Syracuse de `n` acotados por `L`. -/
def BoundedExponents (n L : ℕ) : Prop := ∀ i, sExp (syracuse^[i] n) ≤ L

/-! ## (a) Cotas triviales bajo exponentes acotados -/

/-- `A_p ≤ p·L` si todos los exponentes de la órbita de `x` son `≤ L`. -/
theorem sExpSum_le_of_bounded {x L : ℕ} (hL : BoundedExponents x L) (p : ℕ) :
    sExpSum x p ≤ p * L := by
  induction p with
  | zero => simp [sExpSum_zero]
  | succ p ih =>
    rw [sExpSum_succ, Nat.succ_mul]
    exact Nat.add_le_add ih (hL p)

/-- `p ≤ A_p` para `x` impar (cada paso quita al menos una dos). -/
theorem sExpSum_ge_of_odd {x : ℕ} (hx : x % 2 = 1) (p : ℕ) : p ≤ sExpSum x p :=
  sExpSum_ge hx p

/-- Cota de la suma geométrica `Σ_{i<p} 3^{p-1-i} ≤ 3^p`. -/
theorem bex_sum_three_pow_le (p : ℕ) : ∑ i ∈ range p, 3 ^ (p - 1 - i) ≤ 3 ^ p := by
  rw [sum_range_reflect (fun i => 3 ^ i) p]
  exact (Nat.geomSum_lt (by norm_num) fun k hk => mem_range.mp hk).le

/-- `c_p ≤ 3^p · 2^{pL}` si todos los exponentes de la órbita de `x` son `≤ L`. -/
theorem cSum_le_of_bounded {x L : ℕ} (hL : BoundedExponents x L) (p : ℕ) :
    cSum x p ≤ 3 ^ p * 2 ^ (p * L) := by
  unfold cSum
  calc ∑ i ∈ range p, 3 ^ (p - 1 - i) * 2 ^ sExpSum x i
      ≤ ∑ i ∈ range p, 3 ^ (p - 1 - i) * 2 ^ (p * L) := by
        apply sum_le_sum
        intro i hi
        apply Nat.mul_le_mul_left
        apply Nat.pow_le_pow_right two_pos
        calc sExpSum x i ≤ i * L := sExpSum_le_of_bounded hL i
          _ ≤ p * L := Nat.mul_le_mul_right L (mem_range.mp hi).le
    _ = (∑ i ∈ range p, 3 ^ (p - 1 - i)) * 2 ^ (p * L) := by rw [sum_mul]
    _ ≤ 3 ^ p * 2 ^ (p * L) := Nat.mul_le_mul_right _ (bex_sum_three_pow_le p)

/-- Los exponentes acotados se heredan a cualquier cola `S^{i₀} n`. -/
theorem boundedExponents_iterate {n L : ℕ} (hL : BoundedExponents n L) (i₀ : ℕ) :
    BoundedExponents (syracuse^[i₀] n) L := by
  intro i
  rw [← Function.iterate_add_apply]
  exact hL _

/-! ## (b) Cota de repeticiones explícita -/

/-- **Cota de repeticiones con exponentes acotados.** Si `n` impar diverge con exponentes
`≤ L` y el patrón de largo `p` se repite `M ≥ 1` veces seguidas desde `x = S^{i₀} n`, entonces
`2^{pM} ≤ (2^{pL} + 3^p)·x + 3^p·2^{pL}`. -/
theorem divergent_bounded_repeat_bound {n L i₀ p M : ℕ} (hn : n % 2 = 1)
    (hdiv : SyracuseDivergent n) (hL : BoundedExponents n L) (hp : 0 < p) (hM : 0 < M)
    (hper : ∀ i, i₀ ≤ i → i < i₀ + M * p → sExp (syracuse^[i + p] n) = sExp (syracuse^[i] n)) :
    2 ^ (p * M) ≤ (2 ^ (p * L) + 3 ^ p) * syracuse^[i₀] n + 3 ^ p * 2 ^ (p * L) := by
  have hbase := divergent_repeat_bound hdiv hp hM hper
  set x := syracuse^[i₀] n with hx
  have hxodd : x % 2 = 1 := iterate_syracuse_odd hn i₀
  have hLx : BoundedExponents x L := boundedExponents_iterate hL i₀
  have hA_ge : p ≤ sExpSum x p := sExpSum_ge_of_odd hxodd p
  have hA_le : sExpSum x p ≤ p * L := sExpSum_le_of_bounded hLx p
  have hc : cSum x p ≤ 3 ^ p * 2 ^ (p * L) := cSum_le_of_bounded hLx p
  have h1 : 2 ^ (p * M) ≤ 2 ^ (sExpSum x p * M) :=
    Nat.pow_le_pow_right two_pos (Nat.mul_le_mul_right M hA_ge)
  have h2 : 2 ^ sExpSum x p ≤ 2 ^ (p * L) := Nat.pow_le_pow_right two_pos hA_le
  calc 2 ^ (p * M) ≤ 2 ^ (sExpSum x p * M) := h1
    _ ≤ (2 ^ sExpSum x p + 3 ^ p) * x + cSum x p := hbase
    _ ≤ (2 ^ (p * L) + 3 ^ p) * x + 3 ^ p * 2 ^ (p * L) := by
        apply Nat.add_le_add _ hc
        exact Nat.mul_le_mul_right x (Nat.add_le_add_right h2 _)

/-- Versión logarítmica: `M ≤ log₂((2^{pL} + 3^p)·x + 3^p·2^{pL}) / p`. -/
theorem divergent_bounded_repeat_le_log {n L i₀ p M : ℕ} (hn : n % 2 = 1)
    (hdiv : SyracuseDivergent n) (hL : BoundedExponents n L) (hp : 0 < p) (hM : 0 < M)
    (hper : ∀ i, i₀ ≤ i → i < i₀ + M * p → sExp (syracuse^[i + p] n) = sExp (syracuse^[i] n)) :
    M ≤ Nat.log 2 ((2 ^ (p * L) + 3 ^ p) * syracuse^[i₀] n + 3 ^ p * 2 ^ (p * L)) / p := by
  rw [Nat.le_div_iff_mul_le hp, mul_comm]
  exact Nat.le_log_of_pow_le one_lt_two (divergent_bounded_repeat_bound hn hdiv hL hp hM hper)

/-- **Contrapositivo.** Si `2^{pM}` supera `(2^{pL} + 3^p)·S^{i₀} n + 3^p·2^{pL}`, en el tramo
de `M` bloques de largo `p` desde `i₀` el patrón de exponentes cambia en algún lugar. -/
theorem divergent_bounded_exists_change {n L i₀ p M : ℕ} (hn : n % 2 = 1)
    (hdiv : SyracuseDivergent n) (hL : BoundedExponents n L) (hp : 0 < p) (hM : 0 < M)
    (hbig : (2 ^ (p * L) + 3 ^ p) * syracuse^[i₀] n + 3 ^ p * 2 ^ (p * L) < 2 ^ (p * M)) :
    ∃ i, i₀ ≤ i ∧ i < i₀ + M * p ∧ sExp (syracuse^[i + p] n) ≠ sExp (syracuse^[i] n) := by
  by_contra hcon
  push Not at hcon
  exact absurd (divergent_bounded_repeat_bound hn hdiv hL hp hM hcon) (not_le.mpr hbig)

/-! ## (d) Los residuos mod `2^{L+1}` no son eventualmente periódicos -/

/-- Con `sExp x ≤ L`, el exponente depende solo de `x mod 2^{L+1}`. -/
theorem sExp_eq_of_modEq_of_le {x x' L : ℕ} (hx : sExp x ≤ L)
    (h : x ≡ x' [MOD 2 ^ (L + 1)]) : sExp x' = sExp x :=
  sExp_eq_of_modEq (h.of_dvd (pow_dvd_pow 2 (by omega)))

/-- Si los residuos mod `2^{L+1}` de la órbita son eventualmente periódicos y los exponentes
están acotados por `L`, los exponentes son eventualmente periódicos. -/
theorem sExp_periodic_of_residues_periodic {n L i₀ p : ℕ} (hL : BoundedExponents n L)
    (hres : ∀ i, i₀ ≤ i → syracuse^[i + p] n ≡ syracuse^[i] n [MOD 2 ^ (L + 1)]) :
    ∀ i, i₀ ≤ i → sExp (syracuse^[i + p] n) = sExp (syracuse^[i] n) := fun i hi =>
  sExp_eq_of_modEq_of_le (hL i) (hres i hi).symm

/-- **Divergente con exponentes acotados ⇒ residuos mod `2^{L+1}` aperiódicos.** La sucesión
`(S^i n mod 2^{L+1})_i` toma valores en los `2^L` residuos impares y no es eventualmente
periódica. -/
theorem residues_not_periodic_of_divergent {n L : ℕ} (hn : n % 2 = 1)
    (hdiv : SyracuseDivergent n) (hL : BoundedExponents n L) :
    ¬ ∃ i₀ p, 0 < p ∧ ∀ i, i₀ ≤ i → syracuse^[i + p] n ≡ syracuse^[i] n [MOD 2 ^ (L + 1)] := by
  rintro ⟨i₀, p, hp, hres⟩
  exact sExp_not_periodic_of_divergent hn hdiv
    ⟨i₀, p, hp, sExp_periodic_of_residues_periodic hL hres⟩

end Collatz
