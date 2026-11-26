import Collatz.Forge.Invariants.SyracuseCyclesK12

/-!
# Clases de residuos forzadas: certificados de deriva verificados en el kernel

Una clase `A` (unión de condiciones `n ≡ r (mod 2^k)`) es **forzada** si toda órbita de Collatz
(mapa clásico `collatz`) que no llega a `1` pasa por algún `n` de `A`. Yolcu, Aaronson y Heule
(2023) probaron varias clases forzadas mod 4 y mod 8 por reescritura. El paper rStation collatz_32
(fourier_wren, 2026) da un certificado más simple (grafo de residuos más potencial de deriva más
"pins" de ciclos) y encuentra clases nuevas mod 16 y mod 32.

Acá formalizamos una **versión entera** de ese certificado y probamos su corrección
(`Cert.forced`). El certificado da, para cada residuo `u` módulo `2^g` que no está en `A`:

* un **nivel** `L u`, que no crece a lo largo de las aristas del grafo de residuos;
* en los niveles de **potencial**, un entero `Φ u ≥ 0` con
  `Φ v + a + 1 ≤ Φ u` en los pasos impares y `Φ v + 1 ≤ Φ u + M` en los pares, con
  `(3X₀+1)^M ≤ 2^a X₀^M`. Entonces `x^M · 2^Φ` se divide por dos en cada paso mientras `x ≥ X₀`;
* en los niveles de **pin**, un entero `P u` (pin escalado por `D`) con `P v = 3 P u + D` en los
  pasos impares y `2 P v = P u` en los pares. Entonces `D x − P` se multiplica por `3` o se divide
  por `2`, y tiene que ser `0`. El certificado exige que ningún pin sea entero positivo salvo `1, 2, 4`.

Los números chicos (`< X₀ ≤ 600001`) se cubren con `k12_verifiedBelow_600001` (kernel).
-/

namespace Collatz

namespace Forced

/-- Árbol binario para tablas indexadas por residuo: se baja por los bits de `u`, del menos
significativo al más significativo (búsqueda en `O(g)` pasos, también en el kernel). -/
inductive BT (α : Type) where
  | leaf : α → BT α
  | node : BT α → BT α → BT α

/-- Valor de la tabla en `u`. -/
def BT.get {α : Type} : BT α → ℕ → α
  | .leaf v, _ => v
  | .node l r, u => if u % 2 = 0 then l.get (u / 2) else r.get (u / 2)

/-- Certificado de clase forzada. La clase es la unión de las condiciones `x ≡ r (mod 2^k)`
para `(k, r) ∈ A`. Las tablas (`lvl`, `pinF`, `phi`, `pin`) se indexan por residuo mod `2^g`. -/
structure Cert where
  g : ℕ
  A : List (ℕ × ℕ)
  a : ℕ
  M : ℕ
  X0 : ℕ
  D : ℕ
  lvl : BT ℕ
  pinF : BT Bool
  phi : BT ℕ
  pin : BT ℤ

namespace Cert

variable (c : Cert)

def N : ℕ := 2 ^ c.g

def isNode (u : ℕ) : Bool := c.A.all fun p => u % 2 ^ p.1 != p.2

def succs (u : ℕ) : List ℕ :=
  if u % 2 = 1 then [(3 * u + 1) % c.N] else [u / 2, u / 2 + c.N / 2]

def L (u : ℕ) : ℕ := c.lvl.get u

def isPin (u : ℕ) : Bool := c.pinF.get u

def Φ (u : ℕ) : ℕ := c.phi.get u

def P (u : ℕ) : ℤ := c.pin.get u

/-- La arista `u → v` respeta los niveles y, dentro de un nivel, el potencial o el pin. -/
def edgeOK (u v : ℕ) : Bool :=
  !c.isNode v || (decide (c.L v ≤ c.L u) &&
    (decide (c.L v < c.L u) || (decide (c.isPin v = c.isPin u) &&
      (if c.isPin u then
         (if u % 2 = 1 then decide (c.P v = 3 * c.P u + c.D) else decide (2 * c.P v = c.P u))
       else
         (if u % 2 = 1 then decide (c.Φ v + c.a + 1 ≤ c.Φ u)
          else decide (c.Φ v + 1 ≤ c.Φ u + c.M))))))

/-- Ningún pin es entero positivo salvo `1, 2, 4`. -/
def pinOK (u : ℕ) : Bool :=
  !c.isPin u || !(decide (0 < c.P u) && decide ((c.D : ℤ) ∣ c.P u)) ||
    decide (c.P u = c.D ∨ c.P u = 2 * c.D ∨ c.P u = 4 * c.D)

/-- El chequeo completo (decidible por cómputo). -/
def check : Bool :=
  (c.A.all fun p => decide (p.1 ≤ c.g)) && decide (1 ≤ c.g) && decide (1 ≤ c.D) &&
  decide ((3 * c.X0 + 1) ^ c.M ≤ 2 ^ c.a * c.X0 ^ c.M) && decide (c.X0 ≤ 600001) &&
  (List.range c.N).all fun u => !c.isNode u || (c.pinOK u && (c.succs u).all (c.edgeOK u))

/-! ## Lemas aritméticos -/

theorem collatz_pos {n : ℕ} (hn : 0 < n) : 0 < collatz n := by
  unfold collatz; split_ifs with h <;> omega

theorem iterate_pos {n : ℕ} (hn : 0 < n) : ∀ t, 0 < collatz^[t] n
  | 0 => hn
  | t + 1 => by rw [Function.iterate_succ_apply']; exact collatz_pos (iterate_pos hn t)

theorem reaches_of_iterate {n t : ℕ} (h : ReachesOne (collatz^[t] n)) : ReachesOne n := by
  obtain ⟨k, hk⟩ := h
  exact ⟨k + t, by rw [Function.iterate_add_apply]; exact hk⟩

theorem reaches_small {x : ℕ} (h : x = 1 ∨ x = 2 ∨ x = 4) : ReachesOne x := by
  rcases h with rfl | rfl | rfl
  · exact ⟨0, rfl⟩
  · exact ⟨1, by decide⟩
  · exact ⟨2, by decide⟩

/-- La cota de `X₀` se propaga a todo `x ≥ X₀`. -/
theorem pow_bound {a M X0 x : ℕ} (h : (3 * X0 + 1) ^ M ≤ 2 ^ a * X0 ^ M) (hx : X0 ≤ x) :
    (3 * x + 1) ^ M ≤ 2 ^ a * x ^ M := by
  rcases Nat.eq_zero_or_pos X0 with h0 | h0
  · subst h0
    rcases Nat.eq_zero_or_pos M with hM | hM
    · subst hM; simpa using Nat.one_le_two_pow
    · simp [Nat.zero_pow hM] at h
  have h1 : ((3 * x + 1) * X0) ^ M ≤ ((3 * X0 + 1) * x) ^ M :=
    Nat.pow_le_pow_left (by nlinarith) M
  rw [mul_pow, mul_pow] at h1
  have h2 : (3 * x + 1) ^ M * X0 ^ M ≤ 2 ^ a * x ^ M * X0 ^ M := by
    calc (3 * x + 1) ^ M * X0 ^ M ≤ (3 * X0 + 1) ^ M * x ^ M := h1
      _ ≤ 2 ^ a * X0 ^ M * x ^ M := Nat.mul_le_mul_right _ h
      _ = 2 ^ a * x ^ M * X0 ^ M := by ring
  exact Nat.le_of_mul_le_mul_right h2 (Nat.pow_pos h0)

/-- El residuo de `x / 2` módulo `2K` es `(x mod 2K)/2` o eso más `K`. -/
theorem half_mod {x K : ℕ} (hx : x % 2 = 0) :
    (x / 2) % (2 * K) = (x % (2 * K)) / 2 ∨ (x / 2) % (2 * K) = (x % (2 * K)) / 2 + K := by
  obtain ⟨y, rfl⟩ : ∃ y, x = 2 * y := ⟨x / 2, by omega⟩
  rw [Nat.mul_div_cancel_left _ two_pos, Nat.mul_mod_mul_left,
    Nat.mul_div_cancel_left _ two_pos]
  rcases Nat.eq_zero_or_pos K with hK | hK
  · subst hK; simp
  set s := y % (2 * K)
  have h1 : s % K = y % K := Nat.mod_mod_of_dvd _ (dvd_mul_left K 2)
  have h2 : s < 2 * K := Nat.mod_lt _ (by omega)
  have h3 : s / K < 2 := (Nat.div_lt_iff_lt_mul hK).2 (by linarith)
  have h4 := Nat.div_add_mod s K
  rw [← h1]
  interval_cases hq : s / K <;> omega

/-! ## El teorema de corrección -/

/-- **Corrección del certificado.** Si `c.check`, toda órbita que no llega a `1` pasa por `A`. -/
theorem forced (h : c.check = true) (n : ℕ) (hn : 0 < n) (hnr : ¬ ReachesOne n) :
    ∃ t, ∃ p ∈ c.A, collatz^[t] n % 2 ^ p.1 = p.2 := by
  simp only [check, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, List.mem_range] at h
  obtain ⟨⟨⟨⟨⟨hmg, hg⟩, hD⟩, hX⟩, hX6⟩, hall⟩ := h
  by_contra hA
  push Not at hA
  set x : ℕ → ℕ := fun t => collatz^[t] n with hxdef
  have hxpos : ∀ t, 0 < x t := iterate_pos hn
  have hxs : ∀ t, x (t + 1) = collatz (x t) := fun t => by
    simp only [hxdef]; rw [Function.iterate_succ_apply']
  have hnr' : ∀ t, ¬ ReachesOne (x t) := fun t h => hnr (reaches_of_iterate h)
  have hxX : ∀ t, c.X0 ≤ x t := by
    intro t
    by_contra hlt
    exact hnr' t (k12_verifiedBelow_600001 _ (hxpos t) (by omega))
  -- residuos
  have hNpos : 0 < c.N := Nat.pow_pos two_pos
  have hN2 : c.N = 2 * 2 ^ (c.g - 1) := by
    simp only [N]; rw [← pow_succ']; congr 1; omega
  set r : ℕ → ℕ := fun t => x t % c.N with hrdef
  have hrlt : ∀ t, r t < c.N := fun t => Nat.mod_lt _ hNpos
  have hpar : ∀ t, r t % 2 = x t % 2 := fun t => by
    simp only [hrdef]; rw [hN2, Nat.mod_mul_right_mod]
  have hnode : ∀ t, c.isNode (r t) = true := by
    intro t
    simp only [isNode, List.all_eq_true, bne_iff_ne, ne_eq]
    intro p hp
    have hm : r t % 2 ^ p.1 = x t % 2 ^ p.1 := by
      simp only [hrdef, N]
      exact Nat.mod_mod_of_dvd _ (Nat.pow_dvd_pow 2 (hmg p hp))
    rw [hm]
    exact hA t p hp
  have hsucc : ∀ t, r (t + 1) ∈ c.succs (r t) := by
    intro t
    have hr1 : r (t + 1) = collatz (x t) % c.N := by simp only [hrdef]; rw [hxs]
    rw [hr1]
    simp only [succs, hpar]
    split_ifs with ho
    · simp only [collatz, show x t % 2 ≠ 0 by omega, ↓reduceIte, List.mem_singleton, hrdef]
      exact (Nat.ModEq.add_right 1 (Nat.ModEq.mul_left 3 (Nat.mod_modEq _ _))).symm
    · have he : x t % 2 = 0 := by omega
      simp only [collatz, he, ↓reduceIte, List.mem_cons, List.mem_singleton, List.not_mem_nil,
        or_false, hrdef]
      rw [hN2]
      have := half_mod (K := 2 ^ (c.g - 1)) he
      rw [show 2 * 2 ^ (c.g - 1) / 2 = 2 ^ (c.g - 1) by omega]
      exact this
  have hedge : ∀ t, c.edgeOK (r t) (r (t + 1)) = true := by
    intro t
    have := hall (r t) (hrlt t)
    simp [hnode t] at this
    exact this.2 _ (hsucc t)
  have hpinOK : ∀ t, c.pinOK (r t) = true := by
    intro t
    have := hall (r t) (hrlt t)
    simp [hnode t] at this
    exact this.1
  -- los niveles no crecen
  have hle : ∀ t, c.L (r (t + 1)) ≤ c.L (r t) := by
    intro t
    have := hedge t
    simp only [edgeOK, hnode (t + 1), Bool.not_true, Bool.false_or, Bool.and_eq_true,
      decide_eq_true_eq] at this
    exact this.1
  -- nivel final
  have hex : ∃ v, ∃ t, c.L (r t) = v := ⟨_, 0, rfl⟩
  classical
  obtain ⟨t0, ht0⟩ := Nat.find_spec hex
  have hmin : ∀ t, c.L (r t0) ≤ c.L (r t) := fun t => by
    rw [ht0]; exact Nat.find_min' hex ⟨t, rfl⟩
  have hanti : ∀ j, c.L (r (t0 + j)) ≤ c.L (r t0) := by
    intro j
    induction j with
    | zero => rfl
    | succ j ih => exact (hle _).trans ih
  have hconst : ∀ j, c.L (r (t0 + j)) = c.L (r t0) := fun j =>
    le_antisymm (hanti j) (hmin _)
  -- en el nivel final, cada paso cumple la relación del nivel
  have hstep : ∀ j, c.isPin (r (t0 + j + 1)) = c.isPin (r (t0 + j)) ∧
      (if c.isPin (r (t0 + j)) then
         (if r (t0 + j) % 2 = 1 then c.P (r (t0 + j + 1)) = 3 * c.P (r (t0 + j)) + c.D
          else 2 * c.P (r (t0 + j + 1)) = c.P (r (t0 + j)))
       else
         (if r (t0 + j) % 2 = 1 then c.Φ (r (t0 + j + 1)) + c.a + 1 ≤ c.Φ (r (t0 + j))
          else c.Φ (r (t0 + j + 1)) + 1 ≤ c.Φ (r (t0 + j)) + c.M)) := by
    intro j
    have := hedge (t0 + j)
    have hc1 := hconst (j + 1)
    have hc0 := hconst j
    rw [← add_assoc] at hc1
    have hnlt : ¬ c.L (r (t0 + j + 1)) < c.L (r (t0 + j)) := by omega
    simp only [edgeOK, hnode (t0 + j + 1), Bool.not_true, Bool.false_or, Bool.and_eq_true,
      Bool.or_eq_true, decide_eq_true_eq, hnlt, false_or] at this
    obtain ⟨-, hpe, h2⟩ := this
    refine ⟨hpe, ?_⟩
    split_ifs at h2 ⊢ <;> simpa using h2
  have hrel := fun j => (hstep j).2
  have hpinc : ∀ j, c.isPin (r (t0 + j)) = c.isPin (r t0) := by
    intro j
    induction j with
    | zero => rfl
    | succ j ih => rw [← add_assoc, (hstep j).1, ih]
  by_cases hp : c.isPin (r t0) = true
  · -- nivel de pin: z = D x − P se anula
    set z : ℕ → ℤ := fun j => (c.D : ℤ) * x (t0 + j) - c.P (r (t0 + j)) with hzdef
    have hz : ∀ j, (x (t0 + j) % 2 = 1 → z (j + 1) = 3 * z j) ∧
        (x (t0 + j) % 2 = 0 → 2 * z (j + 1) = z j) := by
      intro j
      have hr := hrel j
      rw [hpinc j, if_pos hp, hpar] at hr
      have hxj := hxs (t0 + j)
      constructor
      · intro ho
        rw [if_pos ho] at hr
        simp only [collatz, show x (t0 + j) % 2 ≠ 0 by omega, ↓reduceIte] at hxj
        simp only [hzdef, ← add_assoc, hxj, hr]; push_cast; ring
      · intro he
        rw [if_neg (by omega)] at hr
        simp only [collatz, he, ↓reduceIte] at hxj
        have h2 : 2 * x (t0 + j + 1) = x (t0 + j) := by rw [hxj]; omega
        simp only [hzdef, ← add_assoc]
        have h2' : (2 : ℤ) * x (t0 + j + 1) = x (t0 + j) := by exact_mod_cast h2
        linear_combination (c.D : ℤ) * h2' - hr
    have hpow : ∀ i, ∃ J e k, i ≤ e ∧ 2 ^ e * z J = 3 ^ k * z 0 := by
      intro i
      induction i with
      | zero => exact ⟨0, 0, 0, le_rfl, by simp⟩
      | succ i ih =>
        obtain ⟨J, e, k, hie, hJ⟩ := ih
        rcases Nat.mod_two_eq_zero_or_one (x (t0 + J)) with he | ho
        · refine ⟨J + 1, e + 1, k, by omega, ?_⟩
          rw [pow_succ, mul_assoc, (hz J).2 he, hJ]
        · have hx1 := hxs (t0 + J)
          simp only [collatz, show x (t0 + J) % 2 ≠ 0 by omega, ↓reduceIte] at hx1
          have he1 : x (t0 + (J + 1)) % 2 = 0 := by rw [← add_assoc, hx1]; omega
          refine ⟨J + 2, e + 1, k + 1, by omega, ?_⟩
          rw [show J + 2 = J + 1 + 1 by omega, pow_succ, mul_assoc, (hz (J + 1)).2 he1,
            (hz J).1 ho, pow_succ]
          linear_combination 3 * hJ
    have hz0 : z 0 = 0 := by
      by_contra hne
      obtain ⟨J, e, k, hie, hJ⟩ := hpow ((z 0).natAbs + 1)
      have hdvd : (2 : ℤ) ^ e ∣ 3 ^ k * z 0 := ⟨z J, by rw [← hJ]⟩
      have hdvd' : 2 ^ e ∣ 3 ^ k * (z 0).natAbs := by
        have := Int.natAbs_dvd_natAbs.2 hdvd
        simpa [Int.natAbs_mul, Int.natAbs_pow] using this
      have hcop : Nat.Coprime (2 ^ e) (3 ^ k) := Nat.Coprime.pow _ _ (by norm_num)
      have h2 := Nat.le_of_dvd (Int.natAbs_pos.2 hne) (hcop.dvd_of_dvd_mul_left hdvd')
      have := Nat.lt_two_pow_self (n := e)
      omega
    have hDx : (c.D : ℤ) * x t0 = c.P (r t0) := by
      have := hz0; simp only [hzdef, add_zero] at this; linarith
    have hpo := hpinOK t0
    simp only [pinOK, hp, Bool.not_true, Bool.false_or, Bool.or_eq_true, Bool.not_eq_true',
      Bool.and_eq_false_iff, decide_eq_false_iff_not, decide_eq_true_eq] at hpo
    have hPpos : 0 < c.P (r t0) := by
      rw [← hDx]; have := hxpos t0; positivity
    have hPdvd : (c.D : ℤ) ∣ c.P (r t0) := ⟨x t0, by rw [← hDx]⟩
    rcases hpo with (h1 | h1) | h1
    · exact h1 hPpos
    · exact h1 hPdvd
    · apply hnr' t0
      apply reaches_small
      have hDpos : (0 : ℤ) < c.D := by exact_mod_cast hD
      rcases h1 with h1 | h1 | h1 <;> rw [← hDx] at h1
      · left; exact_mod_cast (mul_right_cancel₀ hDpos.ne' (by linarith : (x t0 : ℤ) * c.D = 1 * c.D))
      · right; left; exact_mod_cast (mul_right_cancel₀ hDpos.ne' (by linarith : (x t0 : ℤ) * c.D = 2 * c.D))
      · right; right; exact_mod_cast (mul_right_cancel₀ hDpos.ne' (by linarith : (x t0 : ℤ) * c.D = 4 * c.D))
  · -- nivel de potencial: W = x^M · 2^Φ se divide por dos en cada paso
    have hp' : c.isPin (r t0) = false := by simpa using hp
    set W : ℕ → ℕ := fun j => x (t0 + j) ^ c.M * 2 ^ c.Φ (r (t0 + j)) with hWdef
    have hW : ∀ j, 2 * W (j + 1) ≤ W j := by
      intro j
      have hr := hrel j
      rw [hpinc j, hp', hpar] at hr
      simp only [Bool.false_eq_true, ↓reduceIte] at hr
      have hxj := hxs (t0 + j)
      simp only [hWdef, ← add_assoc]
      rcases Nat.mod_two_eq_zero_or_one (x (t0 + j)) with he | ho
      · rw [if_neg (by omega)] at hr
        simp only [collatz, he, ↓reduceIte] at hxj
        have h2 : x (t0 + j) = 2 * x (t0 + j + 1) := by rw [hxj]; omega
        rw [h2, mul_pow]
        calc 2 * (x (t0 + j + 1) ^ c.M * 2 ^ c.Φ (r (t0 + j + 1)))
            = x (t0 + j + 1) ^ c.M * 2 ^ (c.Φ (r (t0 + j + 1)) + 1) := by ring
          _ ≤ x (t0 + j + 1) ^ c.M * 2 ^ (c.M + c.Φ (r (t0 + j))) :=
              Nat.mul_le_mul_left _ (Nat.pow_le_pow_right two_pos (by omega))
          _ = 2 ^ c.M * x (t0 + j + 1) ^ c.M * 2 ^ c.Φ (r (t0 + j)) := by ring
      · rw [if_pos ho] at hr
        simp only [collatz, show x (t0 + j) % 2 ≠ 0 by omega, ↓reduceIte] at hxj
        rw [hxj]
        have hb := pow_bound hX (hxX (t0 + j))
        calc 2 * ((3 * x (t0 + j) + 1) ^ c.M * 2 ^ c.Φ (r (t0 + j + 1)))
            ≤ 2 * (2 ^ c.a * x (t0 + j) ^ c.M * 2 ^ c.Φ (r (t0 + j + 1))) := by gcongr
          _ = x (t0 + j) ^ c.M * 2 ^ (c.Φ (r (t0 + j + 1)) + c.a + 1) := by ring
          _ ≤ x (t0 + j) ^ c.M * 2 ^ c.Φ (r (t0 + j)) :=
              Nat.mul_le_mul_left _ (Nat.pow_le_pow_right two_pos hr)
    have hWj : ∀ j, W j * 2 ^ j ≤ W 0 := by
      intro j
      induction j with
      | zero => simp
      | succ j ih => calc W (j + 1) * 2 ^ (j + 1) = (2 * W (j + 1)) * 2 ^ j := by ring
          _ ≤ W j * 2 ^ j := Nat.mul_le_mul_right _ (hW j)
          _ ≤ W 0 := ih
    have hWpos : ∀ j, 1 ≤ W j := fun j =>
      Nat.mul_pos (Nat.pow_pos (hxpos _)) (Nat.pow_pos two_pos)
    have := hWj (W 0)
    have := Nat.lt_two_pow_self (n := W 0)
    have := hWpos (W 0)
    nlinarith

end Cert

end Forced

end Collatz
