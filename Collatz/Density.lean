import Mathlib
import Collatz.Reductions

/-!
# Collatz ⟺ casi todo entero llega a 1 (dada la densidad positiva de los predecesores)

Ronda 9 del laboratorio (`Ideas/tao_constante.md`), paso 1.

Hipótesis `PredDensity`: para todo `a ≥ 1` no divisible por 3, los `n` cuya órbita pasa por `a`
tienen densidad natural inferior positiva. Es la forma, para el mapa clásico `T`, del resultado M2 de
ProofAtlas (verificado en Lean por ellos y no arbitrado; ver `docs/audit_conjectureA.md`). El puente
`M2.predDensity_of_statement` (al final) prueba que el enunciado literal de M2 implica `PredDensity`;
`scripts/m2_fidelity/M2Fidelity.lean` comprueba, dentro del proyecto de ProofAtlas, que su teorema prueba
exactamente ese enunciado.

Resultado (`collatz_iff_density_one`, `collatz_iff_upperDensity_one`): bajo `PredDensity`, Collatz
equivale a que el conjunto de los `n` que llegan a 1 tenga densidad natural 1, e incluso a que tenga
densidad **superior** 1. La idea: si `n₀` es un contraejemplo, en su órbita hay un `a` no divisible por 3,
y todos los predecesores de `a` (una fracción positiva de los enteros) también son contraejemplos.

Esto **no** es un avance hacia la conjetura: la traduce a un enunciado de "casi todos". Tampoco es nuevo:
ProofAtlas ya tiene en Lean la versión natural (`universal_reaches_one_of_arbitrarily_dense_convergence`) y
Lech Mazur la publicó en el blog de Tao (6/9/2026). Lo propio: la versión logarítmica (la de Tao).
-/

open Filter Topology

/-! ## Llegar a 1 -/

/-- `n` llega a 1. -/
def ReachesOne (n : ℕ) : Prop := ∃ k, iter k n = 1

/-- `n` pasa por `a`. -/
def HitsVal (a n : ℕ) : Prop := ∃ k, iter k n = a

theorem reachesOne_iter (n m : ℕ) (h : ReachesOne (iter m n)) : ReachesOne n := by
  obtain ⟨j, hj⟩ := h
  exact ⟨m + j, by rw [iter_add]; exact hj⟩

/-- Desde el ciclo trivial siempre se vuelve a 1. -/
theorem reachesOne_iter_one (m : ℕ) : ReachesOne (iter m 1) :=
  trivialCycle_reaches_one (iter_trivialCycle m (Or.inl rfl))

/-- Si `n` pasa por `a` y `a` no llega a 1, tampoco `n`. -/
theorem not_reachesOne_of_hits {a n : ℕ} (hn : HitsVal a n) (ha : ¬ ReachesOne a) :
    ¬ ReachesOne n := by
  rintro ⟨j, hj⟩
  obtain ⟨k, rfl⟩ := hn
  rcases le_total k j with hkj | hjk
  · apply ha
    refine ⟨j - k, ?_⟩
    rw [← iter_add, Nat.add_sub_cancel' hkj, hj]
  · apply ha
    have : iter k n = iter (k - j) (iter j n) := by
      rw [← iter_add, Nat.add_sub_cancel' hjk]
    rw [this, hj]
    exact reachesOne_iter_one _

/-- En la órbita de todo `n ≥ 1` hay un valor `≥ 1` no divisible por 3 (un `3m + 1`). -/
theorem exists_hits_not_dvd_three (n : ℕ) (hn : 1 ≤ n) :
    ∃ k, 1 ≤ iter k n ∧ ¬ 3 ∣ iter k n := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    rcases Nat.even_or_odd n with ⟨r, hr⟩ | hodd
    · have hT : T n = r := by unfold T; split <;> omega
      obtain ⟨k, hk1, hk3⟩ := ih r (by omega) (by omega)
      refine ⟨k + 1, ?_, ?_⟩ <;> simpa [iter, hT] using (by assumption)
    · have hT : T n = 3 * n + 1 := by
        unfold T; rw [if_neg]; obtain ⟨r, hr⟩ := hodd; omega
      refine ⟨1, ?_, ?_⟩ <;> simp only [iter, hT] <;> omega

/-- Si hay un contraejemplo, hay uno no divisible por 3. -/
theorem exists_counterexample_not_dvd_three (h : ¬ Collatz) :
    ∃ a, 1 ≤ a ∧ ¬ 3 ∣ a ∧ ¬ ReachesOne a := by
  simp only [Collatz, not_forall] at h
  obtain ⟨n, hn, hn1⟩ := h
  obtain ⟨k, hk1, hk3⟩ := exists_hits_not_dvd_three n hn
  exact ⟨_, hk1, hk3, fun h' => hn1 (reachesOne_iter n k h')⟩

/-! ## Conteos -/

open Classical in
/-- `#{1 ≤ n ≤ x : n llega a 1}`. -/
noncomputable def reachCount (x : ℕ) : ℕ := ((Finset.Icc 1 x).filter ReachesOne).card

open Classical in
/-- `#{1 ≤ n ≤ x : la órbita de n pasa por a}`. -/
noncomputable def predCount (a x : ℕ) : ℕ := ((Finset.Icc 1 x).filter (HitsVal a)).card

/-- Densidad natural inferior positiva de los predecesores de todo `a ≥ 1` no divisible por 3
(consecuencia de M2 de ProofAtlas; aquí, hipótesis). -/
def PredDensity : Prop :=
  ∀ a, 1 ≤ a → ¬ 3 ∣ a → ∃ c : ℝ, 0 < c ∧ ∀ᶠ x : ℕ in atTop, c * x ≤ predCount a x

/-- Si `a` no llega a 1, los que llegan a 1 y los predecesores de `a` son disjuntos en `[1, x]`. -/
theorem reachCount_add_predCount_le {a : ℕ} (ha : ¬ ReachesOne a) (x : ℕ) :
    reachCount x + predCount a x ≤ x := by
  classical
  unfold reachCount predCount
  rw [← Finset.card_union_of_disjoint]
  · calc _ ≤ (Finset.Icc 1 x).card := Finset.card_le_card (Finset.union_subset
            (Finset.filter_subset _ _) (Finset.filter_subset _ _))
      _ = x := by simp
  · rw [Finset.disjoint_filter]
    intro n _ hr hp
    exact not_reachesOne_of_hits hp ha hr

theorem reachCount_of_collatz (h : Collatz) (x : ℕ) : reachCount x = x := by
  classical
  unfold reachCount
  rw [Finset.filter_true_of_mem (p := ReachesOne) (fun n hn => h n (Finset.mem_Icc.mp hn).1)]
  simp

/-- Bajo `PredDensity`, un contraejemplo deja a los que llegan a 1 con densidad superior `≤ 1 - c`. -/
theorem reachCount_le_of_not_collatz (H : PredDensity) (h : ¬ Collatz) :
    ∃ c : ℝ, 0 < c ∧ ∀ᶠ x : ℕ in atTop, (reachCount x : ℝ) ≤ (1 - c) * x := by
  obtain ⟨a, ha1, ha3, ha⟩ := exists_counterexample_not_dvd_three h
  obtain ⟨c, hc, hev⟩ := H a ha1 ha3
  refine ⟨c, hc, hev.mono fun x hx => ?_⟩
  have := reachCount_add_predCount_le ha x
  have : (reachCount x : ℝ) + predCount a x ≤ x := by exact_mod_cast this
  linarith

/-! ## Los teoremas -/

/-- **Collatz ⟺ densidad superior 1** (bajo `PredDensity`): Collatz equivale a que para todo `ε > 0`
haya `x` arbitrariamente grandes con `#{n ≤ x : n llega a 1} > (1 - ε) x`. -/
theorem collatz_iff_upperDensity_one (H : PredDensity) :
    Collatz ↔ ∀ ε : ℝ, 0 < ε → ∃ᶠ x : ℕ in atTop, (1 - ε) * x < reachCount x := by
  constructor
  · intro h ε hε
    refine (eventually_gt_atTop 0).frequently.mono fun x hx => ?_
    rw [reachCount_of_collatz h]
    have : (0 : ℝ) < x := by exact_mod_cast hx
    nlinarith
  · intro h
    by_contra hc
    obtain ⟨c, hc0, hev⟩ := reachCount_le_of_not_collatz H hc
    obtain ⟨x, hx1, hx2⟩ := ((h c hc0).and_eventually hev).exists
    linarith

/-- **Collatz ⟺ casi todo entero llega a 1** (densidad natural 1, bajo `PredDensity`). -/
theorem collatz_iff_density_one (H : PredDensity) :
    Collatz ↔ Tendsto (fun x : ℕ => (reachCount x : ℝ) / x) atTop (𝓝 1) := by
  constructor
  · intro h
    refine tendsto_const_nhds.congr' ((eventually_gt_atTop 0).mono fun x hx => ?_)
    show (1 : ℝ) = reachCount x / x
    rw [reachCount_of_collatz h]
    have : (x : ℝ) ≠ 0 := by exact_mod_cast hx.ne'
    field_simp
  · intro h
    rw [collatz_iff_upperDensity_one H]
    intro ε hε
    refine (((h.eventually (lt_mem_nhds (by linarith : 1 - ε < 1))).and
      (eventually_gt_atTop 0)).mono fun x ⟨hx, hx0⟩ => ?_).frequently
    have : (0 : ℝ) < x := by exact_mod_cast hx0
    rwa [lt_div_iff₀ this] at hx

/-! ## Densidad logarítmica (la de Tao), paso 1b

`logSum p x = ∑_{1 ≤ n ≤ x, p n} 1/n`. Tao prueba sus resultados en densidad logarítmica:
`logSum p x / log x → 1`. Pasamos de la densidad natural inferior positiva de los predecesores a la
logarítmica con sumación por partes: `Φ(x) = logSum P x − N(x)/x` crece al menos `c/(x+1)` por paso.
-/

open Classical in
/-- `∑_{1 ≤ n ≤ x, p n} 1/n`. -/
noncomputable def logSum (p : ℕ → Prop) (x : ℕ) : ℝ :=
  ∑ n ∈ Finset.Icc 1 x, if p n then (1 : ℝ) / n else 0

open Classical in
/-- `#{1 ≤ n ≤ x : p n}`, en `ℝ`. -/
noncomputable def cntR (p : ℕ → Prop) (x : ℕ) : ℝ :=
  ∑ n ∈ Finset.Icc 1 x, if p n then (1 : ℝ) else 0

/-- Número armónico `∑_{1 ≤ n ≤ x} 1/n`, en `ℝ`. -/
noncomputable def harm (x : ℕ) : ℝ := ∑ n ∈ Finset.Icc 1 x, (1 : ℝ) / n

theorem sum_Icc_one_succ (f : ℕ → ℝ) (x : ℕ) :
    ∑ n ∈ Finset.Icc 1 (x + 1), f n = ∑ n ∈ Finset.Icc 1 x, f n + f (x + 1) := by
  have h : ∀ y, Finset.Icc 1 y = Finset.Ioc 0 y := by intro y; ext; simp; omega
  rw [h, h, Finset.sum_Ioc_succ_top (Nat.zero_le _)]

theorem harm_eq (x : ℕ) : harm x = (harmonic x : ℝ) := by
  rw [harmonic_eq_sum_Icc]; push_cast; simp [harm]

theorem log_le_harm (x : ℕ) : Real.log x ≤ harm x := by
  rw [harm_eq]
  refine le_trans ?_ (log_add_one_le_harmonic x)
  rcases Nat.eq_zero_or_pos x with rfl | hx
  · simp
  · exact Real.log_le_log (by exact_mod_cast hx) (by push_cast; linarith)

theorem harm_le (x : ℕ) : harm x ≤ 1 + Real.log x := by
  rw [harm_eq]; exact harmonic_le_one_add_log x

theorem predCount_eq_cntR (a x : ℕ) : (predCount a x : ℝ) = cntR (HitsVal a) x := by
  classical
  unfold predCount cntR
  rw [Finset.card_filter]; push_cast; rfl

theorem cntR_nonneg (p : ℕ → Prop) (x : ℕ) : 0 ≤ cntR p x := by
  unfold cntR; exact Finset.sum_nonneg fun n _ => by split <;> norm_num

open Classical in
theorem logSum_succ (p : ℕ → Prop) (x : ℕ) :
    logSum p (x + 1) = logSum p x + if p (x + 1) then (1 : ℝ) / (x + 1) else 0 := by
  unfold logSum; rw [sum_Icc_one_succ]; push_cast; rfl

open Classical in
theorem cntR_succ (p : ℕ → Prop) (x : ℕ) :
    cntR p (x + 1) = cntR p x + if p (x + 1) then (1 : ℝ) else 0 := by
  unfold cntR; rw [sum_Icc_one_succ]

theorem harm_succ (x : ℕ) : harm (x + 1) = harm x + 1 / (x + 1) := by
  unfold harm; rw [sum_Icc_one_succ]; push_cast; rfl

/-- Sumación por partes: `Φ(x) = logSum p x − N(x)/x` crece al menos `c·(H(x) − H(X))`. -/
theorem phi_growth {p : ℕ → Prop} {c : ℝ} {X : ℕ} (hX : 1 ≤ X)
    (hN : ∀ x ≥ X, c * x ≤ cntR p x) :
    ∀ x ≥ X, logSum p X - cntR p X / X + c * (harm x - harm X) ≤ logSum p x - cntR p x / x := by
  intro x hx
  induction x, hx using Nat.le_induction with
  | base => simp
  | succ x hx ih =>
    have hx0 : (0 : ℝ) < x := by exact_mod_cast (by omega : 0 < x)
    have hNx := hN x hx
    have key : c / (x + 1) ≤ cntR p x / x - cntR p x / (x + 1) := by
      rw [div_sub_div _ _ hx0.ne' (by positivity), div_le_div_iff₀ (by positivity) (by positivity)]
      nlinarith [cntR_nonneg p x]
    rw [logSum_succ, cntR_succ, harm_succ]
    push_cast
    have e1 : c * (harm x + 1 / (x + 1) - harm X) = c * (harm x - harm X) + c / (x + 1) := by ring
    rw [e1]
    split_ifs with hp
    · rw [add_div (cntR p x) 1]; linarith
    · rw [add_zero, add_zero]; linarith

/-- Bajo `PredDensity`, un contraejemplo deja a los que llegan a 1 con densidad logarítmica superior
`≤ 1 − c`: `logSum ReachesOne x ≤ (1 − c)·log x + K`. -/
theorem logSum_le_of_not_collatz (H : PredDensity) (h : ¬ Collatz) :
    ∃ c : ℝ, 0 < c ∧ ∃ K : ℝ, ∀ᶠ x : ℕ in atTop,
      logSum ReachesOne x ≤ (1 - c) * Real.log x + K := by
  obtain ⟨a, ha1, ha3, ha⟩ := exists_counterexample_not_dvd_three h
  obtain ⟨c, hc, hev⟩ := H a ha1 ha3
  obtain ⟨X₀, hX₀⟩ := eventually_atTop.mp hev
  set X := max X₀ 1
  have hN : ∀ x ≥ X, c * x ≤ cntR (HitsVal a) x := fun x hx => by
    rw [← predCount_eq_cntR]; exact hX₀ x (le_trans (le_max_left _ _) hx)
  refine ⟨c, hc, 1 - (logSum (HitsVal a) X - cntR (HitsVal a) X / X - c * harm X), ?_⟩
  refine (eventually_ge_atTop X).mono fun x hx => ?_
  have hphi := phi_growth (le_max_right _ _) hN x hx
  have hx0 : (0 : ℝ) < x := by exact_mod_cast (by omega : 0 < x)
  have hdiv : 0 ≤ cntR (HitsVal a) x / x := div_nonneg (cntR_nonneg _ _) hx0.le
  -- disjuntos: logSum R + logSum P ≤ H
  have hdisj : logSum ReachesOne x + logSum (HitsVal a) x ≤ harm x := by
    unfold logSum harm
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_le_sum fun n _ => ?_
    have hn : (0 : ℝ) ≤ 1 / n := by positivity
    by_cases hr : ReachesOne n
    · have hp : ¬ HitsVal a n := fun hp => not_reachesOne_of_hits hp ha hr
      simp [hr, hp]
    · by_cases hp : HitsVal a n <;> simp [hr, hp]
  have := log_le_harm x
  have := harm_le x
  nlinarith

/-- **Collatz ⟺ densidad logarítmica superior 1** de los que llegan a 1 (bajo `PredDensity`). -/
theorem collatz_iff_upperLogDensity_one (H : PredDensity) :
    Collatz ↔ ∀ ε : ℝ, 0 < ε → ∃ᶠ x : ℕ in atTop, (1 - ε) * Real.log x < logSum ReachesOne x := by
  have hlog : Tendsto (fun x : ℕ => Real.log x) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  constructor
  · intro h ε hε
    refine ((hlog.eventually_gt_atTop 0).mono fun x hx => ?_).frequently
    have : logSum ReachesOne x = harm x := by
      unfold logSum harm
      refine Finset.sum_congr rfl fun n hn => ?_
      exact if_pos (show ReachesOne n from h n (Finset.mem_Icc.mp hn).1)
    rw [this]
    nlinarith [log_le_harm x]
  · intro h
    by_contra hc
    obtain ⟨c, hc0, K, hev⟩ := logSum_le_of_not_collatz H hc
    have hbig := hlog.eventually_gt_atTop (2 * |K| / c)
    obtain ⟨x, hx1, hx2, hx3⟩ := ((h (c / 2) (by linarith)).and_eventually (hev.and hbig)).exists
    have : 2 * |K| < c * Real.log x := by rw [div_lt_iff₀ hc0] at hx3; linarith
    nlinarith [le_abs_self K]

/-- **Collatz ⟺ casi todo entero llega a 1 en densidad logarítmica** (bajo `PredDensity`).
Es el teorema de Tao (2019) con `f` constante: Tao da `min órbita(n) < f(n)` para casi todo `n` en
densidad logarítmica, para toda `f → ∞`. -/
theorem collatz_iff_logDensity_one (H : PredDensity) :
    Collatz ↔ Tendsto (fun x : ℕ => logSum ReachesOne x / Real.log x) atTop (𝓝 1) := by
  have hlog : Tendsto (fun x : ℕ => Real.log x) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  constructor
  · intro h
    have heq : ∀ x, logSum ReachesOne x = harm x := fun x => by
      unfold logSum harm
      refine Finset.sum_congr rfl fun n hn => ?_
      exact if_pos (show ReachesOne n from h n (Finset.mem_Icc.mp hn).1)
    have hup : Tendsto (fun x : ℕ => 1 + (Real.log x)⁻¹) atTop (𝓝 1) := by
      simpa using tendsto_const_nhds.add (tendsto_inv_atTop_zero.comp hlog)
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hup ?_ ?_
    · refine (hlog.eventually_gt_atTop 0).mono fun x hx => ?_
      rw [heq, le_div_iff₀ hx, one_mul]; exact log_le_harm x
    · refine (hlog.eventually_gt_atTop 0).mono fun x hx => ?_
      rw [heq, div_le_iff₀ hx, add_mul, inv_mul_cancel₀ hx.ne', one_mul, add_comm]
      exact harm_le x
  · intro h
    rw [collatz_iff_upperLogDensity_one H]
    intro ε hε
    refine (((h.eventually (lt_mem_nhds (by linarith : 1 - ε < 1))).and
      (hlog.eventually_gt_atTop 0)).mono fun x ⟨hx, hx0⟩ => ?_).frequently
    rwa [lt_div_iff₀ hx0] at hx

/-! ## Puente: el enunciado de M2 (ProofAtlas) implica `PredDensity`

M2 está demostrado en el paquete de ProofAtlas (Lean `v4.30.0-rc2`, ~124 000 líneas), que no se puede importar en este
proyecto (Lean `v4.33.1`). Aquí transcribimos **literalmente** su enunciado, desplegando sus definiciones, y probamos
que implica `PredDensity`. Fuente: `Erdos1135/ND/PositiveDensity/GeneralTargetPositiveDensity.lean`,
`Erdos1135.ND.PositiveDensity.generalTarget_predecessors_positive_lower_density`, con
- `CollatzConjecture.collatzStep n = if Even n then n / 2 else 3 * n + 1` (`FormalConjectures/Wikipedia/CollatzConjecture.lean`),
- `Erdos1135.Reaches a b = ∃ m, collatzStep^[m] a = b` (`Erdos1135/StoppingTime.lean`),
- `ordinaryPredecessorSet a = {n | 0 < n ∧ Reaches n a}`,
- `Terras.natCount s N = Nat.count (· ∈ s) N` con decidibilidad clásica (cuenta `n < N`).
Auditado en `docs/audit_conjectureA.md` (kernel independiente nanoda, prueba de mutación sobre este mismo teorema).
-/

namespace M2

/-- `CollatzConjecture.collatzStep` de ProofAtlas / Formal Conjectures. -/
def collatzStep (n : ℕ) : ℕ := if Even n then n / 2 else 3 * n + 1

/-- `Erdos1135.Reaches`. -/
def Reaches (a b : ℕ) : Prop := ∃ m, collatzStep^[m] a = b

/-- `Erdos1135.ND.PositiveDensity.ordinaryPredecessorSet`. -/
def ordinaryPredecessorSet (a : ℕ) : Set ℕ := {n | 0 < n ∧ Reaches n a}

/-- `Erdos1135.Terras.natCount`. -/
noncomputable def natCount (s : Set ℕ) (N : ℕ) : ℕ :=
  @Nat.count (fun n => n ∈ s) (fun n => Classical.propDecidable (n ∈ s)) N

/-- El enunciado de `generalTarget_predecessors_positive_lower_density` (M2), cuantificado en `a`. -/
def Statement : Prop :=
  ∀ {a : ℕ}, 0 < a → ¬ 3 ∣ a →
    ∃ c : ℝ, 0 < c ∧ ∃ X0 : ℕ, ∀ X : ℕ, X0 ≤ X →
      c * (X : ℝ) ≤ (natCount (ordinaryPredecessorSet a) X : ℝ)

theorem collatzStep_eq_T (n : ℕ) : collatzStep n = T n := by
  unfold collatzStep T
  by_cases h : n % 2 = 0
  · rw [if_pos (Nat.even_iff.mpr h), if_pos h]
  · rw [if_neg (fun he => h (Nat.even_iff.mp he)), if_neg h]

theorem iterate_eq_iter (m n : ℕ) : collatzStep^[m] n = iter m n := by
  induction m generalizing n with
  | zero => rfl
  | succ m ih => rw [Function.iterate_succ_apply, ih, collatzStep_eq_T]; rfl

theorem natCount_le_predCount (a X : ℕ) :
    natCount (ordinaryPredecessorSet a) X ≤ predCount a X := by
  classical
  unfold natCount predCount
  rw [Nat.count_eq_card_filter_range]
  refine Finset.card_le_card fun n hn => ?_
  simp only [Finset.mem_filter, Finset.mem_range] at hn
  obtain ⟨hnX, hpos, m, hm⟩ := hn
  simp only [Finset.mem_filter, Finset.mem_Icc]
  exact ⟨⟨hpos, hnX.le⟩, m, by rw [← iterate_eq_iter]; exact hm⟩

/-- **Puente:** el enunciado de M2 implica `PredDensity`. -/
theorem predDensity_of_statement (h : Statement) : PredDensity := by
  intro a ha1 ha3
  obtain ⟨c, hc, X0, hX0⟩ := h (by omega) ha3
  refine ⟨c, hc, eventually_atTop.mpr ⟨X0, fun X hX => ?_⟩⟩
  exact (hX0 X hX).trans (by exact_mod_cast natCount_le_predCount a X)

end M2

/-- Collatz ⟺ casi todo entero llega a 1 (densidad logarítmica), dado el enunciado de M2. -/
theorem collatz_iff_logDensity_one_of_M2 (h : M2.Statement) :
    Collatz ↔ Tendsto (fun x : ℕ => logSum ReachesOne x / Real.log x) atTop (𝓝 1) :=
  collatz_iff_logDensity_one (M2.predDensity_of_statement h)
