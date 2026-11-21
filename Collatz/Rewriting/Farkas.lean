import Collatz.Rewriting.FarkasCert

/-!
# La variante de Farkas: prueba automática verificada

Yolcu–Aaronson–Heule (arXiv 2105.14697, §4.2) consideran la función

  `F n = (n-1)/3` si `n ≡ 1 (mod 3)`, `n/2` si `n ≡ 0, 2 (mod 6)`, `(3n+1)/2` si `n ≡ 3, 5 (mod 6)`,

equivalente a la de Farkas (2005), y el sistema `ℱ = 𝒟_F ∪ 𝒳` con reglas dinámicas
`1◁ → ◁`, `0f◁ → 0◁`, `1f◁ → 1◁`, `1t◁ → 12◁`, `2t◁ → 22◁` y las 9 auxiliares/de inicio de `𝒯`.

* `termF_all`: `ℱ` termina sobre palabras canónicas, con el certificado ártico 5×5 del paper
  (sobre `ℱ^rev`, eliminando las reglas dinámicas como reglas "top" del lado derecho).
* `farkas_convergent`: **toda trayectoria de `F` desde `n ≥ 1` llega a `1`** (Teorema 4.2 del paper),
  deducido de `termF_all`.

**Nota sobre el paper.** §4.2 afirma que la reescritura "más a la derecha" desde la escritura ternaria
simula toda la trayectoria de `F`. No es así: la derivación se traba en `▷t◁` (3), `▷f◁` (2) o `▷ft◁` (5)
cuando se acaban los dígitos ternarios (`scripts/farkas_check.py`). La conclusión se salva: con el
invariante `Shape` (a lo sumo dos binarios al principio, el resto ternario) la forma normal final vale
`≤ 7`, y esos valores convergen (chequeo finito).
-/

namespace SRS.Farkas

open SRS

/-- La función de Farkas en la forma de Yolcu–Aaronson–Heule. -/
def F (n : ℕ) : ℕ :=
  if n % 3 = 1 then (n - 1) / 3 else if n % 6 = 0 ∨ n % 6 = 2 then n / 2 else (3 * n + 1) / 2

/-! ## El sistema `ℱ` -/

inductive FRule | d1 | d2 | d3 | d4 | d5 | a1 | a2 | a3 | a4 | a5 | a6 | s1 | s2 | s3
  deriving DecidableEq, Repr

instance : Fintype FRule :=
  Fintype.ofList [.d1, .d2, .d3, .d4, .d5, .a1, .a2, .a3, .a4, .a5, .a6, .s1, .s2, .s3]
    (by intro x; cases x <;> simp)

/-- Lados izquierdos, con el alfabeto ASCII de `rules/farkas.srs`. -/
def FRule.lhs : FRule → List X
  | .d1 => [.f, .d] | .d2 => [.e, .a, .d] | .d3 => [.f, .a, .d] | .d4 => [.f, .b, .d]
  | .d5 => [.g, .b, .d]
  | .a1 => [.a, .e] | .a2 => [.a, .f] | .a3 => [.a, .g]
  | .a4 => [.b, .e] | .a5 => [.b, .f] | .a6 => [.b, .g]
  | .s1 => [.c, .e] | .s2 => [.c, .f] | .s3 => [.c, .g]

def FRule.rhs : FRule → List X
  | .d1 => [.d] | .d2 => [.e, .d] | .d3 => [.f, .d] | .d4 => [.f, .g, .d] | .d5 => [.g, .g, .d]
  | .a1 => [.e, .a] | .a2 => [.e, .b] | .a3 => [.f, .a]
  | .a4 => [.f, .b] | .a5 => [.g, .a] | .a6 => [.g, .b]
  | .s1 => [.c, .b] | .s2 => [.c, .a, .a] | .s3 => [.c, .a, .b]

def FRule.isDyn : FRule → Bool
  | .d1 | .d2 | .d3 | .d4 | .d5 => true
  | _ => false

def FRule.isStart : FRule → Bool
  | .s1 | .s2 | .s3 => true
  | _ => false

inductive FStep : FRule → List Sym → List Sym → Prop
  | d1 (u : List Sym) : FStep .d1 (u ++ [.d1]) u
  | d2 (u : List Sym) : FStep .d2 (u ++ [.d0, .f]) (u ++ [.d0])
  | d3 (u : List Sym) : FStep .d3 (u ++ [.d1, .f]) (u ++ [.d1])
  | d4 (u : List Sym) : FStep .d4 (u ++ [.d1, .t]) (u ++ [.d1, .d2])
  | d5 (u : List Sym) : FStep .d5 (u ++ [.d2, .t]) (u ++ [.d2, .d2])
  | a1 (u v : List Sym) : FStep .a1 (u ++ .f :: .d0 :: v) (u ++ .d0 :: .f :: v)
  | a2 (u v : List Sym) : FStep .a2 (u ++ .f :: .d1 :: v) (u ++ .d0 :: .t :: v)
  | a3 (u v : List Sym) : FStep .a3 (u ++ .f :: .d2 :: v) (u ++ .d1 :: .f :: v)
  | a4 (u v : List Sym) : FStep .a4 (u ++ .t :: .d0 :: v) (u ++ .d1 :: .t :: v)
  | a5 (u v : List Sym) : FStep .a5 (u ++ .t :: .d1 :: v) (u ++ .d2 :: .f :: v)
  | a6 (u v : List Sym) : FStep .a6 (u ++ .t :: .d2 :: v) (u ++ .d2 :: .t :: v)
  | s1 (v : List Sym) : FStep .s1 (.d0 :: v) (.t :: v)
  | s2 (v : List Sym) : FStep .s2 (.d1 :: v) (.f :: .f :: v)
  | s3 (v : List Sym) : FStep .s3 (.d2 :: v) (.f :: .t :: v)

/-- Las reglas dinámicas actúan en el extremo derecho. -/
theorem FStep.decomp {ρ : FRule} {w w' : List Sym} (h : FStep ρ w w') :
    ∃ p q, full w = p ++ ρ.lhs ++ q ∧ full w' = p ++ ρ.rhs ++ q ∧ (ρ.isDyn = true → q = []) := by
  cases h
  case d1 => exact ⟨.c :: w'.map Sym.toX, [], by simp [full, FRule.lhs, Sym.toX],
      by simp [full, FRule.rhs], fun _ => rfl⟩
  case s1 v => exact ⟨[], v.map Sym.toX ++ [.d], by simp [full, FRule.lhs, Sym.toX],
      by simp [full, FRule.rhs, Sym.toX], by simp [FRule.isDyn]⟩
  case s2 v => exact ⟨[], v.map Sym.toX ++ [.d], by simp [full, FRule.lhs, Sym.toX],
      by simp [full, FRule.rhs, Sym.toX], by simp [FRule.isDyn]⟩
  case s3 v => exact ⟨[], v.map Sym.toX ++ [.d], by simp [full, FRule.lhs, Sym.toX],
      by simp [full, FRule.rhs, Sym.toX], by simp [FRule.isDyn]⟩
  case d2 u | d3 u | d4 u | d5 u =>
    exact ⟨.c :: u.map Sym.toX, [], by simp [full, FRule.lhs, Sym.toX],
      by simp [full, FRule.rhs, Sym.toX], fun _ => rfl⟩
  all_goals
    rename_i u v
    exact ⟨.c :: u.map Sym.toX, v.map Sym.toX ++ [.d],
      by simp [full, FRule.lhs, Sym.toX], by simp [full, FRule.rhs, Sym.toX],
      by simp [FRule.isDyn]⟩

def StepF (S : FRule → Bool) (w w' : List Sym) : Prop := ∃ ρ, S ρ = true ∧ FStep ρ w w'

def TermF (S : FRule → Bool) : Prop := ∀ w, Acc (fun y x => StepF S x y) w

theorem TermF.mono {S S' : FRule → Bool} (h : TermF S) (hS : ∀ ρ, S' ρ = true → S ρ = true) :
    TermF S' := fun w =>
  Subrelation.accessible (fun ⟨ρ, h1, h2⟩ => ⟨ρ, hS ρ h1, h2⟩) (h w)

theorem termF_none : TermF (fun _ => false) :=
  fun _ => Acc.intro _ fun _ ⟨_, h, _⟩ => absurd h (by simp)

theorem TermF.removal {S S₁ : FRule → Bool} (φ : List Sym → ℕ)
    (hle : ∀ ρ w w', S ρ = true → FStep ρ w w' → φ w' ≤ φ w)
    (hlt : ∀ ρ w w', S ρ = true → S₁ ρ = true → FStep ρ w w' → φ w' < φ w)
    (hrest : TermF (fun ρ => S ρ && !S₁ ρ)) : TermF S := by
  suffices H : ∀ n w, φ w = n → Acc (fun y x => StepF S x y) w from fun w => H _ w rfl
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro w hw
    revert hw
    induction hrest w with
    | intro w _ ihw =>
      intro hw
      refine Acc.intro _ fun w' ⟨ρ, hS, hst⟩ => ?_
      cases h1 : S₁ ρ
      · rcases (hle ρ w w' hS hst).lt_or_eq with hl | he
        · exact ih _ (hw ▸ hl) w' rfl
        · exact ihw w' ⟨ρ, by simp [hS, h1], hst⟩ (he.trans hw)
      · exact ih _ (hw ▸ hlt ρ w w' hS h1 hst) w' rfl

/-! ## `𝒳` (auxiliares + inicio) termina -/

theorem tc_step {ρ : FRule} {w w' : List Sym} (h : FStep ρ w w') (hρ : ρ.isDyn = false) :
    tc w' ≤ tc w ∧ (ρ.isStart = true → tc w' < tc w) := by
  cases h <;> simp_all [FRule.isStart, FRule.isDyn, tc_append, tc, Sym.isBin]

theorem inv_step {ρ : FRule} {w w' : List Sym} (h : FStep ρ w w') (hρ : ρ.isDyn = false)
    (hs : ρ.isStart = false) : inv w' < inv w := by
  cases h <;> simp_all [FRule.isStart, FRule.isDyn, inv_append, inv, tc, Sym.isBin]

theorem termF_noDyn : TermF (fun ρ => !ρ.isDyn) := by
  refine TermF.removal (S₁ := FRule.isStart) tc
    (fun ρ w w' hS h => (tc_step h (by simpa using hS)).1)
    (fun ρ w w' hS h1 h => (tc_step h (by simpa using hS)).2 h1) ?_
  refine TermF.removal (S₁ := fun _ => true) inv
    (fun ρ w w' hS h => (inv_step h (by simp_all) (by simp_all)).le)
    (fun ρ w w' hS _ h => inv_step h (by simp_all) (by simp_all)) ?_
  exact termF_none.mono (by simp)

/-! ## Medida ártica sobre la palabra invertida -/

variable {d : ℕ}

/-- Primera coordenada de `[(▷ w ◁)^rev](0)`. -/
def arcMeasureRev (I : X → AAff (d + 1)) (w : List Sym) : ℕ :=
  WithBot.unbotD 0 (aev I (full w).reverse (fun _ => 0) 0)

theorem arcMeasureRev_le (I : X → AAff (d + 1)) (hI : ∀ z, (I z).wm) {ρ : FRule}
    {w w' : List Sym} (h : FStep ρ w w') (hge : (awI I ρ.lhs.reverse).ge (awI I ρ.rhs.reverse)) :
    arcMeasureRev I w' ≤ arcMeasureRev I w := by
  obtain ⟨p, q, hw, hw', -⟩ := h.decomp
  have hle : aev I (full w').reverse (fun _ => 0) ≤ aev I (full w).reverse (fun _ => 0) := by
    rw [hw, hw', List.reverse_append, List.reverse_append, List.reverse_append,
      List.reverse_append, aev_append, aev_append, aev_append, aev_append,
      ← awI_app I ρ.lhs.reverse, ← awI_app I ρ.rhs.reverse]
    exact aev_mono I q.reverse (AAff.app_le_of_ge hge _)
  exact unbotD_le (hle 0) (aev_ne_bot I hI _)

theorem arcMeasureRev_lt (I : X → AAff (d + 1)) (hI : ∀ z, (I z).wm) {ρ : FRule}
    {w w' : List Sym} (h : FStep ρ w w') (hs : ρ.isDyn = true)
    (hgt : (awI I ρ.lhs.reverse).gt (awI I ρ.rhs.reverse)) :
    arcMeasureRev I w' < arcMeasureRev I w := by
  obtain ⟨p, q, hw, hw', hq⟩ := h.decomp
  have hq := hq hs
  subst hq
  have e1 : aev I (full w).reverse (fun _ => 0) =
      (awI I ρ.lhs.reverse).app (aev I p.reverse (fun _ => 0)) := by
    rw [hw, List.append_nil, List.reverse_append, aev_append, awI_app]
  have e2 : aev I (full w').reverse (fun _ => 0) =
      (awI I ρ.rhs.reverse).app (aev I p.reverse (fun _ => 0)) := by
    rw [hw', List.append_nil, List.reverse_append, aev_append, awI_app]
  have hne := aev_ne_bot I hI (full w').reverse
  rw [e2] at hne
  unfold arcMeasureRev
  rw [e1, e2]
  exact unbotD_lt (AAff.app_lt_of_gt hgt _ hne) hne

theorem TermF.removal_arc_rev (I : X → AAff (d + 1)) {S S₁ : FRule → Bool}
    (hI : ∀ z, (I z).wm)
    (hweak : ∀ ρ, S ρ = true → (awI I ρ.lhs.reverse).ge (awI I ρ.rhs.reverse))
    (hstrict : ∀ ρ, S ρ = true → S₁ ρ = true →
      ρ.isDyn = true ∧ (awI I ρ.lhs.reverse).gt (awI I ρ.rhs.reverse))
    (hrest : TermF (fun ρ => S ρ && !S₁ ρ)) : TermF S :=
  TermF.removal (arcMeasureRev I)
    (fun ρ _ _ hS h => arcMeasureRev_le I hI h (hweak ρ hS))
    (fun ρ _ _ hS h1 h => arcMeasureRev_lt I hI h (hstrict ρ hS h1).1 (hstrict ρ hS h1).2) hrest

set_option maxRecDepth 20000 in
/-- **`ℱ` termina** sobre palabras canónicas (certificado `proofs/farkas.log`). -/
theorem termF_all : TermF (fun _ => true) :=
  TermF.removal_arc_rev I_farkas_1 (S₁ := FRule.isDyn)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) <|
  termF_noDyn.mono (by decide)

/-! ## Semántica -/

theorem FStep.val_eq {ρ : FRule} {w w' : List Sym} (h : FStep ρ w w') :
    (ρ.isDyn = true → val w' = F (val w)) ∧ (ρ.isDyn = false → val w' = val w) := by
  cases h
  case s1 | s2 | s3 => exact ⟨by simp [FRule.isDyn], fun _ => rfl⟩
  case d1 | d2 | d3 | d4 | d5 =>
    refine ⟨fun _ => ?_, by simp [FRule.isDyn]⟩
    simp only [val, valFrom_append, valFrom_cons, valFrom_nil, Sym.act]
    unfold F
    split_ifs <;> omega
  all_goals
    refine ⟨by simp [FRule.isDyn], fun _ => ?_⟩
    simp only [val, valFrom_append, valFrom_cons, Sym.act]
    congr 1; ring

/-! ## Simulación -/

abbrev R := fun x y => StepF (fun _ => true) x y

/-- A lo sumo dos dígitos binarios al principio; el resto, ternarios. -/
def Shape (w : List Sym) : Prop :=
  ∃ B T, w = B ++ T ∧ B.length ≤ 2 ∧ (∀ x ∈ B, x.isBin = true) ∧ (∀ x ∈ T, x.isBin = false)

/-- Un dígito binario atraviesa un bloque ternario con pasos auxiliares (que no cambian el valor). -/
theorem pass (T : List Sym) (hT : ∀ x ∈ T, x.isBin = false) :
    ∀ (u v : List Sym) (b : Sym), b.isBin = true →
      ∃ T' b', b'.isBin = true ∧ (∀ x ∈ T', x.isBin = false) ∧ T'.length = T.length ∧
        Relation.ReflTransGen R (u ++ b :: T ++ v) (u ++ T' ++ b' :: v) ∧
        val (u ++ T' ++ b' :: v) = val (u ++ b :: T ++ v) := by
  induction T with
  | nil => intro u v b hb; exact ⟨[], b, hb, by simp, rfl, by simpa using Relation.ReflTransGen.refl, by simp⟩
  | cons s T ih =>
    intro u v b hb
    have ht : s.isBin = false := hT s (by simp)
    have hT' : ∀ x ∈ T, x.isBin = false := fun x hx => hT x (by simp [hx])
    -- un paso auxiliar `b s → t' b''`
    obtain ⟨t', b'', ht', hb'', hstep⟩ : ∃ t' b'', t'.isBin = false ∧ b''.isBin = true ∧
        ∃ ρ, ρ.isDyn = false ∧ FStep ρ (u ++ b :: s :: (T ++ v)) (u ++ t' :: b'' :: (T ++ v)) := by
      cases b <;> cases s <;> simp [Sym.isBin] at hb ht
      exacts [⟨.d0, .f, rfl, rfl, .a1, rfl, .a1 _ _⟩, ⟨.d0, .t, rfl, rfl, .a2, rfl, .a2 _ _⟩,
        ⟨.d1, .f, rfl, rfl, .a3, rfl, .a3 _ _⟩, ⟨.d1, .t, rfl, rfl, .a4, rfl, .a4 _ _⟩,
        ⟨.d2, .f, rfl, rfl, .a5, rfl, .a5 _ _⟩, ⟨.d2, .t, rfl, rfl, .a6, rfl, .a6 _ _⟩]
    obtain ⟨ρ, hρ, hs⟩ := hstep
    obtain ⟨T'', b', hb', hT'', hlen, hrt, hval⟩ := ih hT' (u ++ [t']) v b'' hb''
    refine ⟨t' :: T'', b', hb', ?_, by simp [hlen], ?_, ?_⟩
    · intro x hx; simp at hx; rcases hx with rfl | hx; exacts [ht', hT'' x hx]
    · refine Relation.ReflTransGen.head ⟨ρ, rfl, by simpa using hs⟩ ?_
      simpa using hrt
    · rw [show u ++ t' :: T'' ++ b' :: v = u ++ [t'] ++ T'' ++ b' :: v by simp, hval,
        show u ++ b :: s :: T ++ v = u ++ b :: s :: (T ++ v) by simp,
        ← (hs.val_eq).2 hρ]
      simp

theorem val_concat (u : List Sym) (s : Sym) : val (u ++ [s]) = s.act (val u) := by simp [val]

theorem tg_flip {x y : List Sym} (h : Relation.TransGen R x y) :
    Relation.TransGen (fun y x => R x y) y x := by
  induction h with
  | single h => exact .single h
  | tail _ h ih => exact .head h ih

/-- El paso dinámico final: si la palabra termina en `c b` (ternario, binario) y su valor no es
`≡ 1 (mod 3)`, hay una regla dinámica que deja un sufijo ternario. -/
theorem dyn_step (u : List Sym) (c b : Sym) (hc : c.isBin = false) (hb : b.isBin = true)
    (hmod : val (u ++ [c, b]) % 3 ≠ 1) :
    ∃ r, (∀ x ∈ r, x.isBin = false) ∧ R (u ++ [c, b]) (u ++ r) ∧
      val (u ++ r) = F (val (u ++ [c, b])) := by
  cases c <;> cases b <;> simp [Sym.isBin] at hc hb
  · exact ⟨[.d0], by simp [Sym.isBin], ⟨.d2, rfl, .d2 u⟩, ((FStep.d2 u).val_eq).1 rfl⟩
  · simp [val, Sym.act] at hmod; omega
  · exact ⟨[.d1], by simp [Sym.isBin], ⟨.d3, rfl, .d3 u⟩, ((FStep.d3 u).val_eq).1 rfl⟩
  · exact ⟨[.d1, .d2], by simp [Sym.isBin], ⟨.d4, rfl, .d4 u⟩, ((FStep.d4 u).val_eq).1 rfl⟩
  · simp [val, Sym.act] at hmod; omega
  · exact ⟨[.d2, .d2], by simp [Sym.isBin], ⟨.d5, rfl, .d5 u⟩, ((FStep.d5 u).val_eq).1 rfl⟩

theorem small_converges : ∀ n < 8, 1 ≤ n → ∃ k < 6, F^[k] n = 1 := by decide

theorem shape_nf_val {B : List Sym} (hB : B.length ≤ 2) (hb : ∀ x ∈ B, x.isBin = true) :
    val B < 8 := by
  match B, hB with
  | [], _ => simp [val]
  | [x], _ => cases x <;> simp_all [val, Sym.act, Sym.isBin]
  | [x, y], _ => cases x <;> cases y <;> simp_all [val, Sym.act, Sym.isBin]

/-- Desde una palabra con `Shape` en la que el sistema no admite reducciones infinitas,
la trayectoria de `F` llega a `1`. -/
theorem converges_of_acc {w : List Sym} (h : Acc (fun y x => R x y) w) (hw : Shape w) :
    ∃ k, F^[k] (val w) = 1 := by
  have h' := h.transGen
  clear h
  induction h' with
  | intro w _ ih =>
    obtain ⟨B, T, rfl, hBl, hB, hT⟩ := hw
    rcases List.eq_nil_or_concat T with rfl | ⟨T₀, z, rfl⟩
    · obtain ⟨k, -, hk⟩ := small_converges _ (by simpa using shape_nf_val hBl hB)
        (one_le_val _)
      exact ⟨k, by simpa using hk⟩
    · simp only [List.concat_eq_append] at hT ih ⊢
      have ht : z.isBin = false := hT z (by simp)
      have hT₀ : ∀ x ∈ T₀, x.isBin = false := fun x hx => hT x (by simp [hx])
      by_cases h1 : z = .d1
      · subst h1
        -- `1◁ → ◁`
        have hs : FStep .d1 ((B ++ T₀) ++ [.d1]) (B ++ T₀) := .d1 _
        obtain ⟨k, hk⟩ := ih (B ++ T₀) (tg_flip (.single ⟨.d1, rfl, by simpa using hs⟩))
          ⟨B, T₀, rfl, hBl, hB, hT₀⟩
        have hv := (hs.val_eq).1 rfl
        rw [List.append_assoc] at hv
        exact ⟨k + 1, by rw [Function.iterate_succ_apply, ← hv]; exact hk⟩
      · rcases List.eq_nil_or_concat B with rfl | ⟨B₀, b, rfl⟩
        · -- sin binarios: regla de inicio sobre el primer dígito
          obtain ⟨s, T₁, hs⟩ := List.exists_cons_of_ne_nil (show T₀ ++ [z] ≠ [] by simp)
          have hsb : s.isBin = false := hT s (by rw [hs]; simp)
          have hT₁ : ∀ x ∈ T₁, x.isBin = false := fun x hx => hT x (by rw [hs]; simp [hx])
          obtain ⟨B', hB'l, hB', ρ, hst, hρ⟩ : ∃ B', B'.length ≤ 2 ∧ (∀ x ∈ B', x.isBin = true) ∧
              ∃ ρ, FStep ρ (s :: T₁) (B' ++ T₁) ∧ ρ.isDyn = false := by
            cases s <;> simp [Sym.isBin] at hsb
            exacts [⟨[.t], by simp, by simp [Sym.isBin], .s1, .s1 T₁, rfl⟩,
              ⟨[.f, .f], by simp, by simp [Sym.isBin], .s2, .s2 T₁, rfl⟩,
              ⟨[.f, .t], by simp, by simp [Sym.isBin], .s3, .s3 T₁, rfl⟩]
          obtain ⟨k, hk⟩ := ih (B' ++ T₁) (tg_flip (.single ⟨ρ, rfl, by simpa [hs] using hst⟩))
            ⟨B', T₁, rfl, hB'l, hB', hT₁⟩
          rw [(hst.val_eq).2 hρ] at hk
          exact ⟨k, by simpa [hs] using hk⟩
        · -- el último binario atraviesa el bloque ternario y se aplica una regla dinámica
          simp only [List.concat_eq_append] at hT ih hBl hB ⊢
          have hb : b.isBin = true := hB b (by simp)
          have hB₀ : ∀ x ∈ B₀, x.isBin = true := fun x hx => hB x (by simp [hx])
          obtain ⟨T', b', hb', hT', hlen, hrt, hval⟩ := pass (T₀ ++ [z]) hT B₀ [] b hb
          rcases List.eq_nil_or_concat T' with rfl | ⟨T'', c, rfl⟩
          · simp at hlen
          · simp only [List.concat_eq_append] at hT' hrt hval
            have hc : c.isBin = false := hT' c (by simp)
            have hT'' : ∀ x ∈ T'', x.isBin = false := fun x hx => hT' x (by simp [hx])
            have hv0 : val ((B₀ ++ T'') ++ [c, b']) = val (B₀ ++ [b] ++ (T₀ ++ [z])) := by
              simpa using hval
            have hmod : val ((B₀ ++ T'') ++ [c, b']) % 3 ≠ 1 := by
              rw [hv0, ← List.append_assoc, val_concat]
              cases z <;> simp [Sym.act, Sym.isBin] at ht h1 ⊢
            obtain ⟨r, hr, hstep, hv⟩ := dyn_step (B₀ ++ T'') c b' hc hb' hmod
            have htg : Relation.TransGen R (B₀ ++ [b] ++ (T₀ ++ [z])) ((B₀ ++ T'') ++ r) :=
              Relation.TransGen.tail' (by simpa using hrt) hstep
            obtain ⟨k, hk⟩ := ih _ (tg_flip htg) ⟨B₀, T'' ++ r, by simp,
              by simp at hBl; omega, hB₀, fun x hx => by
                rcases List.mem_append.mp hx with h | h
                exacts [hT'' x h, hr x h]⟩
            exact ⟨k + 1, by rw [Function.iterate_succ_apply, ← hv0, ← hv]; exact hk⟩

/-- Toda palabra `n ≥ 1` tiene una representación con `Shape`: su escritura ternaria. -/
theorem exists_shape {n : ℕ} (hn : 1 ≤ n) : ∃ w, Shape w ∧ val w = n := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    rcases Nat.lt_or_ge n 3 with h | h
    · interval_cases n
      · exact ⟨[], ⟨[], [], rfl, by simp, by simp, by simp⟩, rfl⟩
      · exact ⟨[.f], ⟨[.f], [], rfl, by simp, by simp [Sym.isBin], by simp⟩, rfl⟩
    · obtain ⟨w, ⟨B, T, rfl, hBl, hB, hT⟩, hw⟩ := ih (n / 3) (by omega) (by omega)
      have key : ∀ s : Sym, s.isBin = false → s.act (n / 3) = n →
          ∃ w, Shape w ∧ val w = n := fun s hs hv =>
        ⟨B ++ T ++ [s], ⟨B, T ++ [s], by simp, hBl, hB, fun x hx => by
          rcases List.mem_append.mp hx with h | h
          · exact hT x h
          · simp at h; rw [h]; exact hs⟩, by rw [val_concat, hw, hv]⟩
      rcases (by omega : n % 3 = 0 ∨ n % 3 = 1 ∨ n % 3 = 2) with h3 | h3 | h3
      · exact key .d0 rfl (by simp [Sym.act]; omega)
      · exact key .d1 rfl (by simp [Sym.act]; omega)
      · exact key .d2 rfl (by simp [Sym.act]; omega)

end SRS.Farkas

/-- **Teorema de Farkas (Yolcu–Aaronson–Heule, Teorema 4.2), por la vía automática.** Toda
trayectoria de `F` desde `n ≥ 1` llega a `1`. La prueba usa sólo la terminación de `ℱ`
(`termF_all`, certificado ártico verificado por Lean) y la simulación `converges_of_acc`. -/
theorem farkas_convergent : ∀ n, 1 ≤ n → ∃ k, SRS.Farkas.F^[k] n = 1 := by
  intro n hn
  obtain ⟨w, hw, rfl⟩ := SRS.Farkas.exists_shape hn
  exact SRS.Farkas.converges_of_acc (SRS.Farkas.termF_all w) hw
