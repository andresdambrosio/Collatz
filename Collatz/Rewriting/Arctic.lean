import Collatz.Rewriting.Natural

/-!
# Interpretaciones matriciales árticas

Semianillo max-plus sobre `WithBot ℕ` (`⊥ = -∞`): `x ⊕ y = max x y`, `x ⊗ y = x + y`.
Una interpretación ártica asigna a cada símbolo `x ↦ M ⊗ x ⊕ v`. Para terminación "top"
(Koprowski–Waldmann; Yolcu–Aaronson–Heule §2.3.2) se usa el dominio `ℕ × A^{d-1}`:

* débil: `M_l ≥ M_r` y `v_l ≥ v_r` coeficiente a coeficiente;
* estricta: `M_l ≫ M_r` y `v_l ≫ v_r`, donde `a ≫ b` significa `b = ⊥ ∨ b < a`;
* buena definición: cada símbolo tiene `M₀₀ ≠ ⊥` o `v₀ ≠ ⊥` (la primera coordenada queda finita).

La medida es la primera coordenada de `[▷ w ◁](0)`, que es finita.
-/

namespace SRS

abbrev Arc := WithBot ℕ

abbrev AVec (d : ℕ) := Fin d → Arc

/-- Función afín ártica `x ↦ M ⊗ x ⊕ v`. -/
structure AAff (d : ℕ) where
  M : Fin d → Fin d → Arc
  v : Fin d → Arc

/-! ## Lemas del semianillo -/

theorem arc_add_sup (a : Arc) {ι : Type*} (s : Finset ι) (f : ι → Arc) :
    a + s.sup f = s.sup (fun j => a + f j) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert j s _ ih =>
    simp only [Finset.sup_insert, ← ih]
    exact (max_add_add_left _ _ _).symm

theorem arc_add_max (a b c : Arc) : a + (b ⊔ c) = (a + b) ⊔ (a + c) :=
  (max_add_add_left _ _ _).symm

theorem sup_sup' {ι : Type*} (s : Finset ι) (P Q : ι → Arc) :
    s.sup (fun j => P j ⊔ Q j) = s.sup P ⊔ s.sup Q := Finset.sup_sup

namespace AAff

variable {d : ℕ}

def app (f : AAff d) (x : AVec d) : AVec d := fun i => (Finset.univ.sup fun j => f.M i j + x j) ⊔ f.v i

def id : AAff d := ⟨fun i j => if i = j then 0 else ⊥, fun _ => ⊥⟩

/-- `f.comp g = f ∘ g`. -/
def comp (f g : AAff d) : AAff d :=
  ⟨fun i k => Finset.univ.sup fun j => f.M i j + g.M j k,
   fun i => (Finset.univ.sup fun j => f.M i j + g.v j) ⊔ f.v i⟩

def ge (f g : AAff d) : Prop := (∀ i j, g.M i j ≤ f.M i j) ∧ ∀ i, g.v i ≤ f.v i

/-- `a ≫ b`. -/
def gg (a b : Arc) : Prop := b = ⊥ ∨ b < a

instance (a b : Arc) : Decidable (gg a b) := by unfold gg; infer_instance

/-- Estricta coeficiente a coeficiente (incluye la débil). -/
def gt (f g : AAff d) : Prop := f.ge g ∧ (∀ i j, gg (f.M i j) (g.M i j)) ∧ ∀ i, gg (f.v i) (g.v i)

/-- La primera coordenada no se vuelve `-∞`. -/
def wm (f : AAff (d + 1)) : Prop := f.M 0 0 ≠ ⊥ ∨ f.v 0 ≠ ⊥

instance (f g : AAff d) : Decidable (f.ge g) := by unfold ge; infer_instance
instance (f g : AAff d) : Decidable (f.gt g) := by unfold gt; infer_instance
instance (f : AAff (d + 1)) : Decidable f.wm := by unfold wm; infer_instance

theorem app_id (x : AVec d) : (id : AAff d).app x = x := by
  funext i
  simp only [app, id]
  apply le_antisymm
  · refine sup_le (Finset.sup_le fun j _ => ?_) bot_le
    by_cases h : i = j
    · subst h; simp
    · simp [h]
  · exact le_sup_of_le_left (Finset.le_sup_of_le (Finset.mem_univ i) (by simp))

theorem app_comp (f g : AAff d) (x : AVec d) : (f.comp g).app x = f.app (g.app x) := by
  funext i
  simp only [app, comp]
  have h1 : ∀ k, (Finset.univ.sup fun j => f.M i j + g.M j k) + x k =
      Finset.univ.sup fun j => f.M i j + (g.M j k + x k) := by
    intro k; rw [add_comm, arc_add_sup]; congr 1; funext j; rw [add_comm, add_assoc]
  have h2 : ∀ j, f.M i j + ((Finset.univ.sup fun k => g.M j k + x k) ⊔ g.v j) =
      (Finset.univ.sup fun k => f.M i j + (g.M j k + x k)) ⊔ (f.M i j + g.v j) := by
    intro j; rw [arc_add_max, arc_add_sup]
  simp only [h1, h2]
  rw [sup_sup', Finset.sup_comm]
  ac_rfl

theorem app_mono (f : AAff d) {x y : AVec d} (h : x ≤ y) : f.app x ≤ f.app y := fun _ =>
  sup_le_sup_right (Finset.sup_mono_fun fun j _ => add_le_add le_rfl (h j)) _

theorem app_le_of_ge {f g : AAff d} (h : f.ge g) (x : AVec d) : g.app x ≤ f.app x := fun i =>
  sup_le_sup (Finset.sup_mono_fun fun j _ => add_le_add (h.1 i j) le_rfl) (h.2 i)

theorem app_ne_bot {f : AAff (d + 1)} (h : f.wm) {x : AVec (d + 1)} (hx : x 0 ≠ ⊥) :
    f.app x 0 ≠ ⊥ := by
  intro hb
  simp only [app] at hb
  rcases h with h | h
  · have : f.M 0 0 + x 0 ≤ ⊥ :=
      hb ▸ le_sup_of_le_left (Finset.le_sup (f := fun j => f.M 0 j + x j) (Finset.mem_univ 0))
    exact WithBot.add_ne_bot.mpr ⟨h, hx⟩ (le_bot_iff.mp this)
  · exact h (le_bot_iff.mp (hb ▸ le_sup_right))

theorem lt_of_gg_add {a b y : Arc} (h : gg a b) : b + y = ⊥ ∨ b + y < a + y := by
  rcases h with h | h
  · left; simp [h]
  · induction y using WithBot.recBotCoe with
    | bot => left; simp
    | coe n =>
      induction b using WithBot.recBotCoe with
      | bot => left; simp
      | coe m =>
        induction a using WithBot.recBotCoe with
        | bot => exact absurd h (by simp)
        | coe k =>
          right
          have : m < k := WithBot.coe_lt_coe.mp h
          rw [← WithBot.coe_add, ← WithBot.coe_add]
          exact WithBot.coe_lt_coe.mpr (by omega)

/-- Si cada término de la derecha es `⊥` o menor que el de la izquierda, y la derecha no es `⊥`,
entonces la derecha es menor. -/
theorem sup_lt_sup {ι : Type*} (s : Finset ι) (f g : ι → Arc) (a b : Arc)
    (hf : ∀ j ∈ s, f j = ⊥ ∨ f j < g j) (hab : b = ⊥ ∨ b < a) (hne : s.sup f ⊔ b ≠ ⊥) :
    s.sup f ⊔ b < s.sup g ⊔ a := by
  have key : ∀ j ∈ s, f j ≠ ⊥ → f j < s.sup g ⊔ a := fun j hj hne' =>
    lt_of_lt_of_le ((hf j hj).resolve_left hne') (le_sup_of_le_left (Finset.le_sup hj))
  by_cases hfb : s.sup f = ⊥
  · rw [hfb, bot_sup_eq] at hne ⊢
    exact lt_of_lt_of_le (hab.resolve_left hne) le_sup_right
  · obtain ⟨j, hj, hjne⟩ : ∃ j ∈ s, f j ≠ ⊥ := by
      by_contra hc; push Not at hc; exact hfb (Finset.sup_eq_bot_iff _ _ |>.mpr hc)
    have hpos : ⊥ < s.sup g ⊔ a := lt_of_le_of_lt bot_le (key j hj hjne)
    refine sup_lt_iff.mpr ⟨(Finset.sup_lt_iff hpos).mpr fun k hk => ?_, ?_⟩
    · by_cases hk' : f k = ⊥
      · rw [hk']; exact hpos
      · exact key k hk hk'
    · rcases hab with hb | hb
      · rw [hb]; exact hpos
      · exact lt_of_lt_of_le hb le_sup_right

theorem app_lt_of_gt {f g : AAff (d + 1)} (h : f.gt g) (x : AVec (d + 1)) (hne : g.app x 0 ≠ ⊥) :
    g.app x 0 < f.app x 0 :=
  sup_lt_sup _ _ _ _ _ (fun j _ => lt_of_gg_add (h.2.1 0 j)) (h.2.2 0) hne

end AAff

variable {d : ℕ}

def awI (I : X → AAff d) (s : List X) : AAff d := s.foldr (fun x acc => (I x).comp acc) AAff.id

def aev (I : X → AAff d) (s : List X) (x : AVec d) : AVec d := s.foldr (fun z y => (I z).app y) x

theorem aev_append (I : X → AAff d) (s t : List X) (x : AVec d) :
    aev I (s ++ t) x = aev I s (aev I t x) := List.foldr_append

theorem awI_app (I : X → AAff d) (s : List X) (x : AVec d) : (awI I s).app x = aev I s x := by
  induction s with
  | nil => exact AAff.app_id x
  | cons z s ih => simp only [awI, aev, List.foldr_cons] at ih ⊢; rw [AAff.app_comp, ih]

theorem aev_mono (I : X → AAff d) (s : List X) {x y : AVec d} (h : x ≤ y) :
    aev I s x ≤ aev I s y := by
  induction s with
  | nil => exact h
  | cons z s ih => exact (I z).app_mono ih

theorem aev_ne_bot (I : X → AAff (d + 1)) (hI : ∀ z, (I z).wm) (s : List X) :
    aev I s (fun _ => 0) 0 ≠ ⊥ := by
  induction s with
  | nil => simp [aev]
  | cons z s ih => exact AAff.app_ne_bot (hI z) ih

/-- Medida ártica: primera coordenada (finita) de `[▷ w ◁](0)`. -/
def arcMeasure (I : X → AAff (d + 1)) (w : List Sym) : ℕ :=
  WithBot.unbotD 0 (aev I (full w) (fun _ => 0) 0)

theorem unbotD_le {a b : Arc} (h : a ≤ b) (ha : a ≠ ⊥) : WithBot.unbotD 0 a ≤ WithBot.unbotD 0 b := by
  induction a using WithBot.recBotCoe with
  | bot => exact absurd rfl ha
  | coe m =>
    induction b using WithBot.recBotCoe with
    | bot => exact absurd h (by simp)
    | coe k => simpa using h

theorem unbotD_lt {a b : Arc} (h : a < b) (ha : a ≠ ⊥) : WithBot.unbotD 0 a < WithBot.unbotD 0 b := by
  induction a using WithBot.recBotCoe with
  | bot => exact absurd rfl ha
  | coe m =>
    induction b using WithBot.recBotCoe with
    | bot => exact absurd h (by simp)
    | coe k => simpa using h

theorem arcMeasure_le (I : X → AAff (d + 1)) (hI : ∀ z, (I z).wm) {ρ : RuleName}
    {w w' : List Sym} (h : IStep ρ w w') (hge : (awI I ρ.lhs).ge (awI I ρ.rhs)) :
    arcMeasure I w' ≤ arcMeasure I w := by
  obtain ⟨p, q, hw, hw', -⟩ := h.decomp
  have hle : aev I (full w') (fun _ => 0) ≤ aev I (full w) (fun _ => 0) := by
    rw [hw, hw', aev_append, aev_append, aev_append, aev_append, ← awI_app I ρ.lhs,
      ← awI_app I ρ.rhs]
    exact aev_mono I p (AAff.app_le_of_ge hge _)
  exact unbotD_le (hle 0) (aev_ne_bot I hI _)

theorem arcMeasure_lt (I : X → AAff (d + 1)) (hI : ∀ z, (I z).wm) {ρ : RuleName}
    {w w' : List Sym} (h : IStep ρ w w') (hs : ρ.isStart = true)
    (hgt : (awI I ρ.lhs).gt (awI I ρ.rhs)) : arcMeasure I w' < arcMeasure I w := by
  obtain ⟨p, q, hw, hw', hp⟩ := h.decomp
  have hp := hp hs
  subst hp
  have e1 : aev I (full w) (fun _ => 0) = (awI I ρ.lhs).app (aev I q (fun _ => 0)) := by
    rw [hw, List.nil_append, aev_append, awI_app]
  have e2 : aev I (full w') (fun _ => 0) = (awI I ρ.rhs).app (aev I q (fun _ => 0)) := by
    rw [hw', List.nil_append, aev_append, awI_app]
  have hne := aev_ne_bot I hI (full w')
  rw [e2] at hne
  unfold arcMeasure
  rw [e1, e2]
  exact unbotD_lt (AAff.app_lt_of_gt hgt _ hne) hne

/-- **Un paso de un certificado ártico.** -/
theorem TermIn.removal_arc (I : X → AAff (d + 1)) {S S₁ : RuleName → Bool}
    (hI : ∀ z, (I z).wm)
    (hweak : ∀ ρ, S ρ = true → (awI I ρ.lhs).ge (awI I ρ.rhs))
    (hstrict : ∀ ρ, S ρ = true → S₁ ρ = true → ρ.isStart = true ∧ (awI I ρ.lhs).gt (awI I ρ.rhs))
    (hrest : TermIn (fun ρ => S ρ && !S₁ ρ)) : TermIn S :=
  TermIn.removal (arcMeasure I)
    (fun ρ _ _ hS h => arcMeasure_le I hI h (hweak ρ hS))
    (fun ρ _ _ hS h1 h => arcMeasure_lt I hI h (hstrict ρ hS h1).1 (hstrict ρ hS h1).2) hrest

end SRS
