import Collatz.Rewriting

/-!
# Subsistemas de `𝒯`: eliminación de reglas e interpretaciones matriciales naturales

Infraestructura para verificar en Lean los certificados de terminación de Yolcu–Aaronson–Heule
(arXiv 2105.14697, §4.3; certificados en `github.com/emreyolcu/rewriting-collatz/proofs`).

Todo es sobre palabras canónicas `▷ w ◁` (como `SRS.Terminates`). En ese marco las reglas de
inicio `ℬ` sólo actúan en el extremo izquierdo, así que basta con álgebras débilmente monótonas
(el Lema 3.18 del paper es inmediato acá).

* `IStep ρ`: paso con la regla `ρ` (las 11 reglas, en el orden de `rules/collatz-T.srs`).
* `TermIn S`: el subsistema con las reglas `S` termina sobre palabras canónicas.
* `TermIn.removal`: eliminación de reglas con una medida `φ : List Sym → ℕ` (Teorema 2.6 del paper,
  versión con medida).
* `TermIn.removal_nat`: la medida es la primera coordenada de `[▷ w ◁](0)` para una
  interpretación afín natural; las condiciones son comparaciones de matrices, chequeables
  con `decide`.
* `termIn_noStart`: `𝒯 ∖ ℬ` termina (Lema 3.15 del paper), con la medida lexicográfica `(bc, inv)`.
-/

namespace SRS

/-! ## Reglas con nombre -/

/-- Alfabeto con marcadores, con los nombres ASCII del repositorio del paper:
`a = f`, `b = t`, `c = ▷`, `d = ◁`, `e = 0`, `f = 1`, `g = 2`. -/
inductive X | a | b | c | d | e | f | g
  deriving DecidableEq, Repr

instance : Fintype X :=
  Fintype.ofList [.a, .b, .c, .d, .e, .f, .g] (by intro x; cases x <;> simp)

def Sym.toX : Sym → X
  | .f => .a
  | .t => .b
  | .d0 => .e
  | .d1 => .f
  | .d2 => .g

/-- La palabra completa `▷ w ◁`. -/
def full (w : List Sym) : List X := .c :: (w.map Sym.toX ++ [.d])

/-- Las 11 reglas de `𝒯`, en el orden de `rules/collatz-T.srs`. -/
inductive RuleName | r01 | r02 | r03 | r04 | r05 | r06 | r07 | r08 | r09 | r10 | r11
  deriving DecidableEq, Repr

instance : Fintype RuleName :=
  Fintype.ofList [.r01, .r02, .r03, .r04, .r05, .r06, .r07, .r08, .r09, .r10, .r11]
    (by intro x; cases x <;> simp)

def RuleName.lhs : RuleName → List X
  | .r01 => [.a, .d] | .r02 => [.b, .d]
  | .r03 => [.a, .e] | .r04 => [.a, .f] | .r05 => [.a, .g]
  | .r06 => [.b, .e] | .r07 => [.b, .f] | .r08 => [.b, .g]
  | .r09 => [.c, .e] | .r10 => [.c, .f] | .r11 => [.c, .g]

def RuleName.rhs : RuleName → List X
  | .r01 => [.d] | .r02 => [.g, .d]
  | .r03 => [.e, .a] | .r04 => [.e, .b] | .r05 => [.f, .a]
  | .r06 => [.f, .b] | .r07 => [.g, .a] | .r08 => [.g, .b]
  | .r09 => [.c, .b] | .r10 => [.c, .a, .a] | .r11 => [.c, .a, .b]

/-- Reglas de inicio `ℬ` (actúan sólo en el extremo izquierdo). -/
def RuleName.isStart : RuleName → Bool
  | .r09 | .r10 | .r11 => true
  | _ => false

/-- Reglas dinámicas `𝒟_T`. -/
def RuleName.isDyn : RuleName → Bool
  | .r01 | .r02 => true
  | _ => false

/-- Paso con una regla determinada, sobre la palabra interna. -/
inductive IStep : RuleName → List Sym → List Sym → Prop
  | r01 (u : List Sym) : IStep .r01 (u ++ [.f]) u
  | r02 (u : List Sym) : IStep .r02 (u ++ [.t]) (u ++ [.d2])
  | r03 (u v : List Sym) : IStep .r03 (u ++ .f :: .d0 :: v) (u ++ .d0 :: .f :: v)
  | r04 (u v : List Sym) : IStep .r04 (u ++ .f :: .d1 :: v) (u ++ .d0 :: .t :: v)
  | r05 (u v : List Sym) : IStep .r05 (u ++ .f :: .d2 :: v) (u ++ .d1 :: .f :: v)
  | r06 (u v : List Sym) : IStep .r06 (u ++ .t :: .d0 :: v) (u ++ .d1 :: .t :: v)
  | r07 (u v : List Sym) : IStep .r07 (u ++ .t :: .d1 :: v) (u ++ .d2 :: .f :: v)
  | r08 (u v : List Sym) : IStep .r08 (u ++ .t :: .d2 :: v) (u ++ .d2 :: .t :: v)
  | r09 (v : List Sym) : IStep .r09 (.d0 :: v) (.t :: v)
  | r10 (v : List Sym) : IStep .r10 (.d1 :: v) (.f :: .f :: v)
  | r11 (v : List Sym) : IStep .r11 (.d2 :: v) (.f :: .t :: v)

theorem step_iff {w w' : List Sym} : Step w w' ↔ ∃ ρ, IStep ρ w w' := by
  constructor
  · intro h
    cases h
    exacts [⟨_, .r01 _⟩, ⟨_, .r02 _⟩, ⟨_, .r03 _ _⟩, ⟨_, .r04 _ _⟩, ⟨_, .r05 _ _⟩,
      ⟨_, .r06 _ _⟩, ⟨_, .r07 _ _⟩, ⟨_, .r08 _ _⟩, ⟨_, .r09 _⟩, ⟨_, .r10 _⟩, ⟨_, .r11 _⟩]
  · rintro ⟨ρ, h⟩
    cases h
    exacts [.endF _, .endT _, .f0 _ _, .f1 _ _, .f2 _ _, .t0 _ _, .t1 _ _, .t2 _ _,
      .s0 _, .s1 _, .s2 _]

/-- Todo paso es una aplicación literal de su regla dentro de `▷ w ◁`; las de inicio, en el
extremo izquierdo. -/
theorem IStep.decomp {ρ : RuleName} {w w' : List Sym} (h : IStep ρ w w') :
    ∃ p q, full w = p ++ ρ.lhs ++ q ∧ full w' = p ++ ρ.rhs ++ q ∧
      (ρ.isStart = true → p = []) := by
  cases h
  case r01 => exact ⟨.c :: w'.map Sym.toX, [], by simp [full, RuleName.lhs, Sym.toX],
      by simp [full, RuleName.rhs], by simp [RuleName.isStart]⟩
  case r02 u => exact ⟨.c :: u.map Sym.toX, [], by simp [full, RuleName.lhs, Sym.toX],
      by simp [full, RuleName.rhs, Sym.toX], by simp [RuleName.isStart]⟩
  case r09 v => exact ⟨[], v.map Sym.toX ++ [.d], by simp [full, RuleName.lhs, Sym.toX],
      by simp [full, RuleName.rhs, Sym.toX], by simp⟩
  case r10 v => exact ⟨[], v.map Sym.toX ++ [.d], by simp [full, RuleName.lhs, Sym.toX],
      by simp [full, RuleName.rhs, Sym.toX], by simp⟩
  case r11 v => exact ⟨[], v.map Sym.toX ++ [.d], by simp [full, RuleName.lhs, Sym.toX],
      by simp [full, RuleName.rhs, Sym.toX], by simp⟩
  all_goals
    rename_i u v
    exact ⟨.c :: u.map Sym.toX, v.map Sym.toX ++ [.d],
      by simp [full, RuleName.lhs, Sym.toX], by simp [full, RuleName.rhs, Sym.toX],
      by simp [RuleName.isStart]⟩

/-! ## Subsistemas -/

/-- Paso con alguna regla de `S`. -/
def StepIn (S : RuleName → Bool) (w w' : List Sym) : Prop := ∃ ρ, S ρ = true ∧ IStep ρ w w'

/-- El subsistema `S` termina sobre las palabras canónicas `▷ w ◁`. -/
def TermIn (S : RuleName → Bool) : Prop := ∀ w, Acc (fun y x => StepIn S x y) w

theorem terminates_iff_termIn : Terminates ↔ TermIn (fun _ => true) := by
  have : (fun y x => Step x y) = (fun y x => StepIn (fun _ => true) x y) := by
    funext y x; simp [StepIn, step_iff]
  unfold Terminates TermIn; rw [this]

theorem TermIn.mono {S S' : RuleName → Bool} (h : TermIn S) (hS : ∀ ρ, S' ρ = true → S ρ = true) :
    TermIn S' := fun w =>
  Subrelation.accessible (fun ⟨ρ, h1, h2⟩ => ⟨ρ, hS ρ h1, h2⟩) (h w)

theorem termIn_none : TermIn (fun _ => false) :=
  fun _ => Acc.intro _ fun _ ⟨_, h, _⟩ => absurd h (by simp)

/-- **Eliminación de reglas con una medida.** Si `φ` no crece en ningún paso de `S` y baja
estrictamente en los pasos de `S₁`, la terminación de `S ∖ S₁` implica la de `S`. -/
theorem TermIn.removal {S S₁ : RuleName → Bool} (φ : List Sym → ℕ)
    (hle : ∀ ρ w w', S ρ = true → IStep ρ w w' → φ w' ≤ φ w)
    (hlt : ∀ ρ w w', S ρ = true → S₁ ρ = true → IStep ρ w w' → φ w' < φ w)
    (hrest : TermIn (fun ρ => S ρ && !S₁ ρ)) : TermIn S := by
  suffices H : ∀ n w, φ w = n → Acc (fun y x => StepIn S x y) w from fun w => H _ w rfl
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

/-! ## `𝒯 ∖ ℬ` termina -/

theorem bc_map_lt {ρ : RuleName} {w w' : List Sym} (h : IStep ρ w w') (hρ : ρ.isStart = false) :
    bc w' ≤ bc w ∧ (ρ.isDyn = true → bc w' < bc w) := by
  cases h <;> simp_all [RuleName.isStart, RuleName.isDyn, bc_append, bc, Sym.isBin]

theorem inv_lt {ρ : RuleName} {w w' : List Sym} (h : IStep ρ w w') (hρ : ρ.isStart = false)
    (hd : ρ.isDyn = false) : inv w' < inv w := by
  cases h <;> simp_all [RuleName.isStart, RuleName.isDyn, inv_append, inv, tc, Sym.isBin]

/-- **Lema 3.15 (forma canónica).** Sin reglas de inicio, el sistema termina. -/
theorem termIn_noStart : TermIn (fun ρ => !ρ.isStart) := by
  refine TermIn.removal (S₁ := RuleName.isDyn) bc
    (fun ρ w w' hS h => (bc_map_lt h (by simpa using hS)).1)
    (fun ρ w w' hS h1 h => (bc_map_lt h (by simpa using hS)).2 h1) ?_
  refine TermIn.removal (S₁ := fun _ => true) inv
    (fun ρ w w' hS h => (inv_lt h (by simp_all) (by simp_all)).le)
    (fun ρ w w' hS _ h => inv_lt h (by simp_all) (by simp_all)) ?_
  exact termIn_none.mono (by simp)

/-! ## Interpretaciones afines naturales -/

abbrev Vec (d : ℕ) := Fin d → ℕ

/-- Función afín `x ↦ M x + v` sobre `ℕ^d`. -/
structure Aff (d : ℕ) where
  M : Fin d → Fin d → ℕ
  v : Fin d → ℕ

namespace Aff

variable {d : ℕ}

def app (f : Aff d) (x : Vec d) : Vec d := fun i => (∑ j, f.M i j * x j) + f.v i

def id : Aff d := ⟨fun i j => if i = j then 1 else 0, fun _ => 0⟩

/-- `f.comp g = f ∘ g`. -/
def comp (f g : Aff d) : Aff d :=
  ⟨fun i k => ∑ j, f.M i j * g.M j k, fun i => (∑ j, f.M i j * g.v j) + f.v i⟩

/-- `f ≥ g` coeficiente a coeficiente; implica `f x ≥ g x` para todo `x`. -/
def ge (f g : Aff d) : Prop := (∀ i j, g.M i j ≤ f.M i j) ∧ ∀ i, g.v i ≤ f.v i

/-- Además, estricto en la primera coordenada del término constante. -/
def gt (f g : Aff (d + 1)) : Prop := f.ge g ∧ g.v 0 < f.v 0

instance (f g : Aff d) : Decidable (f.ge g) := by unfold ge; infer_instance
instance (f g : Aff (d + 1)) : Decidable (f.gt g) := by unfold gt; infer_instance

theorem app_id (x : Vec d) : (id : Aff d).app x = x := by
  funext i; simp [app, id]

theorem app_comp (f g : Aff d) (x : Vec d) : (f.comp g).app x = f.app (g.app x) := by
  funext i
  simp only [app, comp, Finset.sum_mul, mul_add, Finset.sum_add_distrib, Finset.mul_sum]
  rw [Finset.sum_comm]
  simp only [mul_assoc]
  ring

theorem app_mono (f : Aff d) {x y : Vec d} (h : x ≤ y) : f.app x ≤ f.app y := fun _ =>
  Nat.add_le_add_right (Finset.sum_le_sum fun j _ => Nat.mul_le_mul_left _ (h j)) _

theorem app_le_of_ge {f g : Aff d} (h : f.ge g) (x : Vec d) : g.app x ≤ f.app x := fun i =>
  Nat.add_le_add (Finset.sum_le_sum fun j _ => Nat.mul_le_mul_right _ (h.1 i j)) (h.2 i)

theorem app_lt_of_gt {f g : Aff (d + 1)} (h : f.gt g) (x : Vec (d + 1)) :
    g.app x 0 < f.app x 0 :=
  Nat.add_lt_add_of_le_of_lt (Finset.sum_le_sum fun j _ => Nat.mul_le_mul_right _ (h.1.1 0 j)) h.2

end Aff

variable {d : ℕ}

/-- Interpretación de una palabra: `[s₁ ⋯ sₙ] = [s₁] ∘ ⋯ ∘ [sₙ]`. -/
def wI (I : X → Aff d) (s : List X) : Aff d := s.foldr (fun x acc => (I x).comp acc) Aff.id

/-- Evaluación de una palabra en un vector. -/
def ev (I : X → Aff d) (s : List X) (x : Vec d) : Vec d := s.foldr (fun z y => (I z).app y) x

theorem ev_append (I : X → Aff d) (s t : List X) (x : Vec d) :
    ev I (s ++ t) x = ev I s (ev I t x) := List.foldr_append

theorem wI_app (I : X → Aff d) (s : List X) (x : Vec d) : (wI I s).app x = ev I s x := by
  induction s with
  | nil => exact Aff.app_id x
  | cons z s ih => simp only [wI, ev, List.foldr_cons] at ih ⊢; rw [Aff.app_comp, ih]

theorem ev_mono (I : X → Aff d) (s : List X) {x y : Vec d} (h : x ≤ y) : ev I s x ≤ ev I s y := by
  induction s with
  | nil => exact h
  | cons z s ih => exact (I z).app_mono ih

/-- Medida asociada a una interpretación: primera coordenada de `[▷ w ◁](0)`. -/
def natMeasure (I : X → Aff (d + 1)) (w : List Sym) : ℕ := ev I (full w) 0 0

theorem natMeasure_le (I : X → Aff (d + 1)) {ρ : RuleName} {w w' : List Sym} (h : IStep ρ w w')
    (hge : (wI I ρ.lhs).ge (wI I ρ.rhs)) : natMeasure I w' ≤ natMeasure I w := by
  obtain ⟨p, q, hw, hw', -⟩ := h.decomp
  unfold natMeasure
  rw [hw, hw', ev_append, ev_append, ev_append, ev_append, ← wI_app I ρ.lhs, ← wI_app I ρ.rhs]
  exact ev_mono I p (Aff.app_le_of_ge hge _) 0

theorem natMeasure_lt (I : X → Aff (d + 1)) {ρ : RuleName} {w w' : List Sym} (h : IStep ρ w w')
    (hs : ρ.isStart = true) (hgt : (wI I ρ.lhs).gt (wI I ρ.rhs)) :
    natMeasure I w' < natMeasure I w := by
  obtain ⟨p, q, hw, hw', hp⟩ := h.decomp
  have hp := hp hs
  subst hp
  unfold natMeasure
  rw [hw, hw', List.nil_append, List.nil_append, ev_append, ev_append, ← wI_app I ρ.lhs,
    ← wI_app I ρ.rhs]
  exact Aff.app_lt_of_gt hgt _

/-- **Un paso de un certificado natural.** Si la interpretación `I` decrece (débilmente) en todas
las reglas de `S` y estrictamente en las de `S₁`, que son de inicio, basta con que termine
`S ∖ S₁`. Las hipótesis son decidibles y se chequean con `decide`. -/
theorem TermIn.removal_nat (I : X → Aff (d + 1)) {S S₁ : RuleName → Bool}
    (hweak : ∀ ρ, S ρ = true → (wI I ρ.lhs).ge (wI I ρ.rhs))
    (hstrict : ∀ ρ, S ρ = true → S₁ ρ = true → ρ.isStart = true ∧ (wI I ρ.lhs).gt (wI I ρ.rhs))
    (hrest : TermIn (fun ρ => S ρ && !S₁ ρ)) : TermIn S :=
  TermIn.removal (natMeasure I)
    (fun ρ _ _ hS h => natMeasure_le I h (hweak ρ hS))
    (fun ρ _ _ hS h1 h => natMeasure_lt I h (hstrict ρ hS h1).1 (hstrict ρ hS h1).2) hrest

end SRS
