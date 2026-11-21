import Collatz.Rewriting.AllWords

/-!
# Vecinos de `𝒯`: el mismo sistema con `t◁ → e◁`

Ver `Ideas/vecinos_de_T.md`. Sobre el alfabeto completo (`SRS.Full`) definimos la familia de
sistemas `𝒯ₑ`, idénticos a `𝒯` salvo la regla dinámica `t◁ → e◁`. En los impares simulan
`x ↦ (3x + 2e − 3)/2`:
* `e = 2`: Collatz (`nstep_d2_iff`: `𝒯₂` es exactamente `WStep`);
* `e = 1`: `3x − 1`, que tiene ciclos;
* `e = 0`: `3x − 3`, con el punto fijo `3`.

**Resultado:** en `𝒯₁` y en `𝒯₀` *ninguna* regla se puede eliminar: para cada regla `ρ` hay
una derivación cíclica que usa `ρ`, así que `SN(ρ/𝒯ₑ)` es falso (`not_relSN_d1`, `not_relSN_d0`).
Los ciclos (315 y 392 pasos) los generó `scripts/neighbors.py` y los chequea el kernel.

Consecuencia: un certificado de `SN(ρ/𝒯)` en un álgebra monótona ordenada no puede orientar a
la vez `𝒯` y `t◁ → 1◁` (o `t◁ → 0◁`). Eso descarta, por ejemplo, toda interpretación afín de
dimensión 1 sobre `ℝ≥0` (chequeo con z3, `scripts/neighbor_classes.py`; no formalizado acá).
-/

namespace SRS.Neighbor

open SRS

/-- Nombres de las 11 reglas. -/
inductive RName | fR | tR | f0 | f1 | f2 | t0 | t1 | t2 | s0 | s1 | s2
  deriving DecidableEq, Repr

abbrev Lm : Full := .mk .l
abbrev Rm : Full := .mk .r
abbrev F : Full := .sym .f
abbrev Tt : Full := .sym .t
abbrev D0 : Full := .sym .d0
abbrev D1 : Full := .sym .d1
abbrev D2 : Full := .sym .d2

def RName.all : List RName := [.fR, .tR, .f0, .f1, .f2, .t0, .t1, .t2, .s0, .s1, .s2]

theorem RName.mem_all (ρ : RName) : ρ ∈ RName.all := by cases ρ <;> simp [RName.all]

def RName.lhs : RName → List Full
  | .fR => [F, Rm] | .tR => [Tt, Rm]
  | .f0 => [F, D0] | .f1 => [F, D1] | .f2 => [F, D2]
  | .t0 => [Tt, D0] | .t1 => [Tt, D1] | .t2 => [Tt, D2]
  | .s0 => [Lm, D0] | .s1 => [Lm, D1] | .s2 => [Lm, D2]

/-- Lado derecho; `e` es el dígito de la regla dinámica `t◁ → e◁`. -/
def RName.rhs (e : Sym) : RName → List Full
  | .fR => [Rm] | .tR => [.sym e, Rm]
  | .f0 => [D0, F] | .f1 => [D0, Tt] | .f2 => [D1, F]
  | .t0 => [D1, Tt] | .t1 => [D2, F] | .t2 => [D2, Tt]
  | .s0 => [Lm, Tt] | .s1 => [Lm, F, F] | .s2 => [Lm, F, Tt]

/-- Un paso de `𝒯ₑ` con la regla `ρ`, en cualquier posición. -/
inductive NStepN (e : Sym) (ρ : RName) : List Full → List Full → Prop
  | mk (u v : List Full) : NStepN e ρ (u ++ ρ.lhs ++ v) (u ++ ρ.rhs e ++ v)

def NStep (e : Sym) (s s' : List Full) : Prop := ∃ ρ, NStepN e ρ s s'

/-- Para `e = 2` la familia da exactamente el sistema `𝒯` de `AllWords.lean`. -/
theorem nstep_d2_iff {s s' : List Full} : NStep .d2 s s' ↔ WStep s s' := by
  constructor
  · rintro ⟨ρ, ⟨u, v⟩⟩
    cases ρ <;> simp only [RName.lhs, RName.rhs, List.append_assoc, List.cons_append,
      List.nil_append]
    · simpa using WStep.mk u v .endF
    · simpa using WStep.mk u v .endT
    · simpa using WStep.mk u v (.aux .f0)
    · simpa using WStep.mk u v (.aux .f1)
    · simpa using WStep.mk u v (.aux .f2)
    · simpa using WStep.mk u v (.aux .t0)
    · simpa using WStep.mk u v (.aux .t1)
    · simpa using WStep.mk u v (.aux .t2)
    · simpa using WStep.mk u v (.start .s0)
    · simpa using WStep.mk u v (.start .s1)
    · simpa using WStep.mk u v (.start .s2)
  · rintro ⟨u, v, h⟩
    have key : ∀ ρ : RName, NStepN .d2 ρ (u ++ ρ.lhs ++ v) (u ++ ρ.rhs .d2 ++ v) :=
      fun ρ => NStepN.mk u v
    cases h with
    | endF => exact ⟨.fR, by simpa [RName.lhs, RName.rhs] using key .fR⟩
    | endT => exact ⟨.tR, by simpa [RName.lhs, RName.rhs] using key .tR⟩
    | aux h =>
      cases h
      · exact ⟨.f0, by simpa [RName.lhs, RName.rhs] using key .f0⟩
      · exact ⟨.f1, by simpa [RName.lhs, RName.rhs] using key .f1⟩
      · exact ⟨.f2, by simpa [RName.lhs, RName.rhs] using key .f2⟩
      · exact ⟨.t0, by simpa [RName.lhs, RName.rhs] using key .t0⟩
      · exact ⟨.t1, by simpa [RName.lhs, RName.rhs] using key .t1⟩
      · exact ⟨.t2, by simpa [RName.lhs, RName.rhs] using key .t2⟩
    | start h =>
      cases h
      · exact ⟨.s0, by simpa [RName.lhs, RName.rhs] using key .s0⟩
      · exact ⟨.s1, by simpa [RName.lhs, RName.rhs] using key .s1⟩
      · exact ⟨.s2, by simpa [RName.lhs, RName.rhs] using key .s2⟩

/-- Terminación relativa: un paso con `ρ` rodeado de pasos cualesquiera de `𝒯ₑ`.
`SN(ρ/𝒯ₑ)` es que esta relación esté bien fundada. -/
def RelStep (e : Sym) (ρ : RName) (s s' : List Full) : Prop :=
  ∃ s₁ s₂, Relation.ReflTransGen (NStep e) s s₁ ∧ NStepN e ρ s₁ s₂ ∧
    Relation.ReflTransGen (NStep e) s₂ s'

/-! ## Chequeador de derivaciones -/

def splits : List Full → List (List Full × List Full)
  | [] => [([], [])]
  | a :: s => ([], a :: s) :: (splits s).map (fun p => (a :: p.1, p.2))

theorem append_of_mem_splits : ∀ {s u w : List Full}, (u, w) ∈ splits s → u ++ w = s
  | [], u, w, h => by simp [splits] at h; simp [h.1, h.2]
  | a :: s, u, w, h => by
      simp only [splits, List.mem_cons, Prod.mk.injEq, List.mem_map, Prod.exists] at h
      rcases h with ⟨rfl, rfl⟩ | ⟨u', w', hm, rfl, rfl⟩
      · rfl
      · simp [append_of_mem_splits hm]

/-- ¿Es `t` el resultado de aplicar `ρ` a `s` en alguna posición? -/
def isStep (e : Sym) (ρ : RName) (s t : List Full) : Bool :=
  (splits s).any fun p => ρ.lhs.isPrefixOf p.2 && t == p.1 ++ ρ.rhs e ++ p.2.drop ρ.lhs.length

theorem isStep_sound {e : Sym} {ρ : RName} {s t : List Full} (h : isStep e ρ s t = true) :
    NStepN e ρ s t := by
  simp only [isStep, List.any_eq_true, Bool.and_eq_true, beq_iff_eq, Prod.exists] at h
  obtain ⟨u, w, hm, hp, rfl⟩ := h
  rw [← append_of_mem_splits hm]
  obtain ⟨v, rfl⟩ : ∃ v, w = ρ.lhs ++ v :=
    ⟨_, (List.prefix_iff_eq_append.mp (List.isPrefixOf_iff_prefix.mp hp)).symm⟩
  simpa using NStepN.mk (e := e) (ρ := ρ) u v

/-- Chequea una derivación `s → s₁ → … → sₙ` dada como lista de (regla, palabra). -/
def checkWalk (e : Sym) : List Full → List (RName × List Full) → Bool
  | _, [] => true
  | s, (ρ, t) :: w => isStep e ρ s t && checkWalk e t w

def last : List Full → List (RName × List Full) → List Full
  | s, [] => s
  | _, (_, t) :: w => last t w

theorem checkWalk_rtg {e : Sym} : ∀ {s : List Full} {w : List (RName × List Full)},
    checkWalk e s w = true → Relation.ReflTransGen (NStep e) s (last s w)
  | _, [], _ => .refl
  | _, (ρ, t) :: w, h => by
      simp only [checkWalk, Bool.and_eq_true] at h
      exact .head ⟨ρ, isStep_sound h.1⟩ (checkWalk_rtg h.2)

theorem checkWalk_rel {e : Sym} {ρ : RName} : ∀ {s : List Full} {w : List (RName × List Full)},
    checkWalk e s w = true → ρ ∈ w.map Prod.fst → RelStep e ρ s (last s w)
  | _, [], _, hm => by simp at hm
  | s, (ρ', t) :: w, h, hm => by
      simp only [checkWalk, Bool.and_eq_true] at h
      simp only [List.map_cons, List.mem_cons] at hm
      rcases hm with rfl | hm
      · exact ⟨s, t, .refl, isStep_sound h.1, checkWalk_rtg h.2⟩
      · obtain ⟨s₁, s₂, h₁, h₂, h₃⟩ := checkWalk_rel h.2 hm
        exact ⟨s₁, s₂, .head ⟨ρ', isStep_sound h.1⟩ h₁, h₂, h₃⟩

/-- Un ciclo que pasa por `ρ` impide `SN(ρ/𝒯ₑ)`. -/
theorem not_acc_of_cycle {e : Sym} {ρ : RName} {s : List Full} {w : List (RName × List Full)}
    (hc : checkWalk e s w = true) (hl : last s w = s) (hm : ρ ∈ w.map Prod.fst) :
    ¬ Acc (fun y x => RelStep e ρ x y) s := by
  have hr := checkWalk_rel hc hm
  rw [hl] at hr
  suffices ∀ x, Acc (fun y x => RelStep e ρ x y) x → ¬ RelStep e ρ x x from fun h => this s h hr
  intro x hx
  induction hx with
  | intro x _ ih => exact fun hxx => ih x hxx hxx

/-! ## Los ciclos -/

/-- Derivación cíclica de 315 pasos desde `<22>` en el vecino `t◁ → 1◁`. -/
def start_d1 : List Full := [Lm, D2, D2, Rm]

def walk_d1 : List (RName × List Full) := [
  (.s2, [Lm, F, Tt, D2, Rm]),
  (.t2, [Lm, F, D2, Tt, Rm]),
  (.tR, [Lm, F, D2, D1, Rm]),
  (.f2, [Lm, D1, F, D1, Rm]),
  (.f1, [Lm, D1, D0, Tt, Rm]),
  (.tR, [Lm, D1, D0, D1, Rm]),
  (.s1, [Lm, F, F, D0, D1, Rm]),
  (.f0, [Lm, F, D0, F, D1, Rm]),
  (.f0, [Lm, D0, F, F, D1, Rm]),
  (.f1, [Lm, D0, F, D0, Tt, Rm]),
  (.tR, [Lm, D0, F, D0, D1, Rm]),
  (.f0, [Lm, D0, D0, F, D1, Rm]),
  (.f1, [Lm, D0, D0, D0, Tt, Rm]),
  (.tR, [Lm, D0, D0, D0, D1, Rm]),
  (.s0, [Lm, Tt, D0, D0, D1, Rm]),
  (.t0, [Lm, D1, Tt, D0, D1, Rm]),
  (.t0, [Lm, D1, D1, Tt, D1, Rm]),
  (.t1, [Lm, D1, D1, D2, F, Rm]),
  (.fR, [Lm, D1, D1, D2, Rm]),
  (.s1, [Lm, F, F, D1, D2, Rm]),
  (.f1, [Lm, F, D0, Tt, D2, Rm]),
  (.f0, [Lm, D0, F, Tt, D2, Rm]),
  (.t2, [Lm, D0, F, D2, Tt, Rm]),
  (.tR, [Lm, D0, F, D2, D1, Rm]),
  (.f2, [Lm, D0, D1, F, D1, Rm]),
  (.f1, [Lm, D0, D1, D0, Tt, Rm]),
  (.tR, [Lm, D0, D1, D0, D1, Rm]),
  (.s0, [Lm, Tt, D1, D0, D1, Rm]),
  (.t1, [Lm, D2, F, D0, D1, Rm]),
  (.f0, [Lm, D2, D0, F, D1, Rm]),
  (.f1, [Lm, D2, D0, D0, Tt, Rm]),
  (.tR, [Lm, D2, D0, D0, D1, Rm]),
  (.s2, [Lm, F, Tt, D0, D0, D1, Rm]),
  (.t0, [Lm, F, D1, Tt, D0, D1, Rm]),
  (.f1, [Lm, D0, Tt, Tt, D0, D1, Rm]),
  (.t0, [Lm, D0, Tt, D1, Tt, D1, Rm]),
  (.t1, [Lm, D0, D2, F, Tt, D1, Rm]),
  (.t1, [Lm, D0, D2, F, D2, F, Rm]),
  (.fR, [Lm, D0, D2, F, D2, Rm]),
  (.f2, [Lm, D0, D2, D1, F, Rm]),
  (.fR, [Lm, D0, D2, D1, Rm]),
  (.s0, [Lm, Tt, D2, D1, Rm]),
  (.t2, [Lm, D2, Tt, D1, Rm]),
  (.t1, [Lm, D2, D2, F, Rm]),
  (.fR, [Lm, D2, D2, Rm]),
  (.s2, [Lm, F, Tt, D2, Rm]),
  (.t2, [Lm, F, D2, Tt, Rm]),
  (.tR, [Lm, F, D2, D1, Rm]),
  (.f2, [Lm, D1, F, D1, Rm]),
  (.f1, [Lm, D1, D0, Tt, Rm]),
  (.s1, [Lm, F, F, D0, Tt, Rm]),
  (.f0, [Lm, F, D0, F, Tt, Rm]),
  (.tR, [Lm, F, D0, F, D1, Rm]),
  (.f0, [Lm, D0, F, F, D1, Rm]),
  (.f1, [Lm, D0, F, D0, Tt, Rm]),
  (.tR, [Lm, D0, F, D0, D1, Rm]),
  (.f0, [Lm, D0, D0, F, D1, Rm]),
  (.f1, [Lm, D0, D0, D0, Tt, Rm]),
  (.tR, [Lm, D0, D0, D0, D1, Rm]),
  (.s0, [Lm, Tt, D0, D0, D1, Rm]),
  (.t0, [Lm, D1, Tt, D0, D1, Rm]),
  (.t0, [Lm, D1, D1, Tt, D1, Rm]),
  (.t1, [Lm, D1, D1, D2, F, Rm]),
  (.fR, [Lm, D1, D1, D2, Rm]),
  (.s1, [Lm, F, F, D1, D2, Rm]),
  (.f1, [Lm, F, D0, Tt, D2, Rm]),
  (.f0, [Lm, D0, F, Tt, D2, Rm]),
  (.t2, [Lm, D0, F, D2, Tt, Rm]),
  (.tR, [Lm, D0, F, D2, D1, Rm]),
  (.f2, [Lm, D0, D1, F, D1, Rm]),
  (.f1, [Lm, D0, D1, D0, Tt, Rm]),
  (.tR, [Lm, D0, D1, D0, D1, Rm]),
  (.s0, [Lm, Tt, D1, D0, D1, Rm]),
  (.t1, [Lm, D2, F, D0, D1, Rm]),
  (.f0, [Lm, D2, D0, F, D1, Rm]),
  (.f1, [Lm, D2, D0, D0, Tt, Rm]),
  (.tR, [Lm, D2, D0, D0, D1, Rm]),
  (.s2, [Lm, F, Tt, D0, D0, D1, Rm]),
  (.t0, [Lm, F, D1, Tt, D0, D1, Rm]),
  (.f1, [Lm, D0, Tt, Tt, D0, D1, Rm]),
  (.t0, [Lm, D0, Tt, D1, Tt, D1, Rm]),
  (.t1, [Lm, D0, D2, F, Tt, D1, Rm]),
  (.t1, [Lm, D0, D2, F, D2, F, Rm]),
  (.fR, [Lm, D0, D2, F, D2, Rm]),
  (.f2, [Lm, D0, D2, D1, F, Rm]),
  (.fR, [Lm, D0, D2, D1, Rm]),
  (.s0, [Lm, Tt, D2, D1, Rm]),
  (.t2, [Lm, D2, Tt, D1, Rm]),
  (.t1, [Lm, D2, D2, F, Rm]),
  (.fR, [Lm, D2, D2, Rm]),
  (.s2, [Lm, F, Tt, D2, Rm]),
  (.t2, [Lm, F, D2, Tt, Rm]),
  (.tR, [Lm, F, D2, D1, Rm]),
  (.f2, [Lm, D1, F, D1, Rm]),
  (.f1, [Lm, D1, D0, Tt, Rm]),
  (.tR, [Lm, D1, D0, D1, Rm]),
  (.s1, [Lm, F, F, D0, D1, Rm]),
  (.f0, [Lm, F, D0, F, D1, Rm]),
  (.f0, [Lm, D0, F, F, D1, Rm]),
  (.f1, [Lm, D0, F, D0, Tt, Rm]),
  (.tR, [Lm, D0, F, D0, D1, Rm]),
  (.f0, [Lm, D0, D0, F, D1, Rm]),
  (.f1, [Lm, D0, D0, D0, Tt, Rm]),
  (.tR, [Lm, D0, D0, D0, D1, Rm]),
  (.s0, [Lm, Tt, D0, D0, D1, Rm]),
  (.t0, [Lm, D1, Tt, D0, D1, Rm]),
  (.t0, [Lm, D1, D1, Tt, D1, Rm]),
  (.t1, [Lm, D1, D1, D2, F, Rm]),
  (.fR, [Lm, D1, D1, D2, Rm]),
  (.s1, [Lm, F, F, D1, D2, Rm]),
  (.f1, [Lm, F, D0, Tt, D2, Rm]),
  (.f0, [Lm, D0, F, Tt, D2, Rm]),
  (.t2, [Lm, D0, F, D2, Tt, Rm]),
  (.tR, [Lm, D0, F, D2, D1, Rm]),
  (.f2, [Lm, D0, D1, F, D1, Rm]),
  (.f1, [Lm, D0, D1, D0, Tt, Rm]),
  (.tR, [Lm, D0, D1, D0, D1, Rm]),
  (.s0, [Lm, Tt, D1, D0, D1, Rm]),
  (.t1, [Lm, D2, F, D0, D1, Rm]),
  (.f0, [Lm, D2, D0, F, D1, Rm]),
  (.f1, [Lm, D2, D0, D0, Tt, Rm]),
  (.tR, [Lm, D2, D0, D0, D1, Rm]),
  (.s2, [Lm, F, Tt, D0, D0, D1, Rm]),
  (.t0, [Lm, F, D1, Tt, D0, D1, Rm]),
  (.f1, [Lm, D0, Tt, Tt, D0, D1, Rm]),
  (.t0, [Lm, D0, Tt, D1, Tt, D1, Rm]),
  (.t1, [Lm, D0, D2, F, Tt, D1, Rm]),
  (.t1, [Lm, D0, D2, F, D2, F, Rm]),
  (.fR, [Lm, D0, D2, F, D2, Rm]),
  (.f2, [Lm, D0, D2, D1, F, Rm]),
  (.fR, [Lm, D0, D2, D1, Rm]),
  (.s0, [Lm, Tt, D2, D1, Rm]),
  (.t2, [Lm, D2, Tt, D1, Rm]),
  (.t1, [Lm, D2, D2, F, Rm]),
  (.fR, [Lm, D2, D2, Rm]),
  (.s2, [Lm, F, Tt, D2, Rm]),
  (.t2, [Lm, F, D2, Tt, Rm]),
  (.f2, [Lm, D1, F, Tt, Rm]),
  (.tR, [Lm, D1, F, D1, Rm]),
  (.f1, [Lm, D1, D0, Tt, Rm]),
  (.tR, [Lm, D1, D0, D1, Rm]),
  (.s1, [Lm, F, F, D0, D1, Rm]),
  (.f0, [Lm, F, D0, F, D1, Rm]),
  (.f0, [Lm, D0, F, F, D1, Rm]),
  (.f1, [Lm, D0, F, D0, Tt, Rm]),
  (.f0, [Lm, D0, D0, F, Tt, Rm]),
  (.s0, [Lm, Tt, D0, F, Tt, Rm]),
  (.t0, [Lm, D1, Tt, F, Tt, Rm]),
  (.tR, [Lm, D1, Tt, F, D1, Rm]),
  (.f1, [Lm, D1, Tt, D0, Tt, Rm]),
  (.tR, [Lm, D1, Tt, D0, D1, Rm]),
  (.t0, [Lm, D1, D1, Tt, D1, Rm]),
  (.t1, [Lm, D1, D1, D2, F, Rm]),
  (.fR, [Lm, D1, D1, D2, Rm]),
  (.s1, [Lm, F, F, D1, D2, Rm]),
  (.f1, [Lm, F, D0, Tt, D2, Rm]),
  (.f0, [Lm, D0, F, Tt, D2, Rm]),
  (.t2, [Lm, D0, F, D2, Tt, Rm]),
  (.tR, [Lm, D0, F, D2, D1, Rm]),
  (.f2, [Lm, D0, D1, F, D1, Rm]),
  (.f1, [Lm, D0, D1, D0, Tt, Rm]),
  (.tR, [Lm, D0, D1, D0, D1, Rm]),
  (.s0, [Lm, Tt, D1, D0, D1, Rm]),
  (.t1, [Lm, D2, F, D0, D1, Rm]),
  (.f0, [Lm, D2, D0, F, D1, Rm]),
  (.f1, [Lm, D2, D0, D0, Tt, Rm]),
  (.tR, [Lm, D2, D0, D0, D1, Rm]),
  (.s2, [Lm, F, Tt, D0, D0, D1, Rm]),
  (.t0, [Lm, F, D1, Tt, D0, D1, Rm]),
  (.f1, [Lm, D0, Tt, Tt, D0, D1, Rm]),
  (.t0, [Lm, D0, Tt, D1, Tt, D1, Rm]),
  (.t1, [Lm, D0, D2, F, Tt, D1, Rm]),
  (.t1, [Lm, D0, D2, F, D2, F, Rm]),
  (.fR, [Lm, D0, D2, F, D2, Rm]),
  (.f2, [Lm, D0, D2, D1, F, Rm]),
  (.fR, [Lm, D0, D2, D1, Rm]),
  (.s0, [Lm, Tt, D2, D1, Rm]),
  (.t2, [Lm, D2, Tt, D1, Rm]),
  (.t1, [Lm, D2, D2, F, Rm]),
  (.fR, [Lm, D2, D2, Rm]),
  (.s2, [Lm, F, Tt, D2, Rm]),
  (.t2, [Lm, F, D2, Tt, Rm]),
  (.tR, [Lm, F, D2, D1, Rm]),
  (.f2, [Lm, D1, F, D1, Rm]),
  (.f1, [Lm, D1, D0, Tt, Rm]),
  (.tR, [Lm, D1, D0, D1, Rm]),
  (.s1, [Lm, F, F, D0, D1, Rm]),
  (.f0, [Lm, F, D0, F, D1, Rm]),
  (.f0, [Lm, D0, F, F, D1, Rm]),
  (.f1, [Lm, D0, F, D0, Tt, Rm]),
  (.tR, [Lm, D0, F, D0, D1, Rm]),
  (.f0, [Lm, D0, D0, F, D1, Rm]),
  (.f1, [Lm, D0, D0, D0, Tt, Rm]),
  (.tR, [Lm, D0, D0, D0, D1, Rm]),
  (.s0, [Lm, Tt, D0, D0, D1, Rm]),
  (.t0, [Lm, D1, Tt, D0, D1, Rm]),
  (.t0, [Lm, D1, D1, Tt, D1, Rm]),
  (.t1, [Lm, D1, D1, D2, F, Rm]),
  (.fR, [Lm, D1, D1, D2, Rm]),
  (.s1, [Lm, F, F, D1, D2, Rm]),
  (.f1, [Lm, F, D0, Tt, D2, Rm]),
  (.f0, [Lm, D0, F, Tt, D2, Rm]),
  (.t2, [Lm, D0, F, D2, Tt, Rm]),
  (.tR, [Lm, D0, F, D2, D1, Rm]),
  (.f2, [Lm, D0, D1, F, D1, Rm]),
  (.f1, [Lm, D0, D1, D0, Tt, Rm]),
  (.tR, [Lm, D0, D1, D0, D1, Rm]),
  (.s0, [Lm, Tt, D1, D0, D1, Rm]),
  (.t1, [Lm, D2, F, D0, D1, Rm]),
  (.f0, [Lm, D2, D0, F, D1, Rm]),
  (.f1, [Lm, D2, D0, D0, Tt, Rm]),
  (.tR, [Lm, D2, D0, D0, D1, Rm]),
  (.s2, [Lm, F, Tt, D0, D0, D1, Rm]),
  (.t0, [Lm, F, D1, Tt, D0, D1, Rm]),
  (.f1, [Lm, D0, Tt, Tt, D0, D1, Rm]),
  (.t0, [Lm, D0, Tt, D1, Tt, D1, Rm]),
  (.t1, [Lm, D0, D2, F, Tt, D1, Rm]),
  (.t1, [Lm, D0, D2, F, D2, F, Rm]),
  (.fR, [Lm, D0, D2, F, D2, Rm]),
  (.f2, [Lm, D0, D2, D1, F, Rm]),
  (.fR, [Lm, D0, D2, D1, Rm]),
  (.s0, [Lm, Tt, D2, D1, Rm]),
  (.t2, [Lm, D2, Tt, D1, Rm]),
  (.t1, [Lm, D2, D2, F, Rm]),
  (.fR, [Lm, D2, D2, Rm]),
  (.s2, [Lm, F, Tt, D2, Rm]),
  (.t2, [Lm, F, D2, Tt, Rm]),
  (.f2, [Lm, D1, F, Tt, Rm]),
  (.s1, [Lm, F, F, F, Tt, Rm]),
  (.tR, [Lm, F, F, F, D1, Rm]),
  (.f1, [Lm, F, F, D0, Tt, Rm]),
  (.tR, [Lm, F, F, D0, D1, Rm]),
  (.f0, [Lm, F, D0, F, D1, Rm]),
  (.f0, [Lm, D0, F, F, D1, Rm]),
  (.f1, [Lm, D0, F, D0, Tt, Rm]),
  (.tR, [Lm, D0, F, D0, D1, Rm]),
  (.f0, [Lm, D0, D0, F, D1, Rm]),
  (.f1, [Lm, D0, D0, D0, Tt, Rm]),
  (.tR, [Lm, D0, D0, D0, D1, Rm]),
  (.s0, [Lm, Tt, D0, D0, D1, Rm]),
  (.t0, [Lm, D1, Tt, D0, D1, Rm]),
  (.t0, [Lm, D1, D1, Tt, D1, Rm]),
  (.t1, [Lm, D1, D1, D2, F, Rm]),
  (.fR, [Lm, D1, D1, D2, Rm]),
  (.s1, [Lm, F, F, D1, D2, Rm]),
  (.f1, [Lm, F, D0, Tt, D2, Rm]),
  (.f0, [Lm, D0, F, Tt, D2, Rm]),
  (.t2, [Lm, D0, F, D2, Tt, Rm]),
  (.tR, [Lm, D0, F, D2, D1, Rm]),
  (.f2, [Lm, D0, D1, F, D1, Rm]),
  (.f1, [Lm, D0, D1, D0, Tt, Rm]),
  (.tR, [Lm, D0, D1, D0, D1, Rm]),
  (.s0, [Lm, Tt, D1, D0, D1, Rm]),
  (.t1, [Lm, D2, F, D0, D1, Rm]),
  (.f0, [Lm, D2, D0, F, D1, Rm]),
  (.f1, [Lm, D2, D0, D0, Tt, Rm]),
  (.tR, [Lm, D2, D0, D0, D1, Rm]),
  (.s2, [Lm, F, Tt, D0, D0, D1, Rm]),
  (.t0, [Lm, F, D1, Tt, D0, D1, Rm]),
  (.f1, [Lm, D0, Tt, Tt, D0, D1, Rm]),
  (.t0, [Lm, D0, Tt, D1, Tt, D1, Rm]),
  (.t1, [Lm, D0, D2, F, Tt, D1, Rm]),
  (.t1, [Lm, D0, D2, F, D2, F, Rm]),
  (.fR, [Lm, D0, D2, F, D2, Rm]),
  (.f2, [Lm, D0, D2, D1, F, Rm]),
  (.fR, [Lm, D0, D2, D1, Rm]),
  (.s0, [Lm, Tt, D2, D1, Rm]),
  (.t2, [Lm, D2, Tt, D1, Rm]),
  (.t1, [Lm, D2, D2, F, Rm]),
  (.fR, [Lm, D2, D2, Rm]),
  (.s2, [Lm, F, Tt, D2, Rm]),
  (.t2, [Lm, F, D2, Tt, Rm]),
  (.tR, [Lm, F, D2, D1, Rm]),
  (.f2, [Lm, D1, F, D1, Rm]),
  (.f1, [Lm, D1, D0, Tt, Rm]),
  (.tR, [Lm, D1, D0, D1, Rm]),
  (.s1, [Lm, F, F, D0, D1, Rm]),
  (.f0, [Lm, F, D0, F, D1, Rm]),
  (.f0, [Lm, D0, F, F, D1, Rm]),
  (.f1, [Lm, D0, F, D0, Tt, Rm]),
  (.tR, [Lm, D0, F, D0, D1, Rm]),
  (.f0, [Lm, D0, D0, F, D1, Rm]),
  (.f1, [Lm, D0, D0, D0, Tt, Rm]),
  (.tR, [Lm, D0, D0, D0, D1, Rm]),
  (.s0, [Lm, Tt, D0, D0, D1, Rm]),
  (.t0, [Lm, D1, Tt, D0, D1, Rm]),
  (.t0, [Lm, D1, D1, Tt, D1, Rm]),
  (.t1, [Lm, D1, D1, D2, F, Rm]),
  (.fR, [Lm, D1, D1, D2, Rm]),
  (.s1, [Lm, F, F, D1, D2, Rm]),
  (.f1, [Lm, F, D0, Tt, D2, Rm]),
  (.f0, [Lm, D0, F, Tt, D2, Rm]),
  (.t2, [Lm, D0, F, D2, Tt, Rm]),
  (.tR, [Lm, D0, F, D2, D1, Rm]),
  (.f2, [Lm, D0, D1, F, D1, Rm]),
  (.f1, [Lm, D0, D1, D0, Tt, Rm]),
  (.tR, [Lm, D0, D1, D0, D1, Rm]),
  (.s0, [Lm, Tt, D1, D0, D1, Rm]),
  (.t1, [Lm, D2, F, D0, D1, Rm]),
  (.f0, [Lm, D2, D0, F, D1, Rm]),
  (.f1, [Lm, D2, D0, D0, Tt, Rm]),
  (.tR, [Lm, D2, D0, D0, D1, Rm]),
  (.s2, [Lm, F, Tt, D0, D0, D1, Rm]),
  (.t0, [Lm, F, D1, Tt, D0, D1, Rm]),
  (.f1, [Lm, D0, Tt, Tt, D0, D1, Rm]),
  (.t0, [Lm, D0, Tt, D1, Tt, D1, Rm]),
  (.t1, [Lm, D0, D2, F, Tt, D1, Rm]),
  (.t1, [Lm, D0, D2, F, D2, F, Rm]),
  (.fR, [Lm, D0, D2, F, D2, Rm]),
  (.f2, [Lm, D0, D2, D1, F, Rm]),
  (.fR, [Lm, D0, D2, D1, Rm]),
  (.s0, [Lm, Tt, D2, D1, Rm]),
  (.t2, [Lm, D2, Tt, D1, Rm]),
  (.t1, [Lm, D2, D2, F, Rm]),
  (.fR, [Lm, D2, D2, Rm])]
/-- Derivación cíclica de 392 pasos desde `<220>` en el vecino `t◁ → 0◁`. -/
def start_d0 : List Full := [Lm, D2, D2, D0, Rm]

def walk_d0 : List (RName × List Full) := [
  (.s2, [Lm, F, Tt, D2, D0, Rm]),
  (.t2, [Lm, F, D2, Tt, D0, Rm]),
  (.f2, [Lm, D1, F, Tt, D0, Rm]),
  (.t0, [Lm, D1, F, D1, Tt, Rm]),
  (.tR, [Lm, D1, F, D1, D0, Rm]),
  (.f1, [Lm, D1, D0, Tt, D0, Rm]),
  (.t0, [Lm, D1, D0, D1, Tt, Rm]),
  (.tR, [Lm, D1, D0, D1, D0, Rm]),
  (.s1, [Lm, F, F, D0, D1, D0, Rm]),
  (.f0, [Lm, F, D0, F, D1, D0, Rm]),
  (.f0, [Lm, D0, F, F, D1, D0, Rm]),
  (.f1, [Lm, D0, F, D0, Tt, D0, Rm]),
  (.f0, [Lm, D0, D0, F, Tt, D0, Rm]),
  (.t0, [Lm, D0, D0, F, D1, Tt, Rm]),
  (.tR, [Lm, D0, D0, F, D1, D0, Rm]),
  (.f1, [Lm, D0, D0, D0, Tt, D0, Rm]),
  (.t0, [Lm, D0, D0, D0, D1, Tt, Rm]),
  (.tR, [Lm, D0, D0, D0, D1, D0, Rm]),
  (.s0, [Lm, Tt, D0, D0, D1, D0, Rm]),
  (.t0, [Lm, D1, Tt, D0, D1, D0, Rm]),
  (.t0, [Lm, D1, D1, Tt, D1, D0, Rm]),
  (.t1, [Lm, D1, D1, D2, F, D0, Rm]),
  (.f0, [Lm, D1, D1, D2, D0, F, Rm]),
  (.fR, [Lm, D1, D1, D2, D0, Rm]),
  (.s1, [Lm, F, F, D1, D2, D0, Rm]),
  (.f1, [Lm, F, D0, Tt, D2, D0, Rm]),
  (.f0, [Lm, D0, F, Tt, D2, D0, Rm]),
  (.t2, [Lm, D0, F, D2, Tt, D0, Rm]),
  (.f2, [Lm, D0, D1, F, Tt, D0, Rm]),
  (.t0, [Lm, D0, D1, F, D1, Tt, Rm]),
  (.tR, [Lm, D0, D1, F, D1, D0, Rm]),
  (.f1, [Lm, D0, D1, D0, Tt, D0, Rm]),
  (.t0, [Lm, D0, D1, D0, D1, Tt, Rm]),
  (.tR, [Lm, D0, D1, D0, D1, D0, Rm]),
  (.s0, [Lm, Tt, D1, D0, D1, D0, Rm]),
  (.t1, [Lm, D2, F, D0, D1, D0, Rm]),
  (.f0, [Lm, D2, D0, F, D1, D0, Rm]),
  (.f1, [Lm, D2, D0, D0, Tt, D0, Rm]),
  (.t0, [Lm, D2, D0, D0, D1, Tt, Rm]),
  (.tR, [Lm, D2, D0, D0, D1, D0, Rm]),
  (.s2, [Lm, F, Tt, D0, D0, D1, D0, Rm]),
  (.t0, [Lm, F, D1, Tt, D0, D1, D0, Rm]),
  (.f1, [Lm, D0, Tt, Tt, D0, D1, D0, Rm]),
  (.t0, [Lm, D0, Tt, D1, Tt, D1, D0, Rm]),
  (.t1, [Lm, D0, D2, F, Tt, D1, D0, Rm]),
  (.t1, [Lm, D0, D2, F, D2, F, D0, Rm]),
  (.f0, [Lm, D0, D2, F, D2, D0, F, Rm]),
  (.fR, [Lm, D0, D2, F, D2, D0, Rm]),
  (.f2, [Lm, D0, D2, D1, F, D0, Rm]),
  (.f0, [Lm, D0, D2, D1, D0, F, Rm]),
  (.fR, [Lm, D0, D2, D1, D0, Rm]),
  (.s0, [Lm, Tt, D2, D1, D0, Rm]),
  (.t2, [Lm, D2, Tt, D1, D0, Rm]),
  (.t1, [Lm, D2, D2, F, D0, Rm]),
  (.f0, [Lm, D2, D2, D0, F, Rm]),
  (.fR, [Lm, D2, D2, D0, Rm]),
  (.s2, [Lm, F, Tt, D2, D0, Rm]),
  (.t2, [Lm, F, D2, Tt, D0, Rm]),
  (.t0, [Lm, F, D2, D1, Tt, Rm]),
  (.tR, [Lm, F, D2, D1, D0, Rm]),
  (.f2, [Lm, D1, F, D1, D0, Rm]),
  (.f1, [Lm, D1, D0, Tt, D0, Rm]),
  (.t0, [Lm, D1, D0, D1, Tt, Rm]),
  (.tR, [Lm, D1, D0, D1, D0, Rm]),
  (.s1, [Lm, F, F, D0, D1, D0, Rm]),
  (.f0, [Lm, F, D0, F, D1, D0, Rm]),
  (.f0, [Lm, D0, F, F, D1, D0, Rm]),
  (.f1, [Lm, D0, F, D0, Tt, D0, Rm]),
  (.f0, [Lm, D0, D0, F, Tt, D0, Rm]),
  (.t0, [Lm, D0, D0, F, D1, Tt, Rm]),
  (.tR, [Lm, D0, D0, F, D1, D0, Rm]),
  (.f1, [Lm, D0, D0, D0, Tt, D0, Rm]),
  (.t0, [Lm, D0, D0, D0, D1, Tt, Rm]),
  (.tR, [Lm, D0, D0, D0, D1, D0, Rm]),
  (.s0, [Lm, Tt, D0, D0, D1, D0, Rm]),
  (.t0, [Lm, D1, Tt, D0, D1, D0, Rm]),
  (.t0, [Lm, D1, D1, Tt, D1, D0, Rm]),
  (.t1, [Lm, D1, D1, D2, F, D0, Rm]),
  (.f0, [Lm, D1, D1, D2, D0, F, Rm]),
  (.fR, [Lm, D1, D1, D2, D0, Rm]),
  (.s1, [Lm, F, F, D1, D2, D0, Rm]),
  (.f1, [Lm, F, D0, Tt, D2, D0, Rm]),
  (.f0, [Lm, D0, F, Tt, D2, D0, Rm]),
  (.t2, [Lm, D0, F, D2, Tt, D0, Rm]),
  (.f2, [Lm, D0, D1, F, Tt, D0, Rm]),
  (.t0, [Lm, D0, D1, F, D1, Tt, Rm]),
  (.tR, [Lm, D0, D1, F, D1, D0, Rm]),
  (.f1, [Lm, D0, D1, D0, Tt, D0, Rm]),
  (.t0, [Lm, D0, D1, D0, D1, Tt, Rm]),
  (.tR, [Lm, D0, D1, D0, D1, D0, Rm]),
  (.s0, [Lm, Tt, D1, D0, D1, D0, Rm]),
  (.t1, [Lm, D2, F, D0, D1, D0, Rm]),
  (.f0, [Lm, D2, D0, F, D1, D0, Rm]),
  (.f1, [Lm, D2, D0, D0, Tt, D0, Rm]),
  (.t0, [Lm, D2, D0, D0, D1, Tt, Rm]),
  (.tR, [Lm, D2, D0, D0, D1, D0, Rm]),
  (.s2, [Lm, F, Tt, D0, D0, D1, D0, Rm]),
  (.t0, [Lm, F, D1, Tt, D0, D1, D0, Rm]),
  (.f1, [Lm, D0, Tt, Tt, D0, D1, D0, Rm]),
  (.t0, [Lm, D0, Tt, D1, Tt, D1, D0, Rm]),
  (.t1, [Lm, D0, D2, F, Tt, D1, D0, Rm]),
  (.t1, [Lm, D0, D2, F, D2, F, D0, Rm]),
  (.f0, [Lm, D0, D2, F, D2, D0, F, Rm]),
  (.fR, [Lm, D0, D2, F, D2, D0, Rm]),
  (.f2, [Lm, D0, D2, D1, F, D0, Rm]),
  (.f0, [Lm, D0, D2, D1, D0, F, Rm]),
  (.fR, [Lm, D0, D2, D1, D0, Rm]),
  (.s0, [Lm, Tt, D2, D1, D0, Rm]),
  (.t2, [Lm, D2, Tt, D1, D0, Rm]),
  (.t1, [Lm, D2, D2, F, D0, Rm]),
  (.f0, [Lm, D2, D2, D0, F, Rm]),
  (.fR, [Lm, D2, D2, D0, Rm]),
  (.s2, [Lm, F, Tt, D2, D0, Rm]),
  (.t2, [Lm, F, D2, Tt, D0, Rm]),
  (.f2, [Lm, D1, F, Tt, D0, Rm]),
  (.t0, [Lm, D1, F, D1, Tt, Rm]),
  (.f1, [Lm, D1, D0, Tt, Tt, Rm]),
  (.tR, [Lm, D1, D0, Tt, D0, Rm]),
  (.t0, [Lm, D1, D0, D1, Tt, Rm]),
  (.tR, [Lm, D1, D0, D1, D0, Rm]),
  (.s1, [Lm, F, F, D0, D1, D0, Rm]),
  (.f0, [Lm, F, D0, F, D1, D0, Rm]),
  (.f0, [Lm, D0, F, F, D1, D0, Rm]),
  (.f1, [Lm, D0, F, D0, Tt, D0, Rm]),
  (.f0, [Lm, D0, D0, F, Tt, D0, Rm]),
  (.t0, [Lm, D0, D0, F, D1, Tt, Rm]),
  (.tR, [Lm, D0, D0, F, D1, D0, Rm]),
  (.f1, [Lm, D0, D0, D0, Tt, D0, Rm]),
  (.t0, [Lm, D0, D0, D0, D1, Tt, Rm]),
  (.tR, [Lm, D0, D0, D0, D1, D0, Rm]),
  (.s0, [Lm, Tt, D0, D0, D1, D0, Rm]),
  (.t0, [Lm, D1, Tt, D0, D1, D0, Rm]),
  (.t0, [Lm, D1, D1, Tt, D1, D0, Rm]),
  (.t1, [Lm, D1, D1, D2, F, D0, Rm]),
  (.f0, [Lm, D1, D1, D2, D0, F, Rm]),
  (.fR, [Lm, D1, D1, D2, D0, Rm]),
  (.s1, [Lm, F, F, D1, D2, D0, Rm]),
  (.f1, [Lm, F, D0, Tt, D2, D0, Rm]),
  (.f0, [Lm, D0, F, Tt, D2, D0, Rm]),
  (.t2, [Lm, D0, F, D2, Tt, D0, Rm]),
  (.f2, [Lm, D0, D1, F, Tt, D0, Rm]),
  (.t0, [Lm, D0, D1, F, D1, Tt, Rm]),
  (.tR, [Lm, D0, D1, F, D1, D0, Rm]),
  (.f1, [Lm, D0, D1, D0, Tt, D0, Rm]),
  (.t0, [Lm, D0, D1, D0, D1, Tt, Rm]),
  (.tR, [Lm, D0, D1, D0, D1, D0, Rm]),
  (.s0, [Lm, Tt, D1, D0, D1, D0, Rm]),
  (.t1, [Lm, D2, F, D0, D1, D0, Rm]),
  (.f0, [Lm, D2, D0, F, D1, D0, Rm]),
  (.f1, [Lm, D2, D0, D0, Tt, D0, Rm]),
  (.t0, [Lm, D2, D0, D0, D1, Tt, Rm]),
  (.tR, [Lm, D2, D0, D0, D1, D0, Rm]),
  (.s2, [Lm, F, Tt, D0, D0, D1, D0, Rm]),
  (.t0, [Lm, F, D1, Tt, D0, D1, D0, Rm]),
  (.f1, [Lm, D0, Tt, Tt, D0, D1, D0, Rm]),
  (.t0, [Lm, D0, Tt, D1, Tt, D1, D0, Rm]),
  (.t1, [Lm, D0, D2, F, Tt, D1, D0, Rm]),
  (.t1, [Lm, D0, D2, F, D2, F, D0, Rm]),
  (.f0, [Lm, D0, D2, F, D2, D0, F, Rm]),
  (.fR, [Lm, D0, D2, F, D2, D0, Rm]),
  (.f2, [Lm, D0, D2, D1, F, D0, Rm]),
  (.f0, [Lm, D0, D2, D1, D0, F, Rm]),
  (.fR, [Lm, D0, D2, D1, D0, Rm]),
  (.s0, [Lm, Tt, D2, D1, D0, Rm]),
  (.t2, [Lm, D2, Tt, D1, D0, Rm]),
  (.t1, [Lm, D2, D2, F, D0, Rm]),
  (.f0, [Lm, D2, D2, D0, F, Rm]),
  (.fR, [Lm, D2, D2, D0, Rm]),
  (.s2, [Lm, F, Tt, D2, D0, Rm]),
  (.t2, [Lm, F, D2, Tt, D0, Rm]),
  (.f2, [Lm, D1, F, Tt, D0, Rm]),
  (.t0, [Lm, D1, F, D1, Tt, Rm]),
  (.tR, [Lm, D1, F, D1, D0, Rm]),
  (.f1, [Lm, D1, D0, Tt, D0, Rm]),
  (.t0, [Lm, D1, D0, D1, Tt, Rm]),
  (.tR, [Lm, D1, D0, D1, D0, Rm]),
  (.s1, [Lm, F, F, D0, D1, D0, Rm]),
  (.f0, [Lm, F, D0, F, D1, D0, Rm]),
  (.f0, [Lm, D0, F, F, D1, D0, Rm]),
  (.f1, [Lm, D0, F, D0, Tt, D0, Rm]),
  (.f0, [Lm, D0, D0, F, Tt, D0, Rm]),
  (.t0, [Lm, D0, D0, F, D1, Tt, Rm]),
  (.tR, [Lm, D0, D0, F, D1, D0, Rm]),
  (.f1, [Lm, D0, D0, D0, Tt, D0, Rm]),
  (.t0, [Lm, D0, D0, D0, D1, Tt, Rm]),
  (.tR, [Lm, D0, D0, D0, D1, D0, Rm]),
  (.s0, [Lm, Tt, D0, D0, D1, D0, Rm]),
  (.t0, [Lm, D1, Tt, D0, D1, D0, Rm]),
  (.t0, [Lm, D1, D1, Tt, D1, D0, Rm]),
  (.t1, [Lm, D1, D1, D2, F, D0, Rm]),
  (.f0, [Lm, D1, D1, D2, D0, F, Rm]),
  (.fR, [Lm, D1, D1, D2, D0, Rm]),
  (.s1, [Lm, F, F, D1, D2, D0, Rm]),
  (.f1, [Lm, F, D0, Tt, D2, D0, Rm]),
  (.f0, [Lm, D0, F, Tt, D2, D0, Rm]),
  (.t2, [Lm, D0, F, D2, Tt, D0, Rm]),
  (.f2, [Lm, D0, D1, F, Tt, D0, Rm]),
  (.t0, [Lm, D0, D1, F, D1, Tt, Rm]),
  (.tR, [Lm, D0, D1, F, D1, D0, Rm]),
  (.f1, [Lm, D0, D1, D0, Tt, D0, Rm]),
  (.t0, [Lm, D0, D1, D0, D1, Tt, Rm]),
  (.tR, [Lm, D0, D1, D0, D1, D0, Rm]),
  (.s0, [Lm, Tt, D1, D0, D1, D0, Rm]),
  (.t1, [Lm, D2, F, D0, D1, D0, Rm]),
  (.f0, [Lm, D2, D0, F, D1, D0, Rm]),
  (.f1, [Lm, D2, D0, D0, Tt, D0, Rm]),
  (.t0, [Lm, D2, D0, D0, D1, Tt, Rm]),
  (.tR, [Lm, D2, D0, D0, D1, D0, Rm]),
  (.s2, [Lm, F, Tt, D0, D0, D1, D0, Rm]),
  (.t0, [Lm, F, D1, Tt, D0, D1, D0, Rm]),
  (.f1, [Lm, D0, Tt, Tt, D0, D1, D0, Rm]),
  (.t0, [Lm, D0, Tt, D1, Tt, D1, D0, Rm]),
  (.t1, [Lm, D0, D2, F, Tt, D1, D0, Rm]),
  (.t1, [Lm, D0, D2, F, D2, F, D0, Rm]),
  (.f0, [Lm, D0, D2, F, D2, D0, F, Rm]),
  (.fR, [Lm, D0, D2, F, D2, D0, Rm]),
  (.f2, [Lm, D0, D2, D1, F, D0, Rm]),
  (.f0, [Lm, D0, D2, D1, D0, F, Rm]),
  (.fR, [Lm, D0, D2, D1, D0, Rm]),
  (.s0, [Lm, Tt, D2, D1, D0, Rm]),
  (.t2, [Lm, D2, Tt, D1, D0, Rm]),
  (.t1, [Lm, D2, D2, F, D0, Rm]),
  (.f0, [Lm, D2, D2, D0, F, Rm]),
  (.fR, [Lm, D2, D2, D0, Rm]),
  (.s2, [Lm, F, Tt, D2, D0, Rm]),
  (.t2, [Lm, F, D2, Tt, D0, Rm]),
  (.f2, [Lm, D1, F, Tt, D0, Rm]),
  (.t0, [Lm, D1, F, D1, Tt, Rm]),
  (.tR, [Lm, D1, F, D1, D0, Rm]),
  (.f1, [Lm, D1, D0, Tt, D0, Rm]),
  (.t0, [Lm, D1, D0, D1, Tt, Rm]),
  (.tR, [Lm, D1, D0, D1, D0, Rm]),
  (.s1, [Lm, F, F, D0, D1, D0, Rm]),
  (.f0, [Lm, F, D0, F, D1, D0, Rm]),
  (.f0, [Lm, D0, F, F, D1, D0, Rm]),
  (.f1, [Lm, D0, F, D0, Tt, D0, Rm]),
  (.f0, [Lm, D0, D0, F, Tt, D0, Rm]),
  (.t0, [Lm, D0, D0, F, D1, Tt, Rm]),
  (.tR, [Lm, D0, D0, F, D1, D0, Rm]),
  (.f1, [Lm, D0, D0, D0, Tt, D0, Rm]),
  (.t0, [Lm, D0, D0, D0, D1, Tt, Rm]),
  (.tR, [Lm, D0, D0, D0, D1, D0, Rm]),
  (.s0, [Lm, Tt, D0, D0, D1, D0, Rm]),
  (.t0, [Lm, D1, Tt, D0, D1, D0, Rm]),
  (.t0, [Lm, D1, D1, Tt, D1, D0, Rm]),
  (.t1, [Lm, D1, D1, D2, F, D0, Rm]),
  (.f0, [Lm, D1, D1, D2, D0, F, Rm]),
  (.fR, [Lm, D1, D1, D2, D0, Rm]),
  (.s1, [Lm, F, F, D1, D2, D0, Rm]),
  (.f1, [Lm, F, D0, Tt, D2, D0, Rm]),
  (.f0, [Lm, D0, F, Tt, D2, D0, Rm]),
  (.t2, [Lm, D0, F, D2, Tt, D0, Rm]),
  (.f2, [Lm, D0, D1, F, Tt, D0, Rm]),
  (.t0, [Lm, D0, D1, F, D1, Tt, Rm]),
  (.tR, [Lm, D0, D1, F, D1, D0, Rm]),
  (.f1, [Lm, D0, D1, D0, Tt, D0, Rm]),
  (.t0, [Lm, D0, D1, D0, D1, Tt, Rm]),
  (.tR, [Lm, D0, D1, D0, D1, D0, Rm]),
  (.s0, [Lm, Tt, D1, D0, D1, D0, Rm]),
  (.t1, [Lm, D2, F, D0, D1, D0, Rm]),
  (.f0, [Lm, D2, D0, F, D1, D0, Rm]),
  (.f1, [Lm, D2, D0, D0, Tt, D0, Rm]),
  (.t0, [Lm, D2, D0, D0, D1, Tt, Rm]),
  (.tR, [Lm, D2, D0, D0, D1, D0, Rm]),
  (.s2, [Lm, F, Tt, D0, D0, D1, D0, Rm]),
  (.t0, [Lm, F, D1, Tt, D0, D1, D0, Rm]),
  (.f1, [Lm, D0, Tt, Tt, D0, D1, D0, Rm]),
  (.t0, [Lm, D0, Tt, D1, Tt, D1, D0, Rm]),
  (.t1, [Lm, D0, D2, F, Tt, D1, D0, Rm]),
  (.t1, [Lm, D0, D2, F, D2, F, D0, Rm]),
  (.f0, [Lm, D0, D2, F, D2, D0, F, Rm]),
  (.fR, [Lm, D0, D2, F, D2, D0, Rm]),
  (.f2, [Lm, D0, D2, D1, F, D0, Rm]),
  (.f0, [Lm, D0, D2, D1, D0, F, Rm]),
  (.fR, [Lm, D0, D2, D1, D0, Rm]),
  (.s0, [Lm, Tt, D2, D1, D0, Rm]),
  (.t2, [Lm, D2, Tt, D1, D0, Rm]),
  (.t1, [Lm, D2, D2, F, D0, Rm]),
  (.f0, [Lm, D2, D2, D0, F, Rm]),
  (.fR, [Lm, D2, D2, D0, Rm]),
  (.s2, [Lm, F, Tt, D2, D0, Rm]),
  (.t2, [Lm, F, D2, Tt, D0, Rm]),
  (.f2, [Lm, D1, F, Tt, D0, Rm]),
  (.s1, [Lm, F, F, F, Tt, D0, Rm]),
  (.t0, [Lm, F, F, F, D1, Tt, Rm]),
  (.tR, [Lm, F, F, F, D1, D0, Rm]),
  (.f1, [Lm, F, F, D0, Tt, D0, Rm]),
  (.f0, [Lm, F, D0, F, Tt, D0, Rm]),
  (.f0, [Lm, D0, F, F, Tt, D0, Rm]),
  (.t0, [Lm, D0, F, F, D1, Tt, Rm]),
  (.tR, [Lm, D0, F, F, D1, D0, Rm]),
  (.f1, [Lm, D0, F, D0, Tt, D0, Rm]),
  (.f0, [Lm, D0, D0, F, Tt, D0, Rm]),
  (.t0, [Lm, D0, D0, F, D1, Tt, Rm]),
  (.tR, [Lm, D0, D0, F, D1, D0, Rm]),
  (.f1, [Lm, D0, D0, D0, Tt, D0, Rm]),
  (.t0, [Lm, D0, D0, D0, D1, Tt, Rm]),
  (.tR, [Lm, D0, D0, D0, D1, D0, Rm]),
  (.s0, [Lm, Tt, D0, D0, D1, D0, Rm]),
  (.t0, [Lm, D1, Tt, D0, D1, D0, Rm]),
  (.t0, [Lm, D1, D1, Tt, D1, D0, Rm]),
  (.t1, [Lm, D1, D1, D2, F, D0, Rm]),
  (.f0, [Lm, D1, D1, D2, D0, F, Rm]),
  (.fR, [Lm, D1, D1, D2, D0, Rm]),
  (.s1, [Lm, F, F, D1, D2, D0, Rm]),
  (.f1, [Lm, F, D0, Tt, D2, D0, Rm]),
  (.f0, [Lm, D0, F, Tt, D2, D0, Rm]),
  (.t2, [Lm, D0, F, D2, Tt, D0, Rm]),
  (.f2, [Lm, D0, D1, F, Tt, D0, Rm]),
  (.t0, [Lm, D0, D1, F, D1, Tt, Rm]),
  (.tR, [Lm, D0, D1, F, D1, D0, Rm]),
  (.f1, [Lm, D0, D1, D0, Tt, D0, Rm]),
  (.t0, [Lm, D0, D1, D0, D1, Tt, Rm]),
  (.tR, [Lm, D0, D1, D0, D1, D0, Rm]),
  (.s0, [Lm, Tt, D1, D0, D1, D0, Rm]),
  (.t1, [Lm, D2, F, D0, D1, D0, Rm]),
  (.f0, [Lm, D2, D0, F, D1, D0, Rm]),
  (.f1, [Lm, D2, D0, D0, Tt, D0, Rm]),
  (.t0, [Lm, D2, D0, D0, D1, Tt, Rm]),
  (.tR, [Lm, D2, D0, D0, D1, D0, Rm]),
  (.s2, [Lm, F, Tt, D0, D0, D1, D0, Rm]),
  (.t0, [Lm, F, D1, Tt, D0, D1, D0, Rm]),
  (.f1, [Lm, D0, Tt, Tt, D0, D1, D0, Rm]),
  (.t0, [Lm, D0, Tt, D1, Tt, D1, D0, Rm]),
  (.t1, [Lm, D0, D2, F, Tt, D1, D0, Rm]),
  (.t1, [Lm, D0, D2, F, D2, F, D0, Rm]),
  (.f0, [Lm, D0, D2, F, D2, D0, F, Rm]),
  (.fR, [Lm, D0, D2, F, D2, D0, Rm]),
  (.f2, [Lm, D0, D2, D1, F, D0, Rm]),
  (.f0, [Lm, D0, D2, D1, D0, F, Rm]),
  (.fR, [Lm, D0, D2, D1, D0, Rm]),
  (.s0, [Lm, Tt, D2, D1, D0, Rm]),
  (.t2, [Lm, D2, Tt, D1, D0, Rm]),
  (.t1, [Lm, D2, D2, F, D0, Rm]),
  (.f0, [Lm, D2, D2, D0, F, Rm]),
  (.fR, [Lm, D2, D2, D0, Rm]),
  (.s2, [Lm, F, Tt, D2, D0, Rm]),
  (.t2, [Lm, F, D2, Tt, D0, Rm]),
  (.f2, [Lm, D1, F, Tt, D0, Rm]),
  (.t0, [Lm, D1, F, D1, Tt, Rm]),
  (.tR, [Lm, D1, F, D1, D0, Rm]),
  (.f1, [Lm, D1, D0, Tt, D0, Rm]),
  (.t0, [Lm, D1, D0, D1, Tt, Rm]),
  (.tR, [Lm, D1, D0, D1, D0, Rm]),
  (.s1, [Lm, F, F, D0, D1, D0, Rm]),
  (.f0, [Lm, F, D0, F, D1, D0, Rm]),
  (.f0, [Lm, D0, F, F, D1, D0, Rm]),
  (.f1, [Lm, D0, F, D0, Tt, D0, Rm]),
  (.f0, [Lm, D0, D0, F, Tt, D0, Rm]),
  (.t0, [Lm, D0, D0, F, D1, Tt, Rm]),
  (.tR, [Lm, D0, D0, F, D1, D0, Rm]),
  (.f1, [Lm, D0, D0, D0, Tt, D0, Rm]),
  (.t0, [Lm, D0, D0, D0, D1, Tt, Rm]),
  (.tR, [Lm, D0, D0, D0, D1, D0, Rm]),
  (.s0, [Lm, Tt, D0, D0, D1, D0, Rm]),
  (.t0, [Lm, D1, Tt, D0, D1, D0, Rm]),
  (.t0, [Lm, D1, D1, Tt, D1, D0, Rm]),
  (.t1, [Lm, D1, D1, D2, F, D0, Rm]),
  (.f0, [Lm, D1, D1, D2, D0, F, Rm]),
  (.fR, [Lm, D1, D1, D2, D0, Rm]),
  (.s1, [Lm, F, F, D1, D2, D0, Rm]),
  (.f1, [Lm, F, D0, Tt, D2, D0, Rm]),
  (.f0, [Lm, D0, F, Tt, D2, D0, Rm]),
  (.t2, [Lm, D0, F, D2, Tt, D0, Rm]),
  (.f2, [Lm, D0, D1, F, Tt, D0, Rm]),
  (.t0, [Lm, D0, D1, F, D1, Tt, Rm]),
  (.tR, [Lm, D0, D1, F, D1, D0, Rm]),
  (.f1, [Lm, D0, D1, D0, Tt, D0, Rm]),
  (.t0, [Lm, D0, D1, D0, D1, Tt, Rm]),
  (.tR, [Lm, D0, D1, D0, D1, D0, Rm]),
  (.s0, [Lm, Tt, D1, D0, D1, D0, Rm]),
  (.t1, [Lm, D2, F, D0, D1, D0, Rm]),
  (.f0, [Lm, D2, D0, F, D1, D0, Rm]),
  (.f1, [Lm, D2, D0, D0, Tt, D0, Rm]),
  (.t0, [Lm, D2, D0, D0, D1, Tt, Rm]),
  (.tR, [Lm, D2, D0, D0, D1, D0, Rm]),
  (.s2, [Lm, F, Tt, D0, D0, D1, D0, Rm]),
  (.t0, [Lm, F, D1, Tt, D0, D1, D0, Rm]),
  (.f1, [Lm, D0, Tt, Tt, D0, D1, D0, Rm]),
  (.t0, [Lm, D0, Tt, D1, Tt, D1, D0, Rm]),
  (.t1, [Lm, D0, D2, F, Tt, D1, D0, Rm]),
  (.t1, [Lm, D0, D2, F, D2, F, D0, Rm]),
  (.f0, [Lm, D0, D2, F, D2, D0, F, Rm]),
  (.fR, [Lm, D0, D2, F, D2, D0, Rm]),
  (.f2, [Lm, D0, D2, D1, F, D0, Rm]),
  (.f0, [Lm, D0, D2, D1, D0, F, Rm]),
  (.fR, [Lm, D0, D2, D1, D0, Rm]),
  (.s0, [Lm, Tt, D2, D1, D0, Rm]),
  (.t2, [Lm, D2, Tt, D1, D0, Rm]),
  (.t1, [Lm, D2, D2, F, D0, Rm]),
  (.f0, [Lm, D2, D2, D0, F, Rm]),
  (.fR, [Lm, D2, D2, D0, Rm])]

theorem walk_d1_ok : checkWalk .d1 start_d1 walk_d1 = true ∧ last start_d1 walk_d1 = start_d1 ∧
    ∀ ρ ∈ RName.all, ρ ∈ walk_d1.map Prod.fst := by decide +kernel

theorem walk_d0_ok : checkWalk .d0 start_d0 walk_d0 = true ∧ last start_d0 walk_d0 = start_d0 ∧
    ∀ ρ ∈ RName.all, ρ ∈ walk_d0.map Prod.fst := by decide +kernel

/-- **En el vecino `3x − 1` no se puede eliminar ninguna regla:** `SN(ρ/𝒯₁)` es falso para
toda regla `ρ`. -/
theorem not_relSN_d1 (ρ : RName) : ¬ WellFounded (fun y x => RelStep .d1 ρ x y) := fun h =>
  not_acc_of_cycle walk_d1_ok.1 walk_d1_ok.2.1 (walk_d1_ok.2.2 ρ ρ.mem_all) (h.apply _)

/-- **Ídem para el vecino `3x − 3`.** -/
theorem not_relSN_d0 (ρ : RName) : ¬ WellFounded (fun y x => RelStep .d0 ρ x y) := fun h =>
  not_acc_of_cycle walk_d0_ok.1 walk_d0_ok.2.1 (walk_d0_ok.2.2 ρ ρ.mem_all) (h.apply _)

end SRS.Neighbor
