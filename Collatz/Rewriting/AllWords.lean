import Collatz.Rewriting

/-!
# Lema 3.16 de YAH: de las palabras canónicas a todas las palabras

`Collatz/Rewriting.lean` trabaja con la palabra interna `w` de `▷ w ◁` (los marcadores
implícitos). Acá consideramos **todas** las palabras sobre el alfabeto completo de 7 letras
`f, t, 0, 1, 2, ▷, ◁`, con los marcadores en cualquier posición y cantidad, y la clausura
contextual de las 11 reglas (`WStep`). Probamos

* `terminatesAll_iff : TerminatesAll ↔ Terminates`, y por lo tanto
* `collatz_iff_terminatesAll : Collatz ↔ SRS.TerminatesAll` (Teorema 3.17 de YAH tal como está
  enunciado en el paper: la conjetura equivale a la terminación del sistema).

La prueba del paper usa *type introduction* (Sabel–Zantema) y el Lema 3.15. Acá usamos un
argumento directo y elemental:

1. Toda regla tiene lado izquierdo de longitud 2 y no crea ni borra marcadores. Un paso en
   `A ++ m :: B` (con `m` marcador) es un paso en `A ++ [m]` o en `m :: B` (`WStep.split`).
   Por eso la terminación de las dos piezas da la de la palabra (`acc_split`, vía `Prod.GameAdd`).
2. Cortando en cada marcador, toda palabra se reduce a piezas `L? x R?` con `x` sin marcadores
   (`wrap`). En una pieza, `WStep` es exactamente el sistema interno `PStep` (`WStep.inv_wrap`),
   donde las reglas de inicio sólo valen si `L = ▷` y las dinámicas sólo si `R = ◁`.
3. Si `L ≠ ▷`, `(#binarios, inversiones)` baja lexicográficamente; si `R ≠ ◁`, baja
   `(#ternarios, inversiones)`. Sólo queda `▷ x ◁`, que es la hipótesis `Terminates`.
-/

namespace SRS

/-- Marcadores: `l` = `▷` (inicio), `r` = `◁` (fin). -/
inductive Mk | l | r
  deriving DecidableEq, Repr

/-- Alfabeto completo: dígitos y marcadores. -/
inductive Full | sym (s : Sym) | mk (m : Mk)
  deriving DecidableEq, Repr

/-- Reglas auxiliares `b d → d' b'`. -/
inductive ARule : Sym → Sym → List Sym → Prop
  | f0 : ARule .f .d0 [.d0, .f]
  | f1 : ARule .f .d1 [.d0, .t]
  | f2 : ARule .f .d2 [.d1, .f]
  | t0 : ARule .t .d0 [.d1, .t]
  | t1 : ARule .t .d1 [.d2, .f]
  | t2 : ARule .t .d2 [.d2, .t]

/-- Reglas de inicio `▷ d → ▷ w`. -/
inductive SRule : Sym → List Sym → Prop
  | s0 : SRule .d0 [.t]
  | s1 : SRule .d1 [.f, .f]
  | s2 : SRule .d2 [.f, .t]

/-- Las 11 reglas de `𝒯` sobre el alfabeto completo. -/
inductive WRule : Full → Full → List Full → Prop
  | endF : WRule (.sym .f) (.mk .r) [.mk .r]
  | endT : WRule (.sym .t) (.mk .r) [.sym .d2, .mk .r]
  | aux {a b : Sym} {w : List Sym} (h : ARule a b w) : WRule (.sym a) (.sym b) (w.map .sym)
  | start {d : Sym} {w : List Sym} (h : SRule d w) :
      WRule (.mk .l) (.sym d) (.mk .l :: w.map .sym)

/-- Un paso de reescritura en cualquier posición de cualquier palabra. -/
inductive WStep : List Full → List Full → Prop
  | mk (u v : List Full) {a b : Full} {w : List Full} (h : WRule a b w) :
      WStep (u ++ a :: b :: v) (u ++ w ++ v)

/-- `𝒯` termina sobre **todas** las palabras del alfabeto completo. -/
def TerminatesAll : Prop := ∀ s, Acc (fun y x => WStep x y) s

/-! ## Piezas: una palabra sin marcadores, con un marcador opcional a cada lado -/

def wrap (L R : Option Mk) (x : List Sym) : List Full :=
  (L.map .mk).toList ++ x.map .sym ++ (R.map .mk).toList

/-- El sistema dentro de una pieza: las reglas de inicio valen si `l`, las dinámicas si `r`. -/
inductive PStep (l r : Prop) : List Sym → List Sym → Prop
  | aux (u v : List Sym) {a b : Sym} {w : List Sym} (h : ARule a b w) :
      PStep l r (u ++ a :: b :: v) (u ++ w ++ v)
  | endF (hr : r) (u : List Sym) : PStep l r (u ++ [.f]) u
  | endT (hr : r) (u : List Sym) : PStep l r (u ++ [.t]) (u ++ [.d2])
  | start (hl : l) (v : List Sym) {d : Sym} {w : List Sym} (h : SRule d w) :
      PStep l r (d :: v) (w ++ v)

theorem PStep.toStep {l r : Prop} {x y : List Sym} (h : PStep l r x y) : Step x y := by
  cases h with
  | aux u v ha => cases ha <;> simpa using (by constructor : Step _ _)
  | endF => exact Step.endF _
  | endT => exact Step.endT _
  | start _ v hs => cases hs <;> simpa using (by constructor : Step _ _)

theorem Step.toPStep {l r : Prop} (hl : l) (hr : r) {x y : List Sym} (h : Step x y) :
    PStep l r x y := by
  cases h with
  | endF => exact PStep.endF hr _
  | endT u => exact PStep.endT hr u
  | f0 u v => simpa using PStep.aux (l := l) (r := r) u v ARule.f0
  | f1 u v => simpa using PStep.aux (l := l) (r := r) u v ARule.f1
  | f2 u v => simpa using PStep.aux (l := l) (r := r) u v ARule.f2
  | t0 u v => simpa using PStep.aux (l := l) (r := r) u v ARule.t0
  | t1 u v => simpa using PStep.aux (l := l) (r := r) u v ARule.t1
  | t2 u v => simpa using PStep.aux (l := l) (r := r) u v ARule.t2
  | s0 v => simpa using PStep.start (r := r) hl v SRule.s0
  | s1 v => simpa using PStep.start (r := r) hl v SRule.s1
  | s2 v => simpa using PStep.start (r := r) hl v SRule.s2

/-! ### Inversión de `WStep` sobre una pieza -/

theorem split_digit₀ {R : Option Mk} {c : Sym} : ∀ {x : List Sym} {u w : List Full},
    u ++ .sym c :: w = x.map .sym ++ (R.map .mk).toList →
    ∃ x₁ x₂, x = x₁ ++ c :: x₂ ∧ u = x₁.map .sym ∧ w = x₂.map .sym ++ (R.map .mk).toList
  | [], u, w, h => by cases R <;> cases u <;> simp at h
  | y :: x, [], w, h => by
      simp only [List.nil_append, List.map_cons, List.cons_append, List.cons.injEq,
        Full.sym.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact ⟨[], x, by simp⟩
  | y :: x, e :: u, w, h => by
      simp only [List.cons_append, List.map_cons, List.cons.injEq] at h
      obtain ⟨rfl, h⟩ := h
      obtain ⟨x₁, x₂, rfl, rfl, rfl⟩ := split_digit₀ h
      exact ⟨y :: x₁, x₂, by simp⟩

theorem split_digit {L R : Option Mk} {x : List Sym} {u w : List Full} {c : Sym}
    (h : u ++ .sym c :: w = wrap L R x) :
    ∃ x₁ x₂, x = x₁ ++ c :: x₂ ∧ u = (L.map .mk).toList ++ x₁.map .sym ∧
      w = x₂.map .sym ++ (R.map .mk).toList := by
  cases L with
  | none => simpa [wrap] using split_digit₀ (by simpa [wrap] using h)
  | some m =>
    cases u with
    | nil => simp [wrap] at h
    | cons e u =>
      simp only [wrap, Option.map_some, Option.toList_some, List.cons_append, List.nil_append,
        List.cons.injEq] at h
      obtain ⟨rfl, h⟩ := h
      obtain ⟨x₁, x₂, rfl, rfl, rfl⟩ := split_digit₀ h
      exact ⟨x₁, x₂, rfl, by simp, rfl⟩

theorem split_mk₀ {R : Option Mk} {m : Mk} : ∀ {x : List Sym} {u w : List Full},
    u ++ .mk m :: w = x.map .sym ++ (R.map .mk).toList → w = []
  | [], u, w, h => by
      cases R <;> rcases u with _ | ⟨e, _ | ⟨e', u⟩⟩ <;> simp_all
  | y :: x, [], w, h => by simp at h
  | y :: x, e :: u, w, h => by
      simp only [List.cons_append, List.map_cons, List.cons.injEq] at h
      exact split_mk₀ h.2

/-- En una pieza, todo paso de `WStep` es un paso de `PStep` sobre la palabra interna. -/
theorem WStep.inv_wrap {L R : Option Mk} {x : List Sym} {s' : List Full}
    (h : WStep (wrap L R x) s') :
    ∃ x', s' = wrap L R x' ∧ PStep (L = some .l) (R = some .r) x x' := by
  generalize hs : wrap L R x = s at h
  obtain ⟨u, v, hr⟩ := h
  cases hr with
  | endF =>
    obtain ⟨x₁, x₂, rfl, rfl, hw⟩ := split_digit hs.symm
    rcases x₂ with _ | ⟨y, x₂⟩
    · rcases R with _ | m
      · simp at hw
      · simp only [List.map_nil, Option.map_some, Option.toList_some, List.nil_append,
          List.cons.injEq, Full.mk.injEq] at hw
        obtain ⟨rfl, rfl⟩ := hw
        exact ⟨x₁, by simp [wrap], PStep.endF rfl x₁⟩
    · simp at hw
  | endT =>
    obtain ⟨x₁, x₂, rfl, rfl, hw⟩ := split_digit hs.symm
    rcases x₂ with _ | ⟨y, x₂⟩
    · rcases R with _ | m
      · simp at hw
      · simp only [List.map_nil, Option.map_some, Option.toList_some, List.nil_append,
          List.cons.injEq, Full.mk.injEq] at hw
        obtain ⟨rfl, rfl⟩ := hw
        exact ⟨x₁ ++ [.d2], by simp [wrap], PStep.endT rfl x₁⟩
    · simp at hw
  | aux ha =>
    obtain ⟨x₁, x₂, rfl, rfl, hw⟩ := split_digit hs.symm
    rcases x₂ with _ | ⟨y, x₂⟩
    · rcases R with _ | m <;> simp at hw
    · simp only [List.map_cons, List.cons_append, List.cons.injEq, Full.sym.injEq] at hw
      obtain ⟨rfl, rfl⟩ := hw
      exact ⟨x₁ ++ _ ++ x₂, by simp [wrap], PStep.aux x₁ x₂ ha⟩
  | start hsr =>
    rcases L with _ | m
    · have := split_mk₀ (by simpa [wrap] using hs.symm)
      simp at this
    · rcases u with _ | ⟨e, u⟩
      · simp only [wrap, Option.map_some, Option.toList_some, List.cons_append,
          List.nil_append, List.cons.injEq, Full.mk.injEq] at hs
        obtain ⟨rfl, hs⟩ := hs
        rcases x with _ | ⟨y, x⟩
        · rcases R with _ | m <;> simp at hs
        · simp only [List.map_cons, List.cons_append, List.cons.injEq, Full.sym.injEq] at hs
          obtain ⟨rfl, rfl⟩ := hs
          exact ⟨_ ++ x, by simp [wrap], PStep.start rfl x hsr⟩
      · simp only [wrap, Option.map_some, Option.toList_some, List.cons_append,
          List.nil_append, List.cons.injEq] at hs
        have := split_mk₀ hs.2.symm
        simp at this

/-- Recíproca: un paso de `PStep` es un paso de `WStep` en la pieza. -/
theorem PStep.wrap_step {L R : Option Mk} {x y : List Sym}
    (h : PStep (L = some .l) (R = some .r) x y) : WStep (wrap L R x) (wrap L R y) := by
  cases h with
  | aux u v ha =>
    convert WStep.mk ((L.map .mk).toList ++ u.map .sym) (v.map .sym ++ (R.map .mk).toList)
      (WRule.aux ha) using 1 <;> simp [wrap]
  | endF hr =>
    subst hr
    convert WStep.mk ((L.map .mk).toList ++ y.map .sym) [] WRule.endF using 1 <;> simp [wrap]
  | endT hr u =>
    subst hr
    convert WStep.mk ((L.map .mk).toList ++ u.map .sym) [] WRule.endT using 1 <;> simp [wrap]
  | start hl v hs =>
    subst hl
    simpa [wrap] using WStep.mk [] (v.map .sym ++ (R.map .mk).toList) (WRule.start hs)

/-! ### Terminación de las piezas -/

theorem ARule.measure {a b : Sym} {w : List Sym} (h : ARule a b w) (u v : List Sym) :
    tc (u ++ w ++ v) = tc (u ++ a :: b :: v) ∧ bc (u ++ w ++ v) = bc (u ++ a :: b :: v) ∧
      inv (u ++ w ++ v) < inv (u ++ a :: b :: v) := by
  cases h <;> simp [tc_append, bc_append, inv_append, tc, bc, inv, Sym.isBin]

/-- Sin `▷` a la izquierda: baja `(#binarios, inversiones)`. -/
theorem PStep.lt_left {l r : Prop} (hl : ¬ l) {x y : List Sym} (h : PStep l r x y) :
    LexLt (bc y, inv y) (bc x, inv x) := by
  unfold LexLt
  cases h with
  | aux u v ha =>
    obtain ⟨-, hb, hi⟩ := ha.measure u v
    rw [hb]; exact Prod.Lex.right _ hi
  | endF _ u => exact Prod.Lex.left _ _ (by simp [bc_append, bc, Sym.isBin])
  | endT _ u => exact Prod.Lex.left _ _ (by simp [bc_append, bc, Sym.isBin])
  | start h' => exact absurd h' hl

/-- Sin `◁` a la derecha: baja `(#ternarios, inversiones)`. -/
theorem PStep.lt_right {l r : Prop} (hr : ¬ r) {x y : List Sym} (h : PStep l r x y) :
    LexLt (tc y, inv y) (tc x, inv x) := by
  unfold LexLt
  cases h with
  | aux u v ha =>
    obtain ⟨ht, -, hi⟩ := ha.measure u v
    rw [ht]; exact Prod.Lex.right _ hi
  | endF h' => exact absurd h' hr
  | endT h' => exact absurd h' hr
  | start _ v hs =>
    exact Prod.Lex.left _ _ (by cases hs <;> simp [tc, Sym.isBin])

theorem acc_istep (hT : Terminates) (L R : Option Mk) (x : List Sym) :
    Acc (fun y x => PStep (L = some .l) (R = some .r) x y) x := by
  by_cases hl : L = some .l
  · by_cases hr : R = some .r
    · exact Subrelation.accessible (fun h => h.toStep) (hT x)
    · exact (Subrelation.wf (fun h => h.lt_right hr)
        (InvImage.wf (fun x => (tc x, inv x)) lexLt_wf)).apply x
  · exact (Subrelation.wf (fun h => h.lt_left hl)
      (InvImage.wf (fun x => (bc x, inv x)) lexLt_wf)).apply x

theorem acc_wrap_of_acc {L R : Option Mk} {x : List Sym}
    (h : Acc (fun y x => PStep (L = some .l) (R = some .r) x y) x) :
    Acc (fun y x => WStep x y) (wrap L R x) := by
  induction h with
  | intro x _ ih =>
    refine Acc.intro _ fun s' hs => ?_
    obtain ⟨x', rfl, hi⟩ := hs.inv_wrap
    exact ih x' hi

/-! ## Cortar en un marcador -/

theorem WRule.left_mk {a b : Full} {w : List Full} {m : Mk} (h : WRule a b w) (ha : a = .mk m) :
    ∃ w', w = .mk m :: w' := by
  cases h <;> simp_all

theorem WRule.right_mk {a b : Full} {w : List Full} {m : Mk} (h : WRule a b w) (hb : b = .mk m) :
    ∃ w', w = w' ++ [.mk m] := by
  cases h <;> simp_all
  exact ⟨[.sym .d2], rfl⟩

/-- Un paso en `A ++ m :: B` es un paso en `A ++ [m]` o en `m :: B`. -/
theorem WStep.split {A B : List Full} {m : Mk} {s' : List Full}
    (h : WStep (A ++ .mk m :: B) s') :
    (∃ A', WStep (A ++ [.mk m]) (A' ++ [.mk m]) ∧ s' = A' ++ .mk m :: B) ∨
    (∃ B', WStep (.mk m :: B) (.mk m :: B') ∧ s' = A ++ .mk m :: B') := by
  generalize hs : A ++ .mk m :: B = s at h
  obtain ⟨u, v, hr⟩ := h
  rw [List.append_eq_append_iff] at hs
  rcases hs with ⟨a', rfl, h2⟩ | ⟨c', rfl, h2⟩
  · -- el redex empieza en `u = A ++ m :: …` o en el marcador mismo
    rcases a' with _ | ⟨e, a'⟩
    · simp only [List.nil_append, List.cons.injEq] at h2
      obtain ⟨rfl, rfl⟩ := h2
      obtain ⟨w', rfl⟩ := hr.left_mk rfl
      exact Or.inr ⟨w' ++ v, by simpa using WStep.mk [] v hr, by simp⟩
    · simp only [List.cons_append, List.cons.injEq] at h2
      obtain ⟨rfl, rfl⟩ := h2
      exact Or.inr ⟨a' ++ _ ++ v, by simpa using WStep.mk (.mk m :: a') v hr, by simp⟩
  · rcases c' with _ | ⟨e, _ | ⟨e', c'⟩⟩
    · simp only [List.nil_append, List.cons.injEq] at h2
      obtain ⟨rfl, rfl⟩ := h2
      obtain ⟨w', rfl⟩ := hr.left_mk rfl
      exact Or.inr ⟨w' ++ v, by simpa using WStep.mk [] v hr, by simp⟩
    · simp only [List.cons_append, List.nil_append, List.cons.injEq] at h2
      obtain ⟨rfl, rfl, rfl⟩ := h2
      obtain ⟨w', rfl⟩ := hr.right_mk rfl
      exact Or.inl ⟨u ++ w', by simpa using WStep.mk u [] hr, by simp⟩
    · simp only [List.cons_append, List.cons.injEq] at h2
      obtain ⟨rfl, rfl, rfl⟩ := h2
      exact Or.inl ⟨u ++ _ ++ c', by simpa using WStep.mk u (c' ++ [.mk m]) hr, by simp⟩

theorem acc_split {A B : List Full} {m : Mk}
    (hA : Acc (fun y x => WStep x y) (A ++ [.mk m]))
    (hB : Acc (fun y x => WStep x y) (.mk m :: B)) :
    Acc (fun y x => WStep x y) (A ++ .mk m :: B) := by
  have hA' : Acc (InvImage (fun y x => WStep x y) (· ++ [.mk m])) A := InvImage.accessible _ hA
  have hB' : Acc (InvImage (fun y x => WStep x y) (.mk m :: ·)) B := InvImage.accessible _ hB
  have hp := Acc.prod_gameAdd hA' hB'
  clear hA hB hA' hB'
  generalize hAB : (A, B) = p at hp
  induction hp generalizing A B with
  | intro p _ ih =>
    subst hAB
    refine Acc.intro _ fun s' hs => ?_
    rcases hs.split with ⟨A', hA'', rfl⟩ | ⟨B', hB'', rfl⟩
    · exact ih (A', B) (Prod.GameAdd.fst hA'') rfl
    · exact ih (A, B') (Prod.GameAdd.snd hB'') rfl

/-! ## Resultado -/

theorem exists_decomp : ∀ s : List Full, ∃ (x : List Sym) (rest : List Full),
    s = x.map .sym ++ rest ∧ (rest = [] ∨ ∃ m rest', rest = .mk m :: rest')
  | [] => ⟨[], [], rfl, Or.inl rfl⟩
  | .mk m :: s => ⟨[], .mk m :: s, rfl, Or.inr ⟨m, s, rfl⟩⟩
  | .sym c :: s => by
      obtain ⟨x, rest, rfl, h⟩ := exists_decomp s
      exact ⟨c :: x, rest, rfl, h⟩

theorem acc_all (hT : Terminates) :
    ∀ n (s : List Full), s.length = n → ∀ L : Option Mk,
      Acc (fun y x => WStep x y) ((L.map .mk).toList ++ s) := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro s hn L
    obtain ⟨x, rest, rfl, hr⟩ := exists_decomp s
    rcases hr with rfl | ⟨m, rest', rfl⟩
    · simpa [wrap] using acc_wrap_of_acc (acc_istep hT L none x)
    · have hA := acc_wrap_of_acc (acc_istep hT L (some m) x)
      have hB := ih rest'.length (by simp at hn; omega) rest' rfl (some m)
      simp only [wrap, Option.map_some, Option.toList_some] at hA hB
      simpa using acc_split hA hB

/-- **Lema 3.16 de YAH** (y su recíproca): terminar sobre las palabras canónicas `▷w◁`
equivale a terminar sobre todas las palabras del alfabeto completo. -/
theorem terminatesAll_iff : TerminatesAll ↔ Terminates := by
  constructor
  · intro hA w
    have h := hA (wrap (some .l) (some .r) w)
    generalize hs : wrap (some .l) (some .r) w = s at h
    induction h generalizing w with
    | intro s _ ih =>
      subst hs
      exact Acc.intro _ fun y hy => ih _ ((Step.toPStep rfl rfl hy).wrap_step) y rfl
  · intro hT s
    simpa using acc_all hT s.length s rfl none

end SRS

/-- **Yolcu–Aaronson–Heule, Teorema 3.17.** La conjetura de Collatz equivale a la terminación
del sistema de 11 reglas sobre todas las palabras del alfabeto `{f, t, 0, 1, 2, ▷, ◁}`. -/
theorem collatz_iff_terminatesAll : Collatz ↔ SRS.TerminatesAll :=
  collatz_iff_terminates.trans SRS.terminatesAll_iff.symm
