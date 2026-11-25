import Mathlib

/-!
# Programas WHILE sobre registros

Primer eslabón de la formalización del teorema de Conway (1972): un lenguaje estructurado mínimo
sobre registros naturales (`inc`, `dec`, secuencia y `while r ≠ 0`), con semántica de paso grande.

* `Prog.Runs p s s'`: el programa `p`, desde los registros `s`, termina con los registros `s'`.
* `Prog.rename σ p`: renombre de registros; con `σ` inyectiva, el programa renombrado se comporta
  como el original sobre `s ∘ σ` y no toca los registros fuera de la imagen de `σ`.
* Macros: `clear`, `moveAdd`, `copy`, con su efecto exacto.
-/

namespace Conway

/-- Valuación de los registros. -/
abbrev Regs := ℕ → ℕ

/-- Programas WHILE: `loop r p` es `while r ≠ 0 do p`. -/
inductive Prog
  | skip
  | inc (r : ℕ)
  | dec (r : ℕ)
  | addc (r k : ℕ)
  | seq (p q : Prog)
  | loop (r : ℕ) (p : Prog)
  deriving DecidableEq

namespace Prog

open Function

/-- Semántica de paso grande (`dec` en 0 no hace nada). -/
inductive Runs : Prog → Regs → Regs → Prop
  | skip (s) : Runs skip s s
  | inc (r s) : Runs (inc r) s (update s r (s r + 1))
  | dec (r s) : Runs (dec r) s (update s r (s r - 1))
  | addc (r k s) : Runs (addc r k) s (update s r (s r + k))
  | seq {p q s t u} : Runs p s t → Runs q t u → Runs (seq p q) s u
  | loopStop {r p s} : s r = 0 → Runs (loop r p) s s
  | loopStep {r p s t u} : s r ≠ 0 → Runs p s t → Runs (loop r p) t u → Runs (loop r p) s u

theorem Runs.det {p s t u} (h1 : Runs p s t) (h2 : Runs p s u) : t = u := by
  induction h1 generalizing u with
  | skip => cases h2; rfl
  | inc => cases h2; rfl
  | dec => cases h2; rfl
  | addc => cases h2; rfl
  | seq _ _ ih1 ih2 =>
    cases h2 with
    | seq h h' => obtain rfl := ih1 h; exact ih2 h'
  | loopStop h =>
    cases h2 with
    | loopStop => rfl
    | loopStep h' => exact absurd h h'
  | loopStep h _ _ ih1 ih2 =>
    cases h2 with
    | loopStop h' => exact absurd h' h
    | loopStep _ h1 h2 => obtain rfl := ih1 h1; exact ih2 h2

theorem Runs.iff_eq {p s t} (h : Runs p s t) {u} : Runs p s u ↔ u = t :=
  ⟨fun h' => h'.det h, fun e => e ▸ h⟩

@[simp] theorem runs_skip {s s'} : Runs skip s s' ↔ s' = s :=
  (Runs.skip s).iff_eq

@[simp] theorem runs_inc {r s s'} : Runs (inc r) s s' ↔ s' = update s r (s r + 1) :=
  (Runs.inc r s).iff_eq

@[simp] theorem runs_dec {r s s'} : Runs (dec r) s s' ↔ s' = update s r (s r - 1) :=
  (Runs.dec r s).iff_eq

@[simp] theorem runs_addc {r k s s'} : Runs (addc r k) s s' ↔ s' = update s r (s r + k) :=
  (Runs.addc r k s).iff_eq

theorem runs_seq {p q s u} : Runs (seq p q) s u ↔ ∃ t, Runs p s t ∧ Runs q t u :=
  ⟨fun h => by cases h with | seq h1 h2 => exact ⟨_, h1, h2⟩, fun ⟨_, h1, h2⟩ => .seq h1 h2⟩

/-! ## Renombre de registros -/

/-- Renombra los registros de un programa. -/
def rename (σ : ℕ → ℕ) : Prog → Prog
  | skip => skip
  | inc r => inc (σ r)
  | dec r => dec (σ r)
  | addc r k => addc (σ r) k
  | seq p q => seq (rename σ p) (rename σ q)
  | loop r p => loop (σ r) (rename σ p)

section extend

variable {σ : ℕ → ℕ}

theorem extend_comp_self (hσ : Injective σ) (s : Regs) : extend σ (s ∘ σ) s = s := by
  funext x
  by_cases hx : ∃ a, σ a = x
  · obtain ⟨a, rfl⟩ := hx
    rw [hσ.extend_apply]; rfl
  · rw [extend_apply' _ _ _ hx]

theorem extend_update (hσ : Injective σ) (s : Regs) (k v : ℕ) :
    extend σ (update (s ∘ σ) k v) s = update s (σ k) v := by
  funext x
  by_cases hx : ∃ a, σ a = x
  · obtain ⟨a, rfl⟩ := hx
    rw [hσ.extend_apply]
    by_cases hak : a = k
    · subst hak; simp
    · rw [update_of_ne hak, update_of_ne (hσ.ne hak)]; rfl
  · rw [extend_apply' _ _ _ hx, update_of_ne]
    rintro rfl; exact hx ⟨k, rfl⟩

theorem extend_extend (hσ : Injective σ) (b t s : Regs) :
    extend σ b (extend σ t s) = extend σ b s := by
  funext x
  by_cases hx : ∃ a, σ a = x
  · obtain ⟨a, rfl⟩ := hx
    simp [hσ.extend_apply]
  · rw [extend_apply' _ _ _ hx, extend_apply' _ _ _ hx, extend_apply' _ _ _ hx]

theorem extend_comp (hσ : Injective σ) (b s : Regs) : extend σ b s ∘ σ = b := by
  funext a; simp [hσ.extend_apply]

end extend

theorem Runs.rename {σ : ℕ → ℕ} (hσ : Injective σ) {p a b} (h : Runs p a b) :
    ∀ s, a = s ∘ σ → Runs (p.rename σ) s (extend σ b s) := by
  induction h with
  | skip a =>
    intro s rfl; rw [extend_comp_self hσ]; exact .skip s
  | inc r a =>
    intro s rfl
    rw [extend_update hσ]; exact .inc _ _
  | dec r a =>
    intro s rfl
    rw [extend_update hσ]; exact .dec _ _
  | addc r k a =>
    intro s rfl
    rw [extend_update hσ]; exact .addc _ _ _
  | @seq p q a t u _ _ ih1 ih2 =>
    intro s rfl
    have h1 := ih1 s rfl
    have h2 := ih2 (extend σ t s) (extend_comp hσ t s).symm
    rw [extend_extend hσ] at h2
    exact .seq h1 h2
  | loopStop h =>
    intro s rfl
    rw [extend_comp_self hσ]; exact .loopStop h
  | @loopStep r p a t u hr _ _ ih1 ih2 =>
    intro s rfl
    have h1 := ih1 s rfl
    have h2 := ih2 (extend σ t s) (extend_comp hσ t s).symm
    rw [extend_extend hσ] at h2
    exact .loopStep hr h1 h2

theorem update_comp {σ : ℕ → ℕ} (hσ : Injective σ) (s : Regs) (r v : ℕ) :
    update s (σ r) v ∘ σ = update (s ∘ σ) r v :=
  update_comp_eq_of_injective s hσ r v

theorem runs_of_rename {σ : ℕ → ℕ} (hσ : Injective σ) :
    ∀ p s s', Runs (p.rename σ) s s' → Runs p (s ∘ σ) (s' ∘ σ) ∧ s' = extend σ (s' ∘ σ) s
  | skip, s, s', h => by
    simp only [rename, runs_skip] at h; subst s'
    exact ⟨.skip _, (extend_comp_self hσ s).symm⟩
  | inc r, s, s', h => by
    simp only [rename, runs_inc] at h; subst h
    rw [update_comp hσ, extend_update hσ]
    exact ⟨.inc _ _, rfl⟩
  | dec r, s, s', h => by
    simp only [rename, runs_dec] at h; subst h
    rw [update_comp hσ, extend_update hσ]
    exact ⟨.dec _ _, rfl⟩
  | addc r k, s, s', h => by
    simp only [rename, runs_addc] at h; subst h
    rw [update_comp hσ, extend_update hσ]
    exact ⟨.addc _ _ _, rfl⟩
  | seq p q, s, s', h => by
    simp only [rename, runs_seq] at h
    obtain ⟨t, h1, h2⟩ := h
    obtain ⟨h1, e1⟩ := runs_of_rename hσ p s t h1
    obtain ⟨h2, e2⟩ := runs_of_rename hσ q t s' h2
    refine ⟨.seq h1 h2, ?_⟩
    rw [e1, extend_extend hσ] at e2; exact e2
  | loop r p, s, s', h => by
    have ih := runs_of_rename hσ p
    simp only [rename] at h
    generalize hq : loop (σ r) (p.rename σ) = q at h
    induction h with
    | loopStop hr =>
      cases hq
      exact ⟨.loopStop hr, (extend_comp_self hσ _).symm⟩
    | @loopStep r' p' s t u hr h1 _ _ ih2 =>
      cases hq
      obtain ⟨h1, e1⟩ := ih s t h1
      obtain ⟨h2, e2⟩ := ih2 rfl
      refine ⟨.loopStep hr h1 h2, ?_⟩
      rw [e1, extend_extend hσ] at e2; exact e2
    | _ => cases hq

/-! ## Macros -/

/-- `r := 0`. -/
abbrev clear (r : ℕ) : Prog := loop r (dec r)

theorem runs_clear (r : ℕ) (s : Regs) : Runs (clear r) s (update s r 0) := by
  generalize hk : s r = k
  induction k generalizing s with
  | zero => rw [← hk, update_eq_self]; exact .loopStop hk
  | succ k ih =>
    refine .loopStep (by omega) (.dec r s) ?_
    have := ih (update s r (s r - 1)) (by simp [hk])
    simpa using this

/-- `dst := dst + src; src := 0` (con `src ≠ dst`). -/
abbrev moveAdd (src dst : ℕ) : Prog := loop src (seq (dec src) (inc dst))

theorem runs_moveAdd {src dst : ℕ} (h : src ≠ dst) (s : Regs) :
    Runs (moveAdd src dst) s (update (update s dst (s dst + s src)) src 0) := by
  generalize hk : s src = k
  induction k generalizing s with
  | zero =>
    have : update (update s dst (s dst + 0)) src 0 = s := by
      funext x; simp only [update_apply]; split_ifs <;> simp_all
    rw [this]; exact .loopStop hk
  | succ k ih =>
    refine .loopStep (by omega) (.seq (.dec src s) (.inc dst _)) ?_
    have := ih (update (update s src (s src - 1)) dst (update s src (s src - 1) dst + 1))
      (by simp [update_apply, h, hk])
    convert this using 1
    funext x; simp only [update_apply]; split_ifs <;> simp_all <;> omega

/-- `dst := dst + src` usando el auxiliar `tmp` (que debe valer 0). -/
abbrev copy (src dst tmp : ℕ) : Prog :=
  seq (loop src (seq (dec src) (seq (inc dst) (inc tmp)))) (moveAdd tmp src)

theorem runs_copy {src dst tmp : ℕ} (h1 : src ≠ dst) (h2 : src ≠ tmp) (h3 : dst ≠ tmp)
    (s : Regs) (ht : s tmp = 0) : Runs (copy src dst tmp) s (update s dst (s dst + s src)) := by
  have key : ∀ k (t : Regs), t src = k →
      Runs (loop src (seq (dec src) (seq (inc dst) (inc tmp)))) t
        (update (update (update t src 0) dst (t dst + k)) tmp (t tmp + k)) := by
    intro k
    induction k with
    | zero =>
      intro t hk
      have : update (update (update t src 0) dst (t dst + 0)) tmp (t tmp + 0) = t := by
        funext x; simp only [update_apply]; split_ifs <;> simp_all
      rw [this]; exact .loopStop hk
    | succ k ih =>
      intro t hk
      refine .loopStep (by omega) (.seq (.dec src t) (.seq (.inc dst _) (.inc tmp _))) ?_
      convert ih _ ?hk using 1
      · funext x; simp only [update_apply]; split_ifs <;> simp_all <;> omega
      · simp [update_apply, h1, h2, hk]
  refine .seq (key _ s rfl) ?_
  convert runs_moveAdd (Ne.symm h2) _ using 1
  funext x; simp only [update_apply]; split_ifs <;> simp_all <;> omega

/-! ## Especificación: calcular una función parcial -/

/-- `P` calcula `f` (aridad `n`): con la entrada en los registros `0, …, n-1` y los registros
`n, …, N-1` en cero, `P` termina sii `f v` está definida, y entonces sólo cambia el registro `n`,
que pasa a valer el resultado. Los registros `≥ N` son arbitrarios (y quedan intactos). -/
def Computes (n : ℕ) (f : List.Vector ℕ n →. ℕ) (P : Prog) : Prop :=
  ∃ N, ∀ (v : List.Vector ℕ n) (s : Regs), (∀ i : Fin n, s i = v.get i) →
    (∀ r, n ≤ r → r < N → s r = 0) →
    ∀ s', Runs P s s' ↔ ∃ y ∈ f v, s' = update s n y

/-- Renombre para "llamar" a un programa: entradas en `inp 0, …, inp (n-1)`, salida en `out`, y
registros auxiliares desplazados a partir de `H`. -/
def callMap (n : ℕ) (inp : ℕ → ℕ) (out H : ℕ) (r : ℕ) : ℕ :=
  if r < n then inp r else if r = n then out else H + r

theorem callMap_injective {n : ℕ} {inp : ℕ → ℕ} {out H : ℕ}
    (hinj : ∀ i j, i < n → j < n → inp i = inp j → i = j) (hlt : ∀ i < n, inp i < H)
    (hout : out < H) (hne : ∀ i < n, inp i ≠ out) : Injective (callMap n inp out H) := by
  intro a b h
  simp only [callMap] at h
  split_ifs at h with ha hb hb' hb hb' ha' hb hb' ha' hb hb'
  all_goals first
    | omega
    | exact hinj _ _ ‹_› ‹_› h
    | (have := hlt _ ‹_›; omega)
    | (have := hlt _ ‹_›; have := hne _ ‹_›; omega)
    | (have := hne _ ‹_›; omega)

theorem callMap_self {n : ℕ} {inp : ℕ → ℕ} {out H : ℕ} : callMap n inp out H n = out := by
  simp [callMap]

/-- Llamar a un programa que calcula `f`, con entradas/salida/auxiliares reubicados. -/
theorem Computes.call {n : ℕ} {f : List.Vector ℕ n →. ℕ} {P : Prog} (hP : Computes n f P) :
    ∃ N, ∀ (inp : ℕ → ℕ) (out H : ℕ), (∀ i j, i < n → j < n → inp i = inp j → i = j) →
      (∀ i < n, inp i < H) → out < H → (∀ i < n, inp i ≠ out) →
      ∀ (v : List.Vector ℕ n) (s : Regs), (∀ i : Fin n, s (inp i) = v.get i) → s out = 0 →
        (∀ r, H ≤ r → r < H + N → s r = 0) →
        ∀ s', Runs (P.rename (callMap n inp out H)) s s' ↔ ∃ y ∈ f v, s' = update s out y := by
  obtain ⟨N, hN⟩ := hP
  refine ⟨N, fun inp out H hinj hlt hout hne v s hin hs0 hz s' => ?_⟩
  have hσ := callMap_injective hinj hlt hout hne
  have key := hN v (s ∘ callMap n inp out H)
    (by intro i; simp [callMap, i.isLt, hin])
    (by
      intro r h1 h2
      simp only [comp_apply, callMap]
      split_ifs with h3 h4
      · omega
      · exact hs0
      · exact hz _ (by omega) (by omega))
  constructor
  · intro h
    obtain ⟨h1, e⟩ := runs_of_rename hσ P s s' h
    obtain ⟨y, hy, hy'⟩ := (key _).1 h1
    refine ⟨y, hy, ?_⟩
    rw [e, hy', extend_update hσ, callMap_self]
  · rintro ⟨y, hy, rfl⟩
    have := ((key _).2 ⟨y, hy, rfl⟩).rename hσ s rfl
    rwa [extend_update hσ, callMap_self] at this

/-! ## Programas "mortales": sólo bucles `for`

Un programa mortal no usa `addc` y usa bucles de la forma `while r ≠ 0 do (r := r - 1; q)` con `q` sin tocar `r`
(o `clear r`). Compilado, se detiene desde *cualquier* configuración intermedia (ver
`Conway.Prog.exits_compile`). -/

/-- `p` menciona el registro `r`. -/
def Uses (r : ℕ) : Prog → Prop
  | skip => False
  | inc r' => r' = r
  | dec r' => r' = r
  | addc r' _ => r' = r
  | seq p q => Uses r p ∨ Uses r q
  | loop r' p => r' = r ∨ Uses r p

theorem uses_rename {σ : ℕ → ℕ} {r' : ℕ} : ∀ {p : Prog}, (p.rename σ).Uses r' → ∃ r, p.Uses r ∧ σ r = r'
  | skip, h => h.elim
  | inc r, h => ⟨r, rfl, h⟩
  | dec r, h => ⟨r, rfl, h⟩
  | addc r _, h => ⟨r, rfl, h⟩
  | seq p q, h => by
    rcases h with h | h
    · obtain ⟨r, h1, h2⟩ := uses_rename h; exact ⟨r, .inl h1, h2⟩
    · obtain ⟨r, h1, h2⟩ := uses_rename h; exact ⟨r, .inr h1, h2⟩
  | loop r p, h => by
    rcases h with h | h
    · exact ⟨r, .inl rfl, h⟩
    · obtain ⟨r, h1, h2⟩ := uses_rename h; exact ⟨r, .inr h1, h2⟩

/-- Programas con sólo bucles `for` (mortales). -/
inductive Mortal : Prog → Prop
  | skip : Mortal skip
  | inc (r) : Mortal (inc r)
  | dec (r) : Mortal (dec r)
  | seq {p q} : Mortal p → Mortal q → Mortal (seq p q)
  | clear (r) : Mortal (loop r (dec r))
  | forLoop {r q} : Mortal q → ¬ q.Uses r → Mortal (loop r (seq (dec r) q))

theorem Mortal.rename {σ : ℕ → ℕ} (hσ : Injective σ) {p : Prog} (h : p.Mortal) :
    (p.rename σ).Mortal := by
  induction h with
  | skip => exact .skip
  | inc r => exact .inc _
  | dec r => exact .dec _
  | seq _ _ ih1 ih2 => exact .seq ih1 ih2
  | clear r => exact .clear _
  | @forLoop r q _ hu ih =>
    refine .forLoop ih fun h => ?_
    obtain ⟨r', h1, h2⟩ := uses_rename h
    exact hu (hσ h2 ▸ h1)

/-- Cambia la constante de todas las instrucciones `addc` por `m`. -/
def setK (m : ℕ) : Prog → Prog
  | skip => skip
  | inc r => inc r
  | dec r => dec r
  | addc r _ => addc r m
  | seq p q => seq (setK m p) (setK m q)
  | loop r p => loop r (setK m p)

/-- Los programas mortales no usan `addc`. -/
theorem Mortal.setK {p : Prog} (h : p.Mortal) (m : ℕ) : p.setK m = p := by
  induction h with
  | skip => rfl
  | inc => rfl
  | dec => rfl
  | seq _ _ ih1 ih2 => simp [Prog.setK, ih1, ih2]
  | clear => rfl
  | forLoop _ _ ih => simp [Prog.setK, ih]

theorem mortal_moveAdd {src dst : ℕ} (h : src ≠ dst) : (moveAdd src dst).Mortal :=
  .forLoop (.inc _) fun e => h e.symm

theorem mortal_copy {src dst tmp : ℕ} (h1 : src ≠ dst) (h2 : src ≠ tmp) (h3 : dst ≠ tmp) :
    (copy src dst tmp).Mortal :=
  .seq (.forLoop (.seq (.inc _) (.inc _)) (by simp only [Uses]; omega))
    (mortal_moveAdd (Ne.symm h2))

end Prog

end Conway
