import Collatz.Conway.Mortal
import Collatz.Conway.Compile

/-!
# El programa externo de Kurtz–Simon

Dado un programa mortal `C` que calcula una función total `f m x` (entradas en los registros 0 y 1,
salida en el 2), el programa

  `outer C N m`:  `etapa; while r₂ ≠ 0 do (r₁ := r₁ + 1; etapa)`,
  `etapa`:        `r₀ := 0; r₂, …, r_{N+1} := 0; r₀ := r₀ + m; C`

recorre `x = r₁, r₁ + 1, …` hasta encontrar `f m x = 0`. Cada etapa recarga `m` (con una sola
instrucción `addc`, para que `m` quede en la tabla y no en los registros) y limpia los auxiliares;
por eso, aunque se arranque en una configuración arbitraria, a lo sumo la primera vuelta "miente".

**Teorema** (`outer_mortal_iff`): la máquina de `outer C N m` se detiene desde *toda* configuración
sii `∀ x, ∃ x' ≥ x, f m x' = 0`; si no, hay una configuración limpia desde la que no se detiene.
-/

namespace Conway

open Function Prog Machine

/-- `r₀ := 0` y `r₂, …, r_{N+1} := 0`. -/
def clr (N : ℕ) : Prog := .seq (clear 0) (seqUpTo N fun j => clear (2 + j))

/-- Una etapa: limpiar, cargar `m` en `r₀`, calcular `r₂ := f r₀ r₁`. -/
def stage (C : Prog) (N m : ℕ) : Prog := .seq (clr N) (.seq (.addc 0 m) C)

/-- El cuerpo del bucle externo. -/
def obody (C : Prog) (N m : ℕ) : Prog := .seq (.inc 1) (stage C N m)

/-- El programa externo. -/
def outer (C : Prog) (N m : ℕ) : Prog := .seq (stage C N m) (.loop 2 (obody C N m))

theorem mortal_clr (N : ℕ) : (clr N).Mortal :=
  .seq (.clear _) (mortal_seqUpTo (fun _ => .clear _) N)

/-- Una etapa sale de su código desde cualquier configuración. -/
theorem exits_stage {C : Prog} (hC : C.Mortal) (N m : ℕ) {M : Machine} {b : ℕ}
    (hc : M.CodeAt b (compile b (stage C N m))) :
    Exits M (fun _ => True) b (b + len (stage C N m)) := by
  have h1 := (exits_compile (mortal_clr N) M b hc.left).mono fun _ _ => trivial
  have hc2 := hc.right
  rw [length_compile] at hc2
  have h2 : Exits M (fun _ => True) (b + len (clr N)) (b + len (clr N) + 1) :=
    exits_addc (by simpa [compile] using hc2.left.single) trivial
  have hc3 := hc2.right
  simp only [length_compile, compile, List.length_singleton, len] at hc3
  have h3 := (exits_compile hC M _ hc3).mono fun _ _ => trivial
  have e : b + len (stage C N m) = b + len (clr N) + 1 + len C := by
    simp [stage, len]; omega
  rw [e]
  exact h1.seq (h2.seq h3 (by omega)) (by omega)

/-- El cuerpo del bucle externo sale de su código desde cualquier configuración. -/
theorem exits_obody {C : Prog} (hC : C.Mortal) (N m : ℕ) {M : Machine} {b : ℕ}
    (hc : M.CodeAt b (compile b (obody C N m))) :
    Exits M (fun _ => True) b (b + len (obody C N m)) := by
  have h1 := (exits_compile (.inc 1) M b hc.left).mono fun _ _ => trivial
  have hc2 := hc.right
  rw [length_compile] at hc2
  have h2 := exits_stage hC N m hc2
  have e : b + len (obody C N m) = b + len (inc 1) + len (stage C N m) := by
    simp [obody, len]; omega
  rw [e]
  exact h1.seq h2 (by omega)

section

variable {C : Prog} {N : ℕ} {f : ℕ → ℕ → ℕ}
  (hC : ∀ s : Regs, (∀ r, 2 ≤ r → r < N → s r = 0) → Runs C s (update s 2 (f (s 0) (s 1))))
include hC

theorem runs_stage (m : ℕ) (s : Regs) :
    ∃ s', Runs (stage C N m) s s' ∧ s' 1 = s 1 ∧ s' 2 = f m (s 1) := by
  set t : Regs := fun r => if 2 ≤ r ∧ r < 2 + N then 0 else update s 0 0 r with ht
  have h1 : Runs (clr N) s t := .seq (runs_clear 0 s) (runs_clears 2 N _)
  have ht0 : t 0 = 0 := by simp [t]
  have ht1 : t 1 = s 1 := by simp [t]
  have h2 := hC (update t 0 (t 0 + m)) (by
    intro r hr1 hr2; simp only [t, update_apply]; split_ifs <;> omega)
  refine ⟨_, .seq h1 (.seq (.addc 0 m t) h2), ?_, ?_⟩
  · simp [update_apply, ht1]
  · simp [ht0, ht1]

theorem runs_obody (m : ℕ) (s : Regs) :
    ∃ s', Runs (obody C N m) s s' ∧ s' 1 = s 1 + 1 ∧ s' 2 = f m (s 1 + 1) := by
  obtain ⟨s', h, e1, e2⟩ := runs_stage hC m (update s 1 (s 1 + 1))
  exact ⟨s', .seq (.inc 1 s) h, by simpa using e1, by simpa using e2⟩

/-- El bucle termina sii `r₂ = 0` o algún `x' > r₁` anula `f m`. -/
theorem loop_runs_iff (m : ℕ) (s : Regs) :
    (∃ s', Runs (.loop 2 (obody C N m)) s s') ↔ (s 2 = 0 ∨ ∃ x' > s 1, f m x' = 0) := by
  constructor
  · rintro ⟨s', h⟩
    generalize hq : Prog.loop 2 (obody C N m) = q at h
    induction h with
    | loopStop hr => cases hq; exact .inl hr
    | @loopStep r p s t u hr h1 _ _ ih2 =>
      cases hq
      obtain ⟨t', ht', e1, e2⟩ := runs_obody hC m s
      obtain rfl := h1.det ht'
      rcases ih2 rfl with h | ⟨x', hx', hf⟩
      · exact .inr ⟨s 1 + 1, by omega, e2 ▸ h⟩
      · exact .inr ⟨x', by omega, hf⟩
    | _ => cases hq
  · intro h
    suffices ∀ d (s : Regs), (s 2 = 0 ∨ ∃ x', s 1 < x' ∧ x' ≤ s 1 + d ∧ f m x' = 0) →
        ∃ s', Runs (.loop 2 (obody C N m)) s s' by
      rcases h with h | ⟨x', hx', hf⟩
      · exact this 0 s (.inl h)
      · exact this (x' - s 1) s (.inr ⟨x', hx', by omega, hf⟩)
    intro d
    induction d with
    | zero =>
      intro s h
      rcases h with h | ⟨x', h1, h2, -⟩
      · exact ⟨s, .loopStop h⟩
      · omega
    | succ d ih =>
      intro s h
      by_cases h0 : s 2 = 0
      · exact ⟨s, .loopStop h0⟩
      obtain ⟨t, ht, e1, e2⟩ := runs_obody hC m s
      rcases h with h | ⟨x', h1, h2, hf⟩
      · exact absurd h h0
      obtain ⟨u, hu⟩ := ih t (by
        by_cases hx : x' = s 1 + 1
        · exact .inl (by rw [e2, ← hx, hf])
        · exact .inr ⟨x', by omega, by omega, hf⟩)
      exact ⟨u, .loopStep h0 ht hu⟩

variable (hCm : C.Mortal)
include hCm

/-- Desde cualquier configuración, la máquina se detiene o llega a la cabeza del bucle. -/
theorem outer_reach_head (m : ℕ) (c : Cfg) :
    (outer C N m).toMachine.Halted c ∨
      ∃ s, Steps (outer C N m).toMachine (fun _ => True) c ⟨len (stage C N m), s⟩ := by
  set M := (outer C N m).toMachine
  set lS := len (stage C N m)
  set lB := len (obody C N m)
  have hc := (outer C N m).codeAt_toMachine
  have hcS : M.CodeAt 0 (compile 0 (stage C N m)) := hc.left
  have hcL : M.CodeAt lS (compile lS (.loop 2 (obody C N m))) := by
    have := hc.right; simpa [length_compile] using this
  obtain ⟨h0, h1, hbody, h3, h4⟩ := hcL.loop
  have hL : M.length = lS + (lB + 4) := by
    simp [M, Prog.toMachine, length_compile, outer, len, lS, lB]
  have exS := exits_stage hCm N m hcS
  have exB := exits_obody hCm N m hbody
  have T : ∀ r, (fun _ : ℕ => True) r := fun _ => trivial
  have back3 : ∀ s, ∃ s', Steps M (fun _ => True) ⟨lS + lB + 3, s⟩ ⟨lS, s'⟩ :=
    fun s => ⟨_, Steps.decjz_same h4 trivial⟩
  have back2 : ∀ s, ∃ s', Steps M (fun _ => True) ⟨lS + lB + 2, s⟩ ⟨lS, s'⟩ := by
    intro s
    obtain ⟨s', a⟩ := back3 (update s 2 (s 2 + 1))
    exact ⟨s', (Steps.inc h3 trivial).trans a⟩
  have inB : ∀ c : Cfg, lS + 2 ≤ c.pc → c.pc ≤ lS + 2 + lB →
      ∃ s', Steps M (fun _ => True) c ⟨lS, s'⟩ := by
    intro c hlo hhi
    obtain ⟨⟨pc1, s1⟩, a1, e1⟩ := exB c hlo hhi
    simp only at e1; subst e1
    obtain ⟨s', a⟩ := back2 s1
    exact ⟨s', (a1.mono fun r _ => T r).trans (by rwa [show lS + 2 + lB = lS + lB + 2 by omega])⟩
  obtain ⟨pc, s⟩ := c
  by_cases hp : pc ≤ lS
  · obtain ⟨⟨pc1, s1⟩, a1, e1⟩ := exS ⟨pc, s⟩ (Nat.zero_le _) (by simpa using hp)
    simp only [zero_add] at e1; subst e1
    exact .inr ⟨s1, a1.mono fun r _ => T r⟩
  by_cases hp1 : pc = lS + 1
  · subst hp1
    obtain ⟨s', a⟩ := inB ⟨lS + 2, update s 2 (s 2 + 1)⟩ le_rfl (by simp)
    exact .inr ⟨s', (Steps.inc h1 trivial).trans a⟩
  by_cases hp2 : pc ≤ lS + 2 + lB
  · exact .inr (inB ⟨pc, s⟩ (by simp; omega) hp2)
  by_cases hp3 : pc = lS + lB + 3
  · subst hp3; exact .inr (back3 s)
  · left; simp only [Halted, hL]; omega

/-- **Mortalidad del programa externo.** -/
theorem outer_mortal (m : ℕ) (h : ∀ x, ∃ x' ≥ x, f m x' = 0) (c : Cfg) :
    ∃ n, (outer C N m).toMachine.Halted (((outer C N m).toMachine.step)^[n] c) := by
  set M := (outer C N m).toMachine
  have hc := (outer C N m).codeAt_toMachine
  have hcL : M.CodeAt (len (stage C N m)) (compile (len (stage C N m))
      (.loop 2 (obody C N m))) := by
    have := hc.right; simpa [length_compile] using this
  rcases outer_reach_head hC hCm m c with hh | ⟨s, ⟨⟨k, hk⟩, -⟩⟩
  · exact ⟨0, hh⟩
  obtain ⟨x', hx', hf⟩ := h (s 1 + 1)
  obtain ⟨s', hrun⟩ := (loop_runs_iff hC m s).2 (.inr ⟨x', by omega, hf⟩)
  obtain ⟨k2, hk2⟩ := runs_compile hrun M _ hcL
  refine ⟨k2 + k, ?_⟩
  rw [iterate_add_apply, hk, hk2]
  simp [Halted, M, Prog.toMachine, length_compile, outer, len]

/-- Configuración limpia en la cabeza del bucle con `r₁ = x`, `r₂ = f m x`. -/
def headCfg (C : Prog) (N m : ℕ) (f : ℕ → ℕ → ℕ) (x : ℕ) : Cfg :=
  ⟨len (stage C N m), fun r => if r = 1 then x else if r = 2 then f m x else 0⟩

/-- **Inmortalidad.** Si `f m x' ≠ 0` para todo `x' ≥ x`, la máquina no se detiene desde la
configuración limpia `headCfg … x`. -/
theorem outer_not_halts (m x : ℕ) (h : ∀ x' ≥ x, f m x' ≠ 0) (n : ℕ) :
    ¬ (outer C N m).toMachine.Halted
      (((outer C N m).toMachine.step)^[n] (headCfg C N m f x)) := by
  intro hn
  set M := (outer C N m).toMachine
  have hc := (outer C N m).codeAt_toMachine
  have hcL : M.CodeAt (len (stage C N m)) (compile (len (stage C N m))
      (.loop 2 (obody C N m))) := by
    have := hc.right; simpa [length_compile] using this
  obtain ⟨s', -, hrun, -⟩ := halts_compile _ M _ hcL n _ hn
  rcases (loop_runs_iff hC m _).1 ⟨s', hrun⟩ with h0 | ⟨x', hx', hf⟩
  · exact h x le_rfl (by simpa using h0)
  · exact h x' (by simp at hx'; omega) hf

end

end Conway
