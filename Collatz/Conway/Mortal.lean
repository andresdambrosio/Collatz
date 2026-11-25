import Collatz.Conway.Minsky

/-!
# Programas mortales: salen de su código desde cualquier configuración

Para el teorema de Kurtz–Simon ("¿toda órbita llega a 1?") hay que controlar la máquina desde
configuraciones *arbitrarias*, no sólo desde el arranque. Un programa `Prog.Mortal` (sólo bucles
`for`) tiene esa propiedad: compilado en la dirección `b`, desde cualquier contador de programa dentro
de su código y con registros cualesquiera, llega al final de su código (`exits_compile`), sin tocar
los registros que no menciona.
-/

namespace Conway

open Function

namespace Machine

/-- `c'` se alcanza desde `c`, y los registros fuera de `U` no cambian. -/
def Steps (M : Machine) (U : ℕ → Prop) (c c' : Cfg) : Prop :=
  (∃ k, (M.step)^[k] c = c') ∧ ∀ r, ¬ U r → c'.regs r = c.regs r

theorem Steps.refl (M : Machine) (U : ℕ → Prop) (c : Cfg) : Steps M U c c :=
  ⟨⟨0, rfl⟩, fun _ _ => rfl⟩

theorem Steps.trans {M : Machine} {U : ℕ → Prop} {c₁ c₂ c₃ : Cfg} (h₁ : Steps M U c₁ c₂)
    (h₂ : Steps M U c₂ c₃) : Steps M U c₁ c₃ := by
  obtain ⟨⟨k₁, e₁⟩, p₁⟩ := h₁
  obtain ⟨⟨k₂, e₂⟩, p₂⟩ := h₂
  exact ⟨⟨k₂ + k₁, by rw [iterate_add_apply, e₁, e₂]⟩, fun r hr => (p₂ r hr).trans (p₁ r hr)⟩

theorem Steps.mono {M : Machine} {U V : ℕ → Prop} {c c' : Cfg} (h : Steps M U c c')
    (hUV : ∀ r, U r → V r) : Steps M V c c' :=
  ⟨h.1, fun r hr => h.2 r fun hu => hr (hUV r hu)⟩

theorem Steps.one {M : Machine} {U : ℕ → Prop} {pc : ℕ} {s : Regs} {x : Instr}
    (h : M[pc]? = some x) (hx : ∀ r, ¬ U r → (x.exec s).regs r = s r) :
    Steps M U ⟨pc, s⟩ (x.exec s) :=
  ⟨⟨1, by simp [step, h]⟩, hx⟩

theorem Steps.inc {M : Machine} {U : ℕ → Prop} {pc r j : ℕ} {s : Regs}
    (h : M[pc]? = some (.inc r j)) (hr : U r) :
    Steps M U ⟨pc, s⟩ ⟨j, update s r (s r + 1)⟩ :=
  Steps.one h fun r' hr' => update_of_ne (fun e => hr' (by rw [e]; exact hr)) _ _

theorem Steps.addc {M : Machine} {U : ℕ → Prop} {pc r k j : ℕ} {s : Regs}
    (h : M[pc]? = some (.addc r k j)) (hr : U r) :
    Steps M U ⟨pc, s⟩ ⟨j, update s r (s r + k)⟩ :=
  Steps.one h fun r' hr' => update_of_ne (fun e => hr' (by rw [e]; exact hr)) _ _

theorem Steps.decjz_zero {M : Machine} {U : ℕ → Prop} {pc r j k : ℕ} {s : Regs}
    (h : M[pc]? = some (.decjz r j k)) (h0 : s r = 0) : Steps M U ⟨pc, s⟩ ⟨k, s⟩ := by
  have := Steps.one (U := U) (s := s) h fun r' _ => by simp [Instr.exec, h0]
  simpa [Instr.exec, h0] using this

theorem Steps.decjz_pos {M : Machine} {U : ℕ → Prop} {pc r j k : ℕ} {s : Regs}
    (h : M[pc]? = some (.decjz r j k)) (hr : U r) (h0 : s r ≠ 0) :
    Steps M U ⟨pc, s⟩ ⟨j, update s r (s r - 1)⟩ := by
  have := Steps.one (U := U) (s := s) h fun r' hr' => by
    simp only [Instr.exec, h0, ↓reduceIte]; exact update_of_ne (fun e => hr' (by rw [e]; exact hr)) _ _
  simpa [Instr.exec, h0] using this

theorem Steps.decjz_same {M : Machine} {U : ℕ → Prop} {pc r j : ℕ} {s : Regs}
    (h : M[pc]? = some (.decjz r j j)) (hr : U r) :
    Steps M U ⟨pc, s⟩ ⟨j, update s r (s r - 1)⟩ := by
  have := Steps.one (U := U) (s := s) h fun r' hr' => by
    rw [Prog.exec_decjz_same]; exact update_of_ne (fun e => hr' (by rw [e]; exact hr)) _ _
  rwa [Prog.exec_decjz_same] at this

/-- Desde cualquier contador de programa en `[b, e]` se llega a `e`, cambiando sólo registros
de `U`. -/
def Exits (M : Machine) (U : ℕ → Prop) (b e : ℕ) : Prop :=
  ∀ c : Cfg, b ≤ c.pc → c.pc ≤ e → ∃ c', Steps M U c c' ∧ c'.pc = e

theorem Exits.mono {M : Machine} {U V : ℕ → Prop} {b e : ℕ} (h : Exits M U b e)
    (hUV : ∀ r, U r → V r) : Exits M V b e := fun c h1 h2 =>
  let ⟨c', a, hc'⟩ := h c h1 h2; ⟨c', a.mono hUV, hc'⟩

theorem Exits.seq {M : Machine} {U : ℕ → Prop} {b e₁ e₂ : ℕ} (h₁ : Exits M U b e₁)
    (h₂ : Exits M U e₁ e₂) (hle : e₁ ≤ e₂) : Exits M U b e₂ := by
  intro c hlo hhi
  by_cases h : c.pc ≤ e₁
  · obtain ⟨c1, a1, e1⟩ := h₁ c hlo h
    obtain ⟨c2, a2, e2⟩ := h₂ c1 (by omega) (by omega)
    exact ⟨c2, a1.trans a2, e2⟩
  · exact h₂ c (by omega) hhi

theorem exits_addc {M : Machine} {U : ℕ → Prop} {b r k : ℕ} (h : M[b]? = some (.addc r k (b + 1)))
    (hr : U r) : Exits M U b (b + 1) := by
  intro c hlo hhi
  obtain ⟨pc, s⟩ := c
  simp only at hlo hhi
  by_cases e : pc = b
  · subst e; exact ⟨_, Steps.addc h hr, rfl⟩
  · exact ⟨_, Steps.refl _ _ _, by simp; omega⟩

end Machine

namespace Prog

open Machine

/-- El bucle `for`: `while r ≠ 0 do (r := r - 1; q)` con `q` sin tocar `r`. -/
theorem exits_forLoop {M : Machine} {b r : ℕ} {q : Prog}
    (hc : M.CodeAt b (compile b (loop r (seq (dec r) q))))
    (ihq : ∀ b', M.CodeAt b' (compile b' q) → Exits M (fun r' => q.Uses r') b' (b' + len q))
    (hqr : ¬ q.Uses r) :
    Exits M (fun r' => (loop r (seq (dec r) q)).Uses r') b (b + len (loop r (seq (dec r) q))) := by
  set U : ℕ → Prop := fun r' => (loop r (seq (dec r) q)).Uses r' with hU
  have hUr : U r := by simp [U, Uses]
  have hUq : ∀ r', q.Uses r' → U r' := fun r' h => by simp [U, Uses, h]
  obtain ⟨h0, h1, hbody, h3, h4⟩ := hc.loop
  have h2 : M[b + 2]? = some (.decjz r (b + 3) (b + 3)) := by
    simpa [compile] using hbody.left.single
  have hcq : M.CodeAt (b + 3) (compile (b + 3) q) := by
    simpa [compile, len, add_assoc] using hbody.right
  have exq := ihq (b + 3) hcq
  have hlen : len (seq (dec r) q) = len q + 1 := by simp [len]; omega
  rw [hlen] at h0 h3 h4
  rw [show len (loop r (seq (dec r) q)) = len q + 1 + 4 by simp [len]; omega]
  -- desde la cabeza `b`, por inducción en el valor de `r`
  have head : ∀ v s, s r = v → ∃ c', Steps M U ⟨b, s⟩ c' ∧ c'.pc = b + (len q + 1 + 4) := by
    intro v
    induction v using Nat.strong_induction_on with
    | _ v ih =>
    intro s hv
    by_cases hv0 : v = 0
    · exact ⟨_, Steps.decjz_zero h0 (by omega), by dsimp only; omega⟩
    have a1 := Steps.decjz_pos (U := U) (s := s) h0 hUr (by omega)
    have a2 := Steps.inc (U := U) (s := update s r (s r - 1)) h1 hUr
    have a3 := Steps.decjz_same (U := U) (s := update (update s r (s r - 1)) r
      (update s r (s r - 1) r + 1)) h2 hUr
    set s3 := update (update (update s r (s r - 1)) r (update s r (s r - 1) r + 1)) r
      (update (update s r (s r - 1)) r (update s r (s r - 1) r + 1) r - 1) with hs3
    have hs3r : s3 r = v - 1 := by simp [s3]; omega
    obtain ⟨⟨pc4, s4⟩, a4, hpc4⟩ := exq ⟨b + 3, s3⟩ le_rfl (by simp)
    simp only at hpc4; subst hpc4
    have hs4r : s4 r = v - 1 := by
      have := a4.2 r hqr; simp only at this; rw [this]; exact hs3r
    have a5 := Steps.inc (U := U) (s := s4)
      (show M[b + 3 + len q]? = _ by rw [show b + 3 + len q = b + (len q + 1) + 2 by omega]; exact h3)
      hUr
    have a6 := Steps.decjz_same (U := U) (s := update s4 r (s4 r + 1)) h4 hUr
    obtain ⟨c', a7, hc'⟩ := ih (v - 1) (by omega)
      (update (update s4 r (s4 r + 1)) r (update s4 r (s4 r + 1) r - 1)) (by simp [hs4r])
    exact ⟨c', a1.trans (a2.trans (a3.trans ((a4.mono hUq).trans (a5.trans (a6.trans a7))))),
      hc'⟩
  have tail3 : ∀ s, ∃ c', Steps M U ⟨b + (len q + 1) + 3, s⟩ c' ∧
      c'.pc = b + (len q + 1 + 4) := by
    intro s
    obtain ⟨c', a, hc'⟩ := head _ _ rfl
    exact ⟨c', (Steps.decjz_same (s := s) h4 hUr).trans a, hc'⟩
  have inq : ∀ c : Cfg, b + 3 ≤ c.pc → c.pc ≤ b + 3 + len q → ∃ c', Steps M U c c' ∧
      c'.pc = b + (len q + 1 + 4) := by
    intro c hlo hhi
    obtain ⟨⟨pc4, s4⟩, a4, hpc4⟩ := exq c hlo hhi
    simp only at hpc4; subst hpc4
    have a5 := Steps.inc (U := U) (s := s4)
      (show M[b + 3 + len q]? = _ by rw [show b + 3 + len q = b + (len q + 1) + 2 by omega]; exact h3)
      hUr
    obtain ⟨c', a, hc'⟩ := tail3 (update s4 r (s4 r + 1))
    exact ⟨c', (a4.mono hUq).trans (a5.trans a), hc'⟩
  have at2 : ∀ s, ∃ c', Steps M U ⟨b + 2, s⟩ c' ∧ c'.pc = b + (len q + 1 + 4) := by
    intro s
    obtain ⟨c', a, hc'⟩ := inq ⟨b + 3, update s r (s r - 1)⟩ le_rfl (by simp)
    exact ⟨c', (Steps.decjz_same h2 hUr).trans a, hc'⟩
  intro c hlo hhi
  obtain ⟨pc, s⟩ := c
  simp only at hlo hhi
  by_cases e0 : pc = b
  · subst e0; exact head _ s rfl
  by_cases e1 : pc = b + 1
  · subst e1
    obtain ⟨c', a, hc'⟩ := at2 (update s r (s r + 1))
    exact ⟨c', (Steps.inc h1 hUr).trans a, hc'⟩
  by_cases e2 : pc = b + 2
  · subst e2; exact at2 s
  by_cases e3 : pc ≤ b + 3 + len q
  · exact inq ⟨pc, s⟩ (by simp; omega) e3
  by_cases e4 : pc = b + (len q + 1) + 3
  · subst e4; exact tail3 s
  · exact ⟨⟨pc, s⟩, Steps.refl _ _ _, by simp; omega⟩

/-- **Mortalidad.** Un programa mortal, compilado en `b`, llega al final de su código desde
cualquier contador de programa dentro de él y con registros cualesquiera, cambiando sólo los
registros que menciona. -/
theorem exits_compile {p : Prog} (hp : p.Mortal) :
    ∀ (M : Machine) (b : ℕ), M.CodeAt b (compile b p) →
      Exits M (fun r => p.Uses r) b (b + len p) := by
  induction hp with
  | skip =>
    intro M b _ c hlo hhi
    have : len skip = 0 := rfl
    exact ⟨c, Steps.refl _ _ _, by omega⟩
  | inc r =>
    intro M b hc c hlo hhi
    obtain ⟨pc, s⟩ := c
    simp only [len] at hlo hhi
    by_cases e : pc = b
    · subst e; exact ⟨_, Steps.inc hc.single (by simp [Uses]), by simp [len]⟩
    · exact ⟨_, Steps.refl _ _ _, by simp [len]; omega⟩
  | dec r =>
    intro M b hc c hlo hhi
    obtain ⟨pc, s⟩ := c
    simp only [len] at hlo hhi
    by_cases e : pc = b
    · subst e; exact ⟨_, Steps.decjz_same hc.single (by simp [Uses]), by simp [len]⟩
    · exact ⟨_, Steps.refl _ _ _, by simp [len]; omega⟩
  | @seq p q _ _ ihp ihq =>
    intro M b hc c hlo hhi
    have hc2 := hc.right
    rw [length_compile] at hc2
    have ep := ihp M b hc.left
    have eq := ihq M _ hc2
    have hpU : ∀ r, p.Uses r → (seq p q).Uses r := fun r h => Or.inl h
    have hqU : ∀ r, q.Uses r → (seq p q).Uses r := fun r h => Or.inr h
    simp only [len] at hhi ⊢
    by_cases hle : c.pc ≤ b + len p
    · obtain ⟨c1, a1, h1⟩ := ep c hlo hle
      obtain ⟨c2, a2, h2⟩ := eq c1 (by omega) (by omega)
      exact ⟨c2, (a1.mono hpU).trans (a2.mono hqU), by omega⟩
    · obtain ⟨c2, a2, h2⟩ := eq c (by omega) (by omega)
      exact ⟨c2, a2.mono hqU, by omega⟩
  | clear r =>
    intro M b hc
    have hc' : M.CodeAt b (compile b (loop r (seq (dec r) skip))) := by
      simpa [compile, len] using hc
    have := exits_forLoop hc' (fun b' _ c hlo hhi => ⟨c, Steps.refl _ _ _, by
      have : len skip = 0 := rfl; omega⟩) (by simp [Uses])
    intro c hlo hhi
    obtain ⟨c', a, h⟩ := this c hlo (by simpa [len] using hhi)
    exact ⟨c', a.mono fun r' h => by simpa [Uses] using h, by simpa [len] using h⟩
  | @forLoop r q _ hqr ihq =>
    intro M b hc
    exact exits_forLoop hc (ihq M) hqr

end Prog

end Conway
