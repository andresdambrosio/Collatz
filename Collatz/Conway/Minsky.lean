import Collatz.Conway.While

/-!
# De programas WHILE a máquinas de Minsky

Una máquina de Minsky es una lista de instrucciones con saltos absolutos:
* `inc r j`: suma 1 al registro `r` y salta a `j`;
* `decjz r j k`: si el registro `r` vale 0 salta a `k`; si no, le resta 1 y salta a `j`.

La máquina se detiene cuando el contador de programa sale de la lista. Compilamos cada programa
WHILE a una máquina (`Prog.compile`) y probamos que la máquina se detiene exactamente cuando el
programa termina, con los mismos registros.
-/

namespace Conway

open Function

inductive Instr
  | inc (r j : ℕ)
  | decjz (r j k : ℕ)

/-- Una máquina de Minsky. -/
abbrev Machine := List Instr

/-- Configuración: contador de programa y registros. -/
structure Cfg where
  pc : ℕ
  regs : Regs

namespace Instr

/-- Ejecución de una instrucción. -/
def exec : Instr → Regs → Cfg
  | inc r j, s => ⟨j, update s r (s r + 1)⟩
  | decjz r j k, s => if s r = 0 then ⟨k, s⟩ else ⟨j, update s r (s r - 1)⟩

end Instr

namespace Machine

/-- Un paso (las configuraciones detenidas son puntos fijos). -/
def step (M : Machine) (c : Cfg) : Cfg :=
  match M[c.pc]? with
  | some i => i.exec c.regs
  | none => c

/-- Detenida: el contador de programa está fuera de la lista. -/
def Halted (M : Machine) (c : Cfg) : Prop := M.length ≤ c.pc

theorem step_of_halted {M : Machine} {c : Cfg} (h : M.Halted c) : M.step c = c := by
  simp [step, List.getElem?_eq_none h]

theorem iterate_halted {M : Machine} {c : Cfg} (h : M.Halted c) (n : ℕ) : (M.step)^[n] c = c :=
  iterate_fixed (step_of_halted h) n

/-- Si después de `n` pasos la máquina está detenida y después de `m` no, entonces `m < n`. -/
theorem lt_of_halted {M : Machine} {c : Cfg} {n m : ℕ} (hn : M.Halted ((M.step)^[n] c))
    (hm : ¬ M.Halted ((M.step)^[m] c)) : m < n := by
  by_contra hle
  push Not at hle
  apply hm
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hle
  rw [add_comm, iterate_add_apply, iterate_halted hn]
  exact hn

/-- `cd` está escrita en `M` a partir de la dirección `b`. -/
def CodeAt (M : Machine) (b : ℕ) (cd : List Instr) : Prop := ∀ i < cd.length, M[b + i]? = cd[i]?

theorem CodeAt.left {M : Machine} {b : ℕ} {c₁ c₂ : List Instr} (h : M.CodeAt b (c₁ ++ c₂)) :
    M.CodeAt b c₁ := fun i hi => by
  rw [h i (by simp; omega), List.getElem?_append_left hi]

theorem CodeAt.right {M : Machine} {b : ℕ} {c₁ c₂ : List Instr} (h : M.CodeAt b (c₁ ++ c₂)) :
    M.CodeAt (b + c₁.length) c₂ := fun i hi => by
  rw [add_assoc, h _ (by simp; omega), List.getElem?_append_right (by omega)]
  simp

theorem CodeAt.single {M : Machine} {b : ℕ} {x : Instr} (h : M.CodeAt b [x]) : M[b]? = some x := by
  simpa using h 0 (by simp)

theorem CodeAt.lt_length {M : Machine} {b : ℕ} {cd : List Instr} (h : M.CodeAt b cd) (i : ℕ)
    (hi : i < cd.length) : b + i < M.length := by
  have := h i hi
  rw [List.getElem?_eq_getElem hi] at this
  exact (List.getElem?_eq_some_iff.1 this).1

theorem step_at {M : Machine} {b : ℕ} {x : Instr} (h : M[b]? = some x) (s : Regs) :
    M.step ⟨b, s⟩ = x.exec s := by
  simp [step, h]

end Machine

namespace Prog

open Machine

/-- Largo del código compilado. -/
def len : Prog → ℕ
  | skip => 0
  | inc _ => 1
  | dec _ => 1
  | seq p q => len p + len q
  | loop _ p => len p + 4

/-- Compilación a máquina de Minsky, con el código ubicado a partir de la dirección `b`.
El bucle `loop r p` ocupa `len p + 4` instrucciones:
`b: decjz r (b+1) salida`, `b+1: inc r (b+2)` (restituye `r`), el cuerpo, y
`inc r; decjz r b b` (salto incondicional a `b`). -/
def compile (b : ℕ) : Prog → List Instr
  | skip => []
  | inc r => [.inc r (b + 1)]
  | dec r => [.decjz r (b + 1) (b + 1)]
  | seq p q => compile b p ++ compile (b + len p) q
  | loop r p => [.decjz r (b + 1) (b + len p + 4)] ++ [.inc r (b + 2)] ++ compile (b + 2) p ++
      [.inc r (b + len p + 3)] ++ [.decjz r b b]

theorem length_compile : ∀ (b : ℕ) (p : Prog), (compile b p).length = len p
  | _, skip => rfl
  | _, inc _ => rfl
  | _, dec _ => rfl
  | b, seq p q => by simp [compile, len, length_compile]
  | b, loop r p => by simp [compile, len, length_compile]

theorem exec_decjz_same (r j : ℕ) (s : Regs) :
    (Instr.decjz r j j).exec s = ⟨j, update s r (s r - 1)⟩ := by
  simp only [Instr.exec]
  split_ifs with h0
  · congr 1; funext x; simp only [update_apply]; split_ifs with hx <;> simp [hx, h0]
  · rfl

theorem _root_.Conway.Machine.CodeAt.congr_addr {M : Machine} {b b' : ℕ} {cd : List Instr} (h : M.CodeAt b cd)
    (e : b = b') : M.CodeAt b' cd := e ▸ h

/-- Las cinco piezas del código de un bucle. -/
theorem _root_.Conway.Machine.CodeAt.loop {M : Machine} {b r : ℕ} {p : Prog} (hc : M.CodeAt b (compile b (loop r p))) :
    M[b]? = some (.decjz r (b + 1) (b + len p + 4)) ∧ M[b + 1]? = some (.inc r (b + 2)) ∧
      M.CodeAt (b + 2) (compile (b + 2) p) ∧ M[b + len p + 2]? = some (.inc r (b + len p + 3)) ∧
      M[b + len p + 3]? = some (.decjz r b b) := by
  simp only [compile] at hc
  refine ⟨hc.left.left.left.left.single, hc.left.left.left.right.single, ?_, ?_, ?_⟩
  · exact hc.left.left.right.congr_addr (by simp)
  · exact (hc.left.right.congr_addr (by simp [length_compile]; omega)).single
  · exact (hc.right.congr_addr (by simp [length_compile]; omega)).single

/-- Corrección (terminación ⇒ detención): si el programa termina, la máquina llega al final
de su código con los mismos registros. -/
theorem runs_compile {p : Prog} {s s' : Regs} (h : Runs p s s') :
    ∀ (M : Machine) (b : ℕ), M.CodeAt b (compile b p) →
      ∃ k, (M.step)^[k] ⟨b, s⟩ = ⟨b + len p, s'⟩ := by
  induction h with
  | skip s => intro M b _; exact ⟨0, rfl⟩
  | inc r s =>
    intro M b hc
    exact ⟨1, by simp [step_at hc.single, Instr.exec, len]⟩
  | dec r s =>
    intro M b hc
    exact ⟨1, by simp [step_at hc.single, exec_decjz_same, len]⟩
  | @seq p q s t u _ _ ih1 ih2 =>
    intro M b hc
    obtain ⟨k1, h1⟩ := ih1 M b hc.left
    have hc2 := hc.right
    rw [length_compile] at hc2
    obtain ⟨k2, h2⟩ := ih2 M _ hc2
    refine ⟨k2 + k1, ?_⟩
    rw [iterate_add_apply, h1, h2, len, add_assoc]
  | @loopStop r p s hr =>
    intro M b hc
    refine ⟨1, ?_⟩
    simp [step_at hc.loop.1, Instr.exec, hr, len, add_assoc]
  | @loopStep r p s t u hr _ _ ih1 ih2 =>
    intro M b hc
    obtain ⟨h0, h1, hbody, h3, h4⟩ := hc.loop
    obtain ⟨kb, hkb⟩ := ih1 M (b + 2) hbody
    obtain ⟨k', hk'⟩ := ih2 M b hc
    refine ⟨k' + 2 + kb + 2, ?_⟩
    have e1 : (M.step)^[2] ⟨b, s⟩ = ⟨b + 2, s⟩ := by
      simp only [iterate_succ, iterate_zero, comp_apply, id]
      rw [step_at h0, Instr.exec, if_neg hr, step_at h1, Instr.exec]
      congr 1; funext x; simp only [update_apply]; split_ifs with hx <;> simp [hx]; omega
    have e2 : (M.step)^[2] ⟨b + 2 + len p, t⟩ = ⟨b, t⟩ := by
      simp only [iterate_succ, iterate_zero, comp_apply, id]
      rw [show b + 2 + len p = b + len p + 2 by omega, step_at h3, Instr.exec, step_at h4,
        Instr.exec]
      simp
    rw [iterate_add_apply, iterate_add_apply, iterate_add_apply, e1, hkb, e2, hk']

/-- Corrección (detención ⇒ terminación): si la máquina se detiene, el programa termina, y la
máquina pasa por el final de su código con los registros finales del programa. -/
theorem halts_compile : ∀ (p : Prog) (M : Machine) (b : ℕ), M.CodeAt b (compile b p) →
    ∀ n s, M.Halted ((M.step)^[n] ⟨b, s⟩) →
      ∃ s' k, Runs p s s' ∧ k ≤ n ∧ (M.step)^[k] ⟨b, s⟩ = ⟨b + len p, s'⟩
  | skip, M, b, _, n, s, _ => ⟨s, 0, .skip s, Nat.zero_le n, by simp [len]⟩
  | inc r, M, b, hc, n, s, hn => by
    have h0 := hc.single
    have hpos : 0 < n := lt_of_halted hn (m := 0) (by
      simp only [iterate_zero, id, Halted, not_le]; exact (List.getElem?_eq_some_iff.1 h0).1)
    exact ⟨_, 1, .inc r s, hpos, by simp [step_at h0, Instr.exec, len]⟩
  | dec r, M, b, hc, n, s, hn => by
    have h0 := hc.single
    have hpos : 0 < n := lt_of_halted hn (m := 0) (by
      simp only [iterate_zero, id, Halted, not_le]; exact (List.getElem?_eq_some_iff.1 h0).1)
    exact ⟨_, 1, .dec r s, hpos, by simp [step_at h0, exec_decjz_same, len]⟩
  | seq p q, M, b, hc, n, s, hn => by
    obtain ⟨t, k1, h1, hk1, e1⟩ := halts_compile p M b hc.left n s hn
    have hc2 := hc.right
    rw [length_compile] at hc2
    have hn2 : M.Halted ((M.step)^[n - k1] ⟨b + len p, t⟩) := by
      rw [← e1, ← iterate_add_apply, Nat.sub_add_cancel hk1]; exact hn
    obtain ⟨u, k2, h2, hk2, e2⟩ := halts_compile q M _ hc2 _ t hn2
    refine ⟨u, k2 + k1, .seq h1 h2, by omega, ?_⟩
    rw [iterate_add_apply, e1, e2, len, add_assoc]
  | loop r p, M, b, hc, n, s, hn => by
    obtain ⟨h0, h1, hbody, h3, h4⟩ := hc.loop
    have hb : b < M.length := (List.getElem?_eq_some_iff.1 h0).1
    induction n using Nat.strong_induction_on generalizing s with
    | _ n ih =>
    have hpos : 0 < n := lt_of_halted hn (m := 0) (by
      simp only [iterate_zero, id, Halted, not_le]; exact hb)
    by_cases hr : s r = 0
    · exact ⟨s, 1, .loopStop hr, hpos, by simp [step_at h0, Instr.exec, hr, len, add_assoc]⟩
    · have e1 : (M.step)^[2] ⟨b, s⟩ = ⟨b + 2, s⟩ := by
        simp only [iterate_succ, iterate_zero, comp_apply, id]
        rw [step_at h0, Instr.exec, if_neg hr, step_at h1, Instr.exec]
        congr 1; funext x; simp only [update_apply]; split_ifs with hx <;> simp [hx]; omega
      have h2n : 2 ≤ n := by
        have := lt_of_halted hn (m := 1) (by
          simp only [iterate_one, Halted, not_le, step_at h0, Instr.exec, if_neg hr]
          exact (List.getElem?_eq_some_iff.1 h1).1)
        omega
      have hnb : M.Halted ((M.step)^[n - 2] ⟨b + 2, s⟩) := by
        rw [← e1, ← iterate_add_apply, Nat.sub_add_cancel h2n]; exact hn
      obtain ⟨t, kb, hrun, hkb, ekb⟩ := halts_compile p M (b + 2) hbody _ s hnb
      have e2 : (M.step)^[2] ⟨b + 2 + len p, t⟩ = ⟨b, t⟩ := by
        simp only [iterate_succ, iterate_zero, comp_apply, id]
        rw [show b + 2 + len p = b + len p + 2 by omega, step_at h3, Instr.exec, step_at h4,
          Instr.exec]
        simp
      have eb : (M.step)^[2 + kb + 2] ⟨b, s⟩ = ⟨b, t⟩ := by
        rw [iterate_add_apply, iterate_add_apply, e1, ekb, e2]
      have hlt : 2 + kb + 2 < n := lt_of_halted hn (by rw [eb]; simpa [Halted] using hb)
      have hn' : M.Halted ((M.step)^[n - (2 + kb + 2)] ⟨b, t⟩) := by
        rw [← eb, ← iterate_add_apply, Nat.sub_add_cancel hlt.le]; exact hn
      obtain ⟨u, k', hrun', hk', ek'⟩ := ih _ (by omega) t hn'
      exact ⟨u, k' + (2 + kb + 2), .loopStep hr hrun hrun', by omega, by
        rw [iterate_add_apply, eb, ek']⟩

end Prog

/-- La máquina de un programa: su código compilado desde la dirección 0. -/
def Prog.toMachine (p : Prog) : Machine := p.compile 0

theorem Prog.codeAt_toMachine (p : Prog) : p.toMachine.CodeAt 0 (p.compile 0) := by
  intro i _; simp [Prog.toMachine]

/-- La máquina se detiene sii el programa termina; al detenerse lo hace en `len p` con los
registros finales del programa. -/
theorem Prog.toMachine_halts (p : Prog) (s : Regs) :
    (∃ n, p.toMachine.Halted ((p.toMachine.step)^[n] ⟨0, s⟩)) ↔ ∃ s', Runs p s s' := by
  constructor
  · rintro ⟨n, hn⟩
    obtain ⟨s', -, h, -⟩ := halts_compile p _ 0 p.codeAt_toMachine n s hn
    exact ⟨s', h⟩
  · rintro ⟨s', h⟩
    obtain ⟨k, hk⟩ := runs_compile h _ 0 p.codeAt_toMachine
    refine ⟨k, ?_⟩
    rw [hk]; simp [Machine.Halted, Prog.toMachine, length_compile]

end Conway
