import Collatz.Conway.Minsky

/-!
# De máquinas de Minsky a FRACTRAN

Un programa FRACTRAN es una lista de fracciones `a/b` (pares `(a, b)`); un paso manda `n` a
`a · (n / b)` para la primera fracción con `b ∣ n` (si ninguna se aplica, `n` queda fijo).

Codificamos una configuración de una máquina de Minsky como
`enc (pc, e) = p_{R+pc} · ∏_{r<R} p_r ^ e r`, donde `p_k` es el `k`-ésimo primo (`p_0 = 2`): el
registro `r` vive en el exponente del primo `p_r` y el estado en el primo `p_{R+pc}`.

* `inc r j` en el estado `i` es la fracción `p_r p_{R+j} / p_{R+i}`;
* `decjz r j k` en el estado `i` son las fracciones `p_{R+j} / (p_{R+i} p_r)` y `p_{R+k} / p_{R+i}`;
* al final, `1 / p_{R+L}` (borra el estado de detención) y `p_R / 1` (arranque: si no hay ningún
  primo de estado, se entra al estado 0).

Resultado (`fractran_iff_one`, `fractran_iff_pow_two`): si el programa deja todos los registros en
cero al terminar, la órbita de `2^m` llega a `1` (equivalentemente, a una potencia de 2) sii el
programa termina con entrada `m` en el registro 0.
-/

namespace Conway

open Function

/-- Un paso de FRACTRAN. -/
def fstep (l : List (ℕ × ℕ)) (n : ℕ) : ℕ :=
  match l.find? (fun q => decide (q.2 ∣ n)) with
  | some q => q.1 * (n / q.2)
  | none => n

/-! ## Primos -/

/-- El `k`-ésimo primo (`pr 0 = 2`). -/
noncomputable def pr (k : ℕ) : ℕ := Nat.nth Nat.Prime k

theorem pr_prime (k : ℕ) : (pr k).Prime := Nat.prime_nth_prime k

theorem pr_injective : Injective pr := Nat.nth_injective Nat.infinite_setOfPred_prime

theorem pr_zero : pr 0 = 2 := Nat.nth_prime_zero_eq_two

theorem pr_pos (k : ℕ) : 0 < pr k := (pr_prime k).pos

theorem pr_dvd_pr {a b : ℕ} : pr a ∣ pr b ↔ a = b := by
  rw [Nat.prime_dvd_prime_iff_eq (pr_prime a) (pr_prime b)]
  exact pr_injective.eq_iff

/-! ## Codificación -/

/-- Parte de los registros: `∏_{r<R} p_r ^ e r`. -/
noncomputable def body (R : ℕ) (e : Regs) : ℕ := ∏ r ∈ Finset.range R, pr r ^ e r

/-- Codificación de una configuración. -/
noncomputable def enc (R : ℕ) (c : Cfg) : ℕ := pr (R + c.pc) * body R c.regs

theorem body_pos (R : ℕ) (e : Regs) : 0 < body R e :=
  Finset.prod_pos fun r _ => pow_pos (pr_pos r) _

theorem body_zero (R : ℕ) : body R (fun _ => 0) = 1 := by simp [body]

theorem not_pr_dvd_body {R k : ℕ} (e : Regs) (hk : R ≤ k) : ¬ pr k ∣ body R e := by
  intro h
  obtain ⟨r, hr, hdvd⟩ := ((pr_prime k).prime.dvd_finsetProd_iff _).1 h
  have := pr_dvd_pr.1 ((pr_prime k).dvd_of_dvd_pow hdvd)
  simp at hr; omega

theorem body_split {R r : ℕ} (hr : r < R) (e : Regs) :
    body R e = body R (update e r 0) * pr r ^ e r := by
  unfold body
  rw [← Finset.prod_erase_mul _ _ (Finset.mem_range.2 hr),
    ← Finset.prod_erase_mul _ _ (Finset.mem_range.2 hr)]
  simp only [update_self, pow_zero, mul_one]
  congr 1
  refine Finset.prod_congr rfl fun x hx => ?_
  rw [update_of_ne (Finset.ne_of_mem_erase hx)]

theorem not_pr_dvd_body_update {R r : ℕ} (e : Regs) : ¬ pr r ∣ body R (update e r 0) := by
  intro h
  obtain ⟨r', _, hdvd⟩ := ((pr_prime r).prime.dvd_finsetProd_iff _).1 h
  by_cases hr' : r' = r
  · subst hr'; simp only [update_self, pow_zero, Nat.dvd_one] at hdvd
    exact (pr_prime _).one_lt.ne' hdvd
  · rw [update_of_ne hr'] at hdvd
    exact hr' (pr_dvd_pr.1 ((pr_prime r).dvd_of_dvd_pow hdvd)).symm

theorem pr_dvd_body_iff {R r : ℕ} (hr : r < R) (e : Regs) : pr r ∣ body R e ↔ e r ≠ 0 := by
  rw [body_split hr e]
  constructor
  · intro h h0
    rw [h0, pow_zero, mul_one] at h
    exact not_pr_dvd_body_update e h
  · intro h
    exact Dvd.dvd.mul_left (dvd_pow_self _ h) _

theorem body_inc {R r : ℕ} (hr : r < R) (e : Regs) :
    body R (update e r (e r + 1)) = pr r * body R e := by
  rw [body_split hr (update e r _), body_split hr e, update_idem, update_self]
  ring

theorem body_dec {R r : ℕ} (hr : r < R) (e : Regs) (h : e r ≠ 0) :
    body R e = pr r * body R (update e r (e r - 1)) := by
  rw [body_split hr (update e r _), body_split hr e, update_idem, update_self]
  obtain ⟨k, hk⟩ := Nat.exists_eq_succ_of_ne_zero h
  rw [hk, Nat.succ_sub_one, pow_succ]; ring

theorem st_dvd_enc {R i : ℕ} (c : Cfg) : pr (R + i) ∣ enc R c ↔ i = c.pc := by
  constructor
  · intro h
    rcases (Nat.Prime.dvd_mul (pr_prime _)).1 h with h | h
    · have := pr_dvd_pr.1 h; omega
    · exact absurd h (not_pr_dvd_body _ (by omega))
  · rintro rfl; exact dvd_mul_right _ _

/-! ## Las fracciones -/

/-- Registro que usa una instrucción. -/
def Instr.reg : Instr → ℕ
  | .inc r _ => r
  | .decjz r _ _ => r

/-- Fracciones de la instrucción `x` en el estado `i`. -/
noncomputable def block (R i : ℕ) : Instr → List (ℕ × ℕ)
  | .inc r j => [(pr r * pr (R + j), pr (R + i))]
  | .decjz r j k => [(pr (R + j), pr (R + i) * pr r), (pr (R + k), pr (R + i))]

noncomputable def fracsFrom (R : ℕ) : ℕ → List Instr → List (ℕ × ℕ)
  | _, [] => []
  | i, x :: xs => block R i x ++ fracsFrom R (i + 1) xs

/-- El programa FRACTRAN de una máquina. -/
noncomputable def fracs (R : ℕ) (M : Machine) : List (ℕ × ℕ) :=
  fracsFrom R 0 M ++ [(1, pr (R + M.length)), (pr R, 1)]

theorem dvd_of_mem_block {R i : ℕ} {x : Instr} {q : ℕ × ℕ} (h : q ∈ block R i x) :
    pr (R + i) ∣ q.2 := by
  cases x <;> simp [block] at h <;> rcases h with rfl | rfl <;> simp

theorem find_block_none {R i : ℕ} (x : Instr) {n : ℕ} (h : ¬ pr (R + i) ∣ n) :
    (block R i x).find? (fun q => decide (q.2 ∣ n)) = none := by
  rw [List.find?_eq_none]
  intro q hq
  simpa using fun hd => h ((dvd_of_mem_block hq).trans hd)

/-- Un paso de la máquina, en una configuración no detenida, es un paso de FRACTRAN. -/
theorem find_block_self {R : ℕ} (c : Cfg) (x : Instr) (hx : x.reg < R) :
    ∃ q, (block R c.pc x).find? (fun q => decide (q.2 ∣ enc R c)) = some q ∧
      q.1 * (enc R c / q.2) = enc R (x.exec c.regs) := by
  have hst : 0 < pr (R + c.pc) := pr_pos _
  cases x with
  | inc r j =>
    refine ⟨(pr r * pr (R + j), pr (R + c.pc)), by simp [block, enc], ?_⟩
    simp only [enc, Instr.exec, Nat.mul_div_cancel_left _ hst]
    rw [body_inc (r := r) hx]; ring
  | decjz r j k =>
    simp only [Instr.reg] at hx
    by_cases h0 : c.regs r = 0
    · have hnd : ¬ pr (R + c.pc) * pr r ∣ enc R c := by
        intro hd
        rw [enc, Nat.mul_dvd_mul_iff_left hst, pr_dvd_body_iff hx] at hd
        exact hd h0
      have hnd' := hnd
      rw [enc] at hnd'
      refine ⟨(pr (R + k), pr (R + c.pc)), by simp [block, hnd', enc], ?_⟩
      simp only [enc, Instr.exec, h0, ↓reduceIte, Nat.mul_div_cancel_left _ hst]
    · have hd : pr (R + c.pc) * pr r ∣ enc R c := by
        rw [enc, Nat.mul_dvd_mul_iff_left hst, pr_dvd_body_iff hx]; exact h0
      refine ⟨(pr (R + j), pr (R + c.pc) * pr r), by simp [block, hd], ?_⟩
      simp only [enc, Instr.exec, h0, ↓reduceIte]
      rw [Nat.mul_div_mul_left _ _ hst, body_dec hx _ h0,
        Nat.mul_div_cancel_left _ (pr_pos r)]

theorem find_fracsFrom {R : ℕ} (c : Cfg) :
    ∀ (xs : List Instr) (i : ℕ), (∀ x ∈ xs, x.reg < R) →
      (fracsFrom R i xs).find? (fun q => decide (q.2 ∣ enc R c)) =
        if i ≤ c.pc then
          (match xs[c.pc - i]? with
            | some x => (block R c.pc x).find? (fun q => decide (q.2 ∣ enc R c))
            | none => none)
        else none
  | [], i, _ => by simp [fracsFrom]
  | x :: xs, i, hR => by
    simp only [fracsFrom, List.find?_append]
    by_cases hi : i = c.pc
    · subst hi
      obtain ⟨q, hq, -⟩ := find_block_self c x (hR x (by simp))
      simp [hq]
    · rw [find_block_none x (by rw [st_dvd_enc]; exact hi), Option.none_or,
        find_fracsFrom c xs (i + 1) (fun y hy => hR y (by simp [hy]))]
      by_cases hle : i ≤ c.pc
      · rw [if_pos (by omega), if_pos hle,
          show c.pc - i = (c.pc - (i + 1)) + 1 by omega, List.getElem?_cons_succ]
      · rw [if_neg (by omega), if_neg hle]

/-- **Simulación paso a paso.** -/
theorem fstep_enc {R : ℕ} {M : Machine} (hR : ∀ x ∈ M, x.reg < R) (c : Cfg)
    (hc : c.pc < M.length) : fstep (fracs R M) (enc R c) = enc R (M.step c) := by
  obtain ⟨q, hq, hval⟩ := find_block_self c M[c.pc] (hR _ (List.getElem_mem hc))
  have hfind : (fracs R M).find? (fun q => decide (q.2 ∣ enc R c)) = some q := by
    rw [fracs, List.find?_append, find_fracsFrom c M 0 hR, if_pos (Nat.zero_le _),
      Nat.sub_zero, List.getElem?_eq_getElem hc]
    simp [hq]
  rw [fstep, hfind]
  simp only
  rw [hval, Machine.step_at (List.getElem?_eq_getElem hc)]

/-- Detención: con todos los registros en cero, el estado final va a `1`. -/
theorem fstep_halt {R : ℕ} {M : Machine} (hR : ∀ x ∈ M, x.reg < R) (e : Regs)
    (he : ∀ r < R, e r = 0) : fstep (fracs R M) (enc R ⟨M.length, e⟩) = 1 := by
  have hb : body R e = 1 := by
    rw [← body_zero R]; unfold body
    exact Finset.prod_congr rfl fun r hr => by rw [he r (Finset.mem_range.1 hr)]
  have hfind : (fracs R M).find? (fun q => decide (q.2 ∣ enc R ⟨M.length, e⟩)) =
      some (1, pr (R + M.length)) := by
    rw [fracs, List.find?_append, find_fracsFrom _ M 0 hR, if_pos (Nat.zero_le _),
      Nat.sub_zero, List.getElem?_eq_none le_rfl]
    simp [enc]
  rw [fstep, hfind]
  simp [enc, hb, Nat.div_self (pr_pos _)]

/-- Arranque: `2^m` (sin primo de estado) entra al estado 0 con `m` en el registro 0. -/
theorem fstep_start {R : ℕ} (M : Machine) (hR1 : 1 ≤ R) (m : ℕ) :
    fstep (fracs R M) (2 ^ m) = enc R ⟨0, update (fun _ => 0) 0 m⟩ := by
  have hnd : ∀ k, R ≤ k → ¬ pr k ∣ 2 ^ m := by
    intro k hk hd
    have h2 := (Nat.prime_dvd_prime_iff_eq (pr_prime k) Nat.prime_two).1
      ((pr_prime k).dvd_of_dvd_pow hd)
    rw [← pr_zero] at h2
    have := pr_injective h2; omega
  have hnone : ∀ (xs : List Instr) (i : ℕ),
      (fracsFrom R i xs).find? (fun q => decide (q.2 ∣ 2 ^ m)) = none := by
    intro xs
    induction xs with
    | nil => intro i; simp [fracsFrom]
    | cons x xs ih =>
      intro i
      rw [fracsFrom, List.find?_append, find_block_none x (hnd _ (by omega)), ih]; rfl
  have hfind : (fracs R M).find? (fun q => decide (q.2 ∣ 2 ^ m)) = some (pr R, 1) := by
    rw [fracs, List.find?_append, hnone]
    simp [hnd (R + M.length) (by omega)]
  rw [fstep, hfind]
  simp only [Nat.div_one, enc, add_zero]
  congr 1
  have h0 : update (fun _ : ℕ => (0 : ℕ)) 0 0 = fun _ => 0 := by
    funext x; simp [update_apply]
  rw [body_split (r := 0) (by omega), update_idem, update_self, h0, body_zero, pr_zero]
  simp

/-! ## Registros usados por un programa compilado -/

/-- Cota de los registros que menciona un programa. -/
def Prog.bound : Prog → ℕ
  | .skip => 0
  | .inc r => r + 1
  | .dec r => r + 1
  | .seq p q => max p.bound q.bound
  | .loop r p => max (r + 1) p.bound

theorem reg_lt_of_mem_compile : ∀ (p : Prog) (b : ℕ) (x : Instr), x ∈ Prog.compile b p →
    x.reg < p.bound
  | .skip, _, _, h => by simp [Prog.compile] at h
  | .inc r, _, x, h => by simp [Prog.compile] at h; subst h; simp [Instr.reg, Prog.bound]
  | .dec r, _, x, h => by simp [Prog.compile] at h; subst h; simp [Instr.reg, Prog.bound]
  | .seq p q, b, x, h => by
    simp only [Prog.compile, List.mem_append] at h
    rcases h with h | h
    · have := reg_lt_of_mem_compile p _ x h; simp [Prog.bound]; omega
    · have := reg_lt_of_mem_compile q _ x h; simp [Prog.bound]; omega
  | .loop r p, b, x, h => by
    simp only [Prog.compile, List.mem_append, List.mem_singleton] at h
    rcases h with (((h | h) | h) | h) | h
    · subst h; simp [Instr.reg, Prog.bound]
    · subst h; simp [Instr.reg, Prog.bound]
    · have := reg_lt_of_mem_compile p _ x h; simp [Prog.bound]; omega
    · subst h; simp [Instr.reg, Prog.bound]
    · subst h; simp [Instr.reg, Prog.bound]

/-! ## La órbita de `2^m` -/

/-- Registros iniciales: `m` en el registro 0, el resto en cero. -/
def initRegs (m : ℕ) : Regs := update (fun _ => 0) 0 m

/-- **Órbita.** Sea `Q` un programa que, cuando termina desde `initRegs m`, deja todos los
registros en cero. Con `g = fstep (fracs R Q.toMachine)`:
* si `Q` termina, alguna iteración `g^[i] (2^m)` con `i ≥ 1` vale `1`;
* si no termina, toda iteración `g^[i] (2^m)` con `i ≥ 1` es divisible por un primo impar. -/
theorem orbit (Q : Prog) {R : ℕ} (hR : Q.bound ≤ R) (hR1 : 1 ≤ R) (m : ℕ)
    (hQ : ∀ s', Prog.Runs Q (initRegs m) s' → ∀ r, s' r = 0) :
    ((∃ s', Prog.Runs Q (initRegs m) s') →
        ∃ i, 1 ≤ i ∧ (fstep (fracs R Q.toMachine))^[i] (2 ^ m) = 1) ∧
    ((¬ ∃ s', Prog.Runs Q (initRegs m) s') → ∀ i, 1 ≤ i →
        ∃ p, p.Prime ∧ p ≠ 2 ∧ p ∣ (fstep (fracs R Q.toMachine))^[i] (2 ^ m)) := by
  set M := Q.toMachine with hM
  set c0 : Cfg := ⟨0, initRegs m⟩
  have hRM : ∀ x ∈ M, x.reg < R := fun x hx =>
    lt_of_lt_of_le (reg_lt_of_mem_compile Q 0 x hx) hR
  have hL : M.length = Q.len := Prog.length_compile 0 Q
  have sim : ∀ j, (∀ j' < j, ((M.step)^[j'] c0).pc < M.length) →
      (fstep (fracs R M))^[j + 1] (2 ^ m) = enc R ((M.step)^[j] c0) := by
    intro j
    induction j with
    | zero => intro _; simp only [zero_add, iterate_one, iterate_zero, id]; exact fstep_start M hR1 m
    | succ j ih =>
      intro H
      rw [iterate_succ_apply', ih (fun j' h => H j' (by omega)),
        fstep_enc hRM _ (H j (by omega)), ← iterate_succ_apply' M.step]
  constructor
  · intro hrun
    have hex : ∃ n, M.Halted ((M.step)^[n] c0) := (Q.toMachine_halts _).2 hrun
    classical
    set k0 := Nat.find hex
    obtain ⟨s', k, hrun', hk, ek⟩ :=
      Prog.halts_compile Q M 0 Q.codeAt_toMachine k0 _ (Nat.find_spec hex)
    have hk0 : k0 ≤ k := Nat.find_min' hex (by
      rw [ek]; simp [Machine.Halted, hL])
    have hkk : k = k0 := le_antisymm hk hk0
    have hpc : ∀ j' < k0, ((M.step)^[j'] c0).pc < M.length := by
      intro j' hj'
      have := Nat.find_min hex hj'
      simpa [Machine.Halted] using this
    refine ⟨k0 + 2, by omega, ?_⟩
    rw [show k0 + 2 = 1 + (k0 + 1) by omega, iterate_add_apply, sim k0 hpc, ← hkk, ek,
      iterate_one, zero_add, ← hL]
    exact fstep_halt hRM s' fun r _ => hQ s' hrun' r
  · intro hrun i hi
    have hnh : ∀ j, ((M.step)^[j] c0).pc < M.length := by
      intro j
      by_contra h
      exact hrun ((Q.toMachine_halts _).1 ⟨j, by simpa [Machine.Halted] using h⟩)
    obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le' hi
    rw [sim j (fun j' _ => hnh j')]
    refine ⟨pr (R + ((M.step)^[j] c0).pc), pr_prime _, ?_, dvd_mul_right _ _⟩
    rw [← pr_zero]
    intro h; have := pr_injective h; omega

end Conway
