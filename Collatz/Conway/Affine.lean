import Collatz.Conway.Fractran

/-!
# Una función de Collatz afín que llega a 1 desde todo `n` sii la máquina es mortal

Para la versión de Kurtz–Simon ("¿toda órbita llega a 1?") la función tiene que comportarse bien
en *todos* los enteros positivos, no sólo en las codificaciones de configuraciones. Partimos de la
codificación de `Fractran.lean` (registros y estado como exponentes de primos `pr k`) y agregamos:

1. `pairs`: si hay dos primos de estado (o uno al cuadrado), se borran de a dos;
2. las fracciones de la máquina (`fracsFrom`), como en Conway;
3. `(1, pr (R+L))`: se borra el estado final;
4. `strips`: se borran los registros de a uno;
5. si ningún primo de la máquina divide a `n` (regla por defecto, afín): `n ↦ (n+1)/2`.

Todo `n` se escribe `n = body N E * u` con `u` coprimo con los primos de la máquina ("basura").
Las reglas 1–4 no tocan `u`, y la regla 5 lo achica estrictamente. Con eso:

* `allOne_of_mortal`: si la máquina se detiene desde toda configuración, toda órbita llega a 1;
* `iterate_kstep_ne_one`: desde una configuración que no se detiene, la órbita nunca vale 1.
-/

namespace Conway

open Function

/-! ## Saltos acotados -/

/-- Todos los saltos de la instrucción van a direcciones `≤ L`. -/
def Instr.JumpsLe (L : ℕ) : Instr → Prop
  | .inc _ j => j ≤ L
  | .decjz _ j k => j ≤ L ∧ k ≤ L
  | .addc _ _ j => j ≤ L

theorem Instr.JumpsLe.mono {L L' : ℕ} (h : L ≤ L') : ∀ {x : Instr}, x.JumpsLe L → x.JumpsLe L'
  | .inc _ _, hx => le_trans hx h
  | .decjz _ _ _, hx => ⟨le_trans hx.1 h, le_trans hx.2 h⟩
  | .addc _ _ _, hx => le_trans hx h

theorem jumpsLe_compile : ∀ (p : Prog) (b : ℕ), ∀ x ∈ Prog.compile b p, x.JumpsLe (b + p.len)
  | .skip, _, x, h => by simp [Prog.compile] at h
  | .inc r, b, x, h => by simp [Prog.compile] at h; subst h; simp [Instr.JumpsLe, Prog.len]
  | .dec r, b, x, h => by
    simp [Prog.compile] at h; subst h; exact ⟨by simp [Prog.len], by simp [Prog.len]⟩
  | .addc r k, b, x, h => by simp [Prog.compile] at h; subst h; simp [Instr.JumpsLe, Prog.len]
  | .seq p q, b, x, h => by
    simp only [Prog.compile, List.mem_append] at h
    rcases h with h | h
    · exact (jumpsLe_compile p b x h).mono (by simp [Prog.len])
    · exact (jumpsLe_compile q _ x h).mono (by simp [Prog.len]; omega)
  | .loop r p, b, x, h => by
    simp only [Prog.compile, List.mem_append, List.mem_singleton] at h
    rcases h with (((h | h) | h) | h) | h
    · subst h; exact ⟨by simp [Prog.len], by simp [Prog.len]; omega⟩
    · subst h; simp only [Instr.JumpsLe, Prog.len]; omega
    · exact (jumpsLe_compile p _ x h).mono (by simp [Prog.len]; omega)
    · subst h; simp only [Instr.JumpsLe, Prog.len]; omega
    · subst h; exact ⟨by simp [Prog.len], by simp [Prog.len]⟩

theorem step_pc_le {M : Machine} (hJ : ∀ x ∈ M, x.JumpsLe M.length) (c : Cfg) :
    (M.step c).pc ≤ M.length ∨ M.step c = c := by
  unfold Machine.step
  cases h : M[c.pc]? with
  | none => exact .inr rfl
  | some x =>
    left
    have hx := hJ x (List.mem_of_getElem? h)
    cases x with
    | inc r j => exact hx
    | decjz r j k => simp only [Instr.exec]; split_ifs <;> simp [hx.1, hx.2]
    | addc r k j => exact hx

theorem step_regs {M : Machine} {R : ℕ} (hR : ∀ x ∈ M, x.reg < R) (c : Cfg) (r : ℕ)
    (hr : R ≤ r) : (M.step c).regs r = c.regs r := by
  unfold Machine.step
  cases h : M[c.pc]? with
  | none => rfl
  | some x =>
    have hx := hR x (List.mem_of_getElem? h)
    cases x with
    | inc r' j =>
      simp only [Instr.reg] at hx; simp only [Instr.exec]; rw [update_of_ne (by omega)]
    | decjz r' j k =>
      simp only [Instr.reg] at hx; simp only [Instr.exec]
      split_ifs
      · rfl
      · exact update_of_ne (by omega) _ _
    | addc r' k j =>
      simp only [Instr.reg] at hx; simp only [Instr.exec]; rw [update_of_ne (by omega)]

/-! ## La función -/

/-- Borrar pares de primos de estado. -/
noncomputable def pairs (R L : ℕ) : List (ℕ × ℕ) :=
  (List.range (L + 1)).flatMap fun i => (List.range (L + 1)).map fun j =>
    (1, pr (R + i) * pr (R + j))

/-- Borrar registros. -/
noncomputable def strips (R : ℕ) : List (ℕ × ℕ) := (List.range R).map fun r => (1, pr r)

/-- Todas las reglas multiplicativas, en orden. -/
noncomputable def rules (R : ℕ) (M : Machine) : List (ℕ × ℕ) :=
  pairs R M.length ++ (fracsFrom R 0 M ++ ((1, pr (R + M.length)) :: strips R))

/-- La función: la primera regla `(a, b)` con `b ∣ n` da `a * (n / b)`; si no hay, `(n + 1) / 2`. -/
noncomputable def kstep (R : ℕ) (M : Machine) (n : ℕ) : ℕ :=
  match (rules R M).find? (fun q => decide (q.2 ∣ n)) with
  | some q => q.1 * (n / q.2)
  | none => (n + 1) / 2

theorem kstep_of_find {R : ℕ} {M : Machine} {n : ℕ} {q : ℕ × ℕ}
    (h : (rules R M).find? (fun q => decide (q.2 ∣ n)) = some q) : kstep R M n = q.1 * (n / q.2) := by
  simp [kstep, h]

theorem kstep_of_none {R : ℕ} {M : Machine} {n : ℕ}
    (h : (rules R M).find? (fun q => decide (q.2 ∣ n)) = none) : kstep R M n = (n + 1) / 2 := by
  simp [kstep, h]

/-! ## Denominadores -/

theorem mem_fracsFrom {R : ℕ} : ∀ {xs : List Instr} {i : ℕ} {q : ℕ × ℕ}, q ∈ fracsFrom R i xs →
    ∃ j x, i ≤ j ∧ j < i + xs.length ∧ x ∈ xs ∧ q ∈ block R j x
  | [], _, _, h => by simp [fracsFrom] at h
  | x :: xs, i, q, h => by
    simp only [fracsFrom, List.mem_append] at h
    rcases h with h | h
    · exact ⟨i, x, le_rfl, by simp, by simp, h⟩
    · obtain ⟨j, y, h1, h2, h3, h4⟩ := mem_fracsFrom h
      exact ⟨j, y, by omega, by simp; omega, by simp [h3], h4⟩

theorem den_block {R j : ℕ} {x : Instr} {q : ℕ × ℕ} (h : q ∈ block R j x) :
    q.2 = pr (R + j) ∨ q.2 = pr (R + j) * pr x.reg := by
  cases x <;> simp [block] at h <;> rcases h with rfl | rfl <;> simp [Instr.reg]

theorem mem_pairs {R L : ℕ} {q : ℕ × ℕ} (h : q ∈ pairs R L) :
    ∃ a b, a ≤ L ∧ b ≤ L ∧ q = (1, pr (R + a) * pr (R + b)) := by
  simp only [pairs, List.mem_flatMap, List.mem_range, List.mem_map] at h
  obtain ⟨a, ha, b, hb, rfl⟩ := h
  exact ⟨a, b, by omega, by omega, rfl⟩

/-- `u` no es divisible por ningún primo de la máquina (`pr k`, `k < N`). -/
def Good (N u : ℕ) : Prop := ∀ k < N, ¬ pr k ∣ u

theorem Good.coprime {N u k : ℕ} (hu : Good N u) (hk : k < N) : Nat.Coprime (pr k) u :=
  (Nat.Prime.coprime_iff_not_dvd (pr_prime k)).2 (hu k hk)

theorem Good.ne_zero {N u : ℕ} (hu : Good N u) (hN : 0 < N) : u ≠ 0 := by
  rintro rfl; exact hu 0 hN (dvd_zero _)

theorem good_one (N : ℕ) : Good N 1 := fun k _ h =>
  (pr_prime k).one_lt.ne' (Nat.dvd_one.1 h)

theorem coprime_rules {R : ℕ} {M : Machine} (hR : ∀ x ∈ M, x.reg < R) {u : ℕ}
    (hu : Good (R + (M.length + 1)) u) : ∀ q ∈ rules R M, Nat.Coprime q.2 u := by
  intro q hq
  simp only [rules, List.mem_append, List.mem_cons] at hq
  rcases hq with hq | hq | rfl | hq
  · obtain ⟨a, b, ha, hb, rfl⟩ := mem_pairs hq
    exact Nat.Coprime.mul_left (hu.coprime (by omega)) (hu.coprime (by omega))
  · obtain ⟨j, x, -, hj, hx, hqx⟩ := mem_fracsFrom hq
    simp only [zero_add] at hj
    rcases den_block hqx with e | e <;> rw [e]
    · exact hu.coprime (by omega)
    · exact Nat.Coprime.mul_left (hu.coprime (by omega)) (hu.coprime (by have := hR x hx; omega))
  · exact hu.coprime (by omega)
  · simp only [strips, List.mem_map, List.mem_range] at hq
    obtain ⟨r, hr, rfl⟩ := hq
    exact hu.coprime (by omega)

/-- La basura `u` no cambia qué regla se aplica. -/
theorem find_mul_good {l : List (ℕ × ℕ)} {u : ℕ} (h : ∀ q ∈ l, Nat.Coprime q.2 u) (x : ℕ) :
    l.find? (fun q => decide (q.2 ∣ x * u)) = l.find? (fun q => decide (q.2 ∣ x)) := by
  induction l with
  | nil => rfl
  | cons q l ih =>
    have e1 : q.2 ∣ x * u ↔ q.2 ∣ x := (h q (by simp)).dvd_mul_right
    simp only [List.find?_cons, e1, ih fun q' hq' => h q' (by simp [hq'])]

theorem kstep_mul {R : ℕ} {M : Machine} (hR : ∀ x ∈ M, x.reg < R) {u : ℕ}
    (hu : Good (R + (M.length + 1)) u) {x : ℕ} {q : ℕ × ℕ}
    (h : (rules R M).find? (fun q => decide (q.2 ∣ x)) = some q) :
    kstep R M (x * u) = q.1 * (x / q.2) * u := by
  have hd : q.2 ∣ x := by simpa using List.find?_some h
  rw [kstep_of_find (by rwa [find_mul_good (coprime_rules hR hu)]), Nat.mul_div_right_comm hd,
    mul_assoc]

/-! ## Simulación de la máquina -/

theorem pairs_none_enc {R L : ℕ} (c : Cfg) :
    (pairs R L).find? (fun q => decide (q.2 ∣ enc R c)) = none := by
  rw [List.find?_eq_none]
  intro q hq hd
  obtain ⟨a, b, -, -, rfl⟩ := mem_pairs hq
  simp only [decide_eq_true_eq] at hd
  have ha := (st_dvd_enc c).1 ((dvd_mul_right _ _).trans hd)
  have hb := (st_dvd_enc c).1 ((dvd_mul_left _ _).trans hd)
  subst ha hb
  rw [enc, Nat.mul_dvd_mul_iff_left (pr_pos _)] at hd
  exact not_pr_dvd_body _ (by omega) hd

/-- **Un paso de la máquina** (no detenida) es un paso de la función, aun con basura `u`. -/
theorem kstep_enc {R : ℕ} {M : Machine} (hR : ∀ x ∈ M, x.reg < R) {u : ℕ}
    (hu : Good (R + (M.length + 1)) u) (c : Cfg) (hc : c.pc < M.length) :
    kstep R M (enc R c * u) = enc R (M.step c) * u := by
  obtain ⟨q, hq, hval⟩ := find_block_self c M[c.pc] (hR _ (List.getElem_mem hc))
  have hfind : (rules R M).find? (fun q => decide (q.2 ∣ enc R c)) = some q := by
    rw [rules, List.find?_append, pairs_none_enc, Option.none_or, List.find?_append,
      find_fracsFrom c M 0 hR, if_pos (Nat.zero_le _), Nat.sub_zero, List.getElem?_eq_getElem hc]
    simp [hq]
  rw [kstep_mul hR hu hfind, hval, Machine.step_at (List.getElem?_eq_getElem hc)]

/-- Estado final: se borra el primo de estado. -/
theorem kstep_halt {R : ℕ} {M : Machine} (hR : ∀ x ∈ M, x.reg < R) {u : ℕ}
    (hu : Good (R + (M.length + 1)) u) (e : Regs) :
    kstep R M (enc R ⟨M.length, e⟩ * u) = body R e * u := by
  have hfind : (rules R M).find? (fun q => decide (q.2 ∣ enc R ⟨M.length, e⟩)) =
      some (1, pr (R + M.length)) := by
    rw [rules, List.find?_append, pairs_none_enc, Option.none_or, List.find?_append,
      find_fracsFrom _ M 0 hR, if_pos (Nat.zero_le _), Nat.sub_zero, List.getElem?_eq_none le_rfl]
    simp [enc]
  rw [kstep_mul hR hu hfind]
  simp [enc, Nat.mul_div_cancel_left _ (pr_pos _)]

/-- Desde una configuración que nunca se detiene, la órbita nunca vale 1. -/
theorem iterate_kstep_ne_one {R : ℕ} {M : Machine} (hR : ∀ x ∈ M, x.reg < R) (c : Cfg)
    (hnh : ∀ n, ¬ M.Halted ((M.step)^[n] c)) (i : ℕ) : (kstep R M)^[i] (enc R c) ≠ 1 := by
  have sim : ∀ i, (kstep R M)^[i] (enc R c) = enc R ((M.step)^[i] c) := by
    intro i
    induction i with
    | zero => rfl
    | succ i ih =>
      have hc : ((M.step)^[i] c).pc < M.length := by
        have := hnh i; simp only [Machine.Halted, not_le] at this; exact this
      rw [iterate_succ_apply', ih, ← mul_one (enc R _), kstep_enc hR (good_one _) _ hc, mul_one,
        ← iterate_succ_apply' M.step]
  rw [sim]
  intro h
  have : pr (R + ((M.step)^[i] c).pc) ∣ 1 := h ▸ dvd_mul_right _ _
  exact (pr_prime _).one_lt.ne' (Nat.dvd_one.1 this)

/-! ## Descomposición `n = body N E * u` -/

theorem body_update_of_le {N k : ℕ} (hk : N ≤ k) (E : Regs) (v : ℕ) :
    body N (update E k v) = body N E := by
  unfold body
  exact Finset.prod_congr rfl fun r hr => by
    rw [update_of_ne (by simp at hr; omega)]

theorem exists_body_mul : ∀ (N n : ℕ), n ≠ 0 → ∃ E u, Good N u ∧ n = body N E * u
  | 0, n, _ => ⟨fun _ => 0, n, fun k hk => absurd hk (Nat.not_lt_zero _), by simp [body]⟩
  | N + 1, n, hn => by
    obtain ⟨E, u, hu, rfl⟩ := exists_body_mul N n hn
    have hu0 : u ≠ 0 := by rintro rfl; simp at hn
    obtain ⟨a, u', hnd, rfl⟩ := Nat.exists_eq_pow_mul_and_not_dvd hu0 (pr N) (pr_prime N).one_lt.ne'
    refine ⟨update E N a, u', fun k hk h => ?_, ?_⟩
    · rcases Nat.lt_succ_iff_lt_or_eq.1 hk with hk | rfl
      · exact hu k hk (h.trans (dvd_mul_left _ _))
      · exact hnd h
    · have : body (N + 1) (update E N a) = body N E * pr N ^ a := by
        rw [body, Finset.prod_range_succ, ← body, body_update_of_le le_rfl, update_self]
      rw [this]; ring

/-! ## La medida: cuántos primos de estado hay -/

/-- Cantidad de primos de estado (con multiplicidad). -/
def ms (R L : ℕ) (E : Regs) : ℕ := ∑ i ∈ Finset.range (L + 1), E (R + i)

theorem ms_update {R L a : ℕ} (ha : a ≤ L) (E : Regs) (v : ℕ) :
    ms R L (update E (R + a) v) + E (R + a) = ms R L E + v := by
  have hmem : a ∈ Finset.range (L + 1) := Finset.mem_range.2 (by omega)
  unfold ms
  rw [← Finset.add_sum_erase _ _ hmem, ← Finset.add_sum_erase _ _ hmem, update_self,
    Finset.sum_congr rfl fun i hi => update_of_ne (show R + i ≠ R + a by
      have := Finset.ne_of_mem_erase hi; omega) v E]
  ring

theorem ms_update_reg {R L r : ℕ} (hr : r < R) (E : Regs) (v : ℕ) :
    ms R L (update E r v) = ms R L E := by
  unfold ms
  exact Finset.sum_congr rfl fun i _ => update_of_ne (by omega) _ _

/-- Con `ms = 0`, sólo quedan los registros. -/
theorem body_ms_zero {R L : ℕ} {E : Regs} (h : ms R L E = 0) : body (R + (L + 1)) E = body R E := by
  rw [body, Finset.prod_range_add, ← body]
  have : ∀ i ∈ Finset.range (L + 1), E (R + i) = 0 := Finset.sum_eq_zero_iff.1 h
  rw [Finset.prod_eq_one fun i hi => by rw [this i hi, pow_zero], mul_one]

theorem exists_of_ms_ne_zero {R L : ℕ} {E : Regs} (h : ms R L E ≠ 0) : ∃ a ≤ L, E (R + a) ≠ 0 := by
  obtain ⟨a, ha, h⟩ := Finset.exists_ne_zero_of_sum_ne_zero h
  exact ⟨a, by simp at ha; omega, h⟩

/-- Sacar un primo de estado. -/
theorem body_dec_state {R L a : ℕ} (ha : a ≤ L) {E : Regs} (h : E (R + a) ≠ 0) :
    body (R + (L + 1)) E = pr (R + a) * body (R + (L + 1)) (update E (R + a) (E (R + a) - 1)) ∧
      ms R L (update E (R + a) (E (R + a) - 1)) + 1 = ms R L E := by
  refine ⟨body_dec (by omega) E h, ?_⟩
  have := ms_update (R := R) ha E (E (R + a) - 1)
  omega

/-! ## El teorema -/

/-- **Si la máquina se detiene desde toda configuración, toda órbita llega a 1.** -/
theorem allOne_of_mortal {R : ℕ} {M : Machine} (hR : ∀ x ∈ M, x.reg < R)
    (hJ : ∀ x ∈ M, x.JumpsLe M.length)
    (hmort : ∀ c : Cfg, c.pc ≤ M.length → (∀ r, R ≤ r → c.regs r = 0) →
      ∃ n, M.Halted ((M.step)^[n] c)) :
    ∀ n, 0 < n → ∃ i, (kstep R M)^[i] n = 1 := by
  set L := M.length with hLdef
  set N := R + (L + 1) with hN
  have main : ∀ u, Good N u → ∀ E, ∃ i, (kstep R M)^[i] (body N E * u) = 1 := by
    intro u
    induction u using Nat.strong_induction_on with
    | _ u IHu =>
    intro hu
    have hu0 : u ≠ 0 := hu.ne_zero (by omega)
    -- fase de registros
    have C1 : ∀ e : Regs, ∃ i, (kstep R M)^[i] (body R e * u) = 1 := by
      intro e
      generalize hB : body R e = B
      induction B using Nat.strong_induction_on generalizing e with
      | _ B IHB =>
      subst hB
      by_cases h1 : body R e = 1
      · rw [h1, one_mul]
        by_cases hu1 : u = 1
        · exact ⟨0, by simp [hu1]⟩
        have hnone : (rules R M).find? (fun q => decide (q.2 ∣ u)) = none := by
          rw [List.find?_eq_none]
          intro q hq hd
          simp only [decide_eq_true_eq] at hd
          have hcop := coprime_rules hR hu q hq
          have hq1 : q.2 = 1 := Nat.Coprime.eq_one_of_dvd hcop hd
          simp only [rules, List.mem_append, List.mem_cons] at hq
          rcases hq with hq | hq | rfl | hq
          · obtain ⟨a, b, -, -, rfl⟩ := mem_pairs hq
            simp only at hq1
            exact (pr_prime _).one_lt.ne' (Nat.eq_one_of_mul_eq_one_right hq1)
          · obtain ⟨j, x, -, -, -, hqx⟩ := mem_fracsFrom hq
            rcases den_block hqx with e | e <;> rw [e] at hq1
            · exact (pr_prime _).one_lt.ne' hq1
            · exact (pr_prime _).one_lt.ne' (Nat.eq_one_of_mul_eq_one_right hq1)
          · exact (pr_prime _).one_lt.ne' hq1
          · simp only [strips, List.mem_map] at hq
            obtain ⟨r, -, rfl⟩ := hq
            exact (pr_prime _).one_lt.ne' hq1
        have hk := kstep_of_none hnone
        obtain ⟨E', u', hu', he⟩ := exists_body_mul N ((u + 1) / 2) (by omega)
        have hle : u' ≤ (u + 1) / 2 :=
          Nat.le_of_dvd (by omega) ⟨body N E', by rw [he, mul_comm]⟩
        obtain ⟨i, hi⟩ := IHu u' (by omega) hu' E'
        exact ⟨i + 1, by rw [iterate_succ_apply, hk, he, hi]⟩
      · obtain ⟨r, hr, her⟩ : ∃ r < R, e r ≠ 0 := by
          by_contra hcon
          push Not at hcon
          apply h1
          unfold body
          exact Finset.prod_eq_one fun r hr => by rw [hcon r (by simpa using hr), pow_zero]
        -- la primera regla aplicable es un `strip`
        have hst : ∀ k ≤ L, ¬ pr (R + k) ∣ body R e * u := by
          intro k _ hd
          rcases (Nat.Prime.dvd_mul (pr_prime _)).1 hd with hd | hd
          · exact not_pr_dvd_body e (by omega) hd
          · exact hu _ (by omega) hd
        have hpre : (pairs R L ++ (fracsFrom R 0 M ++ [(1, pr (R + L))])).find?
            (fun q : ℕ × ℕ => decide (q.2 ∣ body R e * u)) = none := by
          rw [List.find?_eq_none]
          intro q hq hd
          simp only [decide_eq_true_eq] at hd
          simp only [List.mem_append, List.mem_singleton] at hq
          rcases hq with hq | hq | rfl
          · obtain ⟨a, b, ha, -, rfl⟩ := mem_pairs hq
            exact hst a ha ((dvd_mul_right _ _).trans hd)
          · obtain ⟨j, x, -, hj, -, hqx⟩ := mem_fracsFrom hq
            rcases den_block hqx with e' | e' <;> rw [e'] at hd
            · exact hst j (by omega) hd
            · exact hst j (by omega) ((dvd_mul_right _ _).trans hd)
          · exact hst L le_rfl hd
        have hsome : ((strips R).find? (fun q => decide (q.2 ∣ body R e * u))).isSome := by
          rw [List.find?_isSome]
          refine ⟨(1, pr r), List.mem_map.2 ⟨r, List.mem_range.2 hr, rfl⟩, ?_⟩
          simp only [decide_eq_true_eq]
          exact ((pr_dvd_body_iff hr e).2 her).trans (dvd_mul_right _ _)
        obtain ⟨q, hq⟩ := Option.isSome_iff_exists.1 hsome
        have hfind : (rules R M).find? (fun q => decide (q.2 ∣ body R e * u)) = some q := by
          have : rules R M = (pairs R L ++ (fracsFrom R 0 M ++ [(1, pr (R + L))])) ++ strips R := by
            simp [rules, L]
          rw [this, List.find?_append, hpre, Option.none_or, hq]
        have hqmem := List.mem_of_find?_eq_some hq
        have hqd : q.2 ∣ body R e * u := by simpa using List.find?_some hq
        simp only [strips, List.mem_map, List.mem_range] at hqmem
        obtain ⟨r', hr', rfl⟩ := hqmem
        have hd' : pr r' ∣ body R e := by
          rcases (Nat.Prime.dvd_mul (pr_prime _)).1 hqd with hd | hd
          · exact hd
          · exact absurd hd (hu r' (by omega))
        have her' := (pr_dvd_body_iff hr' e).1 hd'
        have hb := body_dec hr' e her'
        have hk : kstep R M (body R e * u) = body R (update e r' (e r' - 1)) * u := by
          rw [kstep_of_find hfind]
          simp only [one_mul]
          rw [hb, mul_assoc, Nat.mul_div_cancel_left _ (pr_pos _)]
        have hlt : body R (update e r' (e r' - 1)) < body R e := by
          rw [hb]
          have := body_pos R (update e r' (e r' - 1))
          have := (pr_prime r').two_le
          nlinarith
        obtain ⟨i, hi⟩ := IHB _ hlt _ rfl
        exact ⟨i + 1, by rw [iterate_succ_apply, hk, hi]⟩
    -- fase de la máquina
    have C2 : ∀ c : Cfg, c.pc ≤ L → (∀ r, R ≤ r → c.regs r = 0) →
        ∃ i, (kstep R M)^[i] (enc R c * u) = 1 := by
      intro c hpc hreg
      obtain ⟨n0, hn0⟩ := hmort c hpc hreg
      induction n0 generalizing c with
      | zero =>
        have hcL : c.pc = L := le_antisymm hpc hn0
        obtain ⟨i, hi⟩ := C1 c.regs
        refine ⟨i + 1, ?_⟩
        rw [iterate_succ_apply, show c = ⟨M.length, c.regs⟩ by cases c; simpa [hLdef] using hcL,
          kstep_halt hR hu, hi]
      | succ n0 ih =>
        by_cases hcL : c.pc = L
        · obtain ⟨i, hi⟩ := C1 c.regs
          refine ⟨i + 1, ?_⟩
          rw [iterate_succ_apply, show c = ⟨M.length, c.regs⟩ by cases c; simpa [hLdef] using hcL,
          kstep_halt hR hu, hi]
        have hlt : c.pc < M.length := by omega
        have hpc' : (M.step c).pc ≤ L := by
          rcases step_pc_le hJ c with h | h
          · exact h
          · rw [h]; exact hpc
        obtain ⟨i, hi⟩ := ih (M.step c) hpc'
          (fun r hr => by rw [step_regs hR c r hr]; exact hreg r hr)
          (by rw [← iterate_succ_apply]; exact hn0)
        exact ⟨i + 1, by rw [iterate_succ_apply, kstep_enc hR hu c hlt, hi]⟩
    -- fase de los pares
    intro E
    generalize hB : body N E = B
    induction B using Nat.strong_induction_on generalizing E with
    | _ B IHB =>
    subst hB
    by_cases h0 : ms R L E = 0
    · rw [hN, body_ms_zero h0]; exact C1 E
    obtain ⟨a, ha, hEa⟩ := exists_of_ms_ne_zero h0
    obtain ⟨hb1, hms1⟩ := body_dec_state ha hEa
    set E1 := update E (R + a) (E (R + a) - 1)
    by_cases h1 : ms R L E = 1
    · -- un solo primo de estado: una configuración
      have hms0 : ms R L E1 = 0 := by omega
      set e : Regs := fun r => if r < R then E r else 0
      have hbe : body R e = body R E := by
        unfold body
        exact Finset.prod_congr rfl fun r hr => by simp [e, Finset.mem_range.1 hr]
      have henc : body N E = enc R ⟨a, e⟩ := by
        rw [hb1, body_ms_zero hms0, enc, hbe, body_update_of_le (by omega)]
      rw [henc]
      exact C2 ⟨a, e⟩ ha (fun r hr => by simp [e]; omega)
    · -- dos o más: se borra un par
      obtain ⟨b, hb, hEb⟩ := exists_of_ms_ne_zero (show ms R L E1 ≠ 0 by omega)
      obtain ⟨hb2, hms2⟩ := body_dec_state hb hEb
      have hpair : pr (R + a) * pr (R + b) ∣ body N E * u := by
        rw [hb1, hb2, ← mul_assoc]; exact dvd_mul_of_dvd_left (dvd_mul_right _ _) _
      have hsome : ((pairs R L).find? (fun q => decide (q.2 ∣ body N E * u))).isSome := by
        rw [List.find?_isSome]
        exact ⟨(1, pr (R + a) * pr (R + b)), by
          simp only [pairs, List.mem_flatMap, List.mem_range, List.mem_map]
          exact ⟨a, by omega, b, by omega, rfl⟩, by simpa using hpair⟩
      obtain ⟨q, hq⟩ := Option.isSome_iff_exists.1 hsome
      have hfind : (rules R M).find? (fun q => decide (q.2 ∣ body N E * u)) = some q := by
        rw [rules, List.find?_append, hq]; rfl
      obtain ⟨a', b', ha', hb', rfl⟩ := mem_pairs (List.mem_of_find?_eq_some hq)
      have hqd : pr (R + a') * pr (R + b') ∣ body N E := by
        have := List.find?_some hq
        simp only [decide_eq_true_eq] at this
        exact (Nat.Coprime.dvd_mul_right (Nat.Coprime.mul_left (hu.coprime (by omega))
          (hu.coprime (by omega)))).1 this
      have hEa' : E (R + a') ≠ 0 :=
        (pr_dvd_body_iff (by omega) E).1 ((dvd_mul_right _ _).trans hqd)
      obtain ⟨hc1, hmc1⟩ := body_dec_state ha' hEa'
      set F1 := update E (R + a') (E (R + a') - 1)
      have hF1 : pr (R + b') ∣ body N F1 := by
        rw [hc1] at hqd; exact Nat.dvd_of_mul_dvd_mul_left (pr_pos _) hqd
      have hEb' : F1 (R + b') ≠ 0 := (pr_dvd_body_iff (by omega) F1).1 hF1
      obtain ⟨hc2, hmc2⟩ := body_dec_state hb' hEb'
      set F2 := update F1 (R + b') (F1 (R + b') - 1)
      have hk : kstep R M (body N E * u) = body N F2 * u := by
        rw [kstep_of_find hfind]
        simp only [one_mul]
        rw [hc1, hc2, ← mul_assoc, mul_assoc (pr (R + a') * pr (R + b')),
          Nat.mul_div_cancel_left _ (Nat.mul_pos (pr_pos _) (pr_pos _))]
      have hlt : body N F2 < body N E := by
        rw [hc1, hc2]
        have := body_pos N F2
        have := (pr_prime (R + a')).two_le
        have := (pr_prime (R + b')).two_le
        nlinarith
      obtain ⟨i, hi⟩ := IHB _ hlt F2 rfl
      exact ⟨i + 1, by rw [iterate_succ_apply, hk, hi]⟩
  intro n hn
  obtain ⟨E, u, hu, rfl⟩ := exists_body_mul N n (by omega)
  exact main u hu E

end Conway
