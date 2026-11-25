import Collatz.Conway.While

/-!
# Toda función `Nat.Partrec'` se calcula con un programa WHILE

`Nat.Partrec'` (Mathlib) es una base de las funciones parciales recursivas sobre vectores de
naturales, sin función de pares: ceros, sucesor, proyecciones, composición, recursión primitiva y
minimización. Compilamos cada constructor a un programa WHILE (`Conway.Prog`).
-/

namespace Conway

open Function Prog

/-- Secuencia de `Q 0, Q 1, …, Q (k-1)`. -/
def seqUpTo : ℕ → (ℕ → Prog) → Prog
  | 0, _ => .skip
  | k + 1, Q => .seq (seqUpTo k Q) (Q k)

theorem mortal_seqUpTo {Q : ℕ → Prog} (h : ∀ j, (Q j).Mortal) : ∀ k, (seqUpTo k Q).Mortal
  | 0 => .skip
  | k + 1 => .seq (mortal_seqUpTo h k) (h k)

theorem computes_of_total {n : ℕ} {f : List.Vector ℕ n → ℕ} {P : Prog} (N : ℕ)
    (h : ∀ (v : List.Vector ℕ n) (s : Regs), (∀ i : Fin n, s i = v.get i) →
      (∀ r, n ≤ r → r < N → s r = 0) → Runs P s (update s n (f v))) :
    Computes n (f : List.Vector ℕ n →. ℕ) P := by
  refine ⟨N, fun v s hin hz s' => ?_⟩
  rw [(h v s hin hz).iff_eq]
  simp [PFun.coe_val]

/-! ## Casos básicos -/

theorem computes_zero : Computes 0 ((fun _ => 0 : List.Vector ℕ 0 → ℕ) : _ →. ℕ) .skip := by
  refine computes_of_total 1 fun v s _ hz => ?_
  rw [update_eq_self_iff.2 (hz 0 le_rfl one_pos).symm]
  exact .skip s

theorem computes_succ :
    Computes 1 ((fun v => v.head.succ : List.Vector ℕ 1 → ℕ) : _ →. ℕ)
      (.seq (copy 0 1 2) (.inc 1)) := by
  refine computes_of_total 3 fun v s hin hz => ?_
  have h0 : s 0 = v.head := by simpa using hin 0
  refine .seq (runs_copy (by omega) (by omega) (by omega) s (hz 2 (by omega) (by omega))) ?_
  convert Runs.inc 1 _ using 1
  simp [hz 1 le_rfl (by omega), h0]

theorem computes_get {n : ℕ} (i : Fin n) :
    Computes n ((fun v => v.get i : List.Vector ℕ n → ℕ) : _ →. ℕ) (copy i n (n + 1)) := by
  refine computes_of_total (n + 2) fun v s hin hz => ?_
  have := runs_copy (src := i) (dst := n) (tmp := n + 1) (by omega) (by omega) (by omega) s
    (hz _ (by omega) (by omega))
  rwa [hz n le_rfl (by omega), hin i, zero_add] at this

/-! ## Limpieza de un bloque de registros -/

theorem runs_clears (c : ℕ) : ∀ (k : ℕ) (t : Regs),
    Runs (seqUpTo k fun j => clear (c + j)) t (fun r => if c ≤ r ∧ r < c + k then 0 else t r)
  | 0, t => by
    rw [seqUpTo]; convert Runs.skip t using 1
    funext r; simp only [add_zero]; split_ifs <;> first | rfl | omega
  | k + 1, t => by
    refine .seq (runs_clears c k t) ?_
    convert runs_clear (c + k) _ using 1
    funext r; simp only [update_apply]; split_ifs <;> first | rfl | omega

/-! ## Composición -/

theorem mem_mOfFn {n : ℕ} (G : Fin n → Part ℕ) (w : List.Vector ℕ n) :
    w ∈ List.Vector.mOfFn G ↔ ∀ i, w.get i ∈ G i := by
  induction n with
  | zero => simp [List.Vector.mOfFn, List.Vector.eq_nil w]
  | succ n ih =>
    simp only [List.Vector.mOfFn, Part.bind_eq_bind, Part.mem_bind_iff, Part.pure_eq_some,
      Part.mem_some_iff]
    constructor
    · rintro ⟨a, ha, u, hu, rfl⟩ i
      refine Fin.cases ?_ (fun j => ?_) i
      · simpa using ha
      · simpa using (ih _ u).1 hu j
    · intro h
      refine ⟨w.head, by simpa using h 0, w.tail, (ih _ _).2 fun j => ?_, by simp⟩
      simpa using h j.succ

/-- Relleno: los registros `c, …, c+k-1` pasan a valer `w 0, …, w (k-1)`. -/
def fill (s : Regs) (c k : ℕ) (w : ℕ → ℕ) : Regs :=
  fun r => if c ≤ r ∧ r < c + k then w (r - c) else s r

/-- Etapa `i` de la composición: calcular `g i` con salida en `m+1+i`. -/
def compG (m n : ℕ) (Pg : Fin n → Prog) (i : ℕ) : Prog :=
  if h : i < n then (Pg ⟨i, h⟩).rename (callMap m id (m + 1 + i) (m + n + 1)) else .skip

theorem computes_comp {m n : ℕ} {f : List.Vector ℕ n →. ℕ} {g : Fin n → List.Vector ℕ m →. ℕ}
    {Pf : Prog} (hf : Computes n f Pf) (Pg : Fin n → Prog) (hg : ∀ i, Computes m (g i) (Pg i)) :
    ∃ P, Computes m (fun v => (List.Vector.mOfFn fun i => g i v) >>= f) P ∧
      (Pf.Mortal → (∀ i, (Pg i).Mortal) → P.Mortal) := by
  obtain ⟨Nf, hNf⟩ := hf.call
  choose Ng hNg using fun i => (hg i).call
  refine ⟨.seq (seqUpTo n (compG m n Pg)) (.seq (Pf.rename (callMap n (fun j => m + 1 + j) m
    (m + n + 1))) (seqUpTo n fun j => clear (m + 1 + j))), ⟨m + n + 1 + Nf + ∑ i, Ng i, ?_⟩,
    fun hmf hmg => ?_⟩
  swap
  · refine .seq (mortal_seqUpTo (fun j => ?_) n) (.seq (hmf.rename (callMap_injective
      (by intro i j _ _ h; omega) (by intro i _; omega) (by omega) (by intro i _; omega)))
      (mortal_seqUpTo (fun j => .clear _) n))
    unfold compG
    split_ifs
    · exact (hmg _).rename (callMap_injective (by intro i j _ _ h; exact h)
        (by intro i hi; simp; omega) (by omega) (by intro i _; simp; omega))
    · exact .skip
  intro v s hin hz s'
  have hNle : ∀ i, Ng i ≤ ∑ i, Ng i := fun i =>
    Finset.single_le_sum (fun i _ => Nat.zero_le (Ng i)) (Finset.mem_univ i)
  have stage : ∀ k ≤ n, ∀ s', Runs (seqUpTo k (compG m n Pg)) s s' ↔
      ∃ w : ℕ → ℕ, (∀ i (h : i < n), i < k → w i ∈ g ⟨i, h⟩ v) ∧ s' = fill s (m + 1) k w := by
    intro k
    induction k with
    | zero =>
      intro _ s'
      rw [seqUpTo, runs_skip]
      constructor
      · rintro rfl
        exact ⟨fun _ => 0, fun i _ h => absurd h (Nat.not_lt_zero i), by
          funext r; simp only [fill]; split_ifs <;> first | rfl | omega⟩
      · rintro ⟨w, _, rfl⟩
        funext r; simp only [fill]; split_ifs <;> first | rfl | omega
    | succ k ih =>
      intro hk s'
      rw [seqUpTo, runs_seq]
      have hGk : compG m n Pg k = (Pg ⟨k, hk⟩).rename (callMap m id (m + 1 + k) (m + n + 1)) :=
        dif_pos hk
      rw [hGk]
      have call := fun (w : ℕ → ℕ) => hNg ⟨k, hk⟩ id (m + 1 + k) (m + n + 1)
        (fun i j _ _ h => h) (fun i hi => by simp only [id]; omega) (by omega)
        (fun i hi => by simp only [id]; omega) v (fill s (m + 1) k w)
        (fun i => by simp only [fill, id]; rw [if_neg (by omega)]; exact hin i)
        (by simp only [fill]; rw [if_neg (by omega)]; exact hz _ (by omega) (by omega))
        (fun r h1 h2 => by
          simp only [fill]; rw [if_neg (by omega)]
          exact hz _ (by omega) (by have := hNle ⟨k, hk⟩; omega))
      constructor
      · rintro ⟨t, ht, h2⟩
        obtain ⟨w, hw, rfl⟩ := (ih (by omega) t).1 ht
        obtain ⟨y, hy, rfl⟩ := (call w _).1 h2
        refine ⟨update w k y, fun i hin' hi => ?_, ?_⟩
        · by_cases hik : i = k
          · subst hik; simpa using hy
          · rw [update_of_ne hik]; exact hw i hin' (by omega)
        · funext r; simp only [fill, update_apply]
          split_ifs <;> first | rfl | omega | (exfalso; omega) | skip
          all_goals (congr 1; omega)
      · rintro ⟨w, hw, rfl⟩
        refine ⟨fill s (m + 1) k w, (ih (by omega) _).2 ⟨w, fun i h1 h2 => hw i h1 (by omega), rfl⟩, ?_⟩
        rw [call w]
        refine ⟨w k, hw k hk (by omega), ?_⟩
        funext r; simp only [fill, update_apply]
        split_ifs <;> first | rfl | omega | (exfalso; omega) | skip
        all_goals (congr 1; omega)
  have callF := fun (w : ℕ → ℕ) => hNf (fun j => m + 1 + j) m (m + n + 1)
    (fun i j _ _ h => by omega) (fun i hi => by omega) (by omega) (fun i hi => by omega)
    (List.Vector.ofFn fun j : Fin n => w j) (fill s (m + 1) n w)
    (fun i => by simp only [fill]; rw [if_pos (by omega)]; simp)
    (by simp only [fill]; rw [if_neg (by omega)]; exact hz _ le_rfl (by omega))
    (fun r h1 h2 => by
      simp only [fill]; rw [if_neg (by omega)]; exact hz _ (by omega) (by omega))
  have final : ∀ (w : ℕ → ℕ) (y : ℕ),
      (fun r => if m + 1 ≤ r ∧ r < m + 1 + n then 0 else update (fill s (m + 1) n w) m y r) =
        update s m y := by
    intro w y
    funext r; simp only [fill, update_apply]
    split_ifs <;> first | rfl | omega | (exfalso; omega) | (symm; exact hz r (by omega) (by omega))
  constructor
  · intro h
    obtain ⟨t1, h1, h'⟩ := runs_seq.1 h
    obtain ⟨t2, h2, h3⟩ := runs_seq.1 h'
    obtain ⟨w, hw, rfl⟩ := (stage n le_rfl t1).1 h1
    obtain ⟨y, hy, rfl⟩ := (callF w _).1 h2
    rw [(runs_clears _ _ _).iff_eq] at h3
    subst h3
    refine ⟨y, Part.mem_bind_iff.2 ⟨_, (mem_mOfFn _ _).2 fun i => ?_, hy⟩, final w y⟩
    simpa using hw i i.isLt i.isLt
  · rintro ⟨y, hy, rfl⟩
    obtain ⟨a, ha, hy⟩ := Part.mem_bind_iff.1 hy
    rw [mem_mOfFn] at ha
    let w : ℕ → ℕ := fun r => if h : r < n then a.get ⟨r, h⟩ else 0
    have hw : ∀ i (h : i < n), w i ∈ g ⟨i, h⟩ v := by
      intro i h; simp only [w, dif_pos h]; exact ha _
    have ha' : (List.Vector.ofFn fun j : Fin n => w j) = a := by
      ext j; simp [w]
    refine runs_seq.2 ⟨_, (stage n le_rfl _).2 ⟨w, fun i h _ => hw i h, rfl⟩,
      runs_seq.2 ⟨_, (callF w _).2 ⟨y, ha' ▸ hy, rfl⟩, ?_⟩⟩
    rw [← final w y]
    exact runs_clears _ _ _

/-! ## Recursión primitiva -/

/-- Entradas de `g` en la recursión primitiva: `(y, h y, v)` en los registros `(n+2, n+1, 1…n)`. -/
def precInp (n i : ℕ) : ℕ := if i = 0 then n + 2 else if i = 1 then n + 1 else i - 1

theorem computes_prec {n : ℕ} {f : List.Vector ℕ n → ℕ} {g : List.Vector ℕ (n + 2) → ℕ}
    {Pf Pg : Prog} (hf : Computes n (f : _ →. ℕ) Pf) (hg : Computes (n + 2) (g : _ →. ℕ) Pg) :
    ∃ P, Computes (n + 1) ((fun v : List.Vector ℕ (n + 1) =>
      v.head.rec (f v.tail) fun y IH => g (y ::ᵥ IH ::ᵥ v.tail) : List.Vector ℕ (n + 1) → ℕ) :
        _ →. ℕ) P ∧ (Pf.Mortal → Pg.Mortal → P.Mortal) := by
  obtain ⟨Nf, hNf⟩ := hf.call
  obtain ⟨Ng, hNg⟩ := hg.call
  -- registros: salida n+1, Y = n+2, Z = n+3, C = n+4, T = n+5, auxiliares desde H = n+6
  let body : Prog := .seq (.dec (n + 4)) (.seq (Pg.rename (callMap (n + 2) (precInp n) (n + 3)
    (n + 6))) (.seq (clear (n + 1)) (.seq (moveAdd (n + 3) (n + 1)) (.inc (n + 2)))))
  refine ⟨.seq (Pf.rename (callMap n (fun i => i + 1) (n + 1) (n + 6)))
    (.seq (copy 0 (n + 4) (n + 5)) (.seq (.loop (n + 4) body) (clear (n + 2)))), ?_,
    fun hmf hmg => ?_⟩
  swap
  · refine .seq (hmf.rename (callMap_injective (by intro i j _ _ h; omega) (by intro i _; omega)
      (by omega) (by intro i _; omega))) (.seq (mortal_copy (by omega) (by omega) (by omega))
      (.seq (.forLoop (.seq (hmg.rename ?_) (.seq (.clear _) (.seq (mortal_moveAdd (by omega))
      (.inc _)))) ?_) (.clear _)))
    · exact callMap_injective
        (by intro i j hi hj h; simp only [precInp] at h; split_ifs at h <;> omega)
        (by intro i hi; simp only [precInp]; split_ifs <;> omega) (by omega)
        (by intro i hi; simp only [precInp]; split_ifs <;> omega)
    · intro h
      rcases h with h | h
      · obtain ⟨r, -, hr⟩ := uses_rename h
        simp only [callMap, precInp] at hr; split_ifs at hr <;> omega
      · simp only [Prog.Uses] at h; omega
  refine computes_of_total (n + 6 + Nf + Ng) fun v s hin hz => ?_
  have hin0 : s 0 = v.head := by simpa using hin 0
  have hinS : ∀ i : Fin n, s (i + 1) = v.tail.get i := by
    intro i; simpa using hin i.succ
  let hr : ℕ → ℕ := fun y => Nat.rec (motive := fun _ => ℕ) (f v.tail)
    (fun y IH => g (y ::ᵥ IH ::ᵥ v.tail)) y
  let a := v.head
  let L : ℕ → Regs := fun y =>
    update (update (update s (n + 1) (hr y)) (n + 2) y) (n + 4) (a - y)
  have body_step : ∀ y, y < a → Runs body (L y) (L (y + 1)) := by
    intro y hy
    have callG := hNg (precInp n) (n + 3) (n + 6)
      (by intro i j hi hj h; simp only [precInp] at h; split_ifs at h <;> omega)
      (by intro i hi; simp only [precInp]; split_ifs <;> omega) (by omega)
      (by intro i hi; simp only [precInp]; split_ifs <;> omega)
      (y ::ᵥ hr y ::ᵥ v.tail) (update (L y) (n + 4) (L y (n + 4) - 1))
      (by
        intro ⟨i, hi⟩
        rcases i with _ | _ | i
        · simp [L, precInp, update_apply]
        · simp [L, precInp]; rfl
        · have := hinS ⟨i, by omega⟩
          simp only [L, precInp, update_apply, show i + 1 + 1 ≠ 0 by omega,
            show i + 1 + 1 ≠ 1 by omega, ↓reduceIte, show i + 1 + 1 - 1 = i + 1 by omega]
          split_ifs <;> try omega
          exact this.trans rfl)
      (by simp [L, update_apply]; exact hz _ (by omega) (by omega))
      (by
        intro r h1 h2
        simp only [L, update_apply]
        split_ifs <;> try omega
        exact hz _ (by omega) (by omega))
    refine .seq (.dec _ _) (.seq ((callG _).2 ⟨g (y ::ᵥ hr y ::ᵥ v.tail), by simp [PFun.coe_val], rfl⟩)
      (.seq (runs_clear _ _) (.seq (runs_moveAdd (by omega) _) ?_)))
    convert Runs.inc (n + 2) _ using 1
    funext r
    simp only [L, update_apply]
    split_ifs <;> first | omega | rfl | skip
    all_goals first
      | contradiction
      | exact (zero_add _).symm
      | (simp only [hr, zero_add])
      | exact hz _ (by omega) (by omega)
      | (rw [Nat.sub_self]; exact hz _ (by omega) (by omega))
      | (rw [hz (n + 4) (by omega) (by omega), hin0]; simp [a])
  have loop_runs : ∀ j y, y + j = a → Runs (.loop (n + 4) body) (L y) (L a) := by
    intro j
    induction j with
    | zero => intro y hy; subst hy; exact .loopStop (by simp [L])
    | succ j ih =>
      intro y hy
      exact .loopStep (by simp [L]; omega) (body_step y (by omega)) (ih (y + 1) (by omega))
  have callF := hNf (fun i => i + 1) (n + 1) (n + 6) (by intro i j _ _ h; omega)
    (by intro i hi; omega) (by omega) (by intro i hi; omega) v.tail s
    (fun i => hinS i) (hz _ (by omega) (by omega))
    (fun r h1 h2 => hz _ (by omega) (by omega))
  refine .seq ((callF _).2 ⟨f v.tail, by simp [PFun.coe_val], rfl⟩) (.seq (runs_copy (by omega)
    (by omega) (by omega) _ (by simp [update_apply]; exact hz _ (by omega) (by omega))) ?_)
  have e0 : update (update s (n + 1) (f v.tail)) (n + 4)
      (update s (n + 1) (f v.tail) (n + 4) + update s (n + 1) (f v.tail) 0) = L 0 := by
    funext r
    simp only [L, update_apply]
    split_ifs <;> first | omega | rfl | skip
    all_goals first
      | contradiction
      | exact (zero_add _).symm
      | (simp only [hr, zero_add])
      | exact hz _ (by omega) (by omega)
      | (rw [Nat.sub_self]; exact hz _ (by omega) (by omega))
      | (rw [hz (n + 4) (by omega) (by omega), hin0]; simp [a])
  rw [e0]
  refine .seq (loop_runs a 0 (by omega)) ?_
  convert runs_clear (n + 2) _ using 1
  funext r
  simp only [L, update_apply]
  split_ifs <;> first | omega | rfl | skip
  all_goals first
    | contradiction
    | exact (zero_add _).symm
      | (simp only [hr, zero_add])
    | exact hz _ (by omega) (by omega)
    | (rw [Nat.sub_self]; exact hz _ (by omega) (by omega))
    | (rw [hz (n + 4) (by omega) (by omega), hin0]; simp [a])

/-! ## Minimización -/

/-- Entradas de `f` en la minimización: `(k, v)` en los registros `(n, 0…n-1)`. -/
def rfindInp (n i : ℕ) : ℕ := if i = 0 then n else i - 1

theorem computes_rfind {n : ℕ} {f : List.Vector ℕ (n + 1) → ℕ} {Pf : Prog}
    (hf : Computes (n + 1) (f : _ →. ℕ) Pf) :
    ∃ P, Computes n (fun v => Nat.rfind fun k => Part.some (decide (f (k ::ᵥ v) = 0))) P := by
  obtain ⟨Nf, hNf⟩ := hf.call
  let Pf' := Pf.rename (callMap (n + 1) (rfindInp n) (n + 1) (n + 2))
  let body : Prog := .seq (clear (n + 1)) (.seq (.inc n) Pf')
  refine ⟨.seq Pf' (.loop (n + 1) body), n + 2 + Nf, fun v s hin hz s' => ?_⟩
  let K : ℕ → Regs := fun k => update (update s n k) (n + 1) (f (k ::ᵥ v))
  have callF : ∀ k s', Runs Pf' (update s n k) s' ↔ s' = K k := by
    intro k s'
    rw [hNf (rfindInp n) (n + 1) (n + 2)
      (by intro i j hi hj h; simp only [rfindInp] at h; split_ifs at h <;> omega)
      (by intro i hi; simp only [rfindInp]; split_ifs <;> omega) (by omega)
      (by intro i hi; simp only [rfindInp]; split_ifs <;> omega)
      (k ::ᵥ v) (update s n k)
      (by
        intro ⟨i, hi⟩
        rcases i with _ | i
        · simp [rfindInp]
        · have := hin ⟨i, by omega⟩
          simp only [rfindInp, update_apply, show i + 1 ≠ 0 by omega, ↓reduceIte,
            show i + 1 - 1 = i by omega, show i ≠ n by omega]
          exact this.trans rfl)
      (by simp only [update_apply]; rw [if_neg (by omega)]; exact hz _ (by omega) (by omega))
      (by
        intro r h1 h2
        simp only [update_apply]; rw [if_neg (by omega)]; exact hz _ (by omega) (by omega))]
    simp [PFun.coe_val, K]
  have hT : s (n + 1) = 0 := hz _ (by omega) (by omega)
  have bodyK : ∀ k, Runs body (K k) (K (k + 1)) := by
    intro k
    refine .seq (runs_clear _ _) (.seq (.inc n _) ?_)
    have e : update (update (K k) (n + 1) 0) n (update (K k) (n + 1) 0 n + 1) =
        update s n (k + 1) := by
      funext r; simp only [K, update_apply]
      split_ifs <;> first | omega | rfl | (subst_vars; exact hT.symm)
    rw [e]; exact (callF (k + 1) _).2 rfl
  have loopK : ∀ k s', Runs (.loop (n + 1) body) (K k) s' ↔
      ∃ k', k ≤ k' ∧ f (k' ::ᵥ v) = 0 ∧ (∀ j, k ≤ j → j < k' → f (j ::ᵥ v) ≠ 0) ∧ s' = K k' := by
    intro k s'
    constructor
    · intro h
      generalize hst : K k = st at h
      generalize hq : Prog.loop (n + 1) body = q at h
      induction h generalizing k with
      | loopStop hr =>
        cases hq; subst hst
        refine ⟨k, le_rfl, by simpa [K] using hr, fun j h1 h2 => by omega, rfl⟩
      | @loopStep r p st t u hr h1 _ _ ih2 =>
        cases hq; subst hst
        obtain rfl := h1.det (bodyK k)
        obtain ⟨k', hk', h0, hne, rfl⟩ := ih2 (k + 1) rfl rfl
        refine ⟨k', by omega, h0, fun j hj1 hj2 => ?_, rfl⟩
        rcases Nat.eq_or_lt_of_le hj1 with rfl | hj1
        · simpa [K] using hr
        · exact hne j (by omega) hj2
      | _ => cases hq
    · rintro ⟨k', hk', h0, hne, rfl⟩
      obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hk'
      induction d generalizing k with
      | zero => exact .loopStop (by simpa [K] using h0)
      | succ d ih =>
        refine .loopStep (by simpa [K] using hne k le_rfl (by omega)) (bodyK k) ?_
        rw [show k + (d + 1) = (k + 1) + d by omega]
        exact ih (k + 1) (by omega) (by rwa [show k + 1 + d = k + (d + 1) by omega])
          (fun j h1 h2 => hne j (by omega) (by omega))
  have e0 : update s n 0 = s := by
    rw [update_eq_self_iff]; exact (hz n le_rfl (by omega)).symm
  have hKfin : ∀ k, f (k ::ᵥ v) = 0 → K k = update s n k := by
    intro k hk
    funext r; simp only [K, update_apply]
    split_ifs <;> first | omega | rfl | (subst_vars; rw [hk, hT])
  rw [runs_seq]
  constructor
  · rintro ⟨t, h1, h2⟩
    rw [← e0, callF] at h1
    subst h1
    obtain ⟨k', -, h0, hne, rfl⟩ := (loopK 0 s').1 h2
    refine ⟨k', ?_, hKfin k' h0⟩
    refine Nat.mem_rfind.2 ⟨by simpa using h0, fun hm => ?_⟩
    simpa using hne _ (Nat.zero_le _) hm
  · rintro ⟨y, hy, rfl⟩
    obtain ⟨h0, hne⟩ := Nat.mem_rfind.1 hy
    refine ⟨K 0, by rw [← e0, callF], (loopK 0 _).2 ⟨y, Nat.zero_le _, by simpa using h0,
      fun j _ hj => by simpa using hne hj, (hKfin y (by simpa using h0)).symm⟩⟩

/-! ## Teorema de compilación -/

theorem computes_of_primrec' {n : ℕ} {f : List.Vector ℕ n → ℕ} (hf : Nat.Primrec' f) :
    ∃ P, Computes n (f : _ →. ℕ) P ∧ P.Mortal := by
  induction hf with
  | zero => exact ⟨_, computes_zero, .skip⟩
  | succ => exact ⟨_, computes_succ, .seq (mortal_copy (by omega) (by omega) (by omega)) (.inc _)⟩
  | get i => exact ⟨_, computes_get i, mortal_copy (by omega) (by omega) (by omega)⟩
  | @comp m n f g _ _ ihf ihg =>
    obtain ⟨Pf, hPf, hmf⟩ := ihf
    choose Pg hPg hmg using ihg
    obtain ⟨P, hP, hm⟩ := computes_comp hPf Pg hPg
    refine ⟨P, ?_, hm hmf hmg⟩
    have e : ((fun a => f (List.Vector.ofFn fun i => g i a) : List.Vector ℕ m → ℕ) : List.Vector ℕ m →. ℕ) =
        fun v => (List.Vector.mOfFn fun i => ((g i : List.Vector ℕ m → ℕ) : List.Vector ℕ m →. ℕ) v) >>=
          (f : List.Vector ℕ n →. ℕ) := by
      funext v
      simp only [PFun.coe_val, ← Part.pure_eq_some, List.Vector.mOfFn_pure, pure_bind]
      exact (Part.bind_some _ _).symm
    rw [e]; exact hP
  | prec _ _ ihf ihg =>
    obtain ⟨Pf, hPf, hmf⟩ := ihf
    obtain ⟨Pg, hPg, hmg⟩ := ihg
    obtain ⟨P, hP, hm⟩ := computes_prec hPf hPg
    exact ⟨P, hP, hm hmf hmg⟩

/-- **Toda función parcial recursiva (base `Nat.Partrec'`) se calcula con un programa WHILE.** -/
theorem computes_of_partrec' {n : ℕ} {f : List.Vector ℕ n →. ℕ} (hf : Nat.Partrec' f) :
    ∃ P, Computes n f P := by
  induction hf with
  | prim hf => exact (computes_of_primrec' hf).imp fun _ h => h.1
  | comp g _ _ ihf ihg =>
    obtain ⟨Pf, hPf⟩ := ihf
    choose Pg hPg using ihg
    exact (computes_comp hPf Pg hPg).imp fun _ h => h.1
  | rfind _ ihf =>
    obtain ⟨Pf, hPf⟩ := ihf
    exact computes_rfind hPf

end Conway
