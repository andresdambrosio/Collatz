import Collatz.Conway.Outer
import Collatz.Conway.Affine

/-!
# Kurtz–Simon: "¿toda órbita llega a 1?" no es ni semidecidible ni co-semidecidible

Kurtz y Simon (TAMC 2007) probaron que, para funciones de Collatz generalizadas *afines*
`g(n) = a_j n + b_j` (`n ≡ j mod D`, `a_j, b_j` racionales), el problema

  dada `g`, ¿para todo `n > 0` existe `i` con `g^i(n) = 1`?

es Π₂-completo. Acá formalizamos:

* `ks_reduction`: para toda `F` recursiva primitiva de dos variables hay una familia computable
  `m ↦ (D, tabla)` de funciones afines genuinas con
  `(toda órbita llega a 1) ↔ ∀ x, ∃ x' ≥ x, F(m, x') = 0` (la forma normal Π₂);
* `allReachOne_not_re`: el conjunto de presentaciones con "toda órbita llega a 1" no es r.e.;
* `allReachOne_not_core`: su complemento tampoco es r.e.;
* `allReachOne_undecidable`: en particular, no es decidible.

La Π₂-completitud propiamente dicha (que *todo* conjunto Π₂ se reduce) necesita además la forma
normal de Kleene para Π₂ con el predicado recursivo primitivo de Mathlib; no está formalizada acá.

Cadena: `Prog.Mortal` (programas con bucles `for`, que salen de su código desde cualquier
configuración) → `outer` (bucle `while F(m, x) ≠ 0: x++`, que recarga `m` con una instrucción `addc`)
→ `kstep` (función afín: FRACTRAN + limpieza de basura + `n ↦ (n+1)/2`).
-/

namespace Conway

open Function Prog Machine Encodable Denumerable
open Nat.Partrec (Code)
open Nat.Partrec.Code (eval evaln)

/-! ## `m` sólo en la tabla -/

/-- Cambia la constante de una instrucción `addc` por `m`. -/
def Instr.setK (m : ℕ) : Instr → Instr
  | .inc r j => .inc r j
  | .decjz r j k => .decjz r j k
  | .addc r _ j => .addc r m j

theorem len_setK (m : ℕ) : ∀ p : Prog, (p.setK m).len = p.len
  | .skip => rfl
  | .inc _ => rfl
  | .dec _ => rfl
  | .addc _ _ => rfl
  | .seq p q => by simp [Prog.setK, len, len_setK m p, len_setK m q]
  | .loop r p => by simp [Prog.setK, len, len_setK m p]

theorem bound_setK (m : ℕ) : ∀ p : Prog, (p.setK m).bound = p.bound
  | .skip => rfl
  | .inc _ => rfl
  | .dec _ => rfl
  | .addc _ _ => rfl
  | .seq p q => by simp [Prog.setK, Prog.bound, bound_setK m p, bound_setK m q]
  | .loop r p => by simp [Prog.setK, Prog.bound, bound_setK m p]

theorem compile_setK (m : ℕ) : ∀ (b : ℕ) (p : Prog),
    compile b (p.setK m) = (compile b p).map (Instr.setK m)
  | _, .skip => rfl
  | _, .inc _ => rfl
  | _, .dec _ => rfl
  | _, .addc _ _ => rfl
  | b, .seq p q => by
    simp [Prog.setK, compile, compile_setK m b p, compile_setK m _ q, len_setK]
  | b, .loop r p => by simp [Prog.setK, compile, compile_setK m _ p, len_setK, Instr.setK]

theorem outer_setK {C : Prog} (hC : C.Mortal) (N m : ℕ) : (outer C N 0).setK m = outer C N m := by
  simp [outer, stage, obody, Prog.setK, hC.setK, (mortal_clr N).setK]

/-! ## La plantilla de reglas: `m` aparece sólo como factor `2^m` -/

/-- Fracciones de una instrucción con una "base" (la tercera coordenada) que se eleva a `m`. -/
noncomputable def blockT (R i : ℕ) : Instr → List (ℕ × ℕ × ℕ)
  | .inc r j => [(pr r * pr (R + j), pr (R + i), 1)]
  | .decjz r j k => [(pr (R + j), pr (R + i) * pr r, 1), (pr (R + k), pr (R + i), 1)]
  | .addc r _ j => [(pr (R + j), pr (R + i), pr r)]

noncomputable def fracsFromT (R : ℕ) : ℕ → List Instr → List (ℕ × ℕ × ℕ)
  | _, [] => []
  | i, x :: xs => blockT R i x ++ fracsFromT R (i + 1) xs

def lift1 (q : ℕ × ℕ) : ℕ × ℕ × ℕ := (q.1, q.2, 1)

noncomputable def rulesT (R : ℕ) (M : Machine) : List (ℕ × ℕ × ℕ) :=
  (pairs R M.length).map lift1 ++
    (fracsFromT R 0 M ++ ((1, pr (R + M.length), 1) :: (strips R).map lift1))

/-- Evaluar la plantilla en `m`. -/
def evT (m : ℕ) (t : ℕ × ℕ × ℕ) : ℕ × ℕ := (t.2.2 ^ m * t.1, t.2.1)

theorem evT_comp_lift1 (m : ℕ) : evT m ∘ lift1 = id := by
  funext q; simp [evT, lift1]

theorem fracsFrom_setK (R m : ℕ) : ∀ (i : ℕ) (xs : List Instr),
    fracsFrom R i (xs.map (Instr.setK m)) = (fracsFromT R i xs).map (evT m)
  | _, [] => rfl
  | i, x :: xs => by
    rw [List.map_cons, fracsFrom, fracsFromT, List.map_append, fracsFrom_setK R m (i + 1) xs]
    congr 1
    cases x <;> simp [Instr.setK, block, blockT, evT]

theorem rules_setK (R m : ℕ) (M : Machine) :
    rules R (M.map (Instr.setK m)) = (rulesT R M).map (evT m) := by
  simp only [rules, rulesT, List.length_map, fracsFrom_setK, List.map_append, List.map_cons,
    List.map_map, evT_comp_lift1, List.map_id]
  simp [evT]

theorem pos_of_mem_rulesT {R : ℕ} {M : Machine} : ∀ t ∈ rulesT R M, 0 < t.2.1 := by
  have hb : ∀ i x, ∀ t ∈ blockT R i x, 0 < t.2.1 := by
    intro i x t ht
    cases x <;> simp [blockT] at ht <;> rcases ht with rfl | rfl <;>
      simp [Nat.mul_pos, pr_pos]
  have hf : ∀ (xs : List Instr) i, ∀ t ∈ fracsFromT R i xs, 0 < t.2.1 := by
    intro xs
    induction xs with
    | nil => simp [fracsFromT]
    | cons x xs ih =>
      intro i t ht
      simp only [fracsFromT, List.mem_append] at ht
      rcases ht with ht | ht
      · exact hb i x t ht
      · exact ih (i + 1) t ht
  intro t ht
  simp only [rulesT, List.mem_append, List.mem_cons, List.mem_map] at ht
  rcases ht with ⟨q, hq, rfl⟩ | ht | rfl | ⟨q, hq, rfl⟩
  · obtain ⟨a, b, -, -, rfl⟩ := mem_pairs hq
    simp [lift1, Nat.mul_pos, pr_pos]
  · exact hf M 0 t ht
  · simp [pr_pos]
  · simp only [strips, List.mem_map] at hq
    obtain ⟨r, -, rfl⟩ := hq
    simp [lift1, pr_pos]

/-! ## Presentación por residuos -/

/-- Función afín presentada por `(D, tabla)`: si `n ≡ j (mod D)` y la entrada `j` es `(a, b, c)`,
`n ↦ (a n + b) / c`. -/
def agcf (D : ℕ) (t : List (ℕ × ℕ × ℕ)) (n : ℕ) : ℕ :=
  ((t.getD (n % D) (1, 0, 1)).1 * n + (t.getD (n % D) (1, 0, 1)).2.1) /
    (t.getD (n % D) (1, 0, 1)).2.2

/-- La regla "primera fracción aplicable, si no `(n+1)/2`" para una lista de fracciones. -/
def kstepL (l : List (ℕ × ℕ)) (n : ℕ) : ℕ :=
  match l.find? (fun q => decide (q.2 ∣ n)) with
  | some q => q.1 * (n / q.2)
  | none => (n + 1) / 2

theorem kstep_eq_kstepL (R : ℕ) (M : Machine) : kstep R M = kstepL (rules R M) := rfl

def denProd (T : List (ℕ × ℕ × ℕ)) : ℕ := (T.map fun t => t.2.1).prod

/-- Entrada de la tabla para el residuo `j`: `(a, b, c, base)`. -/
def entryT (T : List (ℕ × ℕ × ℕ)) (j : ℕ) : ℕ × ℕ × ℕ × ℕ :=
  match T.find? (fun t => decide (t.2.1 ∣ j)) with
  | some t => (t.1, 0, t.2.1, t.2.2)
  | none => (1, 1, 2, 1)

def tableT (T : List (ℕ × ℕ × ℕ)) : List (ℕ × ℕ × ℕ × ℕ) :=
  (List.range (denProd T)).map (entryT T)

/-- Instanciar una entrada en `m`. -/
def instT (m : ℕ) (e : ℕ × ℕ × ℕ × ℕ) : ℕ × ℕ × ℕ := (e.2.2.2 ^ m * e.1, e.2.1, e.2.2.1)

theorem find?_congr' {α : Type*} {p q : α → Bool} :
    ∀ {l : List α}, (∀ x ∈ l, p x = q x) → l.find? p = l.find? q
  | [], _ => rfl
  | x :: l, h => by
    rw [List.find?_cons, List.find?_cons, h x (by simp), find?_congr' fun y hy => h y (by simp [hy])]

theorem denProd_pos {T : List (ℕ × ℕ × ℕ)} (hT : ∀ t ∈ T, 0 < t.2.1) : 0 < denProd T :=
  List.prod_pos fun b hb => by
    obtain ⟨t, ht, rfl⟩ := List.mem_map.1 hb; exact hT t ht

theorem getD_table {T : List (ℕ × ℕ × ℕ)} (hT : ∀ t ∈ T, 0 < t.2.1) (m n : ℕ) :
    ((tableT T).map (instT m)).getD (n % denProd T) (1, 0, 1) =
      instT m (match T.find? (fun t => decide (t.2.1 ∣ n)) with
        | some t => (t.1, 0, t.2.1, t.2.2)
        | none => (1, 1, 2, 1)) := by
  have hlt : n % denProd T < denProd T := Nat.mod_lt _ (denProd_pos hT)
  rw [List.getD_eq_getElem _ _ (by simpa [tableT] using hlt)]
  simp only [List.getElem_map, tableT, List.getElem_range, entryT]
  rw [find?_congr' (q := fun t => decide (t.2.1 ∣ n)) fun t ht => by
    have hdv : t.2.1 ∣ denProd T := List.dvd_prod (List.mem_map_of_mem (f := fun t => t.2.1) ht)
    simp [Nat.dvd_mod_iff hdv]]

/-- La presentación por residuos calcula la regla de la plantilla. -/
theorem agcf_eq {T : List (ℕ × ℕ × ℕ)} (hT : ∀ t ∈ T, 0 < t.2.1) (m n : ℕ) :
    agcf (denProd T) ((tableT T).map (instT m)) n = kstepL (T.map (evT m)) n := by
  unfold agcf kstepL
  rw [getD_table hT, List.find?_map]
  have : ((fun q : ℕ × ℕ => decide (q.2 ∣ n)) ∘ evT m) = fun t => decide (t.2.1 ∣ n) := rfl
  rw [this]
  cases h : T.find? (fun t => decide (t.2.1 ∣ n)) with
  | none => simp [instT]
  | some t =>
    have hd : t.2.1 ∣ n := by simpa using List.find?_some h
    simp only [instT, Option.map_some, evT, add_zero]
    exact Nat.mul_div_assoc _ hd

/-- **Es una función de Collatz generalizada afín genuina**: en cada clase `j (mod D)` es
`n ↦ a_j n + b_j` con `a_j, b_j` racionales (siempre que la plantilla tenga la regla `(1, 2)`). -/
theorem agcf_rat {T : List (ℕ × ℕ × ℕ)} (hT : ∀ t ∈ T, 0 < t.2.1) (h2 : (1, 2, 1) ∈ T) (m : ℕ) :
    ∃ a b : ℕ → ℚ, ∀ n, (agcf (denProd T) ((tableT T).map (instT m)) n : ℚ) =
      a (n % denProd T) * n + b (n % denProd T) := by
  set tb := (tableT T).map (instT m)
  refine ⟨fun j => ((tb.getD j (1, 0, 1)).1 : ℚ) / (tb.getD j (1, 0, 1)).2.2,
    fun j => ((tb.getD j (1, 0, 1)).2.1 : ℚ) / (tb.getD j (1, 0, 1)).2.2, fun n => ?_⟩
  have key : (tb.getD (n % denProd T) (1, 0, 1)).2.2 ∣
      (tb.getD (n % denProd T) (1, 0, 1)).1 * n + (tb.getD (n % denProd T) (1, 0, 1)).2.1 ∧
      (tb.getD (n % denProd T) (1, 0, 1)).2.2 ≠ 0 := by
    simp only [tb, getD_table hT]
    cases h : T.find? (fun t => decide (t.2.1 ∣ n)) with
    | none =>
      have hn : ¬ 2 ∣ n := by
        have := List.find?_eq_none.1 h _ h2
        simpa using this
      simp only [instT, one_pow, mul_one, one_mul]
      exact ⟨by omega, by norm_num⟩
    | some t =>
      have hd : t.2.1 ∣ n := by simpa using List.find?_some h
      exact ⟨by simpa [instT] using Dvd.dvd.mul_left hd _,
        by simpa [instT] using (hT t (List.mem_of_find?_eq_some h)).ne'⟩
  unfold agcf
  rw [Nat.cast_div key.1 (by exact_mod_cast key.2)]
  push_cast
  rw [add_div, mul_div_right_comm]

/-! ## El teorema genérico -/

/-- Toda órbita (de enteros positivos) llega a 1. -/
def AllReachOne (p : ℕ × List (ℕ × ℕ × ℕ)) : Prop := ∀ n, 0 < n → ∃ i, (agcf p.1 p.2)^[i] n = 1

theorem allReachOne_iff (D : ℕ) (t : List (ℕ × ℕ × ℕ)) :
    AllReachOne (D, t) ↔ ∀ n, 0 < n → ∃ i, (agcf D t)^[i] n = 1 := Iff.rfl

section generic

variable {C : Prog} {N : ℕ} {f : ℕ → ℕ → ℕ}
  (hC : ∀ s : Regs, (∀ r, 2 ≤ r → r < N → s r = 0) → Runs C s (update s 2 (f (s 0) (s 1))))
  (hCm : C.Mortal)
include hC hCm

theorem allOne_iff (m : ℕ) :
    (∀ n, 0 < n → ∃ i, (kstep (outer C N 0).bound (outer C N m).toMachine)^[i] n = 1) ↔
      ∀ x, ∃ x' ≥ x, f m x' = 0 := by
  set R := (outer C N 0).bound
  set M := (outer C N m).toMachine
  have hR : ∀ x ∈ M, x.reg < R := fun x hx => by
    have := reg_lt_of_mem_compile _ 0 x hx
    rwa [← outer_setK hCm N m, bound_setK] at this
  have hJ : ∀ x ∈ M, x.JumpsLe M.length := fun x hx => by
    have := jumpsLe_compile _ 0 x hx
    simpa [M, Prog.toMachine, length_compile] using this
  constructor
  · intro h
    by_contra hcon
    push Not at hcon
    obtain ⟨x, hx⟩ := hcon
    have hnh := outer_not_halts hC hCm m x (fun x' hx' => hx x' hx')
    obtain ⟨i, hi⟩ := h (enc R (headCfg C N m f x)) (Nat.mul_pos (pr_pos _) (body_pos _ _))
    exact iterate_kstep_ne_one hR _ hnh i hi
  · intro h
    exact allOne_of_mortal hR hJ fun c _ _ => outer_mortal hC hCm m h c

end generic

theorem primrec_pow : Primrec₂ ((· ^ ·) : ℕ → ℕ → ℕ) := Primrec₂.unpaired'.1 Nat.Primrec.pow

theorem primrec_instT : Primrec₂ instT := by
  unfold instT
  exact Primrec.pair (Primrec.nat_mul.comp (primrec_pow.comp
    (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.snd))) Primrec.fst)
    (Primrec.fst.comp Primrec.snd)) (Primrec.pair (Primrec.fst.comp (Primrec.snd.comp Primrec.snd))
    (Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.snd))))

/-- **Reducción genérica.** Para toda `F` recursiva primitiva de dos variables hay una familia
computable de funciones de Collatz afines genuinas `ι m = (D, tabla)` con
`toda órbita llega a 1 ↔ ∀ x, ∃ x' ≥ x, F(m, x') = 0`. -/
theorem ks_reduction {F : List.Vector ℕ 2 → ℕ} (hF : Nat.Primrec' F) :
    ∃ ι : ℕ → ℕ × List (ℕ × ℕ × ℕ), Computable ι ∧
      (∀ m, AllReachOne (ι m) ↔ ∀ x, ∃ x' ≥ x, F (m ::ᵥ x' ::ᵥ List.Vector.nil) = 0) ∧
      ∀ m, ∃ a b : ℕ → ℚ, ∀ n, (agcf (ι m).1 (ι m).2 n : ℚ) =
        a (n % (ι m).1) * n + b (n % (ι m).1) := by
  obtain ⟨C, ⟨N, hN⟩, hCm⟩ := computes_of_primrec' hF
  have hC : ∀ s : Regs, (∀ r, 2 ≤ r → r < N → s r = 0) →
      Runs C s (update s 2 ((fun a b => F (a ::ᵥ b ::ᵥ List.Vector.nil)) (s 0) (s 1))) := by
    intro s hz
    refine (hN (s 0 ::ᵥ s 1 ::ᵥ List.Vector.nil) s (fun i => by fin_cases i <;> rfl) hz _).2
      ⟨F _, by simp [PFun.coe_val], rfl⟩
  set R := (outer C N 0).bound
  set M0 := (outer C N 0).toMachine
  set T := rulesT R M0
  have hT : ∀ t ∈ T, 0 < t.2.1 := pos_of_mem_rulesT
  have hM : ∀ m, (outer C N m).toMachine = M0.map (Instr.setK m) := fun m => by
    rw [← outer_setK hCm N m]; exact compile_setK m 0 _
  have hk : ∀ m, kstep R (outer C N m).toMachine = agcf (denProd T) ((tableT T).map (instT m)) := by
    intro m; funext n
    rw [kstep_eq_kstepL, hM, rules_setK, agcf_eq hT]
  refine ⟨fun m => (denProd T, (tableT T).map (instT m)), ?_, fun m => ?_, fun m => ?_⟩
  · exact (Primrec.pair (Primrec.const _)
      (Primrec.list_map (Primrec.const _) (primrec_instT.comp Primrec.fst Primrec.snd))).to_comp
  · have h1 := allOne_iff (f := fun a b => F (a ::ᵥ b ::ᵥ List.Vector.nil)) hC hCm m
    rw [hk m] at h1
    rw [allReachOne_iff]
    exact h1
  · have hR1 : 1 ≤ R := by
      simp only [R, outer, stage, clr, Prog.bound]; omega
    refine agcf_rat hT ?_ m
    simp only [T, rulesT, List.mem_append, List.mem_cons, List.mem_map, strips]
    right; right; right
    exact ⟨(1, 2), ⟨0, List.mem_range.2 hR1, by rw [pr_zero]⟩, rfl⟩

/-! ## Las dos instancias: no r.e. y no co-r.e. -/

/-- `1` si `c` (código `m`) se detuvo en `≤ x` pasos sobre la entrada 0; si no, `0`. -/
def haltedBy (v : List.Vector ℕ 2) : ℕ :=
  bif (evaln v.tail.head (ofNat Code v.head) 0).isSome then 1 else 0

/-- `0` si `c` (código `m`) se detuvo en `≤ x` pasos sobre la entrada 0; si no, `1`. -/
def notHaltedBy (v : List.Vector ℕ 2) : ℕ :=
  bif (evaln v.tail.head (ofNat Code v.head) 0).isSome then 0 else 1

theorem primrec_isSome_evaln :
    Primrec fun v : List.Vector ℕ 2 => (evaln v.tail.head (ofNat Code v.head) 0).isSome :=
  Primrec.option_isSome.comp (Nat.Partrec.Code.primrec_evaln.comp (Primrec.pair (Primrec.pair
    (Primrec.vector_head.comp Primrec.vector_tail) ((Primrec.ofNat Code).comp Primrec.vector_head))
    (Primrec.const 0)))

theorem primrec'_haltedBy : Nat.Primrec' haltedBy :=
  Nat.Primrec'.of_prim (Primrec.cond primrec_isSome_evaln (Primrec.const 1) (Primrec.const 0))

theorem primrec'_notHaltedBy : Nat.Primrec' notHaltedBy :=
  Nat.Primrec'.of_prim (Primrec.cond primrec_isSome_evaln (Primrec.const 0) (Primrec.const 1))

theorem isSome_evaln_iff (c : Code) : (∃ k, (evaln k c 0).isSome) ↔ (eval c 0).Dom := by
  constructor
  · rintro ⟨k, hk⟩
    obtain ⟨y, hy⟩ := Option.isSome_iff_exists.1 hk
    exact Part.dom_iff_mem.2 ⟨y, Nat.Partrec.Code.evaln_sound hy⟩
  · intro h
    obtain ⟨y, hy⟩ := Part.dom_iff_mem.1 h
    obtain ⟨k, hk⟩ := Nat.Partrec.Code.evaln_complete.1 hy
    exact ⟨k, Option.isSome_iff_exists.2 ⟨y, hk⟩⟩

theorem isSome_evaln_mono {c : Code} {k k' : ℕ} (h : k ≤ k') (hk : (evaln k c 0).isSome) :
    (evaln k' c 0).isSome := by
  obtain ⟨y, hy⟩ := Option.isSome_iff_exists.1 hk
  exact Option.isSome_iff_exists.2 ⟨y, Nat.Partrec.Code.evaln_mono h hy⟩

/-- **"Toda órbita llega a 1" no es r.e.** -/
theorem allReachOne_not_re : ¬ REPred AllReachOne := by
  intro hre
  obtain ⟨ι, hι, hiff, -⟩ := ks_reduction primrec'_haltedBy
  apply ComputablePred.halting_problem_not_re 0
  have h2 : REPred fun c : Code => AllReachOne (ι (encode c)) := hre.comp (hι.comp Computable.encode)
  refine h2.of_eq fun c => ?_
  -- `∀ x, ∃ x' ≥ x, haltedBy (c, x') = 0` sii `c` no se detiene
  rw [hiff]
  simp only [haltedBy, List.Vector.head_cons, List.Vector.tail_cons, ofNat_encode]
  constructor
  · intro h hdom
    obtain ⟨k, hk⟩ := (isSome_evaln_iff c).2 hdom
    obtain ⟨x', hx', h0⟩ := h k
    rw [isSome_evaln_mono hx' hk] at h0
    simp at h0
  · intro h x
    refine ⟨x, le_rfl, ?_⟩
    have : (evaln x c 0).isSome = false := by
      by_contra h'
      exact h ((isSome_evaln_iff c).1 ⟨x, by revert h'; cases (evaln x c 0).isSome <;> simp⟩)
    rw [this]; rfl

/-- **El complemento de "toda órbita llega a 1" tampoco es r.e.** -/
theorem allReachOne_not_core : ¬ REPred fun p => ¬ AllReachOne p := by
  intro hre
  obtain ⟨ι, hι, hiff, -⟩ := ks_reduction primrec'_notHaltedBy
  apply ComputablePred.halting_problem_not_re 0
  have h2 : REPred fun c : Code => ¬ AllReachOne (ι (encode c)) :=
    hre.comp (hι.comp Computable.encode)
  refine h2.of_eq fun c => not_congr ?_
  -- `∀ x, ∃ x' ≥ x, notHaltedBy (c, x') = 0` sii `c` se detiene
  rw [hiff]
  simp only [notHaltedBy, List.Vector.head_cons, List.Vector.tail_cons, ofNat_encode]
  constructor
  · intro h
    obtain ⟨x', -, h0⟩ := h 0
    refine (isSome_evaln_iff c).1 ⟨x', ?_⟩
    revert h0; cases (evaln x' c 0).isSome <;> simp
  · intro hdom x
    obtain ⟨k, hk⟩ := (isSome_evaln_iff c).2 hdom
    refine ⟨max x k, le_max_left _ _, ?_⟩
    rw [isSome_evaln_mono (le_max_right _ _) hk]
    rfl

/-- En particular, "toda órbita llega a 1" es indecidible. -/
theorem allReachOne_undecidable : ¬ ComputablePred AllReachOne := fun h =>
  allReachOne_not_re h.to_re

end Conway
