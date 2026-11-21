import Collatz.Bridge

/-!
# Collatz como sistema de reescritura (Yolcu–Aaronson–Heule)

Formalización del sistema `𝒯` de E. Yolcu, S. Aaronson, M. Heule, *An Automated Approach to
the Collatz Conjecture* (arXiv 2105.14697), §3. Alfabeto: dígitos binarios `f` (0), `t` (1) y
ternarios `0, 1, 2`, más marcadores `▷` (inicio, vale 1) y `◁` (fin). Una palabra `▷ w ◁` se lee
de izquierda a derecha empezando en `1`: `f x = 2x`, `t x = 2x+1`, `d x = 3x+d`.

Reglas (11):
* dinámicas: `f◁ → ◁`, `t◁ → 2◁` (aplican el mapa acelerado `Collatz.T`);
* auxiliares: `f0 → 0f`, `f1 → 0t`, `f2 → 1f`, `t0 → 1t`, `t1 → 2f`, `t2 → 2t`;
* de inicio: `▷0 → ▷t`, `▷1 → ▷ff`, `▷2 → ▷ft`.

Las auxiliares y las de inicio no cambian el valor; las dinámicas aplican `Collatz.T`.

Representamos sólo la palabra interna `w` (los marcadores quedan implícitos), así que
`Terminates` es terminación sobre las palabras canónicas `▷ w ◁`. El paper prueba
(Teorema 3.17) la versión sobre **todas** las palabras; el Lema 3.16 reduce a la forma
canónica. Esa reducción está en `Collatz/Rewriting/AllWords.lean`
(`collatz_iff_terminatesAll`).

**Resultado:** `collatz_iff_terminates : Collatz ↔ SRS.Terminates`. Es una reformulación de la
conjetura, no un avance hacia ella. Su valor es que fija en Lean el objeto sobre el que se pueden
verificar certificados de terminación (interpretaciones matriciales) de subsistemas.
-/

namespace SRS

inductive Sym | f | t | d0 | d1 | d2
  deriving DecidableEq, Repr

/-- Acción de cada símbolo leyendo de izquierda a derecha. -/
def Sym.act : Sym → ℕ → ℕ
  | .f, x => 2 * x
  | .t, x => 2 * x + 1
  | .d0, x => 3 * x
  | .d1, x => 3 * x + 1
  | .d2, x => 3 * x + 2

def Sym.isBin : Sym → Bool
  | .f | .t => true
  | _ => false

def valFrom (x : ℕ) (w : List Sym) : ℕ := w.foldl (fun x s => s.act x) x

/-- Valor de `▷ w ◁`. -/
def val (w : List Sym) : ℕ := valFrom 1 w

@[simp] theorem valFrom_nil (x : ℕ) : valFrom x [] = x := rfl
@[simp] theorem valFrom_cons (x : ℕ) (s : Sym) (w : List Sym) :
    valFrom x (s :: w) = valFrom (s.act x) w := rfl
@[simp] theorem valFrom_append (x : ℕ) (u v : List Sym) :
    valFrom x (u ++ v) = valFrom (valFrom x u) v := List.foldl_append

/-- Un paso de reescritura sobre la palabra interna. -/
inductive Step : List Sym → List Sym → Prop
  | endF (u : List Sym) : Step (u ++ [.f]) u
  | endT (u : List Sym) : Step (u ++ [.t]) (u ++ [.d2])
  | f0 (u v : List Sym) : Step (u ++ .f :: .d0 :: v) (u ++ .d0 :: .f :: v)
  | f1 (u v : List Sym) : Step (u ++ .f :: .d1 :: v) (u ++ .d0 :: .t :: v)
  | f2 (u v : List Sym) : Step (u ++ .f :: .d2 :: v) (u ++ .d1 :: .f :: v)
  | t0 (u v : List Sym) : Step (u ++ .t :: .d0 :: v) (u ++ .d1 :: .t :: v)
  | t1 (u v : List Sym) : Step (u ++ .t :: .d1 :: v) (u ++ .d2 :: .f :: v)
  | t2 (u v : List Sym) : Step (u ++ .t :: .d2 :: v) (u ++ .d2 :: .t :: v)
  | s0 (v : List Sym) : Step (.d0 :: v) (.t :: v)
  | s1 (v : List Sym) : Step (.d1 :: v) (.f :: .f :: v)
  | s2 (v : List Sym) : Step (.d2 :: v) (.f :: .t :: v)

/-- El sistema termina sobre toda palabra canónica `▷ w ◁`. -/
def Terminates : Prop := ∀ w, Acc (fun y x => Step x y) w

/-! ## Valores -/

theorem le_valFrom (x : ℕ) (w : List Sym) : x ≤ valFrom x w := by
  induction w generalizing x with
  | nil => simp
  | cons s r ih =>
    rw [valFrom_cons]
    exact le_trans (by cases s <;> simp [Sym.act] <;> omega) (ih _)

theorem one_le_val (w : List Sym) : 1 ≤ val w := le_valFrom 1 w

theorem one_lt_val {w : List Sym} (h : w ≠ []) : 1 < val w := by
  obtain ⟨s, r, rfl⟩ := List.exists_cons_of_ne_nil h
  have := le_valFrom (s.act 1) r
  unfold val; rw [valFrom_cons]
  cases s <;> simp [Sym.act] at this ⊢ <;> omega

theorem exists_val {n : ℕ} (hn : 1 ≤ n) : ∃ w, val w = n := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    rcases Nat.lt_or_ge n 2 with h | h
    · exact ⟨[], by simp [val]; omega⟩
    · obtain ⟨w, hw⟩ := ih (n / 2) (by omega) (by omega)
      rcases Nat.mod_two_eq_zero_or_one n with he | ho
      · exact ⟨w ++ [.f], by simp [val] at hw ⊢; simp [hw, Sym.act]; omega⟩
      · exact ⟨w ++ [.t], by simp [val] at hw ⊢; simp [hw, Sym.act]; omega⟩

/-! ## Medida para los pasos que no cambian el valor -/

/-- Cantidad de dígitos ternarios. -/
def tc : List Sym → ℕ
  | [] => 0
  | s :: r => (if s.isBin then 0 else 1) + tc r

/-- Cantidad de dígitos binarios. -/
def bc : List Sym → ℕ
  | [] => 0
  | s :: r => (if s.isBin then 1 else 0) + bc r

/-- Inversiones: pares (binario, ternario) con el binario a la izquierda. -/
def inv : List Sym → ℕ
  | [] => 0
  | s :: r => (if s.isBin then tc r else 0) + inv r

theorem tc_append (u v : List Sym) : tc (u ++ v) = tc u + tc v := by
  induction u with
  | nil => simp [tc]
  | cons s u ih => simp [tc, ih]; omega

theorem bc_append (u v : List Sym) : bc (u ++ v) = bc u + bc v := by
  induction u with
  | nil => simp [bc]
  | cons s u ih => simp [bc, ih]; omega

theorem inv_append (u v : List Sym) : inv (u ++ v) = inv u + inv v + bc u * tc v := by
  induction u with
  | nil => simp [inv, bc]
  | cons s u ih => cases s <;> simp [inv, bc, Sym.isBin, ih, tc_append] <;> ring

def μ (w : List Sym) : ℕ × ℕ := (tc w, inv w)

def LexLt : ℕ × ℕ → ℕ × ℕ → Prop := Prod.Lex (· < ·) (· < ·)

theorem lexLt_wf : WellFounded LexLt := WellFounded.prod_lex wellFounded_lt wellFounded_lt

/-! ## Clasificación de los pasos -/

theorem T_two_mul (y : ℕ) : Collatz.T (2 * y) = y := by
  unfold Collatz.T; split <;> omega

theorem T_two_mul_add_one (y : ℕ) : Collatz.T (2 * y + 1) = 3 * y + 2 := by
  unfold Collatz.T; split <;> omega

/-- Todo paso es dinámico (aplica `Collatz.T`) o conserva el valor y baja la medida. -/
theorem Step.classify {w w' : List Sym} (h : Step w w') :
    val w' = Collatz.T (val w) ∨ (val w' = val w ∧ LexLt (μ w') (μ w)) := by
  cases h
  case endF => left; simp [val, Sym.act, T_two_mul]
  case endT u => left; simp [val, Sym.act, T_two_mul_add_one]
  case s0 v => right; exact ⟨rfl, Prod.Lex.left _ _ (by simp [tc, Sym.isBin])⟩
  case s1 v => right; exact ⟨rfl, Prod.Lex.left _ _ (by simp [tc, Sym.isBin])⟩
  case s2 v => right; exact ⟨rfl, Prod.Lex.left _ _ (by simp [tc, Sym.isBin])⟩
  all_goals
    right
    refine ⟨?_, ?_⟩
    · simp only [val, valFrom_append, valFrom_cons, Sym.act]; congr 1; ring
    · unfold LexLt μ
      rw [Prod.lex_def]
      right
      simp [tc_append, inv_append, tc, inv, Sym.isBin]

theorem Step.ne_nil {w w' : List Sym} (h : Step w w') : w ≠ [] := by
  cases h <;> simp

theorem not_step_nil {w' : List Sym} : ¬ Step [] w' := fun h => h.ne_nil rfl

/-! ## Progreso: sólo `▷◁` (valor 1) es forma normal -/

theorem Step.cons {r r' : List Sym} (h : Step r r') (s : Sym)
    (hr : ∀ v, r ≠ .d0 :: v ∧ r ≠ .d1 :: v ∧ r ≠ .d2 :: v) : Step (s :: r) (s :: r') := by
  cases h with
  | endF => exact Step.endF (s :: _)
  | endT => exact Step.endT (s :: _)
  | f0 => exact Step.f0 (s :: _) _
  | f1 => exact Step.f1 (s :: _) _
  | f2 => exact Step.f2 (s :: _) _
  | t0 => exact Step.t0 (s :: _) _
  | t1 => exact Step.t1 (s :: _) _
  | t2 => exact Step.t2 (s :: _) _
  | s0 v => exact absurd rfl (hr v).1
  | s1 v => exact absurd rfl (hr v).2.1
  | s2 v => exact absurd rfl (hr v).2.2

theorem exists_step : ∀ {w : List Sym}, w ≠ [] → ∃ w', Step w w'
  | [], h => absurd rfl h
  | [.f], _ => ⟨[], Step.endF []⟩
  | [.t], _ => ⟨[.d2], Step.endT []⟩
  | .d0 :: v, _ => ⟨_, Step.s0 v⟩
  | .d1 :: v, _ => ⟨_, Step.s1 v⟩
  | .d2 :: v, _ => ⟨_, Step.s2 v⟩
  | .f :: .d0 :: v, _ => ⟨_, Step.f0 [] v⟩
  | .f :: .d1 :: v, _ => ⟨_, Step.f1 [] v⟩
  | .f :: .d2 :: v, _ => ⟨_, Step.f2 [] v⟩
  | .t :: .d0 :: v, _ => ⟨_, Step.t0 [] v⟩
  | .t :: .d1 :: v, _ => ⟨_, Step.t1 [] v⟩
  | .t :: .d2 :: v, _ => ⟨_, Step.t2 [] v⟩
  | s :: .f :: v, _ => by
      obtain ⟨w', h⟩ := exists_step (w := .f :: v) (by simp)
      exact ⟨_, h.cons s (by simp)⟩
  | s :: .t :: v, _ => by
      obtain ⟨w', h⟩ := exists_step (w := .t :: v) (by simp)
      exact ⟨_, h.cons s (by simp)⟩

/-! ## Las dos direcciones -/

/-- Si `w` es accesible (ninguna reducción infinita desde `▷w◁`), la órbita de `val w`
bajo el mapa acelerado llega a `1`. -/
theorem reaches_of_acc {w : List Sym} (h : Acc (fun y x => Step x y) w) :
    ∃ k, Collatz.T^[k] (val w) = 1 := by
  induction h with
  | intro w _ ih =>
    by_cases hw : w = []
    · exact ⟨0, by simp [hw, val]⟩
    · obtain ⟨w', hs⟩ := exists_step hw
      obtain ⟨k, hk⟩ := ih w' hs
      rcases hs.classify with hv | ⟨hv, -⟩
      · exact ⟨k + 1, by rw [Function.iterate_succ_apply, ← hv]; exact hk⟩
      · exact ⟨k, by rw [← hv]; exact hk⟩

/-- Si la órbita de `val w` llega a `1` en `k` pasos, no hay reducción infinita desde `▷w◁`. -/
theorem acc_of_iterate (k : ℕ) :
    ∀ w, Collatz.T^[k] (val w) = 1 → Acc (fun y x => Step x y) w := by
  induction k with
  | zero =>
    intro w hw
    have : w = [] := by
      by_contra hne; have := one_lt_val hne; simp at hw; omega
    subst this
    exact Acc.intro _ fun _ h => absurd h not_step_nil
  | succ k ihk =>
    intro w
    induction w using (InvImage.wf μ lexLt_wf).induction with
    | _ w ihw =>
      intro hw
      refine Acc.intro _ fun w' hs => ?_
      rcases hs.classify with hv | ⟨hv, hμ⟩
      · exact ihk w' (by rw [hv, ← Function.iterate_succ_apply]; exact hw)
      · exact ihw w' hμ (by rw [hv]; exact hw)

theorem reachesOne_iff_T (n : ℕ) :
    (∃ k, Collatz.collatz^[k] n = 1) ↔ ∃ k, Collatz.T^[k] n = 1 := by
  constructor
  · rintro ⟨j, hj⟩
    obtain ⟨k, ⟨hk, -⟩ | ⟨-, -, he⟩⟩ := Collatz.T_iterate_track n j
    · exact ⟨k, by rw [hk, hj]⟩
    · rw [hj] at he; omega
  · rintro ⟨k, hk⟩
    obtain ⟨m, -, hm⟩ := Collatz.exists_iterate_collatz_eq_iterate_T n k
    exact ⟨m, by rw [hm, hk]⟩

end SRS

/-- **Yolcu–Aaronson–Heule, Teorema 3.17 (forma canónica).** La conjetura de Collatz equivale
a la terminación del sistema de reescritura de 11 reglas sobre las palabras `▷ w ◁`. -/
theorem collatz_iff_terminates : Collatz ↔ SRS.Terminates := by
  constructor
  · intro hC w
    obtain ⟨k, hk⟩ := hC (SRS.val w) (SRS.one_le_val w)
    rw [iter_eq_iterate] at hk
    obtain ⟨k', hk'⟩ := (SRS.reachesOne_iff_T _).mp ⟨k, hk⟩
    exact SRS.acc_of_iterate k' w hk'
  · intro hT n hn
    obtain ⟨w, rfl⟩ := SRS.exists_val hn
    obtain ⟨k, hk⟩ := (SRS.reachesOne_iff_T _).mpr (SRS.reaches_of_acc (hT w))
    exact ⟨k, by rw [iter_eq_iterate]; exact hk⟩
