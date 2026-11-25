import Collatz.Conway.Compile
import Collatz.Conway.Fractran

/-!
# El teorema de indecidibilidad de Conway (1972)

J. H. Conway, *Unpredictable iterations*, Proc. 1972 Number Theory Conf., Boulder, pp. 49–52.

Una **función de Collatz generalizada multiplicativa** es `g(n) = a_j · n` para `n ≡ j (mod D)`,
con racionales `a_0, …, a_{D-1}` tales que `g` manda naturales en naturales. Conway probó que no
hay algoritmo que, dados `g` y `n`, decida si alguna iteración `g^i(n)` (`i ≥ 1`) es una potencia
de 2. Acá probamos eso y la variante "`g^i(n) = 1`", ambas para una `g` **fija** (la que simula
una función universal), y luego para el problema con `g` como dato.

Cadena de la prueba (todo en Lean, sin axiomas extra):
`ComputablePred.halting_problem` (Mathlib) → función universal `U m = eval (código m) 0` →
`Nat.Partrec'` → programa WHILE (`Conway/Compile.lean`) → máquina de Minsky (`Conway/Minsky.lean`)
→ FRACTRAN (`Conway/Fractran.lean`) → función de Collatz generalizada (este archivo).

Ojo: esto NO dice nada sobre la conjetura de Collatz misma (que es una `g` particular, y además
no multiplicativa); dice que no hay un método general para toda la familia.
-/

open Function Nat.Partrec Encodable

namespace Conway

/-! ## Función universal y su programa -/

/-- Función universal: `U m = eval (código número m) 0`. -/
def U : ℕ →. ℕ := fun m => Code.eval (Denumerable.ofNat Code m) 0

theorem U_partrec : Partrec U :=
  Code.eval_part.comp (Computable.ofNat Code) (Computable.const 0)

theorem computablePred_comp {α β : Type*} [Primcodable α] [Primcodable β] {p : β → Prop}
    {f : α → β} (hp : ComputablePred p) (hf : Computable f) : ComputablePred fun a => p (f a) := by
  obtain ⟨b, hb, rfl⟩ := ComputablePred.computable_iff.1 hp
  exact ComputablePred.computable_iff.2 ⟨b ∘ f, hb.comp hf, rfl⟩

/-- El dominio de `U` no es decidible (problema de la detención, Mathlib). -/
theorem not_computable_U_dom : ¬ ComputablePred fun m => (U m).Dom := by
  intro h
  apply ComputablePred.halting_problem 0
  refine (computablePred_comp h Computable.encode).of_eq fun c => ?_
  simp [U, Denumerable.ofNat_encode]

theorem exists_prog_U : ∃ P : Prog, Prog.Computes 1 (fun v => U v.head) P :=
  computes_of_partrec' (Nat.Partrec'.part_iff₁.2 U_partrec)

/-- Programa que calcula `U` (elegido). -/
noncomputable def progU : Prog := exists_prog_U.choose

/-- `progU` seguido de borrar la entrada y la salida: termina sii `U m` está definida, y deja
todo en cero. -/
noncomputable def progQ : Prog := .seq progU (.seq (Prog.clear 0) (Prog.clear 1))

theorem progQ_spec (m : ℕ) (s' : Regs) :
    Prog.Runs progQ (initRegs m) s' ↔ (U m).Dom ∧ s' = fun _ => 0 := by
  obtain ⟨N, hN⟩ := exists_prog_U.choose_spec
  have key := hN (m ::ᵥ List.Vector.nil) (initRegs m)
    (by intro i; fin_cases i; simp [initRegs])
    (by intro r h1 _; simp [initRegs, update_apply]; omega)
  have hclear : ∀ y, Prog.Runs (.seq (Prog.clear 0) (Prog.clear 1))
      (update (initRegs m) 1 y) (fun _ => 0) := by
    intro y
    refine .seq (Prog.runs_clear 0 _) ?_
    convert Prog.runs_clear 1 _ using 1
    funext r; simp only [initRegs, update_apply]; split_ifs <;> rfl
  rw [progQ, Prog.runs_seq]
  constructor
  · rintro ⟨t, h1, h2⟩
    obtain ⟨y, hy, rfl⟩ := (key t).1 h1
    exact ⟨Part.dom_iff_mem.2 ⟨y, by simpa using hy⟩, h2.det (hclear y)⟩
  · rintro ⟨hd, rfl⟩
    obtain ⟨y, hy⟩ := Part.dom_iff_mem.1 hd
    exact ⟨_, (key _).2 ⟨y, by simpa using hy, rfl⟩, hclear y⟩

/-! ## La función de Collatz generalizada fija -/

/-- **La función de Conway** (paso del programa FRACTRAN que simula `progQ`). -/
noncomputable def conwayMap : ℕ → ℕ := fstep (fracs (progQ.bound + 1) progQ.toMachine)

theorem orbit_progQ (m : ℕ) :
    ((∃ s', Prog.Runs progQ (initRegs m) s') → ∃ i, 1 ≤ i ∧ conwayMap^[i] (2 ^ m) = 1) ∧
    ((¬ ∃ s', Prog.Runs progQ (initRegs m) s') → ∀ i, 1 ≤ i →
        ∃ p, p.Prime ∧ p ≠ 2 ∧ p ∣ conwayMap^[i] (2 ^ m)) :=
  orbit progQ (R := progQ.bound + 1) (by omega) (by omega) m
    (fun s' h r => by rw [((progQ_spec m s').1 h).2])

/-- La órbita de `2^m` llega a `1` sii `U m` está definida. -/
theorem conwayMap_iff_one (m : ℕ) :
    (∃ i, 1 ≤ i ∧ conwayMap^[i] (2 ^ m) = 1) ↔ (U m).Dom := by
  constructor
  · rintro ⟨i, hi, h⟩
    by_contra hd
    obtain ⟨p, hp, -, hdvd⟩ := (orbit_progQ m).2 (fun ⟨s', h'⟩ => hd ((progQ_spec m s').1 h').1)
      i hi
    rw [h] at hdvd
    exact hp.one_lt.ne' (Nat.dvd_one.1 hdvd)
  · intro hd
    exact (orbit_progQ m).1 ⟨_, (progQ_spec m _).2 ⟨hd, rfl⟩⟩

/-- La órbita de `2^m` pasa por una potencia de 2 sii `U m` está definida (forma original). -/
theorem conwayMap_iff_pow_two (m : ℕ) :
    (∃ i, 1 ≤ i ∧ ∃ k, conwayMap^[i] (2 ^ m) = 2 ^ k) ↔ (U m).Dom := by
  constructor
  · rintro ⟨i, hi, k, h⟩
    by_contra hd
    obtain ⟨p, hp, hp2, hdvd⟩ :=
      (orbit_progQ m).2 (fun ⟨s', h'⟩ => hd ((progQ_spec m s').1 h').1) i hi
    rw [h] at hdvd
    exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 (hp.dvd_of_dvd_pow hdvd))
  · intro hd
    obtain ⟨i, hi, h⟩ := (conwayMap_iff_one m).2 hd
    exact ⟨i, hi, 0, by simpa using h⟩

/-- **Conway (función fija), variante `= 1`.** -/
theorem conway_fixed_one : ¬ ComputablePred fun m => ∃ i, 1 ≤ i ∧ conwayMap^[i] (2 ^ m) = 1 :=
  fun h => not_computable_U_dom (h.of_eq conwayMap_iff_one)

/-- **Conway (función fija), forma original: "alguna iteración es potencia de 2".** -/
theorem conway_fixed_pow_two :
    ¬ ComputablePred fun m => ∃ i, 1 ≤ i ∧ ∃ k, conwayMap^[i] (2 ^ m) = 2 ^ k :=
  fun h => not_computable_U_dom (h.of_eq conwayMap_iff_pow_two)

/-! ## Presentación como función de Collatz generalizada -/

/-- Función de Collatz generalizada multiplicativa dada por un módulo `D` y una lista de pares
`(num_j, den_j)` (uno por residuo `j < D`): `g(n) = num_j · n / den_j` si `n ≡ j (mod D)`. -/
def gcf (D : ℕ) (a : List (ℕ × ℕ)) (n : ℕ) : ℕ :=
  (a.getD (n % D) (1, 1)).1 * n / (a.getD (n % D) (1, 1)).2

theorem find?_congr {α : Type*} (p q : α → Bool) :
    ∀ l : List α, (∀ x ∈ l, p x = q x) → l.find? p = l.find? q
  | [], _ => rfl
  | x :: l, h => by
    simp only [List.find?_cons, h x (by simp)]
    rw [find?_congr p q l fun y hy => h y (by simp [hy])]

/-- Tabla de residuos de un programa FRACTRAN. -/
def table (l : List (ℕ × ℕ)) : List (ℕ × ℕ) :=
  List.ofFn fun j : Fin (l.map Prod.snd).prod => (l.find? fun q => decide (q.2 ∣ (j : ℕ))).getD (1, 1)

theorem fstep_eq_gcf (l : List (ℕ × ℕ)) (hpos : ∀ q ∈ l, 0 < q.2) (n : ℕ) :
    fstep l n = gcf (l.map Prod.snd).prod (table l) n ∧
      ∃ q : ℕ × ℕ, 0 < q.2 ∧ (table l).getD (n % (l.map Prod.snd).prod) (1, 1) = q ∧
        q.2 ∣ n ∧ fstep l n = q.1 * (n / q.2) := by
  set D := (l.map Prod.snd).prod
  have hD : 0 < D := List.prod_pos (by simpa using fun b a h => hpos (a, b) h)
  have hdvd : ∀ q ∈ l, q.2 ∣ D := fun q hq => List.dvd_prod (List.mem_map_of_mem hq)
  have hfind : l.find? (fun q => decide (q.2 ∣ n % D)) = l.find? (fun q => decide (q.2 ∣ n)) :=
    find?_congr _ _ l fun q hq => by simp [Nat.dvd_mod_iff (hdvd q hq)]
  have htab : (table l).getD (n % D) (1, 1) = (l.find? fun q => decide (q.2 ∣ n)).getD (1, 1) := by
    rw [table, List.getD_eq_getElem _ _ (by simpa using Nat.mod_lt _ hD), List.getElem_ofFn]
    exact congrArg (fun o => Option.getD o (1, 1)) hfind
  unfold gcf
  rw [htab]
  cases h : l.find? (fun q => decide (q.2 ∣ n)) with
  | none => simp [fstep, h]
  | some q =>
    have hq := List.mem_of_find?_eq_some h
    have hd : q.2 ∣ n := by simpa using List.find?_some h
    simp only [Option.getD_some, fstep, h]
    exact ⟨(Nat.mul_div_assoc q.1 hd).symm, q, hpos q hq, rfl, hd, rfl⟩

theorem pos_of_mem_fracs {R : ℕ} {M : Machine} : ∀ q ∈ fracs R M, 0 < q.2 := by
  have hblock : ∀ i x, ∀ q ∈ block R i x, 0 < q.2 := by
    intro i x q hq
    cases x <;> simp [block] at hq <;> rcases hq with rfl | rfl <;>
      simp [Nat.mul_pos, pr_pos]
  have hfrom : ∀ (xs : List Instr) i, ∀ q ∈ fracsFrom R i xs, 0 < q.2 := by
    intro xs
    induction xs with
    | nil => simp [fracsFrom]
    | cons x xs ih =>
      intro i q hq
      simp only [fracsFrom, List.mem_append] at hq
      rcases hq with hq | hq
      · exact hblock i x q hq
      · exact ih _ q hq
  intro q hq
  simp only [fracs, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hq
  rcases hq with hq | rfl | rfl
  · exact hfrom M 0 q hq
  · exact pr_pos _
  · exact Nat.one_pos

/-- Módulo y tabla de la función de Conway. -/
noncomputable def conwayD : ℕ := ((fracs (progQ.bound + 1) progQ.toMachine).map Prod.snd).prod

noncomputable def conwayTable : List (ℕ × ℕ) := table (fracs (progQ.bound + 1) progQ.toMachine)

theorem conwayMap_eq_gcf : conwayMap = gcf conwayD conwayTable :=
  funext fun n => (fstep_eq_gcf _ pos_of_mem_fracs n).1

/-- La función de Conway es una función de Collatz generalizada multiplicativa:
`g(n) = a_{n mod D} · n` con coeficientes racionales. -/
theorem conwayMap_rat : 0 < conwayD ∧ ∃ a : ℕ → ℚ, ∀ n, (conwayMap n : ℚ) = a (n % conwayD) * n := by
  refine ⟨List.prod_pos (by simpa using fun b a h => pos_of_mem_fracs (a, b) h), fun j =>
    ((conwayTable.getD j (1, 1)).1 : ℚ) / (conwayTable.getD j (1, 1)).2, fun n => ?_⟩
  obtain ⟨-, q, hq0, hq, hd, he⟩ := fstep_eq_gcf _ pos_of_mem_fracs n
  simp only [conwayMap, conwayTable, conwayD] at *
  rw [he, hq, Nat.cast_mul, Nat.cast_div hd (by exact_mod_cast hq0.ne')]
  ring

/-! ## Enunciados finales -/

/-- **Teorema de Conway (1972), forma fija.** Existe una función de Collatz generalizada
multiplicativa `g(n) = a_{n mod D} · n` (coeficientes racionales) tal que no hay algoritmo que
decida, dado `m`, si alguna iteración `g^i(2^m)` (`i ≥ 1`) es una potencia de 2. Lo mismo para
"alguna iteración vale 1". -/
theorem conway_undecidable_fixed :
    ∃ g : ℕ → ℕ, ∃ D, 0 < D ∧ (∃ a : ℕ → ℚ, ∀ n, (g n : ℚ) = a (n % D) * n) ∧
      ¬ ComputablePred (fun m => ∃ i, 1 ≤ i ∧ ∃ k, g^[i] (2 ^ m) = 2 ^ k) ∧
      ¬ ComputablePred (fun m => ∃ i, 1 ≤ i ∧ g^[i] (2 ^ m) = 1) :=
  ⟨conwayMap, conwayD, conwayMap_rat.1, conwayMap_rat.2, conway_fixed_pow_two, conway_fixed_one⟩

theorem computable_instance (D : ℕ) (a : List (ℕ × ℕ)) :
    Computable fun m : ℕ => ((D, a), 2 ^ m) := by
  refine (Computable.const (D, a)).pair ?_
  have hpow : Primrec fun m : ℕ => 2 ^ m := by
    have := (Primrec.nat_iff.2 Nat.Primrec.pow).comp
      (Primrec₂.natPair.comp (Primrec.const 2) Primrec.id)
    refine this.of_eq fun m => ?_
    simp [Nat.unpaired]
  exact hpow.to_comp

/-- **Teorema de Conway (1972), forma uniforme.** No hay algoritmo que, dada una función de Collatz
generalizada multiplicativa (por su módulo `D` y su tabla de fracciones por residuo) y un `n`,
decida si alguna iteración `g^i(n)` (`i ≥ 1`) es una potencia de 2. -/
theorem conway_undecidable :
    ¬ ComputablePred fun x : (ℕ × List (ℕ × ℕ)) × ℕ =>
      ∃ i, 1 ≤ i ∧ ∃ k, (gcf x.1.1 x.1.2)^[i] x.2 = 2 ^ k := by
  intro h
  apply conway_fixed_pow_two
  refine (computablePred_comp h (computable_instance conwayD conwayTable)).of_eq fun m => ?_
  rw [conwayMap_eq_gcf]

/-- Variante uniforme: "alguna iteración vale 1". -/
theorem conway_undecidable_one :
    ¬ ComputablePred fun x : (ℕ × List (ℕ × ℕ)) × ℕ =>
      ∃ i, 1 ≤ i ∧ (gcf x.1.1 x.1.2)^[i] x.2 = 1 := by
  intro h
  apply conway_fixed_one
  refine (computablePred_comp h (computable_instance conwayD conwayTable)).of_eq fun m => ?_
  rw [conwayMap_eq_gcf]

end Conway
