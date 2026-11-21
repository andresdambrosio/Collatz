import Collatz.Rewriting.Arctic

/-!
# Subsistemas de `𝒯` con certificados árticos

Generado por `scripts/certs.py --gen <dir-proofs>` a partir de `proofs/collatz-T-NN.log` del
repositorio `github.com/emreyolcu/rewriting-collatz` (Yolcu–Aaronson–Heule, arXiv 2105.14697,
§4.3, Tabla 1). Las matrices se copian de los certificados; Lean las chequea con `decide +kernel`.

Para cada regla `ρ` de este archivo: `𝒯 ∖ {ρ}` termina sobre palabras canónicas. Esquema (el del
paper): se eliminan las reglas de inicio `ℬ` en 1 a 3 pasos con interpretaciones débilmente
monótonas, y lo que queda está contenido en `𝒯 ∖ ℬ`, que termina (`termIn_noStart`).
-/

namespace SRS

set_option maxRecDepth 20000

/-- `T06`, paso 1: quita cf→caa. -/
def I_T06_1 : X → AAff 3
  | .a => ⟨![![⊥, WithBot.some 0, WithBot.some 1], ![WithBot.some 0, ⊥, ⊥], ![⊥, ⊥, ⊥]], ![WithBot.some 0, ⊥, ⊥]⟩
  | .b => ⟨![![⊥, WithBot.some 0, WithBot.some 1], ![⊥, WithBot.some 0, WithBot.some 1], ![WithBot.some 0, ⊥, WithBot.some 1]], ![WithBot.some 1, WithBot.some 1, WithBot.some 1]⟩
  | .c => ⟨![![⊥, WithBot.some 0, ⊥], ![⊥, ⊥, ⊥], ![⊥, ⊥, ⊥]], ![WithBot.some 0, ⊥, ⊥]⟩
  | .d => ⟨![![⊥, ⊥, ⊥], ![⊥, ⊥, ⊥], ![⊥, ⊥, ⊥]], ![WithBot.some 0, ⊥, ⊥]⟩
  | .e => ⟨![![WithBot.some 0, ⊥, ⊥], ![⊥, WithBot.some 0, WithBot.some 1], ![⊥, ⊥, ⊥]], ![WithBot.some 1, WithBot.some 1, ⊥]⟩
  | .f => ⟨![![WithBot.some 1, WithBot.some 0, WithBot.some 2], ![WithBot.some 0, WithBot.some 1, WithBot.some 2], ![⊥, ⊥, ⊥]], ![WithBot.some 2, WithBot.some 1, ⊥]⟩
  | .g => ⟨![![WithBot.some 1, WithBot.some 0, WithBot.some 1], ![⊥, WithBot.some 0, WithBot.some 1], ![WithBot.some 0, WithBot.some 0, WithBot.some 1]], ![WithBot.some 1, WithBot.some 1, WithBot.some 1]⟩

/-- `T06`, paso 2: quita ce→cb. -/
def I_T06_2 : X → AAff 3
  | .a => ⟨![![WithBot.some 0, ⊥, ⊥], ![WithBot.some 1, ⊥, ⊥], ![⊥, WithBot.some 0, ⊥]], ![⊥, ⊥, ⊥]⟩
  | .b => ⟨![![WithBot.some 0, ⊥, ⊥], ![⊥, ⊥, ⊥], ![⊥, ⊥, ⊥]], ![⊥, ⊥, ⊥]⟩
  | .c => ⟨![![WithBot.some 0, ⊥, WithBot.some 0], ![⊥, ⊥, ⊥], ![⊥, ⊥, ⊥]], ![⊥, ⊥, ⊥]⟩
  | .d => ⟨![![WithBot.some 0, ⊥, ⊥], ![⊥, ⊥, ⊥], ![⊥, ⊥, ⊥]], ![⊥, ⊥, ⊥]⟩
  | .e => ⟨![![WithBot.some 0, ⊥, ⊥], ![WithBot.some 1, ⊥, ⊥], ![WithBot.some 1, ⊥, ⊥]], ![⊥, ⊥, ⊥]⟩
  | .f => ⟨![![WithBot.some 0, ⊥, ⊥], ![WithBot.some 1, ⊥, ⊥], ![⊥, ⊥, ⊥]], ![⊥, ⊥, ⊥]⟩
  | .g => ⟨![![WithBot.some 0, ⊥, ⊥], ![⊥, ⊥, ⊥], ![⊥, ⊥, ⊥]], ![⊥, ⊥, ⊥]⟩

/-- `T06`, paso 3: quita cg→cab. -/
def I_T06_3 : X → AAff 3
  | .a => ⟨![![WithBot.some 0, ⊥, ⊥], ![⊥, WithBot.some 0, WithBot.some 0], ![⊥, ⊥, ⊥]], ![⊥, ⊥, ⊥]⟩
  | .b => ⟨![![WithBot.some 0, ⊥, ⊥], ![⊥, ⊥, ⊥], ![⊥, WithBot.some 0, WithBot.some 0]], ![⊥, ⊥, ⊥]⟩
  | .c => ⟨![![WithBot.some 0, ⊥, WithBot.some 1], ![⊥, ⊥, ⊥], ![⊥, ⊥, ⊥]], ![⊥, ⊥, ⊥]⟩
  | .d => ⟨![![WithBot.some 0, ⊥, ⊥], ![WithBot.some 0, ⊥, ⊥], ![⊥, ⊥, ⊥]], ![⊥, ⊥, ⊥]⟩
  | .e => ⟨![![WithBot.some 0, ⊥, ⊥], ![⊥, ⊥, ⊥], ![⊥, ⊥, ⊥]], ![⊥, ⊥, ⊥]⟩
  | .f => ⟨![![WithBot.some 0, ⊥, ⊥], ![WithBot.some 0, ⊥, ⊥], ![⊥, ⊥, ⊥]], ![⊥, ⊥, ⊥]⟩
  | .g => ⟨![![WithBot.some 0, ⊥, ⊥], ![⊥, ⊥, ⊥], ![WithBot.some 0, ⊥, ⊥]], ![⊥, ⊥, ⊥]⟩

/-- **`𝒯 ∖ {t0 → 1t}` termina** (sobre palabras canónicas). Certificado: `proofs/collatz-T-06.log`. -/
theorem termIn_without_r06 : TermIn (fun ρ => ρ != .r06) :=
  TermIn.removal_arc I_T06_1 (S₁ := fun ρ => ρ == .r10)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) <|
  TermIn.removal_arc I_T06_2 (S₁ := fun ρ => ρ == .r09)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) <|
  TermIn.removal_arc I_T06_3 (S₁ := fun ρ => ρ == .r11)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) <|
  termIn_noStart.mono (by decide)

/-- `T07`, paso 1: quita cg→cab. -/
def I_T07_1 : X → AAff 4
  | .a => ⟨![![WithBot.some 0, ⊥, ⊥, WithBot.some 0], ![⊥, WithBot.some 0, ⊥, ⊥], ![⊥, ⊥, ⊥, WithBot.some 0], ![⊥, ⊥, WithBot.some 0, ⊥]], ![⊥, ⊥, ⊥, ⊥]⟩
  | .b => ⟨![![⊥, ⊥, ⊥, ⊥], ![⊥, ⊥, ⊥, ⊥], ![⊥, WithBot.some 0, WithBot.some 0, ⊥], ![WithBot.some 0, ⊥, ⊥, ⊥]], ![WithBot.some 0, ⊥, WithBot.some 0, ⊥]⟩
  | .c => ⟨![![⊥, ⊥, WithBot.some 0, ⊥], ![⊥, ⊥, ⊥, ⊥], ![⊥, ⊥, ⊥, ⊥], ![⊥, ⊥, ⊥, ⊥]], ![WithBot.some 0, ⊥, ⊥, ⊥]⟩
  | .d => ⟨![![⊥, ⊥, ⊥, ⊥], ![⊥, ⊥, ⊥, ⊥], ![⊥, ⊥, ⊥, ⊥], ![⊥, ⊥, ⊥, ⊥]], ![WithBot.some 0, WithBot.some 1, ⊥, ⊥]⟩
  | .e => ⟨![![⊥, WithBot.some 0, WithBot.some 0, ⊥], ![⊥, ⊥, ⊥, ⊥], ![⊥, WithBot.some 0, WithBot.some 0, ⊥], ![⊥, WithBot.some 0, ⊥, WithBot.some 0]], ![WithBot.some 0, ⊥, ⊥, ⊥]⟩
  | .f => ⟨![![⊥, ⊥, ⊥, ⊥], ![⊥, ⊥, ⊥, ⊥], ![WithBot.some 0, ⊥, WithBot.some 0, ⊥], ![⊥, WithBot.some 0, WithBot.some 0, ⊥]], ![WithBot.some 0, ⊥, ⊥, WithBot.some 0]⟩
  | .g => ⟨![![WithBot.some 0, ⊥, ⊥, ⊥], ![⊥, ⊥, ⊥, ⊥], ![WithBot.some 1, WithBot.some 0, ⊥, WithBot.some 0], ![WithBot.some 0, ⊥, ⊥, WithBot.some 0]], ![WithBot.some 0, ⊥, WithBot.some 1, ⊥]⟩

/-- `T07`, paso 2: quita cf→caa. -/
def I_T07_2 : X → AAff 4
  | .a => ⟨![![WithBot.some 0, ⊥, WithBot.some 0, ⊥], ![WithBot.some 0, ⊥, ⊥, ⊥], ![⊥, WithBot.some 0, ⊥, ⊥], ![⊥, ⊥, ⊥, ⊥]], ![⊥, ⊥, ⊥, ⊥]⟩
  | .b => ⟨![![⊥, ⊥, ⊥, ⊥], ![⊥, WithBot.some 0, ⊥, ⊥], ![WithBot.some 0, ⊥, ⊥, ⊥], ![⊥, ⊥, ⊥, ⊥]], ![WithBot.some 0, WithBot.some 1, ⊥, ⊥]⟩
  | .c => ⟨![![⊥, ⊥, WithBot.some 0, ⊥], ![⊥, ⊥, ⊥, ⊥], ![⊥, ⊥, ⊥, ⊥], ![⊥, ⊥, ⊥, ⊥]], ![WithBot.some 0, ⊥, ⊥, ⊥]⟩
  | .d => ⟨![![⊥, ⊥, ⊥, ⊥], ![⊥, ⊥, ⊥, ⊥], ![⊥, ⊥, ⊥, ⊥], ![⊥, ⊥, ⊥, ⊥]], ![WithBot.some 0, ⊥, ⊥, ⊥]⟩
  | .e => ⟨![![WithBot.some 0, WithBot.some 0, WithBot.some 0, ⊥], ![WithBot.some 0, ⊥, WithBot.some 0, ⊥], ![WithBot.some 0, ⊥, ⊥, ⊥], ![⊥, ⊥, ⊥, ⊥]], ![WithBot.some 1, ⊥, ⊥, ⊥]⟩
  | .f => ⟨![![WithBot.some 0, ⊥, ⊥, ⊥], ![⊥, ⊥, ⊥, ⊥], ![WithBot.some 1, WithBot.some 0, ⊥, ⊥], ![⊥, ⊥, ⊥, ⊥]], ![WithBot.some 0, WithBot.some 0, WithBot.some 1, ⊥]⟩
  | .g => ⟨![![WithBot.some 0, ⊥, ⊥, ⊥], ![WithBot.some 1, ⊥, WithBot.some 1, ⊥], ![⊥, ⊥, WithBot.some 0, ⊥], ![⊥, ⊥, ⊥, ⊥]], ![WithBot.some 0, WithBot.some 1, ⊥, ⊥]⟩

/-- `T07`, paso 3: quita ce→cb. -/
def I_T07_3 : X → AAff 4
  | .a => ⟨![![WithBot.some 0, ⊥, ⊥, ⊥], ![⊥, ⊥, ⊥, ⊥], ![⊥, ⊥, ⊥, ⊥], ![WithBot.some 0, ⊥, ⊥, ⊥]], ![⊥, ⊥, ⊥, ⊥]⟩
  | .b => ⟨![![WithBot.some 0, ⊥, ⊥, ⊥], ![⊥, ⊥, ⊥, ⊥], ![⊥, ⊥, ⊥, ⊥], ![⊥, ⊥, ⊥, ⊥]], ![⊥, ⊥, ⊥, ⊥]⟩
  | .c => ⟨![![WithBot.some 0, ⊥, ⊥, WithBot.some 1], ![⊥, ⊥, ⊥, ⊥], ![⊥, ⊥, ⊥, ⊥], ![⊥, ⊥, ⊥, ⊥]], ![⊥, ⊥, ⊥, ⊥]⟩
  | .d => ⟨![![WithBot.some 0, ⊥, ⊥, ⊥], ![⊥, ⊥, ⊥, ⊥], ![⊥, ⊥, ⊥, ⊥], ![⊥, ⊥, ⊥, ⊥]], ![⊥, ⊥, ⊥, ⊥]⟩
  | .e => ⟨![![WithBot.some 0, ⊥, ⊥, ⊥], ![⊥, ⊥, ⊥, ⊥], ![⊥, ⊥, ⊥, ⊥], ![WithBot.some 0, ⊥, ⊥, ⊥]], ![⊥, ⊥, ⊥, ⊥]⟩
  | .f => ⟨![![WithBot.some 0, ⊥, ⊥, ⊥], ![⊥, ⊥, ⊥, ⊥], ![⊥, ⊥, ⊥, ⊥], ![⊥, ⊥, ⊥, ⊥]], ![⊥, ⊥, ⊥, ⊥]⟩
  | .g => ⟨![![WithBot.some 0, ⊥, ⊥, ⊥], ![⊥, ⊥, ⊥, ⊥], ![⊥, ⊥, ⊥, ⊥], ![⊥, ⊥, ⊥, ⊥]], ![⊥, ⊥, ⊥, ⊥]⟩

/-- **`𝒯 ∖ {t1 → 2f}` termina** (sobre palabras canónicas). Certificado: `proofs/collatz-T-07.log`. -/
theorem termIn_without_r07 : TermIn (fun ρ => ρ != .r07) :=
  TermIn.removal_arc I_T07_1 (S₁ := fun ρ => ρ == .r11)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) <|
  TermIn.removal_arc I_T07_2 (S₁ := fun ρ => ρ == .r10)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) <|
  TermIn.removal_arc I_T07_3 (S₁ := fun ρ => ρ == .r09)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) <|
  termIn_noStart.mono (by decide)

/-- `T08`, paso 1: quita ce→cb. -/
def I_T08_1 : X → AAff 2
  | .a => ⟨![![WithBot.some 0, WithBot.some 0], ![⊥, WithBot.some 1]], ![⊥, ⊥]⟩
  | .b => ⟨![![WithBot.some 0, WithBot.some 0], ![WithBot.some 0, WithBot.some 1]], ![⊥, ⊥]⟩
  | .c => ⟨![![WithBot.some 0, ⊥], ![⊥, ⊥]], ![⊥, ⊥]⟩
  | .d => ⟨![![WithBot.some 0, ⊥], ![⊥, ⊥]], ![⊥, ⊥]⟩
  | .e => ⟨![![WithBot.some 1, WithBot.some 1], ![WithBot.some 1, WithBot.some 2]], ![⊥, ⊥]⟩
  | .f => ⟨![![WithBot.some 0, WithBot.some 1], ![WithBot.some 1, WithBot.some 2]], ![⊥, ⊥]⟩
  | .g => ⟨![![WithBot.some 0, WithBot.some 1], ![WithBot.some 0, WithBot.some 2]], ![⊥, ⊥]⟩

/-- `T08`, paso 2: quita cg→cab. -/
def I_T08_2 : X → AAff 2
  | .a => ⟨![![⊥, ⊥], ![⊥, ⊥]], ![WithBot.some 0, ⊥]⟩
  | .b => ⟨![![⊥, ⊥], ![⊥, ⊥]], ![WithBot.some 0, WithBot.some 0]⟩
  | .c => ⟨![![⊥, WithBot.some 1], ![⊥, ⊥]], ![WithBot.some 0, ⊥]⟩
  | .d => ⟨![![⊥, ⊥], ![⊥, ⊥]], ![WithBot.some 0, ⊥]⟩
  | .e => ⟨![![⊥, ⊥], ![⊥, ⊥]], ![WithBot.some 0, ⊥]⟩
  | .f => ⟨![![⊥, ⊥], ![⊥, ⊥]], ![WithBot.some 0, ⊥]⟩
  | .g => ⟨![![⊥, ⊥], ![⊥, ⊥]], ![WithBot.some 0, WithBot.some 0]⟩

/-- `T08`, paso 3: quita cf→caa. -/
def I_T08_3 : X → AAff 2
  | .a => ⟨![![WithBot.some 0, ⊥], ![⊥, WithBot.some 1]], ![⊥, ⊥]⟩
  | .b => ⟨![![WithBot.some 1, WithBot.some 0], ![⊥, WithBot.some 1]], ![⊥, WithBot.some 1]⟩
  | .c => ⟨![![WithBot.some 0, ⊥], ![⊥, ⊥]], ![⊥, ⊥]⟩
  | .d => ⟨![![⊥, ⊥], ![⊥, ⊥]], ![WithBot.some 0, ⊥]⟩
  | .e => ⟨![![WithBot.some 0, ⊥], ![WithBot.some 2, WithBot.some 2]], ![⊥, WithBot.some 2]⟩
  | .f => ⟨![![WithBot.some 1, WithBot.some 0], ![WithBot.some 2, WithBot.some 2]], ![⊥, WithBot.some 2]⟩
  | .g => ⟨![![WithBot.some 1, WithBot.some 1], ![WithBot.some 1, WithBot.some 2]], ![⊥, WithBot.some 1]⟩

/-- **`𝒯 ∖ {t2 → 2t}` termina** (sobre palabras canónicas). Certificado: `proofs/collatz-T-08.log`. -/
theorem termIn_without_r08 : TermIn (fun ρ => ρ != .r08) :=
  TermIn.removal_arc I_T08_1 (S₁ := fun ρ => ρ == .r09)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) <|
  TermIn.removal_arc I_T08_2 (S₁ := fun ρ => ρ == .r11)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) <|
  TermIn.removal_arc I_T08_3 (S₁ := fun ρ => ρ == .r10)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) <|
  termIn_noStart.mono (by decide)

/-- `T11`, paso 1: quita ce→cb. -/
def I_T11_1 : X → AAff 4
  | .a => ⟨![![⊥, ⊥, WithBot.some 0, ⊥], ![⊥, ⊥, WithBot.some 0, ⊥], ![⊥, WithBot.some 0, ⊥, WithBot.some 0], ![WithBot.some 0, ⊥, ⊥, WithBot.some 0]], ![WithBot.some 0, WithBot.some 0, WithBot.some 0, ⊥]⟩
  | .b => ⟨![![⊥, ⊥, ⊥, WithBot.some 0], ![⊥, ⊥, ⊥, ⊥], ![WithBot.some 0, ⊥, WithBot.some 0, ⊥], ![⊥, ⊥, ⊥, ⊥]], ![WithBot.some 0, ⊥, ⊥, ⊥]⟩
  | .c => ⟨![![WithBot.some 0, WithBot.some 1, ⊥, ⊥], ![⊥, ⊥, ⊥, ⊥], ![⊥, ⊥, ⊥, ⊥], ![⊥, ⊥, ⊥, ⊥]], ![⊥, ⊥, ⊥, ⊥]⟩
  | .d => ⟨![![WithBot.some 0, ⊥, ⊥, ⊥], ![WithBot.some 0, ⊥, ⊥, ⊥], ![WithBot.some 0, ⊥, ⊥, ⊥], ![⊥, ⊥, ⊥, ⊥]], ![⊥, WithBot.some 1, WithBot.some 1, ⊥]⟩
  | .e => ⟨![![⊥, ⊥, ⊥, ⊥], ![⊥, ⊥, ⊥, WithBot.some 0], ![WithBot.some 0, ⊥, ⊥, WithBot.some 0], ![WithBot.some 0, WithBot.some 0, WithBot.some 0, WithBot.some 0]], ![WithBot.some 0, WithBot.some 0, ⊥, WithBot.some 1]⟩
  | .f => ⟨![![WithBot.some 0, WithBot.some 0, WithBot.some 0, WithBot.some 0], ![⊥, WithBot.some 0, ⊥, WithBot.some 0], ![⊥, ⊥, ⊥, ⊥], ![⊥, ⊥, ⊥, ⊥]], ![WithBot.some 1, ⊥, ⊥, ⊥]⟩
  | .g => ⟨![![⊥, ⊥, ⊥, ⊥], ![⊥, ⊥, ⊥, ⊥], ![WithBot.some 0, WithBot.some 0, WithBot.some 0, WithBot.some 0], ![⊥, ⊥, ⊥, ⊥]], ![WithBot.some 0, ⊥, WithBot.some 1, ⊥]⟩

/-- `T11`, paso 2: quita cf→caa. -/
def I_T11_2 : X → AAff 4
  | .a => ⟨![![WithBot.some 0, ⊥, ⊥, ⊥], ![⊥, ⊥, ⊥, ⊥], ![⊥, ⊥, ⊥, ⊥], ![⊥, WithBot.some 0, ⊥, ⊥]], ![⊥, ⊥, WithBot.some 0, ⊥]⟩
  | .b => ⟨![![⊥, ⊥, ⊥, ⊥], ![WithBot.some 1, ⊥, ⊥, WithBot.some 0], ![⊥, ⊥, ⊥, ⊥], ![⊥, ⊥, WithBot.some 1, ⊥]], ![WithBot.some 0, ⊥, ⊥, ⊥]⟩
  | .c => ⟨![![WithBot.some 0, ⊥, ⊥, WithBot.some 0], ![⊥, ⊥, ⊥, ⊥], ![⊥, ⊥, ⊥, ⊥], ![⊥, ⊥, ⊥, ⊥]], ![⊥, ⊥, ⊥, ⊥]⟩
  | .d => ⟨![![WithBot.some 0, ⊥, ⊥, ⊥], ![⊥, ⊥, ⊥, ⊥], ![⊥, ⊥, ⊥, ⊥], ![⊥, ⊥, ⊥, ⊥]], ![⊥, ⊥, ⊥, ⊥]⟩
  | .e => ⟨![![⊥, ⊥, ⊥, ⊥], ![⊥, ⊥, ⊥, ⊥], ![⊥, ⊥, ⊥, ⊥], ![⊥, ⊥, ⊥, ⊥]], ![WithBot.some 0, ⊥, WithBot.some 0, ⊥]⟩
  | .f => ⟨![![⊥, ⊥, ⊥, ⊥], ![⊥, ⊥, ⊥, ⊥], ![⊥, ⊥, ⊥, ⊥], ![WithBot.some 1, ⊥, ⊥, ⊥]], ![WithBot.some 0, ⊥, ⊥, ⊥]⟩
  | .g => ⟨![![⊥, ⊥, ⊥, ⊥], ![WithBot.some 1, ⊥, ⊥, ⊥], ![⊥, ⊥, ⊥, ⊥], ![⊥, ⊥, ⊥, ⊥]], ![WithBot.some 0, ⊥, ⊥, ⊥]⟩

/-- **`𝒯 ∖ {▷2 → ▷ft}` termina** (sobre palabras canónicas). Certificado: `proofs/collatz-T-11.log`. -/
theorem termIn_without_r11 : TermIn (fun ρ => ρ != .r11) :=
  TermIn.removal_arc I_T11_1 (S₁ := fun ρ => ρ == .r09)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) <|
  TermIn.removal_arc I_T11_2 (S₁ := fun ρ => ρ == .r10)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) <|
  termIn_noStart.mono (by decide)

end SRS
