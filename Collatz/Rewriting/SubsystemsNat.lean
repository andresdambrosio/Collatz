import Collatz.Rewriting.Natural

/-!
# Subsistemas de `𝒯` con certificados naturales

Generado por `scripts/certs.py --gen <dir-proofs>` a partir de `proofs/collatz-T-NN.log` del
repositorio `github.com/emreyolcu/rewriting-collatz` (Yolcu–Aaronson–Heule, arXiv 2105.14697,
§4.3, Tabla 1). Las matrices se copian de los certificados; Lean las chequea con `decide +kernel`.

Para cada regla `ρ` de este archivo: `𝒯 ∖ {ρ}` termina sobre palabras canónicas. Esquema (el del
paper): se eliminan las reglas de inicio `ℬ` en 1 a 3 pasos con interpretaciones débilmente
monótonas, y lo que queda está contenido en `𝒯 ∖ ℬ`, que termina (`termIn_noStart`).
-/

namespace SRS

set_option maxRecDepth 20000

/-- `T01`, paso 1: quita ce→cb, cf→caa, cg→cab. -/
def I_T01_1 : X → Aff 3
  | .a => ⟨![![1, 1, 0], ![0, 1, 0], ![0, 0, 0]], ![0, 0, 0]⟩
  | .b => ⟨![![1, 0, 1], ![0, 1, 0], ![0, 0, 1]], ![0, 0, 0]⟩
  | .c => ⟨![![1, 1, 1], ![0, 0, 0], ![0, 0, 0]], ![0, 0, 0]⟩
  | .d => ⟨![![0, 0, 0], ![0, 0, 0], ![0, 0, 0]], ![0, 0, 1]⟩
  | .e => ⟨![![1, 1, 1], ![0, 2, 2], ![0, 0, 0]], ![1, 0, 0]⟩
  | .f => ⟨![![1, 1, 0], ![0, 2, 2], ![0, 0, 0]], ![1, 0, 0]⟩
  | .g => ⟨![![1, 0, 0], ![0, 2, 0], ![0, 0, 1]], ![1, 0, 0]⟩

/-- **`𝒯 ∖ {f◁ → ◁}` termina** (sobre palabras canónicas). Certificado: `proofs/collatz-T-01.log`. -/
theorem termIn_without_r01 : TermIn (fun ρ => ρ != .r01) :=
  TermIn.removal_nat I_T01_1 (S₁ := fun ρ => ρ == .r09 || ρ == .r10 || ρ == .r11)
    (by decide +kernel) (by decide +kernel) <|
  termIn_noStart.mono (by decide)

/-- `T02`, paso 1: quita ce→cb, cf→caa, cg→cab. -/
def I_T02_1 : X → Aff 1
  | .a => ⟨![![1]], ![0]⟩
  | .b => ⟨![![1]], ![0]⟩
  | .c => ⟨![![1]], ![0]⟩
  | .d => ⟨![![1]], ![1]⟩
  | .e => ⟨![![1]], ![1]⟩
  | .f => ⟨![![1]], ![1]⟩
  | .g => ⟨![![1]], ![1]⟩

/-- **`𝒯 ∖ {t◁ → 2◁}` termina** (sobre palabras canónicas). Certificado: `proofs/collatz-T-02.log`. -/
theorem termIn_without_r02 : TermIn (fun ρ => ρ != .r02) :=
  TermIn.removal_nat I_T02_1 (S₁ := fun ρ => ρ == .r09 || ρ == .r10 || ρ == .r11)
    (by decide +kernel) (by decide +kernel) <|
  termIn_noStart.mono (by decide)

/-- `T03`, paso 1: quita cf→caa. -/
def I_T03_1 : X → Aff 4
  | .a => ⟨![![0, 0, 0, 0], ![1, 0, 0, 0], ![0, 1, 0, 0], ![0, 0, 1, 0]], ![0, 0, 0, 0]⟩
  | .b => ⟨![![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 1], ![0, 0, 0, 0]], ![1, 1, 0, 0]⟩
  | .c => ⟨![![1, 0, 1, 0], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0]], ![0, 0, 0, 0]⟩
  | .d => ⟨![![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0]], ![0, 0, 0, 0]⟩
  | .e => ⟨![![0, 0, 0, 1], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0]], ![0, 0, 1, 1]⟩
  | .f => ⟨![![1, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0]], ![0, 1, 1, 0]⟩
  | .g => ⟨![![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0]], ![1, 1, 0, 0]⟩

/-- `T03`, paso 2: quita ce→cb. -/
def I_T03_2 : X → Aff 4
  | .a => ⟨![![0, 0, 0, 0], ![1, 0, 0, 1], ![0, 0, 0, 0], ![0, 0, 0, 0]], ![1, 0, 0, 1]⟩
  | .b => ⟨![![0, 0, 0, 1], ![1, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0]], ![0, 0, 0, 0]⟩
  | .c => ⟨![![0, 1, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0]], ![0, 0, 0, 0]⟩
  | .d => ⟨![![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0]], ![0, 0, 0, 0]⟩
  | .e => ⟨![![0, 0, 0, 0], ![1, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0]], ![0, 1, 0, 1]⟩
  | .f => ⟨![![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 1]], ![1, 0, 0, 0]⟩
  | .g => ⟨![![0, 0, 0, 0], ![0, 0, 0, 1], ![0, 0, 0, 0], ![0, 0, 0, 0]], ![0, 0, 0, 0]⟩

/-- `T03`, paso 3: quita cg→cab. -/
def I_T03_3 : X → Aff 4
  | .a => ⟨![![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0]], ![0, 0, 0, 0]⟩
  | .b => ⟨![![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0]], ![0, 0, 0, 1]⟩
  | .c => ⟨![![0, 0, 0, 1], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0]], ![0, 0, 0, 0]⟩
  | .d => ⟨![![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0]], ![0, 0, 0, 0]⟩
  | .e => ⟨![![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0]], ![0, 0, 0, 0]⟩
  | .f => ⟨![![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0]], ![0, 0, 0, 0]⟩
  | .g => ⟨![![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0]], ![0, 0, 0, 1]⟩

/-- **`𝒯 ∖ {f0 → 0f}` termina** (sobre palabras canónicas). Certificado: `proofs/collatz-T-03.log`. -/
theorem termIn_without_r03 : TermIn (fun ρ => ρ != .r03) :=
  TermIn.removal_nat I_T03_1 (S₁ := fun ρ => ρ == .r10)
    (by decide +kernel) (by decide +kernel) <|
  TermIn.removal_nat I_T03_2 (S₁ := fun ρ => ρ == .r09)
    (by decide +kernel) (by decide +kernel) <|
  TermIn.removal_nat I_T03_3 (S₁ := fun ρ => ρ == .r11)
    (by decide +kernel) (by decide +kernel) <|
  termIn_noStart.mono (by decide)

/-- `T04`, paso 1: quita ce→cb. -/
def I_T04_1 : X → Aff 1
  | .a => ⟨![![1]], ![0]⟩
  | .b => ⟨![![1]], ![0]⟩
  | .c => ⟨![![1]], ![0]⟩
  | .d => ⟨![![2]], ![2]⟩
  | .e => ⟨![![2]], ![2]⟩
  | .f => ⟨![![1]], ![0]⟩
  | .g => ⟨![![1]], ![0]⟩

/-- `T04`, paso 2: quita cf→caa. -/
def I_T04_2 : X → Aff 1
  | .a => ⟨![![1]], ![0]⟩
  | .b => ⟨![![1]], ![1]⟩
  | .c => ⟨![![1]], ![0]⟩
  | .d => ⟨![![0]], ![0]⟩
  | .e => ⟨![![1]], ![1]⟩
  | .f => ⟨![![1]], ![1]⟩
  | .g => ⟨![![1]], ![1]⟩

/-- `T04`, paso 3: quita cg→cab. -/
def I_T04_3 : X → Aff 1
  | .a => ⟨![![0]], ![0]⟩
  | .b => ⟨![![0]], ![1]⟩
  | .c => ⟨![![1]], ![0]⟩
  | .d => ⟨![![0]], ![0]⟩
  | .e => ⟨![![0]], ![0]⟩
  | .f => ⟨![![0]], ![0]⟩
  | .g => ⟨![![0]], ![1]⟩

/-- **`𝒯 ∖ {f1 → 0t}` termina** (sobre palabras canónicas). Certificado: `proofs/collatz-T-04.log`. -/
theorem termIn_without_r04 : TermIn (fun ρ => ρ != .r04) :=
  TermIn.removal_nat I_T04_1 (S₁ := fun ρ => ρ == .r09)
    (by decide +kernel) (by decide +kernel) <|
  TermIn.removal_nat I_T04_2 (S₁ := fun ρ => ρ == .r10)
    (by decide +kernel) (by decide +kernel) <|
  TermIn.removal_nat I_T04_3 (S₁ := fun ρ => ρ == .r11)
    (by decide +kernel) (by decide +kernel) <|
  termIn_noStart.mono (by decide)

/-- `T05`, paso 1: quita ce→cb, cf→caa. -/
def I_T05_1 : X → Aff 1
  | .a => ⟨![![1]], ![0]⟩
  | .b => ⟨![![1]], ![0]⟩
  | .c => ⟨![![1]], ![0]⟩
  | .d => ⟨![![1]], ![1]⟩
  | .e => ⟨![![1]], ![1]⟩
  | .f => ⟨![![1]], ![1]⟩
  | .g => ⟨![![1]], ![0]⟩

/-- `T05`, paso 2: quita cg→cab. -/
def I_T05_2 : X → Aff 1
  | .a => ⟨![![0]], ![0]⟩
  | .b => ⟨![![0]], ![1]⟩
  | .c => ⟨![![1]], ![0]⟩
  | .d => ⟨![![0]], ![0]⟩
  | .e => ⟨![![0]], ![0]⟩
  | .f => ⟨![![0]], ![0]⟩
  | .g => ⟨![![0]], ![1]⟩

/-- **`𝒯 ∖ {f2 → 1f}` termina** (sobre palabras canónicas). Certificado: `proofs/collatz-T-05.log`. -/
theorem termIn_without_r05 : TermIn (fun ρ => ρ != .r05) :=
  TermIn.removal_nat I_T05_1 (S₁ := fun ρ => ρ == .r09 || ρ == .r10)
    (by decide +kernel) (by decide +kernel) <|
  TermIn.removal_nat I_T05_2 (S₁ := fun ρ => ρ == .r11)
    (by decide +kernel) (by decide +kernel) <|
  termIn_noStart.mono (by decide)

/-- `T09`, paso 1: quita cf→caa. -/
def I_T09_1 : X → Aff 2
  | .a => ⟨![![0, 1], ![0, 0]], ![0, 0]⟩
  | .b => ⟨![![0, 0], ![0, 0]], ![1, 1]⟩
  | .c => ⟨![![1, 0], ![0, 0]], ![0, 0]⟩
  | .d => ⟨![![0, 0], ![0, 0]], ![0, 0]⟩
  | .e => ⟨![![0, 0], ![0, 0]], ![0, 0]⟩
  | .f => ⟨![![0, 0], ![0, 0]], ![1, 0]⟩
  | .g => ⟨![![0, 0], ![0, 0]], ![1, 1]⟩

/-- `T09`, paso 2: quita cg→cab. -/
def I_T09_2 : X → Aff 2
  | .a => ⟨![![0, 0], ![0, 0]], ![0, 0]⟩
  | .b => ⟨![![0, 0], ![0, 0]], ![0, 1]⟩
  | .c => ⟨![![0, 1], ![0, 0]], ![0, 0]⟩
  | .d => ⟨![![0, 0], ![0, 0]], ![0, 0]⟩
  | .e => ⟨![![0, 0], ![0, 0]], ![0, 0]⟩
  | .f => ⟨![![0, 0], ![0, 0]], ![0, 0]⟩
  | .g => ⟨![![0, 0], ![0, 0]], ![0, 1]⟩

/-- **`𝒯 ∖ {▷0 → ▷t}` termina** (sobre palabras canónicas). Certificado: `proofs/collatz-T-09.log`. -/
theorem termIn_without_r09 : TermIn (fun ρ => ρ != .r09) :=
  TermIn.removal_nat I_T09_1 (S₁ := fun ρ => ρ == .r10)
    (by decide +kernel) (by decide +kernel) <|
  TermIn.removal_nat I_T09_2 (S₁ := fun ρ => ρ == .r11)
    (by decide +kernel) (by decide +kernel) <|
  termIn_noStart.mono (by decide)

/-- `T10`, paso 1: quita ce→cb. -/
def I_T10_1 : X → Aff 3
  | .a => ⟨![![0, 0, 0], ![2, 0, 1], ![0, 0, 0]], ![1, 0, 1]⟩
  | .b => ⟨![![0, 0, 0], ![0, 0, 1], ![1, 0, 0]], ![0, 0, 0]⟩
  | .c => ⟨![![0, 1, 0], ![0, 0, 0], ![0, 0, 0]], ![0, 0, 0]⟩
  | .d => ⟨![![0, 0, 0], ![0, 0, 0], ![0, 0, 0]], ![0, 0, 0]⟩
  | .e => ⟨![![0, 0, 0], ![0, 0, 1], ![0, 0, 0]], ![1, 1, 0]⟩
  | .f => ⟨![![1, 0, 0], ![0, 0, 0], ![0, 0, 0]], ![0, 0, 1]⟩
  | .g => ⟨![![0, 0, 0], ![1, 0, 0], ![0, 0, 0]], ![0, 0, 0]⟩

/-- `T10`, paso 2: quita cg→cab. -/
def I_T10_2 : X → Aff 3
  | .a => ⟨![![0, 0, 0], ![0, 0, 0], ![0, 0, 0]], ![0, 0, 0]⟩
  | .b => ⟨![![0, 0, 0], ![0, 0, 0], ![0, 0, 0]], ![0, 0, 1]⟩
  | .c => ⟨![![0, 0, 1], ![0, 0, 0], ![0, 0, 0]], ![0, 0, 0]⟩
  | .d => ⟨![![0, 0, 0], ![0, 0, 0], ![0, 0, 0]], ![0, 0, 0]⟩
  | .e => ⟨![![0, 0, 0], ![0, 0, 0], ![0, 0, 0]], ![0, 0, 0]⟩
  | .f => ⟨![![0, 0, 0], ![0, 0, 0], ![0, 0, 0]], ![0, 0, 0]⟩
  | .g => ⟨![![0, 0, 0], ![0, 0, 0], ![0, 0, 0]], ![0, 0, 1]⟩

/-- **`𝒯 ∖ {▷1 → ▷ff}` termina** (sobre palabras canónicas). Certificado: `proofs/collatz-T-10.log`. -/
theorem termIn_without_r10 : TermIn (fun ρ => ρ != .r10) :=
  TermIn.removal_nat I_T10_1 (S₁ := fun ρ => ρ == .r09)
    (by decide +kernel) (by decide +kernel) <|
  TermIn.removal_nat I_T10_2 (S₁ := fun ρ => ρ == .r11)
    (by decide +kernel) (by decide +kernel) <|
  termIn_noStart.mono (by decide)

end SRS
