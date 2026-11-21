import Collatz.Rewriting.Arctic

/-!
# Certificado de Farkas

Generado por `scripts/certs.py --gen <dir-proofs>` a partir de `proofs/farkas.log` del repositorio
`github.com/emreyolcu/rewriting-collatz` (Yolcu–Aaronson–Heule, §4.2, ecuación (9) y Apéndice B).
Interpretación ártica de dimensión 5 para el sistema **invertido** `ℱ^rev`. Se usa en
`Collatz.Rewriting.Farkas`.
-/

namespace SRS

/-- `farkas`, paso 1: quita df→d, dae→de, daf→df, dbf→dgf, dbg→dgg. -/
def I_farkas_1 : X → AAff 5
  | .a => ⟨![![⊥, ⊥, ⊥, ⊥, WithBot.some 0], ![⊥, ⊥, ⊥, ⊥, ⊥], ![WithBot.some 1, ⊥, WithBot.some 2, ⊥, ⊥], ![⊥, ⊥, ⊥, ⊥, ⊥], ![⊥, ⊥, ⊥, WithBot.some 2, ⊥]], ![WithBot.some 0, ⊥, ⊥, ⊥, ⊥]⟩
  | .b => ⟨![![WithBot.some 2, ⊥, ⊥, ⊥, ⊥], ![⊥, ⊥, ⊥, ⊥, ⊥], ![⊥, ⊥, WithBot.some 2, ⊥, ⊥], ![⊥, ⊥, ⊥, ⊥, ⊥], ![⊥, WithBot.some 4, ⊥, ⊥, ⊥]], ![WithBot.some 0, ⊥, ⊥, ⊥, WithBot.some 1]⟩
  | .c => ⟨![![⊥, ⊥, ⊥, ⊥, ⊥], ![⊥, ⊥, ⊥, ⊥, ⊥], ![⊥, ⊥, ⊥, ⊥, ⊥], ![⊥, ⊥, ⊥, ⊥, ⊥], ![⊥, ⊥, ⊥, ⊥, ⊥]], ![WithBot.some 1, ⊥, ⊥, ⊥, ⊥]⟩
  | .d => ⟨![![⊥, ⊥, ⊥, ⊥, WithBot.some 0], ![⊥, ⊥, ⊥, ⊥, ⊥], ![⊥, ⊥, ⊥, ⊥, ⊥], ![⊥, ⊥, ⊥, ⊥, ⊥], ![⊥, ⊥, ⊥, ⊥, ⊥]], ![WithBot.some 0, ⊥, ⊥, ⊥, ⊥]⟩
  | .e => ⟨![![WithBot.some 2, ⊥, WithBot.some 3, ⊥, ⊥], ![⊥, ⊥, ⊥, ⊥, ⊥], ![WithBot.some 3, ⊥, WithBot.some 4, ⊥, ⊥], ![WithBot.some 1, ⊥, WithBot.some 3, ⊥, ⊥], ![WithBot.some 2, ⊥, WithBot.some 4, ⊥, ⊥]], ![⊥, ⊥, ⊥, WithBot.some 0, ⊥]⟩
  | .f => ⟨![![WithBot.some 0, ⊥, WithBot.some 3, ⊥, ⊥], ![WithBot.some 0, ⊥, WithBot.some 2, ⊥, ⊥], ![WithBot.some 3, ⊥, WithBot.some 4, ⊥, ⊥], ![⊥, ⊥, ⊥, ⊥, WithBot.some 0], ![⊥, ⊥, ⊥, ⊥, WithBot.some 1]], ![⊥, ⊥, ⊥, WithBot.some 0, WithBot.some 1]⟩
  | .g => ⟨![![WithBot.some 1, ⊥, ⊥, ⊥, ⊥], ![WithBot.some 0, ⊥, ⊥, ⊥, ⊥], ![WithBot.some 3, ⊥, WithBot.some 4, ⊥, ⊥], ![⊥, ⊥, ⊥, ⊥, ⊥], ![WithBot.some 2, ⊥, ⊥, ⊥, ⊥]], ![⊥, ⊥, ⊥, ⊥, ⊥]⟩
end SRS
