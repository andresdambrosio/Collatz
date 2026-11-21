import Collatz.Rewriting.SubsystemsNat
import Collatz.Rewriting.SubsystemsArc

/-!
# Los 11 subsistemas `𝒯 ∖ {ρ}` terminan

Resumen de `SubsystemsNat` y `SubsystemsArc`: para cada una de las 11 reglas `ρ` del sistema de
Yolcu–Aaronson–Heule, el sistema sin `ρ` termina sobre palabras canónicas `▷ w ◁`
(Yolcu–Aaronson–Heule, §4.3, Tabla 1; certificados de su repositorio, verificados acá por Lean).

Esto **no** dice nada nuevo sobre Collatz: es la versión verificada de un resultado publicado.
Por `collatz_iff_terminates`, la conjetura equivale a `TermIn (fun _ => true)`, y para cualquier
`ρ`, ahora bastaría probar que `ρ` se aplica finitas veces relativo al resto (`SN({ρ} / 𝒯)`).
-/

namespace SRS

theorem termIn_without : ∀ ρ : RuleName, TermIn (fun σ => σ != ρ)
  | .r01 => termIn_without_r01
  | .r02 => termIn_without_r02
  | .r03 => termIn_without_r03
  | .r04 => termIn_without_r04
  | .r05 => termIn_without_r05
  | .r06 => termIn_without_r06
  | .r07 => termIn_without_r07
  | .r08 => termIn_without_r08
  | .r09 => termIn_without_r09
  | .r10 => termIn_without_r10
  | .r11 => termIn_without_r11

end SRS
