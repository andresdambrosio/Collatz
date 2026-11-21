# Collatz en Lean 4

Proyecto Lake (Lean `v4.33.1` + Mathlib) para formalizar la conjetura de Collatz y resultados parciales.

## Estructura
- `Collatz/Basic.lean`: definiciones (`T`, `iter`, `Collatz`) y resultados demostrados:
  potencias de 2, descenso de pares y de n ≡ 1 (mod 4), reducción `collatz_of_descent`
  y verificación con `native_decide` hasta 1000.
- `Collatz/Reductions.lean`: `collatz_iff` (Collatz ⟺ sin ciclos no triviales ∧ sin divergencia).
- `Collatz/Forge/`: librería importada de CollatzForge (namespace `Collatz`, ~3500 líneas, 0 sorry).
  Usa sus propias definiciones (`Collatz.collatz`, `Collatz.T` **acelerado**, `Collatz.syracuse`).
  Tarda ~6 min en compilar desde cero (verificación en el kernel de `n < 600001`).
  Docs originales en `docs/forge/` (journal, known, strategy, prior_art).
- `Collatz/Bridge.lean`: equivalencias entre las dos convenciones y `cycle_period_ge` (período ≥ 2301).
  Ojo: el `T` de la raíz es el mapa clásico; `Collatz.T` es el acelerado.
- `Collatz/Rewriting.lean`: sistema de reescritura de Yolcu–Aaronson–Heule (namespace `SRS`) y `collatz_iff_terminates`.
- `Collatz/Rewriting/`: `Natural.lean`/`Arctic.lean` (verificador de interpretaciones matriciales),
  `SubsystemsNat.lean`/`SubsystemsArc.lean` (**generados** por `scripts/certs.py --gen <dir-proofs>`; no editar a mano),
  `Subsystems.lean` (`termIn_without`: los 11 subsistemas terminan),
  `FarkasCert.lean` (**generado**), `Farkas.lean` (`farkas_convergent`) y
  `AllWords.lean` (Lema 3.16: `collatz_iff_terminatesAll`, terminación sobre todas las palabras),
  `Neighbors.lean` (vecinos `t◁ → e◁` de `𝒯`: en 3x−1 y 3x−3 no se elimina ninguna regla).
- `scripts/neighbors.py`, `neighbor_matrix.py`, `neighbor_classes.py`: vecinos de `𝒯` y filtro de clases de certificados con z3 (`pip install --user z3-solver`).
- `docs/prior_art_rewriting.md`: prior art de la Fase 4 (Nashida 2026: barreras en Lean).
- `scripts/certs.py`: parser/chequeo de certificados de YAH; `scripts/srs.py`, `scripts/farkas_check.py`: chequeos numéricos.
- `Collatz/Main.lean`: los dos objetivos abiertos (`sorry`) y `collatz_conjecture`.
- `PLAN.md`: plan de trabajo por fases; mantenerlo actualizado. `Ideas/`: una idea por archivo (ver `_PLANTILLA.md`).
- `scripts/verify.py`: verificación numérica del descenso (`python3 scripts/verify.py 10000000`).

## Reglas
- La conjetura de Collatz es un **problema abierto**. Nunca declarar "demostrado" algo que use
  `sorry`, `admit`, `axiom` nuevos o hipótesis que equivalgan a la conjetura.
- Antes de afirmar que un teorema está probado: `lake build` sin errores y
  `#print axioms <teorema>` mostrando solo `propext`, `Classical.choice`, `Quot.sound`
  (más un axioma `..._native.native_decide.ax_...` si se usa `native_decide`).
  Nunca `sorryAx`. Chequeo rápido: `lake env lean scripts/Axioms.lean`.
- Lo abierto queda marcado con `sorry` y un comentario explicando qué falta.
- Preferir lemas de Mathlib; buscar con las herramientas del MCP `lean-lsp` (leansearch, loogle).

## Comandos
- `lake build` — compila todo.
- `lake env lean Collatz/Basic.lean` — chequea un archivo.
