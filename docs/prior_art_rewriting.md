# Prior art: Collatz como reescritura, en asistentes de pruebas

Búsqueda del 2026-11-21 (búsqueda web + lectura de los repos encontrados). No es exhaustiva:
no revisé las ediciones recientes de la Termination Competition ni el TPDB problema por problema.

## Lo que existe

**Yolcu–Aaronson–Heule** (arXiv 2105.14697; J. Autom. Reasoning 2023; código y certificados en
github.com/emreyolcu/rewriting-collatz). Definen el sistema `𝒯` y prueban (en papel) que su terminación
equivale a Collatz (Teorema 3.17). Prueban la terminación de los 11 subsistemas `𝒯 ∖ {ρ}`, de la variante
de Farkas, de varias clases mod 4/mod 8 y de otras, con su propio prover (SAT + matrices). **No** chequean
los certificados con CeTA ni con ningún asistente de pruebas.

**Hiroyuki Nashida (2026)**, tres preprints en Zenodo, cada uno con su formalización en Lean 4 + Mathlib
(sólo axiomas estándar):
- *Natural-number and arctic matrix interpretations alone make no progress, in any dimension, on the
  Collatz rewriting system* (doi 10.5281/zenodo.23147025; github.com/harappa/collatz-arctic-interpretation-barriers,
  rev. r5 del 14-oct-2026, ~63 000 líneas de Lean). **Barrera**: las interpretaciones naturales (forma EWZ,
  con las entradas superiores izquierdas ≥ 1) y las árticas (con la entrada superior izquierda finita) que
  orientan débilmente las 11 reglas no orientan estrictamente ninguna. Esto vale también para las formas
  "top" del Lema 3.18 y para el sistema invertido. Consecuencia: la eliminación de reglas con estas
  interpretaciones, *solas*, no elimina ninguna regla de `𝒯`. En su tabla de alcance, el Lema 3.15, el
  Teorema 4.1 y los subsistemas de §4.3 figuran como **"not concerned"**.
- *Dimension-free barriers … and the maximal one-class weakenings of the modulo-8 conjectures*
  (doi 10.5281/zenodo.23081491; github.com/harappa/collatz-matrix-interpretation-barriers). Prueba en Lean, a
  nivel de números, versiones debilitadas de las Conjeturas 4.11–4.14 de YAH (por ejemplo: una órbita no
  convergente contiene un número ≡ 5 o 7 (mod 8) o ≡ 4089 (mod 2¹⁴)).
- *Expanding cycles are not enough: a dichotomy for termination certificates of generalized Collatz maps*
  (doi 10.5281/zenodo.23081447; github.com/harappa/collatz-termination-certificate-dichotomy). Certifica cinco
  mapas, entre ellos el `W` de YAH (Ejemplo 3.3).

**msharpe248/collatz** (Lean 4): no trabaja con reescritura (ver `docs/forge/prior_art.md`).

## Qué parece nuestro (no encontré antecedentes)

- `collatz_iff_terminates`: el Teorema 3.17 de YAH en Lean (sobre palabras canónicas). Nashida no lo formaliza.
- `SRS.termIn_without`: los 11 subsistemas de §4.3, verificados en Lean con los certificados de YAH.
  Nashida los declara fuera de alcance.
- `farkas_convergent`: el Teorema 4.2 de YAH deducido en Lean de su certificado ártico 5×5.
  De paso encontramos un hueco en el argumento de equivalencia de §4.2: la reescritura "más a la derecha"
  **no** simula toda la trayectoria (se traba en `▷t◁`, `▷f◁`, `▷ft◁`). La conclusión vale igual con el
  invariante `Shape` y un chequeo finito (`Collatz/Rewriting/Farkas.lean`, `scripts/farkas_check.py`).

Son verificaciones formales de resultados publicados, no resultados nuevos sobre Collatz.

## Consecuencias para el plan

- El "paso real" (`SN({ρ}/𝒯)` con matrices naturales o árticas) está **bloqueado** por la barrera de Nashida,
  ya formalizada en Lean. Cualquier intento por ese lado tiene que usar otra cosa: formas generales de matrices,
  comparaciones lexicográficas, otros semianillos, o transformaciones previas que él no cubre.
- Las clases mod 4/mod 8 de YAH (§4.5) pierden interés como certificados de reescritura: Nashida ya tiene en
  Lean versiones más fuertes a nivel de números.
