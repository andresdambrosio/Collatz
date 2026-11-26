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

## Actualización 2026-11-23 (búsqueda de novedad para un paper)

- **TPDB** (github.com/TermCOMP/TPDB, `SRS_Standard/Yolcu_21/`): están `collatz-T.xml`, `farkas.xml`, `collatz-L.xml`,
  `collatz-S.xml`, `collatz-T-5or7mod8.xml`, `barina.xml`, `mahler.xml`, `michel.xml` y `silva.xml`. **No** están los 11
  subsistemas `𝒯 ∖ {ρ}`. La Termination Competition tiene una categoría SRS **certificada con CeTA** (Isabelle).
  **Riesgo abierto:** que alguna herramienta (por ejemplo AProVE en modo certificado) haya certificado `farkas.xml` en
  termCOMP 2021–2025. Hay que mirar los resultados por problema en StarExec / termcomp.github.io. Aun así, CeTA
  certifica la terminación del SRS, **no** la equivalencia "terminación ⇒ convergencia", que es donde está el hueco
  de §4.2.
- **YAH v3** (arXiv, 31-dic-2022, la última versión): no menciona CeTA ni ningún asistente de pruebas (grep sobre el
  texto completo). §4.2, cita textual: "repeatedly performing the rightmost possible rewrite results in a rewrite sequence
  that simulates the F-trajectory". Es exactamente lo que encontramos falso en `▷t◁`, `▷f◁`, `▷ft◁`. No hay errata.
- **Nashida**: sin pushes desde el 16-oct-2026. El alcance no cambió (Teo. 3.17 y los subsistemas siguen fuera).
- **Otras formalizaciones de Collatz en Lean**: no encontré ninguna de la vía de reescritura. Paulson (blog, 30-jul-2026)
  cuenta que una "refutación" de Collatz en Lean (Ramana Kumar, xrchz/CollatzLean) explotaba un bug del kernel.
  Es relevante para la sección de confianza del paper: nuestra cota de ciclos usa `decide +kernel` en volumen.

## Chequeo de novedad para el paper (2026-11-26)
- **Versión de revista:** J. Autom. Reasoning 67, art. 15 (recibido 3-dic-2021, aceptado 30-dic-2022, publicado
  25-abr-2023), acceso abierto CC BY 4.0, doi:10.1007/s10817-022-09658-8 (leído del PDF bajado a mano, 26/11). **La frase
  del §4.2 está igual** (pp. 23–24): "Then repeatedly performing the rightmost possible rewrite results in a rewrite
  sequence that simulates the F-trajectory." Misma numeración (Lema 3.15, 3.16, Teo. 3.17, Lema 3.18, Teo. 3.19,
  Teo. 4.2). No menciona CeTA, asistentes de prueba ni chequeo independiente (Sternagel–Thiemann [12] se cita sólo
  como referencia de interpretaciones árticas). Sin declaración de licencia del código; repo: github.com/emreyolcu/rewriting-collatz.
- **Alcance honesto del hueco:** la frase se usa para "trayectoria no convergente ⇒ reescritura infinita". Como enunciado
  general es falsa (ejemplos abajo, todos convergentes), pero sobre trayectorias no convergentes es cierta: trabarse
  obliga a valor ≤ 7, que converge. Falta un argumento (invariante `Shape` + chequeo finito); **el teorema está bien**.
  En el paper hay que presentarlo como un hueco menor reparado, no como un error.
- **TPDB:** `SRS_Standard/Yolcu_21/farkas.xml` (junto con barina, collatz-L, collatz-S, collatz-T-5or7mod8, collatz-T,
  mahler, michel, silva). Los 11 subsistemas no están. El repo TPDB está archivado (oct. 2025; sigue en TPDB-ARI).
  **Pendiente:** resultados por problema en la categoría certificada (StarExec / termcomp.github.io no muestran las tablas
  en una lectura automática). Recordar: CeTA certificaría sólo la terminación, no "terminación ⇒ convergencia".
- **Licencia:** `emreyolcu/rewriting-collatz` no declara licencia (API de GitHub: `license: null`; último push 7-oct-2023).
  Nuestros `SubsystemsNat/Arc.lean` y `FarkasCert.lean` derivan de sus certificados (atribución en `NOTICE`): pedir permiso.
- **Ejemplo concreto del hueco** (`scripts/farkas_check.py`): desde `n = 3` (ternario `10`), la reescritura más a la
  derecha termina en la forma normal `▷t◁` (valor 3) sin simular la trayectoria 3 → 5 → 8 → 4 → 1. Lo mismo para
  2, 5, 6, 7, 9, 10, 12, 14, 16, 18, 19, … (formas normales `▷f◁`, `▷t◁`, `▷ft◁`).
- **Lugar:** ITP 2026 cerró el 19-feb-2026 (abstract 12-feb); ITP 2027 sin fecha (en llamado a sedes). JAR es la alternativa sin fechas.
