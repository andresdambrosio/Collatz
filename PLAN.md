# Plan de trabajo: Collatz

**Objetivo:** demostrar `collatz_conjecture` en Lean sin `sorry`.
**Realismo:** es un problema abierto. Cada fase deja resultados verificados que valen por sí mismos,
aunque la prueba completa no llegue.

## Principios
1. **Lean es el juez.** Nada está "probado" hasta compilar sin `sorry` y pasar `scripts/Axioms.lean`.
2. **Calcular antes de formalizar.** Cada lema candidato se prueba primero con Python en millones de casos.
3. **Filtro de barreras.** Toda idea debe responder:
   - ¿Falla para 5n+1? (debe fallar: 5n+1 tiene ciclos no triviales)
   - ¿Usa que n > 0? (debe usarlo: con negativos hay ciclos −1, −5, −17)
   - ¿Es solo un argumento mod 2^k? (no alcanza: la clase −1 mod 2^k no baja en k pasos)
   - ¿Es solo probabilística? (da "casi todos", no "todos")
   - ¿Usa algo específico de 3n+1? (Conway: no hay método general)
4. **Los fracasos se registran** con su causa precisa en `Ideas/`.

## Fases

### Fase 0 — Infraestructura ✅ (excepto MCP)
- [x] Proyecto Lake + Mathlib, resultados parciales en `Collatz/Basic.lean`
- [ ] Conectar `lean-lsp-mcp` (el usuario ejecuta el comando)

### Fase 1 — Fundamentos en Lean ✅ (importados de CollatzForge, 2026-11-20)
- [x] Reducción `collatz_iff`: Collatz ⟺ sin ciclos no triviales ∧ sin órbitas divergentes
- [x] Puente `Collatz/Bridge.lean`: las definiciones de este proyecto coinciden con las de
      `Collatz.Forge` (`collatz_iff_forge`, `noNontrivialCycles_iff_forge`, `noDivergentOrbits_iff_forge`)
- [x] Mapa acelerado y Syracuse (`Forge/Invariants/IsPeriodicIffT.lean`, `SyracuseCycles.lean`)
- [x] Lema de Terras (`Forge/Invariants/Terras.lean`)
- [x] Ecuación de ciclos (`Forge/Invariants/SyracuseCycleEquation.lean`)

### Fase 2 — Mapa de traducciones
- [ ] Búsqueda bibliográfica que verifique y complete `Ideas/traducciones.md`
- [ ] Para cada traducción: invariante que detecta, si distingue 3 de 5, hasta dónde llegó, por qué se trabó

### Fase 3 — Frente ciclos (`no_nontrivial_cycles`)
- [x] Cota inferior del mínimo de un ciclo a partir de verificación computacional
- [x] **Incondicional:** todo ciclo no trivial tiene ≥ 2301 pasos impares
      (`Collatz.k12_syracuse_cycle_length_ge`); en el lenguaje de este proyecto,
      período ≥ 2301 (`cycle_period_ge`, `Bridge.lean`)
- [x] Bajo `VerifiedBelow 2^71` (Barina, hipótesis explícita): ≥ 72 057 431 991 pasos impares
      (`Collatz.hercher_lower_bound`)
- [ ] Ciclos de un pico (Steiner) en Lean
- [ ] Explorar hasta dónde llegan cotas sobre |2^K − 3^L|

### Fase 4 — Frente reescritura / certificados (ataque principal)
- [x] Sistema `𝒯` de Yolcu–Aaronson–Heule (arXiv 2105.14697, 11 reglas, binario/ternario) en Lean:
      `collatz_iff_terminates : Collatz ↔ SRS.Terminates` (`Collatz/Rewriting.lean`), sobre palabras
      canónicas `▷w◁`; y `collatz_iff_terminatesAll` sobre **todas** las palabras del alfabeto de 7 letras
      (Lema 3.16, `Collatz/Rewriting/AllWords.lean`, con una prueba directa por cortes en los marcadores
      y medidas lexicográficas, sin la *type introduction* del paper).
      Validación numérica previa: `scripts/srs.py`.
- [x] Verificador en Lean: eliminación de reglas por medida + interpretaciones naturales
      (`Rewriting/Natural.lean`) y árticas (`Rewriting/Arctic.lean`), chequeo con `decide +kernel`
- [x] Los 11 subsistemas `𝒯 ∖ {ρ}` terminan (`SRS.termIn_without`, `Rewriting/Subsystems.lean`),
      con los certificados de github.com/emreyolcu/rewriting-collatz (`proofs/collatz-T-NN.log`),
      parseados y re-chequeados por `scripts/certs.py --gen <dir-proofs>`. Sobre palabras canónicas.
- [x] Prior art (`docs/prior_art_rewriting.md`): no encontré verificación formal de estos certificados.
      **Nashida (2026, Lean)** prueba que las matrices naturales/árticas *solas* no eliminan ninguna regla de
      `𝒯` en ninguna dimensión: el "paso real" por esa vía está bloqueado. También tiene en Lean versiones
      más fuertes de las clases mod 8 de YAH.
- [x] Farkas: `ℱ` termina (`SRS.Farkas.termF_all`, certificado ártico 5×5 sobre `ℱ^rev`) y de ahí
      `farkas_convergent` (Teorema 4.2 de YAH). Se corrigió un hueco del argumento de §4.2 (`Shape` + chequeo finito).
- [ ] (descartado por ahora) clases mod 4/mod 8 de §4.5: Nashida ya tiene resultados más fuertes en Lean
- [ ] Si se vuelve a `SN({ρ}/𝒯)`: sólo con técnicas fuera de la barrera de Nashida
- [x] Vecinos `t◁ → e◁` (`e = 1`: 3x−1, `e = 0`: 3x−3) como filtro de técnicas: en ellos ninguna regla se
      puede eliminar (`SRS.Neighbor.not_relSN_d1/d0`, `Collatz/Rewriting/Neighbors.lean`). Descarta las
      interpretaciones afines de dimensión 1 sobre ℝ≥0 (z3). Ver `Ideas/vecinos_de_T.md`
- [ ] Verificar en Lean los certificados de terminación que encuentre la búsqueda
- [ ] Empujar la frontera: variantes más fuertes que las ya demostradas

- [x] Matrices racionales (fuera de Nashida): sin certificados en `d = 2` con entradas `k/D` chicas
      (`scripts/rational_search.py`). **Frente en pausa desde 2026-11-21.**

### Fase 3b — Ciclos: subir la cota incondicional verificada (frente activo desde 2026-11-21)
Para la cota sólo hace falta que ningún elemento de un ciclo sea `< M`: alcanza con que todo impar `n < M`
**baje por debajo de sí mismo** (más barato que llegar a 1). Con criba mod `2^20` sólo queda el ~2,6 % de los enteros.
Cota según `M` (mínimo `k` con `0 < A − k·log₂3 ≤ k·log₂(1 + 1/(3M))`; coincide con Forge en 6·10⁵ y 2⁷¹):

| M | 6·10⁵ (hoy) | 10⁸ | 10⁹ | 10¹⁰ | 2⁴⁰ |
|---|---|---|---|---|---|
| k ≥ | 2 301 | 15 601 | 47 468 | 190 537 | 10 781 274 |

- [x] Lema en Lean: si todo impar `n < M` desciende, no hay elemento de ciclo `< M`
      (`syracuse_cycle_ge_of_descends`, `cycle_sandwich_of_descends`, `Collatz/CycleBound.lean`)
- [x] Criba de Terras verificada (`symDesc_sound`) y chequeo numérico de los sobrevivientes (`dropsB_sound`)
- [x] **`M = 78·2²⁰ = 81 788 928`, todo en el kernel: todo ciclo no trivial tiene ≥ 15 601 pasos impares**
      (`Collatz.syracuse_cycle_length_ge_15601`; período de `T` ≥ 15 601: `cycle_period_ge_15601`).
      Antes: 2301. Archivos generados por `scripts/gen_cycle_blocks.py` en `Collatz/CycleBound/`
- [ ] Siguiente salto: `M ≈ 2,9·10⁸` da `k ≥ 47 468` (3,5× más cómputo); `M ≈ 1,5·10⁹` da `79 335`
Es una mejora del resultado *formal*; la literatura (con verificación a 2⁷¹, no formal) tiene ≥ 1,1·10¹¹.

### Contexto — Indecidibilidad de Conway ✅ (2026-11-25)
- [x] `Conway.conway_undecidable_fixed`: existe una función de Collatz generalizada multiplicativa fija
      (`g(n) = a_{n mod D}·n`, `a_j ∈ ℚ`) cuyo problema "¿alguna iteración de `2^m` es potencia de 2 / vale 1?"
      no es computable; `Conway.conway_undecidable(_one)`: idem con `(D, tabla, n)` como dato.
      Teorema de Conway (1972); lo nuestro es sólo la verificación formal (hay versión en Coq de FRACTRAN).
- [ ] Opcional: versión Π₂ "¿toda órbita llega a 1?" (Kurtz–Simon 2007), que necesita otra reducción.

### Fase 5 — Frente divergencia (`no_divergent_orbits`)
- [x] Retrato de un contraejemplo (Forge): → ∞, densidad de impares ≤ log₂3, aperiódico,
      conjunto fino. Ver `docs/forge/known.md`. Lo que sigue es el muro.
- [ ] Laboratorio de ideas: funciones potencial, árbol inverso, argumentos 2-ádicos, acarreos en binario

## Laboratorio de ideas (desde 2026-11-23)
Cinco rondas documentadas en `Ideas/LAB.md`: minería de literatura, catálogo de Chang (29 paradigmas),
etiquetado semántico + matrices (`scripts/labelled_*.py`), obstrucción de logaritmo discreto (colapsa en
Hercher `m ≥ 92`), problema de Erdős. Síntesis: toda vía termina en probar algo sobre UNA órbita concreta.
Próximo: `Collatz/Frontier.lean` (atlas de enunciados abiertos + reducciones verificadas).

## Estado de los `sorry`
| Teorema | Archivo | Estado |
|---|---|---|
| `collatz_iff` | `Collatz/Reductions.lean` | ✅ demostrado |
| `no_nontrivial_cycles` | `Collatz/Main.lean` | abierto |
| `no_divergent_orbits` | `Collatz/Main.lean` | abierto |
