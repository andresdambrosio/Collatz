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
- [ ] Verificar en Lean los certificados de terminación que encuentre la búsqueda
- [ ] Empujar la frontera: variantes más fuertes que las ya demostradas

### Fase 5 — Frente divergencia (`no_divergent_orbits`)
- [x] Retrato de un contraejemplo (Forge): → ∞, densidad de impares ≤ log₂3, aperiódico,
      conjunto fino. Ver `docs/forge/known.md`. Lo que sigue es el muro.
- [ ] Laboratorio de ideas: funciones potencial, árbol inverso, argumentos 2-ádicos, acarreos en binario

## Estado de los `sorry`
| Teorema | Archivo | Estado |
|---|---|---|
| `collatz_iff` | `Collatz/Reductions.lean` | ✅ demostrado |
| `no_nontrivial_cycles` | `Collatz/Main.lean` | abierto |
| `no_divergent_orbits` | `Collatz/Main.lean` | abierto |
