"""Genera Collatz/CycleBound/{Res00..Res15,Table,Final}.lean (Fase 3b, no editar a mano).

Residuos impares mod 2^J en 2048 bloques de 256 (128 por archivo). MEMORIA: cada bloque usa
~0,65 GB propios en el kernel (uno de 2048 residuos usaba ~3,4 GB y 16 en paralelo colgaban una
máquina de 16 GB). Los archivos forman DOS CADENAS (Res(f) importa Res(f-2)), así `lake` compila
a lo sumo dos a la vez, también en un build desde cero. Tiempo total ~55 min de CPU (~30 min reales).
Tabla del sándwich para 1 ≤ k ≤ KMAX en 16 trozos (un archivo, ~15 s)."""
import os
J, Q, FUEL, CNT = 20, 78, 500, 256
PERFILE, NFILES = 128, 16
KMAX, KCH = 15600, 975
d = 'Collatz/CycleBound'
os.makedirs(d, exist_ok=True)
for old in os.listdir(d):
    os.remove(os.path.join(d, old))
GEN = "-- Generado por scripts/gen_cycle_blocks.py. No editar a mano.\n"
for f in range(NFILES):
    imp = f"Collatz.CycleBound.Res{f - 2:02d}" if f >= 2 else "Collatz.CycleBound"
    with open(f'{d}/Res{f:02d}.lean', 'w') as o:
        o.write(GEN + f"import {imp}\n\nnamespace Collatz\n\n")
        bs = range(PERFILE * f, PERFILE * f + PERFILE)
        for b in bs:
            o.write(f"set_option maxHeartbeats 0 in\ntheorem cb_res_{b} : blockOK {J} {Q} {FUEL} {1 + 2 * CNT * b} {CNT} = true := by\n  decide +kernel\n\n")
        o.write(f"theorem cb_file_{f} (i : ℕ) (hi : i < {PERFILE}) :\n"
                f"    blockOK {J} {Q} {FUEL} (1 + {2 * CNT} * ({PERFILE} * {f} + i)) {CNT} = true := by\n"
                f"  interval_cases i\n  exacts [{', '.join(f'cb_res_{b}' for b in bs)}]\n\nend Collatz\n")
with open(f'{d}/Table.lean', 'w') as o:
    o.write(GEN + "import Collatz.CycleBound\n\nnamespace Collatz\n\n")
    for c in range(KMAX // KCH):
        o.write(f"set_option maxHeartbeats 0 in\ntheorem cb_tab_{c} :\n    (List.range' {1 + KCH * c} {KCH}).all (k12_sandwichFree (2 ^ {J} * {Q})) = true := by\n  decide +kernel\n\n")
    o.write(f"""theorem cb_chunks (c : ℕ) (hc : c < {KMAX // KCH}) :
    (List.range' (1 + {KCH} * c) {KCH}).all (k12_sandwichFree (2 ^ {J} * {Q})) = true := by
  interval_cases c
  exacts [{", ".join(f"cb_tab_{c}" for c in range(KMAX // KCH))}]

theorem cb_table {{k : ℕ}} (hk : 0 < k) (hkK : k ≤ {KMAX}) :
    k12_sandwichFree (2 ^ {J} * {Q}) k = true := by
  have h := cb_chunks ((k - 1) / {KCH}) (by omega)
  simp only [List.all_eq_true, List.mem_range'] at h
  exact h k ⟨k - 1 - {KCH} * ((k - 1) / {KCH}), by omega, by omega⟩

end Collatz
""")
NB = PERFILE * NFILES
with open(f'{d}/Final.lean', 'w') as o:
    o.write(GEN + f"import Collatz.CycleBound.Res{NFILES - 2:02d}\nimport Collatz.CycleBound.Res{NFILES - 1:02d}\nimport Collatz.CycleBound.Table\n")
    o.write(f"""
/-!
# Fase 3b: todo ciclo no trivial tiene al menos {KMAX + 1} pasos impares

Incondicional, chequeado en el kernel. `M = 2^{J} · {Q} = {2 ** J * Q}`: todo impar `1 < n < M`
desciende bajo `T` (criba de Terras mod `2^{J}` + chequeo numérico de los sobrevivientes,
`Res00`–`Res{NFILES - 1:02d}`); por lo tanto ningún elemento de un ciclo no trivial es `< M`
(`syracuse_cycle_ge_of_descends`), y el sándwich no deja ningún `A` para `1 ≤ k ≤ {KMAX}` (`Table`).
-/

namespace Collatz

theorem cb_blocks (b : ℕ) (hb : b < {NB}) : blockOK {J} {Q} {FUEL} (1 + {2 * CNT} * b) {CNT} = true := by
  obtain ⟨f, i, hi, rfl⟩ : ∃ f i, i < {PERFILE} ∧ b = {PERFILE} * f + i :=
    ⟨b / {PERFILE}, b % {PERFILE}, Nat.mod_lt _ (by norm_num), (Nat.div_add_mod b {PERFILE}).symm⟩
  have hf : f < {NFILES} := by omega
  interval_cases f
  exacts [{", ".join(f"cb_file_{f} i hi" for f in range(NFILES))}]

theorem cb_residues : ∀ r, r < 2 ^ {J} → r % 2 = 1 → residueOK {J} {Q} {FUEL} r = true := by
  intro r hr hodd
  exact blockOK_mem (cb_blocks (r / {2 * CNT}) (by omega)) (by omega) (by omega) (by omega)

theorem cb_descendsBelow : DescendsBelow (2 ^ {J} * {Q}) :=
  descendsBelow_of_T (descendsT_of_residueOK (by norm_num) cb_residues)

/-- **Todo ciclo no trivial de Syracuse tiene al menos {KMAX + 1} pasos.** Incondicional
(antes: 2301, `k12_syracuse_cycle_length_ge`). -/
theorem syracuse_cycle_length_ge_{KMAX + 1} {{n k : ℕ}} (hn : n % 2 = 1) (hk : 0 < k)
    (h : syracuse^[k] n = n) (hne : n ≠ 1) : {KMAX + 1} ≤ k := by
  by_contra hlt
  push Not at hlt
  obtain ⟨h1, h2⟩ := cycle_sandwich_of_descends cb_descendsBelow hn hk h hne
  exact k12_no_A_of_sandwichFree (cb_table hk (by omega)) _ h1 h2

end Collatz

/-- **Todo ciclo no trivial de `T` tiene período al menos {KMAX + 1}.** Incondicional. -/
theorem cycle_period_ge_{KMAX + 1} {{n p : ℕ}} (hn : n ≥ 1) (hp : p ≥ 1) (h : iter p n = n)
    (hnt : ¬ InTrivialCycle n) : {KMAX + 1} ≤ p :=
  cycle_period_ge_of (fun hm hk h' hne => Collatz.syracuse_cycle_length_ge_{KMAX + 1} hm hk h' hne)
    hn hp h hnt
""")
print("ok")
