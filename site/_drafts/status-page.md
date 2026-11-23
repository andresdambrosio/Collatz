---
layout: page
title: Status
permalink: /status/
---

*Last updated: November 23, 2026.*

**The Collatz conjecture: <span class="tag open">open</span>.** In our repository the statement
`collatz_conjecture` is still marked `sorry`.

## Verified in Lean

Each row is checked by the Lean kernel with only the standard axioms
(`lake env lean scripts/Axioms.lean`).

| What | Lean name | Origin |
|---|---|---|
| Collatz ⇔ (no nontrivial cycles) ∧ (no divergent orbits) | `collatz_iff` | folklore |
| Collatz ⇔ termination of an 11-rule string rewriting system 𝒯, on canonical words and on all words | `collatz_iff_terminates`, `collatz_iff_terminatesAll` | Yolcu–Aaronson–Heule (2021), Thm 3.17 and Lemma 3.16 |
| Each of the 11 subsystems 𝒯 ∖ {ρ} terminates (their certificates, re-checked) | `SRS.termIn_without` | Yolcu–Aaronson–Heule |
| The Farkas variant converges (with a gap in the original argument fixed) | `farkas_convergent` | Yolcu–Aaronson–Heule, §4.2 |
| In the "3x−1" and "3x−3" neighbors of 𝒯, no rule can be removed | `SRS.Neighbor.not_relSN_d1`, `not_relSN_d0` | this project |
| Every nontrivial cycle has at least **15 601** odd steps (unconditional) | `cycle_period_ge_15601` | this project (method: Terras sieve + Eliahou-type sandwich) |
| Assuming the computer verification up to 2⁷¹, every nontrivial cycle has at least 72 057 431 991 odd steps | `Collatz.hercher_lower_bound` | method of Hercher; hypothesis stated explicitly |
| Constraints on a hypothetical divergent orbit (density of odd steps, aperiodicity) | see `Collatz/Forge/` | CollatzForge |

## Known from the literature (not checked here)

- <span class="tag lit">literature</span> Verified for every starting value below 2⁷¹ (Barina, 2025).
- <span class="tag lit">literature</span> Almost all orbits attain almost bounded values (Tao, 2019/2022).
- <span class="tag lit">literature</span> No nontrivial cycle has 91 or fewer local minima
  ("m-cycles", Hercher 2023, building on Steiner and Simons–de Weger).
- <span class="tag lit">literature</span> Natural and arctic matrix interpretations alone cannot remove
  any rule of 𝒯 (Nashida, 2026, verified in Lean in his own repository).

## Where every attempt stops

<span class="tag heur">heuristic</span> Our idea lab (five rounds, see the posts) and the literature
agree: every known method proves things about *almost all* numbers or about *short* cycles. What is
missing is always a statement about **one specific orbit**. Nobody knows how to prove such statements,
for Collatz or for smaller relatives of it (like Erdős' question on the base-3 digits of powers of 2).
