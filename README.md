# Collatz in Lean

An open, honest attempt at the **Collatz conjecture**, with every claim checked by the
[Lean 4](https://lean-lang.org) proof assistant.

**Blog (progress, explained):** https://andresdambrosio.github.io/Collatz/

> **Status: the Collatz conjecture is open, and it is still open here.**
> `collatz_conjecture` in `Collatz/Main.lean` is marked `sorry`. Everything listed as
> *proved* below is a reformulation, a partial result, or a barrier: none of it is a proof.

## What is the Collatz conjecture?

Take a positive integer. If it is even, halve it; if it is odd, triple it and add one. Repeat.
The conjecture says you always reach 1. It has been checked for every number below 2⁷¹, and
Terence Tao proved that *almost all* orbits get *almost* bounded, but no one knows how to prove
it for *every* number.

## What is verified here

Every theorem below compiles with `lake build`, and `#print axioms` shows only Lean's three
standard axioms (`propext`, `Classical.choice`, `Quot.sound`). Run
`lake env lean scripts/Axioms.lean` to check.

| Result | Lean name | File |
|---|---|---|
| Collatz ⇔ no nontrivial cycles ∧ no divergent orbits | `collatz_iff` | `Collatz/Reductions.lean` |
| Collatz ⇔ termination of the 11-rule string rewriting system 𝒯 of Yolcu–Aaronson–Heule, on canonical words and on **all** words (their Thm 3.17 and Lemma 3.16) | `collatz_iff_terminates`, `collatz_iff_terminatesAll` | `Collatz/Rewriting.lean`, `Collatz/Rewriting/AllWords.lean` |
| Their termination certificates for the 11 subsystems 𝒯 ∖ {ρ} and for the Farkas variant, re-checked (we found and fixed a gap in their §4.2 argument) | `SRS.termIn_without`, `farkas_convergent` | `Collatz/Rewriting/` |
| "Neighbor" systems (3x−1, 3x−3) where no rule can be removed: a filter against certificate techniques | `SRS.Neighbor.not_relSN_d1`, `not_relSN_d0` | `Collatz/Rewriting/Neighbors.lean` |
| **Every nontrivial cycle has at least 15 601 odd steps**: unconditional and checked entirely by the kernel (previously 2 301). The method is Eliahou's (1993); the literature has far larger bounds based on computer verifications that are not formally checked | `cycle_period_ge_15601` | `Collatz/CycleBound/` |
| Library from CollatzForge: Terras' lemma, cycle equation, constraints on a hypothetical divergent orbit | see `Collatz/Forge/` | `Collatz/Forge/` |

What is **not** here: a proof of the conjecture, or of either half of it. The idea lab
(`Ideas/LAB.md`) documents five rounds of attempts and why each one stops where it does.

## Building

```bash
lake exe cache get   # Mathlib cache
lake build
```

A build from scratch takes about **35–40 minutes** on a laptop. Most of it is kernel
computation (`decide +kernel`) for the cycle bound. **Memory:** each block of that computation
uses about 0.65 GB on top of Mathlib. The files are chained so that `lake` compiles at most two at
once; do not enlarge the blocks or break the chains (`scripts/gen_cycle_blocks.py`).

## Layout

- `Collatz/` — Lean sources (see `CLAUDE.md` for a file-by-file map)
- `scripts/` — Python checks and generators (each Lean computation is cross-checked numerically)
- `Ideas/` — one file per idea, including failures and their exact cause
- `docs/` — prior-art notes
- `site/` — the blog (GitHub Pages)
- `PLAN.md` — the work plan

## Contributing

Contributions are welcome. Please read [CONTRIBUTING.md](CONTRIBUTING.md) first. The short version:
nothing counts until Lean accepts it, and nothing is called "proved" unless it really is.

## License and credits

Apache-2.0 (see [LICENSE](LICENSE)). Third-party material and credits are listed in [NOTICE](NOTICE).
The termination certificates are by Yolcu, Aaronson and Heule.
