# Contributing

Thanks for your interest! This project tries to make progress on the Collatz conjecture in the
open, with **Lean as the judge**. These rules keep it trustworthy.

## The rules

1. **Lean is the judge.** A result counts only if `lake build` succeeds and `#print axioms`
   shows only `propext`, `Classical.choice`, `Quot.sound` (plus a `native_decide` axiom if one
   is used, which must be stated). Never `sorryAx`. Add new theorems to `scripts/Axioms.lean`.
2. **Never overclaim.** The conjecture is open. Do not call anything "proved" if it uses `sorry`,
   `admit`, new `axiom`s, or hypotheses equivalent to the conjecture. Hypotheses from the literature
   (e.g. Baker's theorem, a computational verification) must be explicit arguments, with references.
3. **Compute before formalizing.** Test a candidate lemma numerically first (`scripts/`), and look
   for counterexamples before writing Lean.
4. **Pass the barrier filter** (see `PLAN.md`): Does the idea fail for 5n+1 (it must)? Does it use
   n > 0? Does it go beyond mod 2^k arguments and beyond "almost all"?
5. **Record failures.** A failed idea is useful: add a file to `Ideas/` (template:
   `Ideas/_PLANTILLA.md`) with the exact reason it fails.
6. **Credit prior art.** Before claiming something is new, search the literature and say what you
   found. Cite papers in docstrings.
7. **Mind the memory.** Heavy `decide +kernel` computations must be split into small blocks (measure
   one with `/usr/bin/time -l` first) and chained so they do not run in parallel.

## How to contribute

- **Open an issue** to propose an idea, report a gap, or point to literature. Ideas that pass the
  barrier filter are especially welcome.
- **Pull requests**: one topic per PR; include the axioms output for new theorems and the numerical
  check, if any. Generated files (`Collatz/CycleBound/`, `Collatz/Rewriting/Subsystems*.lean`,
  `FarkasCert.lean`) must be regenerated with their scripts, not edited by hand.
- **Blog posts** live in `site/_posts/`. They must be precise: every mathematical claim either links
  to a Lean theorem or is clearly labeled as literature, heuristic, or conjecture.

Most of the existing documentation inside `Collatz/`, `Ideas/` and `PLAN.md` is in Spanish;
contributions in English are welcome.
