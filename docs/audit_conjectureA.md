# Independent audit: the Applegate–Lagarias Conjecture A in Lean (El Jaouhari, 2026)

Date: 2026-11-24. Audited repository: [github.com/neljaouh/ConjectureA](https://github.com/neljaouh/ConjectureA),
commit `afe7f87` (paper: Zenodo [doi:10.5281/zenodo.23025918](https://doi.org/10.5281/zenodo.23025918)).
Run by Andrés D'Ambrosio on a 16 GB macOS machine.

## What is claimed

- **Conjecture A** (Applegate–Lagarias, *Math. Comp.* 64, 1995): for every `a ∈ ℤ` with `3 ∤ a` there is `c_a > 0`
  with `π_a(x) ≥ c_a·x` for every real `x ≥ |a|`, where `π_a(x) = #{n ∈ ℤ : |n| ≤ x, ∃k, T^k(n) = a}` and `T` is the
  accelerated map (`x/2` on evens, `(3x+1)/2` on odds).
- As a corollary, the growth exponent conjecture (`log π_a(x) / log x → 1`).
- The single mathematical input is **M2** from ProofAtlas: positive lower density of the ordinary predecessors of every
  positive target not divisible by 3. That package is AI-assisted and not refereed. According to its README it is
  vendored unmodified.

## What we checked

1. **Dependencies.** `lakefile.toml` is declarative and runs no code. Lean is `v4.30.0-rc2` and Mathlib is `5450b53e`,
   and every dependency comes from the official leanprover-community repositories (`lake-manifest.json`).
2. **Cold build from source** of all 464 modules, the repository's own and the vendored ones, including all of M2.
   Mathlib came from the official cache. No errors. The lowest free memory during the build was 26%.
3. **Search for escape hatches** across the whole source tree: `sorry`, `axiom` (it appears only in comments),
   `native_decide`, `implemented_by`, `@[extern]`, `unsafe`, `opaque`, `debug.skipKernelTC`,
   `ofReduceBool`/`trustCompiler`, custom `elab`/`macro`/`syntax`, `maxHeartbeats 0`. **None found.**
4. **Our own restatement.** In a separate file, we defined `T` and `π_a` from scratch, with sanity checks
   `T 7 = 11`, `T (-5) = -7` and `T 10 = 5`, and proved Conjecture A with `ALConjectureAZ.conjectureA_AL`.
   `#print axioms` gives **`[propext, Classical.choice, Quot.sound]`**, for the whole dependency chain including M2.
5. **Fresh-kernel replay.** `leanchecker --fresh ConjectureAZ` and `leanchecker --fresh GrowthExponent` both
   **exit 0** (about 6 minutes each).
6. **Statement fidelity.** We compared against the text of Applegate–Lagarias, *Density Bounds for the 3x+1 Problem I.
   Tree-Search Method* (AT&T Bell Laboratories preprint dated December 15, 1993; the published version is *Math. Comp.*
   64 (1995), 411–426, [doi:10.1090/S0025-5718-1995-1270612-0](https://doi.org/10.1090/S0025-5718-1995-1270612-0)). In the preprint, (1.1) defines `T : ℤ → ℤ` as `(3x+1)/2` on odd `x` and `x/2` on even `x`;
   (1.2) defines `π_a(x) = #{n : |n| ≤ x and some T^(k)(n) = a, k ≥ 0}`; and Conjecture A reads "For each
   `a ≢ 0 (mod 3)`, there is a positive constant `c_a` such that `π_a(x) ≥ c_a x` for all `x ≥ |a|`." (The absolute-value
   bars are drawn with Symbol-font glyphs, so plain text extraction drops them; we read them from the PDF content
   stream.) **The Lean statement matches exactly.** The same definition of `π_a(x)` appears in Lagarias's summary of the
   published paper (annotated bibliography, arXiv:math/0309224, entry Applegate–Lagarias 1995a).
7. **Integrity of the vendored sources.** The public ProofAtlas source archive
   (`positive-density-log-time-collatz-v2.1-source.zip`) has the published SHA-256 (`23f5cac4…69c1f`). The **377**
   supporting files in the repository are byte-identical to the ones in that archive, and the **13** M2 Lean files match
   the hashes in M2's `source-manifest.json`. The only files that differ or are missing are configuration,
   documentation and assembly scripts (`lakefile.toml`, `lake-manifest.json`, `README.md`, `NOTICE`, scripts), plus 12
   modules the narrowed M2 does not use, which the successful build confirms.
8. **Independent kernel (nanoda).** We exported the two final theorems and their full dependency closure with
   [lean4export](https://github.com/leanprover/lean4export) (tag `v4.30.0-rc2`, NDJSON format 3.1.0). The export has
   44,663 declarations (299 MB), including M2 and the parts of Mathlib that are used. We checked it with
   [nanoda_lib](https://github.com/ammkrn/nanoda_lib) (Rust, commit `0da9f98`). Only `propext`, `Classical.choice` and
   `Quot.sound` were permitted (not even `Lean.trustCompiler`), with the kernel's Nat/String extensions enabled.
   Result: **"Checked 44663 declarations with no errors"** (6 s, 0.6 GB). nanoda prints the checked statement fully
   unfolded: it is Conjecture A with `π_a(x) = #{n ∈ ℤ : |n| ≤ x, ∃k, syrZ^[k] n = a}` and `syrZ n` equal to `n/2` or
   `(3n+1)/2`.
   **Mutation test.** In one copy of the export we replaced the proof of `ALConjectureAZ.conjectureA_AL` with the proof
   of an unrelated theorem. In another copy we did the same to M2's central theorem
   (`generalTarget_predecessors_positive_lower_density`). nanoda rejected both (`assertion failed: self.def_eq(u, v)`),
   so it really does check those proofs.

## Conclusion

The development **verifies in Lean** the Applegate–Lagarias Conjecture A as stated, with no extra axioms. The proof
passes a complete fresh-kernel replay **and an independent kernel (nanoda, written in Rust)**. For it to be wrong, the
same bug would have to be present in Lean's kernel and in nanoda. (In 2026 there was a claimed Lean proof about Collatz
that exploited a Lean kernel bug, as recounted by L. Paulson on his blog, 30 July 2026.)

Not covered yet: we have not done a human reading of the mathematics of M2. (Statement fidelity was checked against
the 1993 preprint of Applegate–Lagarias; we have not seen the typeset *Math. Comp.* version.)

**A notable consequence.** Taking `a = 1`, a positive proportion of all positive integers reach 1, verified in Lean. M2
also implies, again verified, that if there is one counterexample then a positive proportion of integers are
counterexamples. So the Collatz conjecture is equivalent to the proportion of integers that reach 1 tending to 1
(`universal_reaches_one_of_arbitrarily_dense_convergence`). This does **not** prove the Collatz conjecture.

## Tools and versions

| Tool | Version |
|---|---|
| Lean / Lake | `v4.30.0-rc2` (commit `3dc1a088`) |
| Mathlib | `5450b53e` |
| leanchecker | bundled with the toolchain above |
| lean4export | tag `v4.30.0-rc2` (commit `12581a6`) |
| nanoda_lib | commit `0da9f98` (crate `0.4.32`), built with rustc 1.100.0 |
