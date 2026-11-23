---
layout: page
title: The rules of this project
permalink: /rules/
ref: rules
---

This is my project ([Andrés D'Ambrosio](https://x.com/andresdambrosio)). The goal is to prove the
Collatz conjecture, and to share everything along the way. The conjecture attracts a lot of "proofs";
this project wants to be the opposite of that: slow, checkable, and honest about what it has and has not
done. These are the rules.

## 1. Lean is the judge

A result counts only when the [Lean](https://lean-lang.org) proof assistant accepts it. Concretely:
the whole project builds with `lake build`, and `#print axioms` for the theorem shows only Lean's three
standard axioms (`propext`, `Classical.choice`, `Quot.sound`). No `sorry`, no new axioms, no hidden
assumptions. Anyone can re-run this check: it is one command in the
[repository](https://github.com/andresdambrosio/Collatz).

## 2. Every claim wears a label

- <span class="tag verified">verified in Lean</span>: checked by the Lean kernel in the repository,
  with the name of the theorem.
- <span class="tag lit">literature</span>: proved in a published paper or preprint, not (yet) checked
  here. I say who proved it.
- <span class="tag heur">heuristic</span>: a plausibility argument, a computation, or a probabilistic
  model. Useful, not a proof.
- <span class="tag open">open</span>: nobody knows.

## 3. Failures are published

Most ideas fail. When one does, I write down exactly why, in the
[`Ideas/`](https://github.com/andresdambrosio/Collatz/tree/main/Ideas) folder and here. A precise failure
is information; a vague success is noise.

## 4. Credit and prior art come first

Before calling anything new, I search the literature and say what I found. Much of what is verified in
the repository is a *formal check of published mathematics*, and the posts say so.

## 5. How the work is done

I work with an AI assistant (Claude, by Anthropic), which writes much of the Lean code and the analysis.
I set the direction and decide what gets published. That is exactly why rule 1 exists: Lean does not care
who wrote a proof.

## 6. The conjecture is open until Lean says otherwise

Until `collatz_conjecture` in
[`Collatz/Main.lean`](https://github.com/andresdambrosio/Collatz/blob/main/Collatz/Main.lean) compiles
without `sorry` and passes rule 1, the Collatz conjecture is open, here as everywhere.

## 7. Anyone can contribute

The repository is open (Apache-2.0). Ideas, corrections, and Lean proofs are welcome; see
[CONTRIBUTING.md](https://github.com/andresdambrosio/Collatz/blob/main/CONTRIBUTING.md).
