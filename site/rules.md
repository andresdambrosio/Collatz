---
layout: page
title: The rules of this project
permalink: /rules/
---

The Collatz conjecture attracts a lot of "proofs". This project wants to be the opposite of that:
slow, checkable, and honest about what it has and has not done. These are the rules.

## 1. Lean is the judge

A result counts only when the [Lean](https://lean-lang.org) proof assistant accepts it. Concretely:
the whole project builds with `lake build`, and `#print axioms` for the theorem shows only Lean's three
standard axioms (`propext`, `Classical.choice`, `Quot.sound`). No `sorry`, no new axioms, no hidden
assumptions. Anyone can re-run this check: it is one command in the repository.

## 2. Every claim wears a label

- <span class="tag verified">verified in Lean</span>: checked by the Lean kernel in our repository,
  with a link to the theorem.
- <span class="tag lit">literature</span>: proved in a published paper or preprint, not (yet)
  checked here. We say who proved it.
- <span class="tag heur">heuristic</span>: a plausibility argument, a computation, or a probabilistic
  model. Useful, not a proof.
- <span class="tag open">open</span>: nobody knows.

## 3. Failures are published

Most ideas fail. When one does, we write down exactly why, in the
[`Ideas/`](https://github.com/andresdambrosio/Collatz/tree/main/Ideas) folder and here. A precise
failure is information; a vague success is noise.

## 4. Credit and prior art come first

Before calling anything new, we search the literature and say what we found. Most of what is verified
here is a *formal check of published mathematics*, and we say so.

## 5. How the work is done

This project is a collaboration between a human (Andrés D'Ambrosio) and an AI assistant
(Claude, by Anthropic). The AI writes much of the Lean code and the analysis; the human sets the
direction and decides what is published. That is exactly why rule 1 exists: Lean does not care who
wrote a proof.

## 6. The conjecture is open

Until `collatz_conjecture` in
[`Collatz/Main.lean`](https://github.com/andresdambrosio/Collatz/blob/main/Collatz/Main.lean) compiles
without `sorry` and passes rule 1, the Collatz conjecture is open, here as everywhere. We will never
write otherwise.
