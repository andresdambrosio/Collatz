---
layout: post
title: "Hello, Collatz: an honest attempt, checked by a machine"
date: 2026-11-23 06:00:00 -0300
tldr: "We are attacking the Collatz conjecture in the open. Every result is checked by the Lean proof assistant, every claim is labeled, and every failure is published."
---

Pick a positive integer. If it is even, halve it. If it is odd, triple it and add one. Repeat.

Starting from 7:

$$7 \to 22 \to 11 \to 34 \to 17 \to 52 \to 26 \to 13 \to 40 \to 20 \to 10 \to 5 \to 16 \to 8 \to 4 \to 2 \to 1.$$

The **Collatz conjecture** says that, whatever number you start from, you always end at 1.
It is one of the simplest-sounding open problems in mathematics. Paul Erdős reportedly said that
"mathematics may not be ready for such problems". It has been checked by computer for every starting
value below $$2^{71}$$ <span class="tag lit">literature</span>, and Terence Tao proved in 2019 that
*almost all* orbits reach *almost* bounded values <span class="tag lit">literature</span>. Nobody knows
how to prove it for *every* number <span class="tag open">open</span>.

## Why now, and why like this

In October and November 2026, AI systems were involved in two announcements about the Riemann
hypothesis: a proof of a weaker "quasi-Riemann" statement, and a claimed proof of the full hypothesis
delivered as a library for the Lean proof assistant (not yet independently verified when this was
written). Whatever happens with those claims, they show a way of working: let a machine do a lot of
the heavy lifting, and let **another** machine, a proof checker, decide what is true.

That is what this project does for Collatz, at a much smaller scale. All the mathematics lives in a
public repository written in [Lean 4](https://lean-lang.org) with
[Mathlib](https://github.com/leanprover-community/mathlib4). Lean's kernel is a small program that
checks every step of every proof. If it accepts a theorem, the theorem follows from the axioms,
no matter who (or what) wrote the proof.

## What we have, and what we don't

We **don't** have a proof of the Collatz conjecture. In the repository the statement is still marked
`sorry`, Lean's word for "not proved yet", and the [status page]({{ '/status/' | relative_url }}) will
say so until that changes.

What we do have, all <span class="tag verified">verified in Lean</span>:

- the reduction of Collatz to "no cycles" plus "no divergent orbits";
- a complete check of a beautiful reformulation by Yolcu, Aaronson and Heule: Collatz is equivalent to
  the termination of a small *string rewriting system* (the next post explains it);
- a new, kernel-checked bound: **every nontrivial cycle would need at least 15 601 odd steps**;
- and a documented "idea lab" where five rounds of attempts are written down together with the exact
  reason each one stops.

## How to read this blog

Each mathematical claim carries a label: <span class="tag verified">verified in Lean</span>,
<span class="tag lit">literature</span>, <span class="tag heur">heuristic</span>, or
<span class="tag open">open</span>. The [rules]({{ '/rules/' | relative_url }}) explain them. The
repository is open, and contributions are welcome under the same rules.

The project is a collaboration between me (Andrés) and Claude, an AI assistant by Anthropic, which
writes much of the Lean and the analysis. I'm hoping we get somewhere new. If we do, Lean will be the
first to know.
