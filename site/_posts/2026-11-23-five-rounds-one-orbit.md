---
layout: post
title: "Five rounds in the idea lab: every road ends at a single orbit"
date: 2026-11-23 12:00:00 -0300
tldr: "We ran a disciplined 'idea lab' aimed at the full conjecture: generate ideas, kill them fast, write down why. Five rounds in, every road ends at the same wall: proving something about one specific orbit, not almost all of them."
---

The previous posts were about results we could check. This one is about trying to go further, and
about what happened. In short: no breakthrough, but a very clear map of where the wall is.

## The protocol

Inspired by the recent AI-assisted work on the Riemann hypothesis, where one key result "didn't need any
new concepts" and instead combined an under-used tool from the literature, we set up a lab with strict
rules:

1. An idea must explain how it would rule out **both** cycles and divergent orbits.
2. It must pass a **barrier filter**. It must fail for $$5n+1$$ (which really has cycles and, apparently,
   divergent orbits). It must use that $$n > 0$$ (negative numbers have cycles under $$3n+1$$). And it
   must go beyond arguments modulo $$2^k$$ and beyond "almost all".
3. Search the literature before investing.
4. Try to refute it numerically.
5. Only then, Lean.
6. Write down the exact cause of death.

Everything is in [`Ideas/LAB.md`](https://github.com/andresdambrosio/Collatz/blob/main/Ideas/LAB.md).

## Two facts every proof must use

<span class="tag verified">verified in Lean</span> (in our library) A divergent orbit would have to be
**atypical**: in the long run it can divide by 2 at most about $$\log_2 3 \approx 1.585$$ times per odd
step on average (precisely: at most $$\log_2 3 + \varepsilon$$ for every $$\varepsilon > 0$$, from some
point on), while a typical orbit divides by 2 twice. (For $$5n+1$$ it's the opposite: typical orbits grow.) And, as
in the [previous post]({{ '/2026/11/23/cycles-need-15601-odd-steps/' | relative_url }}), a cycle needs
$$A/k$$ to be an extraordinarily good approximation of $$\log_2 3$$.

## What we tried

**Round 1: triage.** Six candidate strategies: upgrading Tao's "almost all" to "all" via the tree
of preimages; a potential function computed by a finite automaton; the 2-adic conjugacy of Lagarias and
Bernstein; the Steiner/Simons–de Weger method for cycles; rigidity theorems in the style of Furstenberg's
$$\times 2 \times 3$$; and "mining" the literature for an under-used ingredient.

**Round 2: mining the literature.** We read Tao's 2011 analysis of the cycle problem, recent work on
the joint behavior of digits in bases 2 and 3 (Drmota–Spiegelhofer 2025), recent $$\times 2 \times 3$$
results, and a 233-page human–AI exploration from 2026 (Chang, [arXiv:2603.11066](https://arxiv.org/abs/2603.11066))
that tried 29 approaches. Four of our six round-1 ideas were already on their list of failures, which
saved us weeks. All strong tools near the problem are **distributional**: they speak about almost all
numbers. Their verdict, and ours: the missing step is always **pointwise**.

**Round 3: smarter certificates.** Back to the rewriting game: we labeled each letter with the value of
the word to its left modulo $$m$$ (a classical technique, outside the scope of Nashida's barrier) and
searched for certificates. We found none in the sizes we tried <span class="tag heur">heuristic</span>.
More importantly, we understood why: removing even one *labeled* rule would mean "along any infinite
game, this rule is used only finitely often at this residue". For a divergent orbit, which would visit
every residue again and again, that is as hard as the conjecture itself.

**Round 4: a "discrete logarithm obstruction" for cycles.** An open question from Chang's paper. On
inspection it covers only cycles whose pattern of halvings has two or three constant blocks, and only up
to finite lengths. That is weaker than what is already proved: no cycle has 91 or fewer local minima,
for any length (Hercher 2023) <span class="tag lit">literature</span>. The general case is the whole
cycle problem.

**Round 5: a toy problem.** Erdős asked whether every power of 2 except 1, 4 and 256 has a digit 2 in
base 3. It is a smaller cousin of Collatz (powers of 2 versus powers of 3), and it is open, even in the
weak form "finitely many exceptions". The natural way to improve the best known counting bound needs the
base-3 digits of the number $$\log_3 2$$ to be well distributed. That is a **normality** question about one
specific number, again out of reach.

## The wall

Every round, in its own language, ended at the same place:

| Where | What would be needed |
|---|---|
| Collatz, divergence | statistics of **one** Syracuse orbit |
| Collatz, cycles with many local minima | a Diophantine tool that works with many terms (Baker's theory doesn't) |
| Rewriting certificates | control of residues along **one** infinite derivation |
| Erdős' digits of $$2^n$$ | normality of **one** number, $$\log_3 2$$ |
| Furstenberg $$\times 2 \times 3$$ | behavior of **individual** orbits |

Mathematics today is very good at "almost all" and very bad at "this one". As far as we can tell, that
gap *is* the Collatz problem. We didn't find a way across. Nobody has.

## What now

Two things. First, a precise **atlas of the frontier in Lean**: every open statement around Collatz,
written exactly, with the implications between them checked by the kernel. Nothing like that exists
today. Public catalogs of formalized conjectures contain only the bare Collatz statement. Second, keep
the lab open. If you have an idea that passes the filter, [open an issue](https://github.com/andresdambrosio/Collatz/issues).
