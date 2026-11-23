---
layout: post
title: "A Collatz cycle would need at least 15,601 odd steps"
date: 2026-11-23 08:00:00 -0300
tldr: "If some number ever came back to itself, that loop would need at least 15,601 odd steps. This bound is fully checked by Lean's kernel, with no unproved assumptions, up from 2,301. The trick: you don't need numbers to reach 1, only to dip below themselves."
---

There are only two ways the Collatz conjecture could fail: some orbit grows forever, or some orbit
**cycles**, coming back to its starting number without passing through 1. This post is about cycles.

## Why cycles must be long

Use the accelerated map: an odd $$n$$ goes to $$(3n+1)/2^a$$, where we divide by 2 as many times
($$a$$) as needed to get an odd number again. Suppose a cycle visits the odd numbers
$$n_1, \dots, n_k$$ and divides by 2 a total of $$A$$ times. Multiplying the steps around the loop, all
the $$n_i$$ cancel and we get

$$2^A = \prod_{i=1}^{k} \left(3 + \frac{1}{n_i}\right).$$

Two things follow. First, $$2^A > 3^k$$. Second, if every number in the cycle is at least $$M$$, then
$$2^A \le (3 + 1/M)^k$$. Taking logarithms:

$$0 < A - k\log_2 3 \le k \log_2\!\left(1 + \frac{1}{3M}\right) \approx \frac{k}{3M\ln 2}.$$

In words: $$A/k$$ must be an **extremely good** approximation of $$\log_2 3 = 1.58496\ldots$$ from above.
Rational approximations that good need large denominators. The continued fraction of $$\log_2 3$$ says
exactly how large. So the bigger $$M$$ is, the longer any cycle must be.

## Where M comes from

The classical way to get $$M$$: check by computer that every number below $$M$$ reaches 1. Then a
cycle can't contain such numbers. Our earlier Lean library did exactly this inside the kernel for
$$M = 600{,}001$$, which gave $$k \ge 2{,}301$$.

But "reaches 1" is more than we need. Look at the **smallest** number in a cycle: by definition, its
orbit never goes below it. So it is enough to check that every odd number $$1 < n < M$$ eventually
**dips below itself**. That is a much cheaper check, and it gets cheaper still with an old trick of
Terras: for most residue classes modulo $$2^{20}$$, the first 20 steps are the same for every number in
the class, and you can prove the dip for the whole class at once, symbolically.

| Step | Numbers |
|---|---|
| Odd residue classes mod $$2^{20}$$ | 524,288 |
| Classes that dip symbolically (for every number in the class) | 496,959 (94.8%) |
| Remaining numbers below $$M = 78 \cdot 2^{20} = 81{,}788{,}928$$, checked one by one | 2,131,661 |
| Longest wait before dipping | 376 steps |

With $$M = 81{,}788{,}928$$ the inequality above leaves no room for any $$k \le 15{,}600$$. The first
length it allows is $$k = 15{,}601$$, a denominator of a continued-fraction convergent of $$\log_2 3$$.

<span class="tag verified">verified in Lean</span> **Every nontrivial Collatz cycle has at least
15,601 odd steps** (`cycle_period_ge_15601`). Everything is computed inside Lean's kernel, with no
external solver, no `native_decide`, and no assumption.

## A lesson about memory

The first version of this computation froze my laptop, several times. Lean's kernel remembers every
intermediate result until it finishes a theorem, and we had asked it to check large blocks in 16 files
**in parallel**. Measured afterwards: about 3.4 GB per block, times 16, on a 16 GB machine. The final
version uses 2,048 small theorems (about 0.65 GB each), chained so that at most two files compile at
once. It takes about 30 minutes, once.

## Perspective

How good is 15,601? Honestly, modest, and the method is not ours: it is Eliahou's (1993), who with a
verification up to $$2^{40}$$ already proved that a cycle has length at least 17,087,915. Our script reproduces
that number exactly from $$M = 2^{40}$$. With the computer verification up to $$2^{71}$$ (which is not
checked in Lean), the same method gives about $$7 \times 10^{10}$$, and we have that as a Lean theorem
*with the verification as an explicit hypothesis* (`hercher_lower_bound`). The literature also rules
out cycles with up to 91 "local minima" for any length (Hercher, 2023) <span class="tag lit">literature</span>.

The real value is that this number is **checked end to end by a machine**. And it shows the limit of
the method: the bound grows roughly like $$\sqrt{M}$$. No amount of computation turns "very long" into
"impossible". That needs an idea, which is what the next post is about.
