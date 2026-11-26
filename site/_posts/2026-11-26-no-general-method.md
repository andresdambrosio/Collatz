---
layout: post
title: "No general method: Conway and Kurtz–Simon, checked in Lean"
date: 2026-11-26 09:00:00 -0300
ref: undecidable
tldr: "Change the rules of Collatz slightly, and the question 'does every number reach 1?' becomes undecidable. No algorithm can answer it for all such rules. This is a theorem of Conway (1972) and Kurtz–Simon (2007), now fully checked by Lean. It does not say Collatz is undecidable. It says a proof has to use something specific about 3n+1."
---

*Fourth post. The [first]({{ site.baseurl }}/2026/11/23/hello-collatz/) laid out the problem and the plan.
The [second]({{ site.baseurl }}/2026/11/24/collatz-as-a-rewriting-game/) checked a reformulation of the whole
conjecture, and the [third]({{ site.baseurl }}/2026/11/25/cycles-need-15601-odd-steps/) a bound on cycles. That one
ended by saying that what we need now is an idea. Before looking for one, it helps to know what a winning idea
**cannot** look like. That is what this post is about.*

## The family

Collatz uses one rule for even numbers and another for odd ones. Generalize: pick a modulus $$D$$, and for each
remainder $$j$$ modulo $$D$$ pick an affine rule $$n \mapsto a_j n + b_j$$, with rational coefficients chosen so
that the result is always a whole number. Collatz is the case $$D = 2$$, with $$n/2$$ and $$3n+1$$.

Every map in this family raises the same question: **does every positive number eventually reach 1?** For
$$3n+1$$ nobody knows. Could there be a general procedure that takes the table of rules and answers yes or no?

## Conway (1972): no

<span class="tag verified">verified in Lean</span> There is **one fixed map** of the form
$$n \mapsto a_{n \bmod D} \cdot n$$ for which no algorithm can decide, given $$m$$, whether the orbit of
$$2^m$$ ever hits a power of 2 again. The same holds for "ever hits 1"
([`conway_undecidable_fixed`](https://github.com/andresdambrosio/Collatz/blob/main/Collatz/Conway.lean)). As a
consequence, no algorithm solves the problem when the map is part of the input
(`conway_undecidable`, `conway_undecidable_one`, same file).

The reason is that these maps can **run programs**. The chain we checked, link by link:

1. **The halting problem.** No algorithm decides whether a program stops. This was already in Mathlib
   ([`Computability/Halting.lean`](https://github.com/leanprover-community/mathlib4/blob/master/Mathlib/Computability/Halting.lean)).
2. **Programs → register machines.** Every computable function becomes a program on registers that can only
   add 1, subtract 1, and loop while a register is nonzero
   ([`Conway/Compile.lean`](https://github.com/andresdambrosio/Collatz/blob/main/Collatz/Conway/Compile.lean),
   [`Conway/Minsky.lean`](https://github.com/andresdambrosio/Collatz/blob/main/Collatz/Conway/Minsky.lean)).
3. **Register machines → fractions.** This is Conway's trick, later called FRACTRAN. Store all registers in
   **one number** as prime exponents, $$2^{r_0}\, 3^{r_1}\, 5^{r_2} \cdots$$, plus one more prime for the
   machine's current state. Each instruction becomes a fraction. For example, multiplying by $$3 \cdot 11 / 7$$
   means "in state 7, add 1 to the register of 3 and move to state 11". You can only divide by a prime if it
   is there, which is exactly the test "is this register nonzero?"
   ([`Conway/Fractran.lean`](https://github.com/andresdambrosio/Collatz/blob/main/Collatz/Conway/Fractran.lean)).
4. **Fractions → the family.** Which fraction applies depends only on $$n$$ modulo the product of the
   denominators. That is a map of the form above.

At the end, the orbit of $$2^m$$ reaches a power of 2 exactly when program number $$m$$ halts. An algorithm for
the first question would solve the second.

## Kurtz and Simon (2007): "every number" is even harder

Conway's theorem is about **one starting number** at a time. Collatz asks about **all** of them. Kurtz and Simon
proved that for affine maps (with a $$+b_j$$, like $$3n+1$$), "every orbit reaches 1" is as hard as "this program
halts on **every** input", which is one level up in the arithmetical hierarchy ($$\Pi_2$$).

<span class="tag verified">verified in Lean</span> Their Theorem 1, as stated: there is a computable translation
from programs to affine maps such that **the program halts on every input if and only if every orbit of its
map reaches 1**
([`allReachOne_iff_total`](https://github.com/andresdambrosio/Collatz/blob/main/Collatz/KurtzSimon.lean)).
Consequently, the set of affine maps where every orbit reaches 1 is not semi-decidable, and neither is its
complement (`allReachOne_not_re`, `allReachOne_not_core`).

<span class="tag lit">literature</span> What we did not formalize: the definition of $$\Pi_2$$ itself and the
fact that totality is $$\Pi_2$$-complete. Mathlib does not have the arithmetical hierarchy yet.

The hard part, compared to Conway, is that now **every** number matters, not just the tidy ones that encode a
computation. A random $$n$$ is garbage: two machine states at once, no state at all, absurd register values. Three
ideas tame it:

1. **Garbage travels unchanged, then wears out.** Write $$n$$ as (machine primes) × $$u$$, where $$u$$ has no
   machine primes. The fractions only look at machine primes, so $$u$$ rides along. When no machine prime is left,
   a fallback affine rule $$n \mapsto (n+1)/2$$ strictly shrinks the number, so the garbage eventually runs out
   ([`Conway/Affine.lean`](https://github.com/andresdambrosio/Collatz/blob/main/Collatz/Conway/Affine.lean)).
2. **Programs that stop from anywhere.** Broken configurations get cleaned up, but what is left can be the
   machine in the middle of a computation, with nonsense in its registers. So the program must halt from
   **every** configuration. We guarantee that by building it only from bounded `for` loops, which always finish
   even when started halfway
   ([`Conway/Mortal.lean`](https://github.com/andresdambrosio/Collatz/blob/main/Collatz/Conway/Mortal.lean)).
3. **An outer loop that repairs itself.** The single unbounded loop is
   `while F(m, x) ≠ 0: x := x + 1`. Each round wipes the registers and reloads $$m$$ from the table, not
   from a register that garbage could corrupt. Started in the middle, at most the first round is nonsense, and
   from then on everything is correct
   ([`Conway/Outer.lean`](https://github.com/andresdambrosio/Collatz/blob/main/Collatz/Conway/Outer.lean)).

## What is ours and what is not

- The theorems are Conway's and Kurtz–Simon's. Ours is the **formal verification**. Everything compiles
  with `lake build`, and `#print axioms` shows only Lean's three standard axioms: no `sorry`, no
  `native_decide`.
- The central idea of Kurtz–Simon is theirs: turn a machine into one that halts from *any* configuration, with
  a bounded inner computation that validates each step of the outer one. Our outer loop is a variant of theirs.
- <span class="tag lit">literature</span> Kurtz–Simon is a conference paper, and Lagarias's annotated
  bibliography notes that it gives no detailed proofs. The draft we read has an empty Section 3. So the
  arithmetic garbage cleanup above is our own construction. It may well differ from what the authors had in mind.
- We did not find an earlier formalization of Kurtz–Simon in any proof assistant. FRACTRAN's undecidability
  was already formalized in Coq by Larchey-Wendling and Forster, as a step toward Hilbert's tenth problem.

## What this does and does not say

It does **not** say that Collatz is undecidable. The theorem is about the family. A single member, like
$$3n+1$$, can still have a proof that uses its particular properties.

What it does say is that such a proof **cannot be a general method**: anything that only uses "affine on residue
classes, and the numbers shrink on average" would also apply to maps where the question has no algorithmic
answer. A proof of Collatz has to use something about $$3$$ and $$2$$ specifically. That is the filter every idea
in our lab now has to pass.

## References

- J. H. Conway, "Unpredictable iterations", *Proceedings of the 1972 Number Theory Conference*, University of
  Colorado, Boulder (1972), 49–52.
- J. H. Conway, "FRACTRAN: A simple universal programming language for arithmetic", in *Open Problems in
  Communication and Computation*, Springer (1987), 4–26.
  [doi:10.1007/978-1-4612-4808-8_2](https://doi.org/10.1007/978-1-4612-4808-8_2)
- S. A. Kurtz and J. Simon, "The undecidability of the generalized Collatz problem", *Theory and Applications
  of Models of Computation (TAMC 2007)*, LNCS 4484 (2007), 542–553.
  [doi:10.1007/978-3-540-72504-6_49](https://doi.org/10.1007/978-3-540-72504-6_49)
- J. C. Lagarias, "The 3x+1 problem: an annotated bibliography, II (2000–2009)".
  [arXiv:math/0608208](https://arxiv.org/abs/math/0608208)
- D. Larchey-Wendling and Y. Forster, "Hilbert's tenth problem in Coq", *FSCD 2019*, LIPIcs 131 (2019), 27:1–27:20.
  [doi:10.4230/LIPIcs.FSCD.2019.27](https://doi.org/10.4230/LIPIcs.FSCD.2019.27)
