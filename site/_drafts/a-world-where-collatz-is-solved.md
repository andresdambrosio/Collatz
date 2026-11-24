---
layout: post
title: "A world where Collatz is solved, and why the proof doesn't travel"
date: 2026-11-24 09:00:00 -0300
ref: solved-cousin
tldr: "There is a close cousin of the Collatz problem where the conjecture is proved: binary arithmetic without carries. We built a ladder of worlds from that cousin to the real integers, letting carries travel a little further at each step. All the difficulty already shows up at the first step, with carries that travel just two places. On the way, we checked in Lean that a 2011 claimed proof was circular."
---

The [lab post]({{ '/2026/11/23/five-rounds-one-orbit/' | relative_url }}) ended at a wall: every
approach we tried came down to proving something about one specific orbit. This week we tried a
different trick, an old one in mathematics: **move the problem to a world where it is easier, solve it
there, and come back.** It didn't work, but the way it failed taught us exactly where the difficulty lives.

## The rules in binary

In binary, the Collatz step is mechanical. Halving an even number deletes its final 0. And
$$3n + 1 = n + 2n + 1$$, where $$2n$$ is just $$n$$ shifted one place to the left. Here is $$3 \cdot 7 + 1$$:

```
    0111      (7)
  + 1110      (14 = 7 shifted)
  +    1
  -------
   10110      (22)
```

Column by column, right to left, every column overflows and passes a **carry** ("one to carry") to the
next column, and the last carry lands in a brand-new column at the top. The 3-digit number 7 became the
5-digit number 22. **Numbers can grow only because carries reach the top.**

## The cousin where Collatz is proved

Now take a world where $$1 + 1 = 0$$ and **nothing is carried**: each column is added on its own. The same
computation gives

```
    0111
  + 1110
  +    1
  -------
    1000      (column by column, no carries)
```

and halving gives `100`: still 3 digits. This always happens. Without carries, $$n + 2n$$ has exactly one
more digit than $$n$$, the result always ends in 0, and halving removes that digit. **The length never
grows.** A sequence that never grows can't escape to infinity, and with a check that there are no stray
cycles, the conjecture in this world is a theorem. <span class="tag lit">literature</span> This world is
the ring $$\mathbb{F}_2[x]$$ of polynomials with coefficients mod 2, with $$x$$ playing the role of 2 and
$$1 + x$$ the role of 3. Hicks, Mullen, Yucas and Zavislak proved in 2008 that every polynomial reaches 1
(as did Snapp and Tracy, independently). Monks observed in 2025 that this map is literally "$$3n+1$$ in
binary without carries".

## A ladder of worlds

So we asked: what happens in between? We built a family of worlds $$C_k$$ where a carry may travel **at
most $$k$$ columns** and then dies:

- $$C_0$$: carries die at birth. This is the solved polynomial world.
- $$C_2$$, $$C_4$$, …: carries travel a bit further.
- $$C_\infty$$: carries never die. This is the real Collatz problem.

Here is $$3 \cdot 5 + 1$$ in the real world and in $$C_2$$:

```
 real:   0101 + 1010 + 1 = 10000  (16)     the carry runs all the way to the top
 C_2:    0101 + 1010 + 1 = 01100  (12)     the same carry dies after two columns
```

The plan: prove $$C_2$$, then $$C_4$$, and see where the easy proof breaks.
(A first attempt, a ring where carries jump far instead of dying, sends every number to infinity. It
breaks the "multiply by 3, divide by 4" balance that makes Collatz plausible, so we dropped it.)

<span class="tag heur">heuristic</span> What the computer shows, with every starting value below 20 000:

- In no world $$C_k$$ did any orbit escape to infinity.
- Some worlds have **spurious cycles** that never reach 1. In $$C_2$$ the smallest is
  $$3 \to 5 \to 6 \to 3$$, and they keep appearing at larger sizes (we found cycles with up to 21
  binary digits). So in $$C_k$$ the right question is "does anything escape?", not "does everything reach 1?".
- The analogue of $$5n+1$$ escapes for $$k = 4, 6, 8$$ (the values we tested), as it does for real integers. The ladder passes the
  same sanity check that any Collatz argument must pass.

And here is the surprise. How often does an odd step make the number one digit longer?

| world | $$C_0$$ | $$C_2$$ | $$C_4$$ | $$C_8$$ | real Collatz |
|---|---|---|---|---|---|
| growth in an odd step | 0% | 48% | 55% | 58% | 58.5% |

(Measured on 4000-digit numbers. For real Collatz the exact value is $$\log_2(3/2) \approx 58.5\%$$, a
consequence of Benford's law for the leading digits.) **With carries that travel just two columns,
numbers already grow almost as often as in the real problem.** The first rung of the ladder is already
as steep as the whole ladder.

## Seen from below, all these worlds are the same

<span class="tag verified">verified in Lean</span> There is a structural reason. In every world
$$C_k$$, and in real Collatz too, each digit of $$n + 2n + 1$$ equals the matching digit of $$n$$, XOR
something that depends only on the digits *below* it. Rules of that shape can be undone column by column,
so if you look only at the last $$m$$ digits, the step is a reshuffling of all possible endings, for every
$$m$$ and for *any* carry rule
([`Collatz.Carries.out_injective_below`](https://github.com/andresdambrosio/Collatz/blob/main/Collatz/Carries.lean)).
<span class="tag lit">literature</span> Seen from the last digits, the
polynomial world, every $$C_k$$, and real Collatz behave **exactly alike**. In the language of the
field, they are all conjugate to the same shift on the 2-adic integers, as Monks shows for the polynomial
case. What tells them apart is only the **size** of the number: how it grows at the top.

That is why the polynomial proof can't climb the ladder. It rests on a single fact, "the length never
grows", and that fact fails the moment any carry can reach the top. It doesn't degrade gracefully. It
just stops being true.

## Hunting for an energy function

Engineers know the trick of a **Lyapunov function**: a quantity, like the energy of a damped system, that
never increases along the motion. If we found one for $$C_2$$ that never increases and is at least the
number of digits, no orbit could escape. In the polynomial world, the length itself works.

<span class="tag heur">heuristic</span> (These are exact computations, a linear program and a SAT solver,
but they are not checked in Lean.)

- **Local energies don't exist.** We searched for energies built from counts of short digit patterns,
  plus terms looking at the last and first digits. A linear program can find the best weights or prove
  that none exist. In the polynomial world it finds one immediately. For $$C_2$$ and for real Collatz,
  none exists. The reason, read off the program's dual, is a family of **sparse numbers** like
  `111010000010`: a block of ones at the top, a block at the bottom, and zeros in between. The bottom block
  decides which steps are odd. The top block grows on odd steps. An energy that only looks at small
  windows can't know that the even steps coming later will pay for that growth.
- **Global energies, built from products of matrices.** These see the whole number at once, and they are
  the tool behind the [rewriting approach]({{ '/2026/11/24/collatz-as-a-rewriting-game/' | relative_url }}).
  With a SAT solver, there are none with matrices up to $$3 \times 3$$. Larger searches are running.

## A detour: a 2011 proof that assumed its conclusion

There is another classic "change of world": Berg and Meinardus (1994) translated Collatz into a pair of
functional equations for holomorphic functions on the unit disk. <span class="tag lit">literature</span>
Collatz is true if and only if those equations have only the obvious two-dimensional space of solutions.
Unpacked, the solutions are exactly the functions that are constant along Collatz orbits. The analytic
condition adds nothing: an indicator series with coefficients 0 and 1 always converges in the disk. So
the translation is "the Collatz graph is connected", written as analysis.

In 2011 Gerhard Opfer announced a proof along this route. A month later he withdrew the claim, writing
that one step of his argument "has turned out to be incomplete". We wanted to know exactly why.
<span class="tag verified">verified in Lean</span> His key step is an "annihilation algorithm" on even
numbers. We formalized it exactly as written in his paper, checked that it reproduces his tables, and
proved that **one annihilation step is a run of the Collatz map** itself. So his Theorem 4.17 ("the
algorithm always ends at 8") is *equivalent* to the Collatz conjecture
([`Collatz.Opfer.theorem_4_17_iff_collatz`](https://github.com/andresdambrosio/Collatz/blob/main/Collatz/Opfer.lean)).
For example, his Table 4.8 (326 → 368 → 184 → … → 8) is the Collatz orbit of 163 (under the map
$$x \mapsto x/2$$ or $$(3x+1)/2$$), doubled, with each run of odd steps jumped over in one move. The tree argument he gave for Theorem 4.17 assumes what it sets out to prove. To be clear
on credit: Opfer found the problem himself, and we only pinpointed it formally.

## What we learned

Every translation we tried this week (polynomials, carry ladders, 2-adic numbers, complex analysis) either
looks exactly as hard as Collatz or turns trivial. What never makes the trip is the same thing every time:
**the interplay between the size of a number and its last digits.** The last digits decide what happens
(odd or even). The size decides whether the number escapes. No tool we know of controls both at once for
a single number. That is a sharper version of the wall from the last post, and it is what any real proof
will have to get past. <span class="tag open">open</span>

All code is in the repository: `scripts/carry_trunc.py`, `carry_potential*.py` and `carry_srs*.py`, and the
lab notes are in [`Ideas/acarreos.md`](https://github.com/andresdambrosio/Collatz/blob/main/Ideas/acarreos.md)
and [`Ideas/berg_meinardus.md`](https://github.com/andresdambrosio/Collatz/blob/main/Ideas/berg_meinardus.md).

## References

- K. Hicks, G. L. Mullen, J. L. Yucas, R. Zavislak, "A Polynomial Analogue of the 3n+1 Problem",
  *American Mathematical Monthly* 115 (2008), 615–622.
  [doi:10.1080/00029890.2008.11920572](https://doi.org/10.1080/00029890.2008.11920572)
- B. Snapp, M. Tracy, "The Collatz Problem and Analogues", *Journal of Integer Sequences* 11 (2008),
  Article 08.4.7. [cs.uwaterloo.ca/journals/JIS/VOL11/Snapp/snapp.html](https://cs.uwaterloo.ca/journals/JIS/VOL11/Snapp/snapp.html)
- K. G. Monks, "On q-analogs of the 3x+1 dynamical system" (2025).
  [arXiv:2508.10153](https://arxiv.org/abs/2508.10153)
- L. Berg, G. Meinardus, "Functional equations connected with the Collatz problem", *Results in
  Mathematics* 25 (1994), 1–12. [doi:10.1007/BF03323136](https://doi.org/10.1007/BF03323136)
- G. Opfer, "An analytic approach to the Collatz 3n+1 problem", Hamburger Beiträge zur Angewandten
  Mathematik 2011-09 (with the author's note of June 17, 2011).
  [preprint.math.uni-hamburg.de](https://preprint.math.uni-hamburg.de/public/papers/hbam/hbam2011-09.pdf)
- E. Yolcu, S. Aaronson, M. J. H. Heule, "An Automated Approach to the Collatz Conjecture",
  *Journal of Automated Reasoning* (2023). [arXiv:2105.14697](https://arxiv.org/abs/2105.14697)
