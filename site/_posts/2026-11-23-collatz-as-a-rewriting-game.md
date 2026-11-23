---
layout: post
title: "Collatz as a game of rewriting words, checked in Lean"
date: 2026-11-23 10:00:00 -0300
tldr: "Yolcu, Aaronson and Heule turned Collatz into a question about 11 rules that rewrite short words. We checked their equivalence, their computer-found certificates, and found (and fixed) a small gap along the way."
---

In 2021, Emre Yolcu, Scott Aaronson and Marijn Heule published a lovely reformulation of the Collatz
conjecture ([arXiv:2105.14697](https://arxiv.org/abs/2105.14697)). It turns the problem into a game
with words, and it is the reformulation we checked first in Lean.

## Numbers as words

Write a number as a word over seven letters: two **binary** digits `f` (zero) and `t` (one), three
**ternary** digits `0`, `1`, `2`, and two end markers `▷` and `◁`. Read the word from left to right,
starting from the value 1 at `▷`:

- `f` doubles: $$x \mapsto 2x$$;
- `t` doubles and adds one: $$x \mapsto 2x+1$$;
- a ternary digit `d` triples and adds `d`: $$x \mapsto 3x+d$$.

So `▷t◁` is 3 (from 1, double and add one) and `▷ft◁` is 5 (1 → 2 → 5). Mixing bases means a number
has many spellings; that is the point.

## Eleven rules

The game has 11 rules. You may apply any of them anywhere in the word:

| Rule | What it does to the value |
|---|---|
| `f◁ → ◁` | halves an even number |
| `t◁ → 2◁` | sends an odd $$2y+1$$ to $$3y+2 = \frac{3(2y+1)+1}{2}$$ |
| `f0 → 0f`, `f1 → 0t`, `f2 → 1f`, `t0 → 1t`, `t1 → 2f`, `t2 → 2t` | nothing: they swap a binary digit past a ternary one |
| `▷0 → ▷t`, `▷1 → ▷ff`, `▷2 → ▷ft` | nothing: they rewrite the leading ternary digit in binary |

The first two rules are the (accelerated) Collatz map: halve if even, $$(3n+1)/2$$ if odd. The other
nine never change the value; they only move ternary digits leftward until they "dissolve" into binary at
the front. Here is 3 being rewritten all the way down:

```
▷t◁ → ▷2◁ → ▷ft◁ → ▷f2◁ → ▷1f◁ → ▷fff◁ → ▷ff◁ → ▷f◁ → ▷◁
 3     5     5      8      8      8       4      2     1
```

## The theorem

**Collatz is true if and only if this game always ends**, whatever word you start from and whatever
rules you choose to apply (in rewriting language: the system *terminates*). Among the words of the form
`▷w◁`, the value 1 (`▷◁`) is the only one where no rule applies; every other one always has a move.

<span class="tag verified">verified in Lean</span> We formalized both versions of this:

- `collatz_iff_terminates`: Collatz ⇔ termination on the "canonical" words `▷w◁`;
- `collatz_iff_terminatesAll`: Collatz ⇔ termination on **all** words over the seven letters, with
  markers anywhere and in any number (the paper's Lemma 3.16). Our proof differs from the paper's: we cut
  every word at its markers, show each piece behaves independently, and close the easy pieces with simple
  counting arguments.

## Why bother? Certificates

Termination of rewriting systems is something computers can sometimes *prove*, by finding a
"certificate": a way to assign matrices to letters so that every rule makes a certain quantity go down.
That is why this reformulation is exciting. It turns Collatz into the kind of problem automated tools
attack.

Yolcu, Aaronson and Heule found such certificates for every **subsystem** obtained by deleting one of
the 11 rules (each of those terminates) and for a variant due to Farkas. Their certificates had never been
checked in a proof assistant, as far as we could find.

<span class="tag verified">verified in Lean</span> We wrote a verifier for natural and arctic matrix
interpretations in Lean and re-checked all of them (`SRS.termIn_without`, `farkas_convergent`). While doing
so we found a small gap in the paper's Farkas argument (§4.2). The "rightmost" rewriting strategy it relies
on gets stuck on three short words. The conclusion still holds; Lean needed an extra invariant and a finite
check to get there.

## The catch

Removing a rule makes the problem much easier. The real prize is a certificate for the **full** system,
and that would be a proof of Collatz. In 2026, Hiroyuki Nashida proved (also in Lean) that the matrix
techniques that worked for the subsystems can **never** remove even one rule of the full system
<span class="tag lit">literature</span>. We added our own small filter: change the rule `t◁ → 2◁` to
`t◁ → 1◁` and the game simulates $$3x-1$$, which has cycles. We checked in Lean that in that "neighbor"
system no rule can be removed at all (`SRS.Neighbor.not_relSN_d1`). Any certificate for Collatz must see
the difference between the digit 2 and the digit 1 in that single rule.

Later posts explain why every attempt in this direction (including ours) stops where it does.
