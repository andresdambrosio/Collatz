---
layout: post
title: "Hello, Collatz: I'm going to try to prove it, in public"
date: 2026-11-23 06:00:00 -0300
ref: hello
tldr: "The Collatz conjecture is one of the simplest open problems in mathematics. My goal is to prove it, sharing everything along the way, with every result checked by the Lean proof assistant. Here is the problem, the plan, and the first results."
---

## The problem

Pick a positive integer. If it is even, halve it. If it is odd, triple it and add one. Repeat.

Starting from 7:

$$7 \to 22 \to 11 \to 34 \to 17 \to 52 \to 26 \to 13 \to 40 \to 20 \to 10 \to 5 \to 16 \to 8 \to 4 \to 2 \to 1.$$

Starting from 27, the journey takes 111 steps and climbs as high as 9,232 before falling back to 1.

The **Collatz conjecture** (1937) says that, whatever number you start from, you always end at 1.
Anyone can understand it in ten seconds; nobody has been able to prove it in almost ninety years. Paul
Erdős is often quoted as saying that "mathematics may not be ready for such problems".

What is known <span class="tag lit">literature</span>:

- It has been checked by computer for every starting number below $$2^{71}$$, about
  $$2.4 \times 10^{21}$$ (Barina, 2025).
- Terence Tao proved in 2019 that *almost all* starting numbers reach *almost* bounded values. It is the
  strongest result to date, and it still says nothing about *every* number.

And what is not: whether it holds for every number is <span class="tag open">open</span>.

## The goal

**My goal is to prove the Collatz conjecture**, and to share everything along the way: the progress, the
dead ends, and the reasons behind each one.

I know how that sounds. Many people have announced proofs of Collatz, and they have all been wrong. So
this project follows strict [rules]({{ '/rules/' | relative_url }}), and the first one is the important one:
**a machine decides what is true.**

Everything lives in a public repository written in [Lean 4](https://lean-lang.org), a proof assistant.
Lean's kernel is a small program that checks every single step of every proof. If it accepts a theorem,
the theorem is correct, no matter who wrote it. That matters here, because I work with an AI assistant
(Claude, by Anthropic) that writes much of the code. In the last few weeks AI systems have been involved
in serious results on the Riemann hypothesis, one of them delivered as a Lean library. I want to find out
how far this way of working can go on Collatz.

Every claim on this blog carries a label: <span class="tag verified">verified in Lean</span>,
<span class="tag lit">literature</span>, <span class="tag heur">heuristic</span>, or
<span class="tag open">open</span>. The conjecture itself stays <span class="tag open">open</span> until
Lean accepts a proof.

## First results

The first weeks went into building the foundations. Each of these will get its own post:

- **Two ways the conjecture could fail.** It is false if and only if some number cycles back to itself
  without reaching 1, or some number grows forever. <span class="tag verified">verified in Lean</span>
- **Collatz as a game with words.** In 2021, Yolcu, Aaronson and Heule showed that the conjecture is
  equivalent to a game that rewrites short words using 11 rules. I checked their theorem and their
  computer-found certificates in Lean. Along the way I found, and fixed, a small gap in one of their
  arguments. <span class="tag verified">verified in Lean</span>
- **A first new number.** If a cycle exists, it needs at least **15,601** odd steps. My previous bound,
  also checked end to end in Lean, was 2,301. <span class="tag verified">verified in Lean</span>
- **A lab for ideas.** I have also started testing ideas aimed at the full conjecture, and writing down
  why each one fails. The first lessons are sobering, and I'll share them honestly.

None of this proves Collatz. It is the ground I'll build on.

## Follow along

New posts will come as the work advances. I'll announce them on X:
[@andresdambrosio](https://x.com/andresdambrosio). The
[repository](https://github.com/andresdambrosio/Collatz) is open: if you have an idea, a correction, or a
Lean proof, contributions are welcome.
