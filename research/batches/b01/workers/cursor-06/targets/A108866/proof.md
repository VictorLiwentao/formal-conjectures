# Proof notes — A108866

Copyright 2026 The Formal Conjectures Authors. Copyright 2026 Wentao Li.
Original Lean formalization: The Formal Conjectures Authors.
New proof development and write-up: Wentao Li.

AI assistance: Cursor Grok 4.6 Extra High, worker `cursor-06`.

## Frozen claim

For `n > 3`,
`numerator(-2/n + ∑_{k=1}^n 2^k/k) ≡ 0 (mod n^2)` if and only if `n` is prime.
The numerator is reduced.

Write `T(n)` for that rational.

## What is proved in Lean

`not_n_sq_dvd_num_of_even`: if `n > 3` is even, then `n^2` does not divide `T(n).num`.
Kernel-checked; axioms `propext`, `Classical.choice`, `Quot.sound`.

Argument: `T(n) = ∑_{k=1}^{n-1} 2^k/k + (2^n-2)/n`. The first sum has 2-adic valuation at least 2. The second term has valuation `1 - v_2(n) ≤ 0`. Ultrametric inequality gives `v_2(T(n)) ≤ 0`. A reduced rational with nonpositive 2-adic valuation has odd numerator, so an even `n^2` cannot divide it.

This is the even half of the converse. It is not the full iff.

`ratExpression_eq_two_mul_n_sum_choose_sq`: for odd `n > 1`,
`T(n) = 2 n ∑_{odd r < n} C(n-1, r-1) / r^2`.
This is Komatsu–Sury Lemma 2 at `x = -2`, after cancelling the last binomial term against `-2/n` and using `C(n,r)/r = n C(n-1,r-1)/r^2`. The identity is polynomial: the derivatives of the two generating polynomials agree, and evaluation at `-2` gives the odd-sum formula. Python checks it for odd `n ≤ 121`.

## Prime direction (published, not kernel-checked here)

For odd prime `p`,
`T(p) = ∑_{k=1}^{p-1} 2^k/k + (2^p-2)/p`.
The denominator of the first sum divides `lcm(1,…,p-1)`, hence is coprime to `p`, and Fermat’s little theorem makes the second term an integer. So `p ∤ T(p).den` and `p^2 | T(p).num` iff `T(p) ≡ 0` in `ℤ_{(p)}/p^2`.

Komatsu–Sury, arXiv:2309.09491, Proposition 1, and Zhi-Hong Sun, J. Number Theory 128 (2008), give
`∑_{k=1}^{p-1} 2^k/k ≡ -(2^p-2)/p (mod p^2)`.

From the odd identity, it is enough to show that the inner sum `∑_{odd r < p} C(p-1,r-1)/r^2` is `0` in `ℤ_{(p)}/p`. Mathlib has `ZMod.cast_descFactorial`, so `C(p-1,i) ≡ (-1)^i (mod p)` for `i < p`. For odd `r` this is `1`, and `∑_{x=1}^{p-1} x^{-2} = ∑ x^2 = 0` in `𝔽_p` for `p ≥ 5`.

## Odd composite converse

Open. c5-k4 found no counterexample for `n ≤ 4000`. The binomial identity reduces the problem to showing that for some prime `p | n` one has `v_p(T(n)) < 2 v_p(n)`.

A332786 is equivalent for odd `n` (OEIS formula). It is reserved for literature, not a second solve target.

## Methods

Deterministic exact arithmetic; 2-adic valuations; binomial identities. No `native_decide` on the claimed even lemma. External Python is experimental only.
