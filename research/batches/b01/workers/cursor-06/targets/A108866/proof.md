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

`ratExpression_eq_two_mul_n_sum_choose_sq`: for odd `n > 1`,
`T(n) = 2 n ∑_{odd r < n} C(n-1, r-1) / r^2`.
This is Komatsu–Sury Lemma 2 at `x = -2`, after cancelling the last binomial term against `-2/n` and using `C(n,r)/r = n C(n-1,r-1)/r^2`.

`n_sq_dvd_num_of_prime`: if `p > 3` is prime, then `p^2` divides `T(p).num`.
Kernel-checked; axioms `propext`, `Classical.choice`, `Quot.sound`.

Argument: Mathlib `ZMod.cast_descFactorial` gives `C(p-1,i) ≡ (-1)^i (mod p)` for `i < p`. For odd `r` this is `1`. Clearing denominators by `((p-1)!)^2` shows that the inner sum is `0` in `𝔽_p`, because `∑_{x=1}^{p-1} x^{-2} = ∑ x^2 = 0` for `p ≥ 5` and the odd residues contribute half that sum. Thus `v_p(T(p)) ≥ 2`. A reduced rational with nonnegative `p`-adic valuation cannot have `p` in the denominator, so `p^2` divides the reduced numerator.

`conjecture_of_odd_composite_converse`: the frozen iff follows from the odd-composite converse together with the two theorems above.

This is not the full iff.

## Odd composite converse

Open. c5-k4 found no counterexample for `n ≤ 4000`. The binomial identity reduces the problem to showing that for some prime `p | n` one has `v_p(T(n)) < 2 v_p(n)`.

A332786 is equivalent for odd `n` (OEIS formula). It is reserved for literature, not a second solve target.

## Methods

Deterministic exact arithmetic; 2-adic and `p`-adic valuations; binomial identities; finite-field sums in `ZMod p`. No `native_decide` on the claimed lemmas. External Python is experimental only.
