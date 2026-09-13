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

`padicValRat_ratExpression_of_odd_prime`: for odd `n > 1` and odd prime `p`,
`v_p(T(n)) = v_p(n) + v_p(oddInnerNum n) - v_p(oddDenom n)`.

`not_n_sq_dvd_num_of_odd_inner_lt`: if that valuation is strictly less than `2 v_p(n)`, the reduced-numerator congruence fails.

`not_n_sq_dvd_num_of_inner_le_denom`: the same conclusion if `v_p(oddInnerNum n) ≤ v_p(oddDenom n)`.

`four_le_padicValNat_oddDenom`: for an odd composite `n > 3` and `p | n`, Legendre gives `v_p((n-1)!) ≥ 2`, so `v_p(oddDenom n) ≥ 4`.

`q_mul_ratExpression_sub_eq_sum`: `q T(pq) - T(p)` equals the difference of the unsigned power sums, because the `-2/n` terms cancel.

`q_dvd_two_pow_mul_sub` / `one_le_padicValRat_two_pow_mul_sub`: Fermat in characteristic `q` gives `2^{jq} ≡ 2^j (mod q)`, hence `v_q(2^{jq}-2^j) ≥ 1` for `j > 0`.

`q_mul_ratExpression_sub_eq_fermat_add`: that difference splits as a Fermat sum plus a sum of terms `q · 2^k/k` with `q ∤ k`.

`not_dvd_den_ratExpression_of_lt`: if `n < q` then `q` does not divide `T(n).den`.

`padicValRat_ratExpression_mul_eq_neg_one`: if `1 < m < q` with `q` prime and `q` does not divide `T(m).num`, then `v_q(T(mq)) = -1`.

`not_n_sq_dvd_num_of_mul_odd_primes`: the same hypotheses give the converse at `n = mq`. Kernel-checked; axioms `propext`, `Classical.choice`, `Quot.sound`. This is not the frozen iff.

## Odd composite converse

Not finished. c5-k4 found no counterexample for `n ≤ 4000`. The binomial identity reduces the problem to showing that for some prime `p | n` one has `v_p(T(n)) < 2 v_p(n)`.

A sufficient criterion is `v_p(oddInnerNum n) ≤ v_p(oddDenom n)` for some odd prime `p | n`.

For `n = mq` with prime `q`, `1 < m < q`, and `q ∤ T(m).num`, the identity `q T(mq) - T(m)` has `q`-adic valuation at least `1`, `v_q(T(m)) = 0`, and ultrametric comparison gives `v_q(T(mq)) = -1 < 2 = 2 v_q(mq)`. Deterministic `p`-adic experiments (`experiments/padic_converse.py`) give:

- `v_p(T(p^2)) ∈ {0,1,2}` for primes `p ≤ 61`, always `< 4`. For `11 ≤ p ≤ 61` this valuation is `1`.
- For square-free `n = pq ≤ 200`, `v_q(T(n)) = -1` except when `T(p) ≡ 0 (mod q)`, where it is `0`; both are `< 2`.
- Fermat base-2 pseudoprimes up to `7957` all have some local valuation strictly below `2 e`.

These scans are experimental and do not replace a kernel proof.

A332786 is equivalent for odd `n` (OEIS formula). It is reserved for literature, not a second solve target.

## Methods

Deterministic exact arithmetic; 2-adic and `p`-adic valuations; binomial identities; finite-field sums in `ZMod p`. No `native_decide` on the claimed lemmas. External Python is experimental only.
