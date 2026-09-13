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

`padicValNat.pow_sub_pow` (lifting the exponent) gives `v_q(2^{jq}-2^j)=v_q(2^q-2)+v_q(j)` for odd primes `q`. Hence every Fermat term `(2^{jq}-2^j)/j` has valuation at least `1` with no restriction `j<q`. Combined with the rest sum, `v_q(q T(mq)-T(m))≥1` whenever the difference is nonzero.

`padicValRat_ratExpression_mul_of_val_lt_one`: if `v_q(T(m))<1`, then `v_q(T(mq))=v_q(T(m))-1`.

`padicValRat_ratExpression_mul_eq_min_sub_one`: if those two valuations are unequal, `v_q(T(mq))` is the minimum minus `1`.

`padicValRat_ratExpression_eq_neg_one_of_unique`: if `p≤m<2p` and `p∤m`, then `k=p` is the unique multiple of `p` in `1..m`, so `v_p(T(m))=-1`.

`not_n_sq_dvd_num_of_unique_prime_mul`: the same hypotheses give the converse at `n=mp`.

`padicValRat_ratExpression_eq_neg_pow_of_trunc`: if `p^e ≤ m < p^{e+1}`, `p ∤ m`, and
`L(m/p^e) := ∑_{j=1}^{m/p^e} 2^j/j ≠ 0` in `𝔽_p`, then `v_p(T(m)) = -e`.
The proof splits the terms whose denominator is divisible by `p^e`, reduces their
leading coefficients to `L` by Fermat (`2^{p^e} ≡ 2` in `𝔽_p`), and uses the ultrametric
inequality against the remaining terms of valuation at least `1-e`.

`not_n_sq_dvd_num_of_trunc` / `not_n_sq_dvd_num_of_log`: the same hypotheses give the converse
at `n = mp`. The `Nat.log` form takes `e = ⌊log_p m⌋`.

`twoHarmonicTrunc_two_ne_zero`: `L(2) = 4 ≠ 0` in `𝔽_p` for odd primes `p`, so the criterion
applies whenever `2p ≤ m < 3p` and `p ∤ m`.

`not_n_sq_dvd_num_of_prime_factor`: packages the `m < p` Fermat case with the `L ≠ 0` case.

`p_mul_ratExpression_sq_sub_pos`: `p T(p^2) - T(p) > 0` for prime `p`, so the min-lemma
applies whenever `v_p(T(p)) ≠ v_p(p T(p^2)-T(p))`.

Exact evaluations (kernel `norm_num`, not `native_decide`): the converse holds at
`n = 9, 25, 27, 49`.

`not_n_sq_dvd_num_of_three_pow`: for `e ≥ 2`, `v_3(T(3^e)) = 2-e < 2e`.
Kummer gives `v_3(C(3^e-1,k))=0`. Among odd `r < 3^e` the unique index with
`v_3(r)=e-1` is `r=3^{e-1}` (`a=2` is even). Ultrametric uniqueness then
gives `v_3` of the inner sum equal to `-2(e-1)`. Kernel-checked; axioms
`propext`, `Classical.choice`, `Quot.sound`. This is not the frozen iff.

`not_n_sq_dvd_num_of_three_mul_pow`: for an odd prime `p ≥ 5` and `e ≥ 1`,
`v_p(T(3 p^e)) = -e < 2e`. Kummer gives `v_p(C(3 p^e-1, p^e-1))=0`.
Among odd `r < 3 p^e` the unique multiple of `p^e` is `r=p^e`
(`a=2` is even). The reusable unique-min lemma
`padicValRat_inner_of_unique` then gives `v_p` of the inner sum equal to
`-2e`. Kernel-checked; same axioms. This is not the frozen iff.

Product lemmas for the remaining prime-power case: for `1 ≤ a ≤ p`,
`C(p^e-1, a p^{e-1}-1) = C(p-1, a-1)` times the product of
`(p^e-j)/j` over those `j ≤ a p^{e-1}-1` not divisible by `p^{e-1}`.
On multiples `j = b p^{e-1}` the ratio is exactly `(p-b)/b`.

`eq_or_two_le_padicValRat_rest_prod_sub_one`: that rest product is `1`
or else `v_p(rest-1)≥2`. Combined with `v_p(C(p-1,a-1))=0`, this gives
`eq_or_two_le_padicValRat_choose_sub`: either the binomials are equal,
or `v_p(C-C0)≥2`. Kernel-checked; axioms
`propext`, `Classical.choice`, `Quot.sound`. This is not the frozen iff.

`eq_or_two_le_padicValRat_leading_sub` / `padicValRat_leading_eq_of_lt`:
the odd leading sums `U` and `U0` therefore agree whenever
`v_p(U0)<2`. The remaining gap for `p^e` is `v_p(U0)=1`
(empirically except `p=7`, where `v=2`).

First-order expansion `C(p-1,a-1)=∏(1-p/b)` for odd `a`, and
`C(p-1,a-1) ≡ 1 - p H_{a-1}` with valuation gap at least 2
(`eq_or_two_le_padicValRat_choose_pred_sub_harmonic`), is kernel-checked
but not yet used to evaluate `v(U0)`.

## Odd composite converse

Not finished. c5-k4 found no counterexample for `n ≤ 4000`. The binomial identity reduces the problem to showing that for some prime `p | n` one has `v_p(T(n)) < 2 v_p(n)`.

A sufficient criterion is `v_p(oddInnerNum n) ≤ v_p(oddDenom n)` for some odd prime `p | n`.

Kernel-checked fragments of the converse:

- even `n`
- `n=mq` with prime `q`, `1<m<q`, and `q∤T(m).num`
- `n=mp` with odd prime `p` and `v_p(T(m))<1`, including:
  - `p≤m<2p` and `p∤m` (unique multiple)
  - `p^e ≤ m < p^{e+1}`, `p∤m`, and `L(m/p^e)≠0` in `𝔽_p`
- exact `n=9, 25, 27, 49`
- all powers `n=3^e` for `e≥2` (`v_3(T(3^e))=2-e`)
- all `n=3 p^e` for primes `p≥5` and `e≥1` (`v_p(T(3 p^e))=-e`)
- `p^e` leading binomials: `C ≡ C0` with valuation gap at least 2,
  so `v_p(U)=v_p(U0)` whenever `v_p(U0)<2`

Remaining odd composites include prime powers `p^e` for `p≥5` and products
where `L(m/p^e)=0` for every eligible prime (for example `n=1027=13·79`),
and mixed powers such as `3^a q^b` with `a≥2`.
Experiments (`experiments/padic_converse.py`, `experiments/remaining_odd.py`,
`experiments/prime_power_leading.py`) give:

- `v_p(T(p^2))∈{0,1,2}` for primes `p≤61`, always `<4`. For `11≤p≤61` this valuation is `1`.
- Empirically `v_p(p T(p^2)-T(p))>v_p(T(p))`, which would give `v_p(T(p^2))=v_p(T(p))-1` from the min lemma. Not kernel-checked.
- For square-free `n=pq≤200`, `v_q(T(n))=-1` except when `T(p)≡0 (mod q)`, where it is `0`; both are `<2`.
- Fermat base-2 pseudoprimes up to `7957` all have some local valuation strictly below `2e`.

These scans are experimental and do not replace a kernel proof.

A332786 is equivalent for odd `n` (OEIS formula). It is reserved for literature, not a second solve target.

## Methods

Deterministic exact arithmetic; 2-adic and `p`-adic valuations; binomial identities; finite-field sums in `ZMod p`. No `native_decide` on the claimed lemmas. External Python is experimental only.
