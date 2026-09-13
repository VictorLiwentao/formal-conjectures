# Proof — A051903 question 2

Target: `OeisA51903.conjecture2`. Answer: **no**.

Let `a n` be the frozen maximum prime-factor exponent

```lean
(n.primeFactorsList.map (n.primeFactorsList.count ·)).foldr max 0
```

The claim is that there is no natural `n` with `Odd n`, `1 < a n`, and `b^n ≡ b^(a n) [MOD n]` for every natural `b`.

## 1. Maximum attainment

Assume `1 < a n`. The mapped count list is nonempty and its `foldr max 0` is attained. Some `p ∈ n.primeFactorsList` therefore satisfies `n.primeFactorsList.count p = a n`. Mathlib identifies that count with `n.factorization p`. Hence `p` is prime and `p^(a n) ∣ n`. In particular `n ≠ 0`.

## 2. The prime is odd and `a n < n`

`Odd n` implies `¬ 2 ∣ n`, so `p ≠ 2` and `3 ≤ p`. Write `e = a n ≥ 2`. Then `e < p^(e-1)` by induction on `e`: the case `e = 2` is `2 < p`, and the step uses `p^e = p · p^(e-1) ≥ 3 · p^(e-1) > 3e ≥ e+1`. Combined with `p^(e-1) ≤ p^e ≤ n` this gives `e < n`, so the natural difference `n - e` is the intended subtraction.

## 3. Modular reduction at base `1+p`

The all-`b` hypothesis includes `b = 1+p`. Reducing modulo `p^e` yields `(1+p)^n ≡ (1+p)^e [MOD p^e]`. The integer `1+p` is coprime to `p^e`, so it is a unit in `ZMod (p^e)`. Cancelling `(1+p)^e` gives `(1+p)^(n-e) = 1` in that ring.

## 4. Order / LTE

Mathlib proves `orderOf (1 + p : ZMod (p^(k+1))) = p^k` for an odd prime `p` (`ZMod.orderOf_one_add_prime`). With `k = e-1` the order is `p^(e-1)`, so `p^(e-1) ∣ n-e`.

The same divisibility is the odd-prime lifting-the-exponent identity `v_p((1+p)^n - (1+p)^e) = 1 + v_p(n-e)` after cancelling the unit `(1+p)^e`; that lemma was not needed as an extra axiom because the order theorem is already in Mathlib.

## 5. Contradiction

`p^(e-1) ∣ n` as well, hence `p^(e-1) ∣ e`. But `0 < e < p^(e-1)`, so no such positive divisor exists.

The argument uses that `n` is odd to guarantee an odd prime of maximal exponent. It is not claimed for even `n`. A327295's "are all terms even?" is the same existence question; this file answers it negatively for the universal all-`b` condition (C2), not for the weaker fixed-base-2 condition (C3).

## 6. Exact negative answer

`A051903C2.no_odd_universal` is the negation of the frozen RHS. `A051903C2.conjecture2` is the same biconditional with `answer(False)` in place of `answer(sorry)`. The `example` identifies the left-hand side with `False`. This is not a proof of the original admitted theorem, and it does not exploit the `answer(sorry) → True` placeholder.
