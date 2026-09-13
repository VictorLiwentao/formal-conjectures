# Informal proof of the corrected Carmichael observation

Copyright 2026 The Formal Conjectures Authors.
Copyright 2026 Wentao Li.
Original Lean formalization: The Formal Conjectures Authors.
New Lean development and write-up: Wentao Li.
AI assistance: Cursor Grok 4.6 Extra High, as a research worker in batch b01.

Prior informal mathematical proof:
https://github.com/google-deepmind/formal-conjectures/pull/5447
by GitHub author j2d9w5xtjn-png (2026-09-10).
This write-up is known mathematics with a newly developed Lean proof.
It is not a new mathematical discovery.

## Statement

Frozen declaration `OeisA237271.observation_carmichael`:

```
∀ (k : ℕ), IsCarmichael k → 3 ≤ OeisA237271.a k
```

`a n` is one plus the number of consecutive pairs in the increasing list of
divisors of `n` whose second term is odd and at least twice the first.
`IsCarmichael n` is `∀ b ≥ 1, n.Coprime b → n.FermatPsp b`. Mathlib's
`FermatPsp` includes compositeness.

The OEIS comment is empirical for the first 10000 Carmichael numbers. The Lean
statement is the infinite reading.

## Argument

The assigned theorem follows from a stronger ordered-divisor lemma:
`3 ≤ a n` for every odd composite `n`.

### Carmichael numbers are odd composites

`IsCarmichael n` at `b = 1` gives `n.FermatPsp 1`, hence `1 < n` and `¬ n.Prime`.

If `n` were even, the coprime base `n - 1` would satisfy
`n ∣ (n - 1)^{n-1} - 1`. In `ZMod n` this is `(-1)^{n-1} = 1`. Even `n`
makes `n - 1` odd, so `(-1)^{n-1} = -1`, hence `2 = 0` in `ZMod n`, so
`n ∣ 2`. That forces `n = 1` or `n = 2`, contradicting compositeness.

### Two jumps in the ordered divisor list

Let `d` be the increasing list of divisors of an odd composite `n`. Then
`#n.divisors ≥ 3`, because `{1, m, n}` are distinct divisors for some
proper divisor `m` with `2 ≤ m < n`.

The consecutive-pair list `zip d d.tail` therefore has length at least 2.

- The first pair is `(d[0], d[1]) = (1, d[1])`. Every divisor of odd `n` is
  odd, and `1 < d[1]`, so `d[1]` is odd and `d[1] ≥ 2`.
- The last pair is `(d[len-2], d[len-1]) = (d[len-2], n)`. The predecessor
  is a proper divisor, so `2 · d[len-2] ≤ n`, and `n` is odd.

Those are two distinct positions in a `countP`, so `a n ≥ 3`.

Odd primes have `a(p) = 2` (only the pair `(1, p)`). Compositeness is
necessary. Even composites may have `a n = 1` (for example powers of two).

## What was not used

The proof does not use `conjecture_2`, `conjecture_1`, `a_odd_prime_pow`,
or any other `sorry` theorem. It does not use `native_decide`. It does not
use Korselt's criterion from `AgohGiuga.lean`.

The prior informal mathematical proof is the open pull request
https://github.com/google-deepmind/formal-conjectures/pull/5447
by GitHub author j2d9w5xtjn-png (2026-09-10). That PR records the odd-composite
argument and states that no public formal proof existed. This file is a newly
developed Lean proof of that known mathematics, not a new mathematical
discovery and not a reproduction of an accepted kernel-checked submission.

## Status

The Lean file is a candidate proof. Self-review cannot set
`independently_verified`. Axioms on the compiled theorems are
`propext`, `Classical.choice`, `Quot.sound`.
