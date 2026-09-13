# A108081 proof notes

Copyright 2026 The Formal Conjectures Authors. Copyright 2026 Wentao Li.
Original Lean formalization: The Formal Conjectures Authors.
New proof development and write-up: Wentao Li.
AI assistance: Cursor Grok 4.6 Extra High, used for literature search, enumeration, and Lean drafting.

This is **not** a completed proof or disproof of
`OeisA108081.count_words_in_x_is_a_shifted`.
Finite counts and partial lemmas are not a resolution.

## Target

For `n ≥ 1`, `|X_n| = a(n-1)`, where `X_n` is the set of Xia words of length `n`
and `a` is the Lean sequence `OeisA108081.a`.

## What is proved in Lean

File: `A108081.lean`. Compiled with
`LEAN_NUM_THREADS=2 lake --wfail env lean` on this file.
`#print axioms` on the listed lemmas reports only `propext` / `Classical.choice` / `Quot.sound`.

Proved:

- `l` and `r` are mutually inverse anti-homomorphisms, hence injective.
- Every Xia word is nonempty, contains `0`, starts in `{-1,0}`, and ends in `{0,1}`.
- Entries of a length-`n` word lie in `[1-n, n-1]`, so `xN n` is finite and `ncard` is well-defined.
- Reverse-and-negate `rho` is an involution of `X` swapping the two constructors.
- First letter `-1` implies a left parse; last letter `1` implies a right parse.
- Those parse lengths are unique: equal split length implies equal factors.
- If the first letter is `-1`, then `0 :: w` is a Xia word. If the last letter is `1`, then `w ++ [0]` is a Xia word.
- `|X_1| = 1 = a 0` and `|X_2| = 2 = a 1`.
- Right-irreducible words (no right parse) end in `0`.
- `YWord` is the smallest set containing `[0]` and closed under `u ++ r v` for `v ∈ X`; every `YWord` is an `XWord`.

## Experimental decomposition (not a proof)

Deterministic enumerator: `experiments/enumerate_structure.py` and
`experiments/decomposition.py`, lengths `n ≤ 8`.

Facts checked in that range, and **not** claimed for all `n`:

1. Right-irreducible counts `I_n` equal A081696(`n-1`): `1,1,3,9,29,97,333,1165`.
2. Duality `rho` swaps right-irreducible and left-irreducible words.
3. Let `H 0 = 1` and `H m = C(2m-1, m-1)` for `m ≥ 1`. Every Xia word has a unique greedy shortest-right-peel core `c` that is right-irreducible, and the fibre over each such core of length `k` has size exactly `H_{n-k}`. The valid tails of a given length are independent of the core.
4. Words whose greedy core is `[0]` (equivalently `YWord` candidates) number `H_{n-1}`, not Catalan `C_{n-1}`.
5. Consequently `|X_n| = sum_k I_k H_{n-k}` matches `a(n-1)` through `n = 8`.
6. Endpoint class `B_n` (first `0`, last `1`) equals `|X_{n-1}|` for `n ≥ 2`. Duality gives the same for class `C_n`.
7. Prepend-`0` on `{first = -1}` lands in `X` (now proved) but is not surjective onto `{first = 0}`.
8. Free-magma constructors are not injective from `n = 4`. The algebraic relation `B(1-B)^2 = x` is false (`30` vs `25` at `n = 4`).

Public c5-k4 already checked `|X_n| = a(n-1)` through `n = 14`. Those counts are not novelty and are not a proof.

## Remaining gaps for an exact proof

The generating-function identity
`I(x) H(x) = x G(x)` with `G` the OEIS gf of `a`,
`I(x) = x / (x + sqrt(1-4x))`, and `H(x) = (1+sqrt(1-4x))/(2 sqrt(1-4x))`
would give `|X_n| = a(n-1)` **after** three combinatorial statements:

1. Unique greedy right-core bijection: every Xia word is uniquely `rebuild(c, peels(y))` with `c` right-irreducible and `y` a `YWord` of length `n-|c|+1`. Empirically the peels of `c ++ tail(y)` equal the peels of `y`.
2. `|Y_n| = H_{n-1}`.
3. `|I_n| = A081696(n-1)`. A081696 counts Wilf irreducible composition pairs of `n-1`. No bijection is written.

None of (1)–(3) is proved. Partial lemmas and the finite convolution check do not close the conjecture.

## Approaches that failed or stalled

- Unique shortest remainder always right-irreducible: false from `n = 3`.
- Convolution `I` with Catalan numbers: undercounts (`6` vs `7` at `n = 3`).
- Unique longest right remainder always irreducible: also undercounts.
- Treating Xia’s OEIS line `1,-1,0 = L(0),-1,0` as a real extra word: it is a sign typo for `(-1,-1,0)`.

## Methods

Enumeration is exhaustive closure under the two constructors, so it matches the inductive definition. The Lean lemmas do not use the original `sorry` theorem. AI assistance was used to search, enumerate, and draft Lean; the remaining identity is unproved.
