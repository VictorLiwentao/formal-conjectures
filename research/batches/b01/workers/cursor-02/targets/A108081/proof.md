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
- The letter set of a Xia word is an integer interval (`XWord.convex`). Hence a negative letter forces `-1` to occur, and a positive letter forces `1`.
- Entries of a length-`n` word lie in `[1-n, n-1]`, so `xN n` is finite and `ncard` is well-defined.
- Reverse-and-negate `rho` is an involution of `X` swapping the two constructors.
- First letter `-1` implies a left parse; last letter `1` implies a right parse.
- Right parses at a fixed split length are unique. A word with any right parse has a unique shortest remainder (`exists_shortest_right_parse`).
- If the first letter is `-1`, then `0 :: w` is a Xia word. If the last letter is `1`, then `w ++ [0]` is a Xia word.
- `|X_1| = 1 = a 0`, `|X_2| = 2 = a 1`, `|X_3| = 7 = a 2`.
- Right-irreducible words (no right parse) end in `0`.
- `YWord` is the smallest set containing `[0]` and closed under `u ++ r v` for `v ∈ X`; every `YWord` is an `XWord`. Concatenating any Xia word with the tail of a `YWord` stays in `X`.
- `PWord`: Xia words with a unique `0`. Concatenation of two Xia words has at least two zeros, so a `PWord` is concatenation-prime. A right-constructed `PWord` has `PWord` left factor and no `-1` in the right factor, hence that factor is nonnegative. Dual left-constructed facts give a nonpositive left factor.
- Sign pattern (`XWord.pword_sign`): letters before the unique `0` are strictly negative and letters after it are strictly positive.
- Unique right parse of `[0] ++ r v` when `v` is a `PWord`: that parse is `([0], v)`.
- Catalan split: `w.take (idxOf 0) ++ [0]` and `0 :: w.drop (idxOf 0 + 1)` are `PWord`s, and concatenating them recovers `w`.
- Reverse-and-negate preserves `PWord`. A `PWord` that starts with `0` is a `YWord`. Gluing `p ++ q.tail` stays a `PWord` when `q` starts with `0`. Two start-with-`0` `PWord`s may be combined by `u ++ r v`. If `v` is a `PWord` and `u` is Xia, every right parse of `u ++ r v` has remainder at least as long as `v`. A start-with-`0` `PWord` of length at least 2 ends in `1`.
- Concatenation split (`XWord.exists_concat_split`): a Xia word with at least two zeros is `u ++ v` for nonempty Xia `u, v`.
- The shortest right-parse remainder of any Xia word is a `PWord` (`XWord.of_isRightParse_shortest`). In particular this holds for `YWord`s.
- A start-with-`0` `PWord` of length at least 2 factors uniquely as `u ++ r v` with both factors start-with-`0` `PWord`s (`PWord.shortest_right_parse_factors`, `PWord.eq_of_step_right`, `PWord.remainder_head_eq_zero`). This is the combinatorial identity `S = x + S^2`.
- Catalan cardinality (`ncard_rightN_eq_catalan`): `|Right_n| = C_{n-1}` for `n ≥ 1`, matching Mathlib `catalan`.
- Unique-zero count (`ncard_pN_eq_catalan`): `|P_n| = C_n` via the index split `w ↦ (ρ(w.take(idxOf 0) ++ [0]), 0 :: w.drop (idxOf 0 + 1))` onto `Right_{k+1} × Right_{n-k}`.
- Every `YWord` of length at least 2 has a unique shortest right parse whose remainder is a `PWord` and whose left factor is a `YWord` (`YWord.shortest_left_is_yword`).
- Y-count (`ncard_yN_eq_H`): `|Y_n| = H_{n-1}` for `n ≥ 1`. The bijection is `Y_n ≅ ⊔_{k=1}^{n-1} Y_k × P_{n-k}` via `u ++ r p`, and the resulting Catalan convolution equals `H`.
- Unique I×Y rebuild (`xword_exists_rIrreducible_yword`, `eq_of_rIrreducible_yword`): every Xia word is uniquely `c ++ y.tail` with `c` right-irreducible and `y` a `YWord`. Hence `|X_n| = ∑_{k=1}^n |I_k| H_{n-k}` (`ncard_xN_eq_sum_iN_H`).
- Left parses of I-words: every I-word of length at least 2 has a left parse (`RIrreducible.exists_left_parse`). Any left-parse remainder is again I. The unique shortest left factor is a `PWord`.
- Unique-zero words that end in `0` are I-words (`LeftWord.rIrreducible`). They are the `rho` dual of `RightWord`, so `|Left_n| = C_{n-1}`. Hence `C_{n-1} ≤ |I_n|`. I-words with a unique `0` are exactly the LeftWords.
- Left combs `ZWord` are the `rho` dual of `YWord`, so `|Z_n| = H_{n-1}`. Every I-word is a `ZWord`, hence `C_{n-1} ≤ |I_n| ≤ H_{n-1}`.

## Experimental decomposition (not a proof)

Deterministic enumerator: `experiments/enumerate_structure.py`,
`experiments/decomposition.py`, `experiments/bijection_search.py`,
`experiments/catalan_peels.py`, `experiments/pword_signs.py`,
`experiments/pword_catalan_split.py`, `experiments/right_pword_factor.py`,
`experiments/iword_left_factors.py`,
lengths `n ≤ 8`.

Facts checked in that range, and **not** claimed for all `n`:

1. The map `(c, y) ↦ c ++ y.tail` from right-irreducible cores of length `k` and `YWord`s of length `n-k+1` is a bijection onto `X_n`. Rebuild recovers greedy peels. No split inside a right-irreducible core.
2. First peels of `YWord`s are uniform: for every `Y`-prefix `u` and every `k`, the allowed next peels of length `k` are exactly `P_k = { v ∈ X_k | v has exactly one 0 }`, and `|P_k| = C_k`.
3. Every one-zero Xia word has all letters before the unique `0` strictly negative and all letters after it strictly positive. The sign pattern has no exceptions through length 7, and `|P_n| = C_n`.
4. Consequently `|Y_n| = ∑_k C_k |Y_{n-k}|` with `|Y_1|=1`, so `|Y_n| = H_{n-1}` with `H_0=1` and `H_m = C(2m-1, m-1)` for `m ≥ 1`.
5. Right-irreducible counts `I_n` equal A081696(`n-1`): generating function `x/(x+sqrt(1-4x))`. Convolution `I * H` matches `a(n-1)` through `n = 8`.
6. Endpoint class `B_n` (first `0`, last `1`) equals `|X_{n-1}|` for `n ≥ 2`. Duality gives the same for class `C_n`.
7. Free-magma constructors are not injective from `n = 4`.

Public c5-k4 already checked `|X_n| = a(n-1)` through `n = 14`. Those counts are not novelty and are not a proof.

## Remaining gaps for an exact proof

An exact proof can be assembled from three Xia-specific statements plus one generating-function identity:

1. `|I_n| = A081696(n-1)` (Wilf irreducible composition pairs of `n-1`, or the D-finite recurrence for that sequence).
2. Algebraic identity `I(x) H(x) = x G(x)` with `G` the OEIS gf of `a`. This does not mention Xia words and can be proved independently.

The unique I×Y rebuild and `|Y_n| = H_{n-1}` are proved. I-words contain the Catalan-many LeftWords and have a unique shortest left `PWord` factor with I remainder. Identifying `|I_n|` with A081696(`n-1`) and the convolution with `a` remain open. The length-3 count and the finite convolution check do not close the conjecture.

## Approaches that failed or stalled

- Unique shortest remainder always right-irreducible: false from `n = 3`.
- Convolution `I` with Catalan numbers: undercounts (`6` vs `7` at `n = 3`).
- Unique longest right remainder always irreducible: also undercounts.
- Treating Xia’s OEIS line `1,-1,0 = L(0),-1,0` as a real extra word: it is a sign typo for `(-1,-1,0)`.
- Simple local maps `X_{n-1} → B_n` (`++[1]`, `[0]++r`, prepend-`0`): not bijections.
- “All R-irreducible words have entries `≤ 0`”: false from `n = 5` (`(0,0,1,-1,0)`).

## Methods

Enumeration is exhaustive closure under the two constructors, so it matches the inductive definition. The Lean lemmas do not use the original `sorry` theorem. AI assistance was used to search, enumerate, and draft Lean; the remaining identity is unproved.
