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
- Prefix cancellation (`LeftWord.xword_of_l_append_prefix`): if `p` is a LeftWord, `b` is a prefix of a Xia word, and `L(p) ++ b` is Xia, then `b` is Xia. The shortest left factor of `L(p) ++ b` cannot be shorter than `p` (the remainder would start with a letter `≤ -2`) and cannot be longer than `p` (that factor would be `r(s) ++ p` with `s` a nonempty prefix of a Xia word forced to start at `≤ -2`).
- Therefore `L(Left) ++ v` is I whenever `v` is I (`LeftWord.append_rIrreducible`). Combined with the unique `P × I` enumeration of I-words (`ncard_iN_eq_card_goodPairs`), this gives `|I_n| ≥ ∑_{k=1}^{n-1} C_{k-1} |I_{n-k}|` for `n ≥ 2`.
- The `01` extra first-return factors: if `p` is a LeftWord then `p ++ [1]` is a `PWord` and `L(p ++ [1]) ++ [0]` is I (`LeftWord.concat_one_l_append_zero_rIrreducible`). Any right-parse left factor of length 1 forces the remainder to end at `-2`; any longer proper prefix of `0 :: L(p)` ends in a strictly negative letter.
- A Xia word of length at least 2 that ends in `1` with penultimate at most `1` has Xia `dropLast` (`XWord.dropLast_of_getLast_eq_one_of_penultimate_le_one`). The shortest right remainder cannot have length `≥ 2`, else the penultimate letter would be at least `2`. This covers both `01` and `11` endings.
- Cons-zero converse (`XWord.of_cons_zero_head_le_zero`): if `0 :: w` is Xia and `w` is nonempty with first letter `≤ 0`, then `w` is Xia. The proof is by strong induction on length. A left construction with head `0` forces the left factor to end in `01` or `11`, so `dropLast` applies; a right construction of left-factor length 1 forces the remainder to end at a letter `≤ -1`.
- Therefore `L(Left ++ [1]) ++ v` is I for every I-word `v` (`LeftWord.concat_one_append_rIrreducible`). Length-1 right parses of `0 :: L(p) ++ v` force remainder last `-2`. Prefixes of `0 :: L(p)` of length at least 2 end in a negative letter. Longer left factors are `0 :: (L(p) ++ v.take k)` with second letter `-1`, so the cons-zero converse and prefix cancellation produce a right parse of `v`. Combined with unique `P × I` enumeration, `|I_n| ≥ ∑_{k=1}^{n-1} C_{k-1}|I_{n-k}| + ∑_{k=2}^{n-1} C_{k-2}|I_{n-k}|` for `n ≥ 2`.
- No Xia word of length 3 starts with `00` (`not_xWord_cons_zero_zero`).
- A Xia word that starts with `00` has a negative letter and a left parse (`XWord.exists_neg_of_start_zero_zero`, `XWord.exists_left_parse_of_start_zero_zero`). Consequently no nonnegative Xia word starts with `00`.
- If `s` is a `PWord` ending in `1`, then any prefix of `0 :: L(s)` of length `m` with `2 ≤ m ≤ |s|+1` is a nonnegative `00`-word, hence not Xia (`not_xWord_take_cons_l_of_getLast_eq_one`). Therefore `L(s ++ [1]) ++ [0]` is I for every `PWord s` (`PWord.concat_one_l_append_zero_rIrreducible`).
- Prefix cancellation (`PWord.xword_of_l_concat_one_append_prefix`): if `s` is a last-`1` `PWord`, `b` is a prefix of a Xia word, and `L(s ++ [1]) ++ b` is Xia, then `b` is Xia. Any left parse of `L(s ++ [1]) ++ b` is at least as long as `|s|+1` (shorter factors are `00`-prefixes or force a remainder letter `≤ -2`). A longer shortest left factor would be `r(t) ++ (s ++ [1])` with `t` a nonempty prefix of a Xia word forced to start at `≤ -2`.
- Therefore `L(s ++ [1]) ++ v` is I for every `PWord s` and every I-word `v` (`PWord.concat_one_append_rIrreducible`). Combined with unique `P × I` enumeration, `|I_n| ≥ ∑_{k=1}^{n-1} C_{k-1}|I_{n-k}| + ∑_{k=2}^{n-1} C_{k-1}|I_{n-k}|` for `n ≥ 2` (`ncard_iN_ge_sum_catalan_iN_add_pConcatOne`). This is the Callan/A081696 first-return lower bound: `q(1)=1` and `q(k)=2 C_{k-1}` for `k≥2`.
- If `s` is a `PWord` ending in `1` with penultimate at most `1`, then `dropLast s` is a `PWord` and `s = dropLast s ++ [1]` (`PWord.eq_concat_one_of_getLast_eq_one_of_penultimate_le_one`). So the extra first-return factors used above are exactly the last-`1` one-zero words with penultimate `≤ 1`.
- List identity: if `s` ends in `1`, then `L(s) ++ [0] = [0] ++ R((-1) :: map(·-2) dropLast s)`. So the length-1 right parse of `L(s) ++ [0]` exists exactly when `(-1) :: map(·-2) dropLast s` is Xia (`isRightParse_l_append_zero_cons_zero`). This holds for many, but not all, last-`1` penultimate-`≥ 2` `PWord`s.
- First-factor-`[0]` obstruction: `L([0] ++ R(v)) ++ [0] = v ++ [-1, 0]`. If `v` has a right parse `a ++ R(b)`, then `v ++ [-1, 0] = a ++ R([-1, -2] ++ b)` with `[-1, -2] ++ b` Xia. Every start-with-`0` unique-zero word of length at least 2 has such a parse, so `L([0] ++ R(v)) ++ [0]` is not I whenever `|v| ≥ 2` (`RightWord.cons_zero_r_l_append_zero_not_rIrreducible`). These are exactly the RightWords whose shortest remainder has length at least 2 and whose left factor is `[0]`.
- If the shortest remainder `v` of a RightWord has penultimate `≤ 1` and `(-1) :: map(·-2) u ++ [0]` is Xia, then `L(u ++ R(v)) ++ [0]` has right parse `(v.dropLast, (-1) :: map(·-2) u ++ [0])`. The extra Xia hypothesis is proved when `u` itself has the form `[0] ++ R(t)`, and when `u = [0]`.

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
8. `L(Left) ++ b` Xia with `b` a prefix of some Xia word implies `b` Xia, through `n = 8` (`experiments/left_prefix_any_xia.py`). This is now a theorem.
9. The set of `p ∈ P_k` with `L(p) ++ v` I is independent of the I-remainder `v` and has size `q(k)` (`q(1)=1`, `q(k)=2 C_{k-1}` for `k≥2`) through `n = 8`. Not a theorem.
10. Through `k = 6` (`experiments/gword_dropLast.py`, `gword_penultimate.py`), `G_k = Left_k ∪ { s ++ [1] | s ∈ P_{k-1} } = { p ∈ P_k | last = 0 ∨ penultimate ≤ 1 }`. Glue of this `G_k` to every I-remainder is now a theorem, as is `|image(++[1] : P_{k-1} → P_k)| = C_{k-1}`. Equality `|I_n| = ∑ q(k)|I_{n-k}|` still needs the converse: every shortest left `PWord` factor of an I-word lies in this `G_k`. Through length 7 (`experiments/rightword_bad_remainder.py`), a RightWord of length at least 2 is last-`1` with penultimate `≥ 2` exactly when its shortest remainder has length at least 2. The first-factor-`[0]` subcase is now a theorem. The remaining gap is longer left factors and head-`-1` `PWord`s.
11. Through length 8, `0 :: w` Xia and `w` starting at `-1` or `0` implies `w` Xia (`experiments/cons_zero_converse.py`). This is now a theorem for every first letter `≤ 0`. The forward map `w ↦ 0 :: w` still requires first letter `-1`.

Public c5-k4 already checked `|X_n| = a(n-1)` through `n = 14`. Those counts are not novelty and are not a proof.

## Remaining gaps for an exact proof

An exact proof can be assembled from three Xia-specific statements plus one generating-function identity:

1. `|I_n| = A081696(n-1)` (Wilf irreducible composition pairs of `n-1`, or the D-finite recurrence for that sequence).
2. Algebraic identity `I(x) H(x) = x G(x)` with `G` the OEIS gf of `a`. This does not mention Xia words and can be proved independently.

The unique I×Y rebuild and `|Y_n| = H_{n-1}` are proved. I-words contain the Catalan-many LeftWords, are closed under `L(Left) ++ ·` and under `L(s ++ [1]) ++ ·` for every `PWord s`, and have a unique shortest left `PWord` factor with I remainder. The Callan/A081696 lower bound `|I_n| ≥ ∑ q(k)|I_{n-k}|` is proved. The first-factor-`[0]` RightWords with remainder length at least 2 are now excluded from I-gluing of `L(p) ++ [0]`. Equality still needs the rest of the converse (longer left factors, head-`-1` `PWord`s), then matching A081696 initials, then the convolution with `H`. The length-3 count and the finite convolution check do not close the conjecture.

## Approaches that failed or stalled

- Unique shortest remainder always right-irreducible: false from `n = 3`.
- Convolution `I` with Catalan numbers: undercounts (`6` vs `7` at `n = 3`).
- Unique longest right remainder always irreducible: also undercounts.
- Treating Xia’s OEIS line `1,-1,0 = L(0),-1,0` as a real extra word: it is a sign typo for `(-1,-1,0)`.
- Simple local maps `X_{n-1} → B_n` (`++[1]`, `[0]++r`, prepend-`0`): not bijections.
- “All R-irreducible words have entries `≤ 0`”: false from `n = 5` (`(0,0,1,-1,0)`).

## Methods

Enumeration is exhaustive closure under the two constructors, so it matches the inductive definition. The Lean lemmas do not use the original `sorry` theorem. AI assistance was used to search, enumerate, and draft Lean; the remaining identity is unproved.
