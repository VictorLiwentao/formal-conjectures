# A108081 literature and novelty audit

Checked on 2026-09-12. Live OEIS HTML history/edit pages were Cloudflare-blocked from this environment; the public JSON/API payload for the sequence was retrieved.

## Frozen statement

- File: `FormalConjectures/OEIS/108081.lean`
- SHA-256: `b03761724c1052d613a676584301d6ad1f3d20aff62aa421525ef8b6b611a54d` (matches assignments.json and the baseline blob)
- Declaration: `OeisA108081.count_words_in_x_is_a_shifted`
- Type: `∀ n, n ≥ 1 → Set.ncard (xN n) = a (n - 1)`
- Category: `research open`
- Baseline: `a2f4a1bb12a28e04a969da78feefac7d1ce49565`

## OEIS A108081

- URL: https://oeis.org/A108081
- JSON: https://oeis.org/search?q=id:A108081&fmt=json (retrieved 2026-09-12)
- Offset 0. Name: `a(n) = Sum_{i=0..n} binomial(2*n-i, n+i)`.
- Revision 39, timestamp `2025-01-19T09:28:27-05:00`.
- Li-yao Xia comment, 2015-10-22: smallest set `X` of integer words containing `0` and closed under `L(a).b` and `a.R(b)`, with `L` reverse-then-subtract-1 and `R` reverse-then-add-1.
- Xia lists words of lengths 1, 2, 3 and asks whether the number of words of length `n` for `n ≤ 12` is `a(n+1)`.
- Listed length-1/2/3 examples have cardinalities 1, 2, 7, which are `a(0), a(1), a(2)`, i.e. `a(n-1)`, not `a(n+1)`.
- One listed length-3 word is written `1, -1, 0 = L(0), -1, 0`. The constructor `L(0).(-1,0)` is `(-1,-1,0)`, so that line is a sign typo in the OEIS prose, not a different construction.
- Formulas: Jovovic gf (2006); Barry Catalan transform of Fibonacci and gf (2007-09-28); Barry Fibonacci-binomial sum; Kotesovec recurrence and asymptotic (2012); Manyama `[x^n] 1/((1-x-x^2)(1-x)^n)` (2024-04-05).
- Triangle A159965 has diagonal sums A108081 and `T(n,k) = binomial(2n+k, n+2k)` (Bala). Row sums are A108080, not this target.
- Editability: public JSON has no draft field. `https://oeis.org/A108081/edit` returned 404 without login. History HTML was Cloudflare-challenged. Record: **unknown** (no visible pending draft in the JSON payload; no logged-in edit check).

## Formal Conjectures / DeepMind

- Added in AutoOeis batch: https://github.com/google-deepmind/formal-conjectures/commit/d7032450c5 (`#4450`, 2026-08-13).
- Source URL at pin: https://github.com/google-deepmind/formal-conjectures/blob/a2f4a1bb12a28e04a969da78feefac7d1ce49565/FormalConjectures/OEIS/108081.lean
- `gh` issue/PR search for `108081` and `count_words_in_x_is_a_shifted` in `google-deepmind/formal-conjectures`: no issue or PR besides the original file add.
- Current theorem remains `sorry`.

## AlphaProof Nexus and Epoch

- `google-deepmind/alphaproof-nexus-results`: code search for `108081` returned no files. Nearby `oeis_108_conjecture_2.lean` is A000108, not A108081.
- `epoch-research/LeanOpenProblems` and `LeanOpenProblems-results`: no file or declaration for A108081 / `count_words_in_x_is_a_shifted`. Hits on the numeral `108081` were unrelated data.

## Public computational work (not a proof)

- https://github.com/Kuberwastaken/c5-k4 `results/expansion/oeis4_20260826/a108081.md`: exhaustive distinct-word counts `|X_n| = a(n-1)` for `n = 2..9`.
- https://github.com/Kuberwastaken/c5-k4/blob/main/results/expansion/oeis108081_n14_report.md: `|X_14| = 16438345 = a(13)`, with an independent packed audit. Explicitly not a universal proof. Prompt forbids treating lengths 13–14 as novelty.

## arXiv / MathOverflow / papers

- Searches for the Xia word construction, `A108081`, `count_words_in_x_is_a_shifted`, and reverse-and-shift concatenation did not find a proof.
- Paul Barry’s Catalan-transform comments explain the sequence `a(n)`, not the word conjecture.
- Sela Fried, arXiv:2607.24832, proves the A108080 row-sum conjecture for triangle A159965. It does not treat A108081 or the Xia words.
- MathOverflow searches for this construction returned unrelated word-enumeration problems.
- Li-yao Xia’s page https://poisson.chat/ does not list this problem.

## Inaccessible sources

- OEIS HTML history and wiki edit UI (Cloudflare or 404 without login).
- Direct `curl` of `oeis.org/A108081` (Cloudflare). JSON/API succeeded.

- Repeat search, 2026-09-13 01:54Z: OEIS A108081 JSON still revision 39 (2025-01-19). No Xia-word proof added.

- OEIS A108081 JSON still revision 39 (2025-01-19). No proof of the Xia word count. Formula list unchanged (Jovovic, Barry, Kotesovec, Manyama).
- Li-yao Xia’s 2014 repo https://github.com/Lysxia/cfpt enumerates a dual constructor pair `a ++ L(b)` and `R(a) ++ b` (Haskell `exhaust.hs` / `dypro.hs`). Last push 2014-05-07. No proof. The README conjecture `X(n) = ∑ C(2n-i, n+i)` has the same off-by-one as the OEIS prose; Xia’s listed length-1/2/3 cardinalities still match `a(n-1)`.
- OEIS A081696 (retrieved 2026-09-13, revision 115) is `1,1,3,9,29,97,333,1165,…` with gf `1/(x+sqrt(1-4x))`, matching experimental `|I_n|` as `A081696(n-1)`. The Wilf comment (irreducible composition pairs) is on this sequence. No published bijection with Xia right-irreducible words was found.
- Fried arXiv:2607.24832 still treats A108080, not A108081.
- Fried–Shattuck, Enumerative Combinatorics and Applications (2026-01-23), “Counting s-Catalan words according to total variation”, is about classical Catalan words / Motzkin polyominoes, not Xia’s reverse-and-shift constructors.
- MathOverflow / arXiv searches for the Xia constructors and “functional pregroup types” counting did not return a proof of `|X_n| = a(n-1)`.

## Novelty conclusion

No accepted Lean proof, Epoch submission, AlphaProof output, or paper proving or disproving `|X_n| = a(n-1)` was found. Finite enumeration through `n = 14` is known and is not a solution. An upstream `sorry` is not evidence of openness; this is only “no public solution found in the checked sources.”
