# A076141 proof report

This is not a new resolution. After the novelty audit, an exact public Lean proof of the frozen statement was found and kernel-checked. Batch rules forbid reproducing that argument as a new result.

## Frozen claim

For every natural number n, including 0, the MSB-first binary word of n occurs at most once as a contiguous infix of the binary word of n^2. Occurrences are counted by `List.tails.countP`, so overlaps count. Zero is the word `[0]`.

Lean:

```lean
theorem conjecture (n : ℕ) : a n ≤ 1
```

## Formalization audit

The formal statement matches the OEIS question.

- Domain is all of `ℕ`. Tests `a 0 = 1`, `a 1 = 1`, `a 3 = 0` show the claim is not vacuous.
- `binaryPattern 0 = [0]` matches the PARI/OEIS zero convention. `Nat.digits 2 0` is empty, so the `if n = 0` branch is required.
- For n > 0, `(Nat.digits 2 n).reverse` is MSB-first and has no leading zeros.
- `tgt.tails.countP (pat.isPrefixOf ·)` counts every start, including overlaps. Maple `SearchAll` and the OEIS PARI loop do the same. A Python `in` test would only decide A018826 existence.
- No hidden restriction on positivity, primality, or denominators.
- Boundary: n = 0 works; n = 1 is a suffix match; for n ≥ 2 a suffix match would require `2^k ∣ n(n-1)` with `k = bitlen(n)`, which forces n = 0 or 1. Powers of two give exactly one (prefix) hit.

No statement_mismatch. Proving a loophole was not available.

## Public prior proof

Artifact: https://github.com/KitaKen1/oeis-a076141-binary-word/blob/b4e179767fa3041c43e019b559ee77e6737317aa/lean/OeisA76141FC.lean

It proves `OeisA76141.a n ≤ 1` by:

1. Reducing `1 < a n` to two strictly ordered prefix starts in `binaryPattern (n^2)`.
2. Converting those list prefixes to arithmetic matches `(n^2 / 2^s) % 2^L = n`.
3. Ruling out the pure suffix s = 0 except n = 1, which cannot host two starts.
4. Overlap implying period d and `n / 2^d = n % 2^(L-d)`.
5. Packaging the two matches as block equations in radices built from powers of two.
6. Coprimality of `2^d - 1` with a complementary power of two, so the low block is nonzero for even and odd n.
7. An integer contradiction: the implied low remainder C cannot lie in `[0, 2T)`.

AI assistance on that artifact is disclosed by its author (OpenAI Codex). This worker used Cursor Grok 4.6 Extra High for the audit and kernel check, and did not submit the argument as original work.

## What this worker did not do

- Did not copy the proof into `A076141.lean` as a new development.
- Did not open a PR or edit OEIS.
- Did not set `independently_verified`. A second reviewer should read the public file and PR 5088.

Finite checks (`a n ≤ 1` for n ≤ 10^6, matching Israel; no hits with a(n) ≥ 2 through n = 10^6 in the overlapping convention) are consistent with the theorem and are not a proof.
