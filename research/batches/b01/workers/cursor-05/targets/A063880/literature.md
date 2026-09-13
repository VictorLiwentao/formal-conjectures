# A063880 literature and novelty audit

Worker: cursor-05. Date of this audit: 2026-09-13 (UTC). Exclusive target: OEIS A063880.

## Frozen statement

- File: `FormalConjectures/OEIS/63880.lean`
- SHA-256: `b50d00e13735613cbe37bd3a25c19130874e8f036ca2a0e3c1aceb177a33c683` (verified on this checkout)
- Source baseline: `a2f4a1bb12a28e04a969da78feefac7d1ce49565`
- Declarations: `OeisA63880.mod_216_of_a`, `OeisA63880.unique_primitive_108`
- Lean: `leanprover/lean4:v4.33.1`

## Formalization vs intended mathematics

The Lean predicate `A n` is `0 < n ∧ σ 1 n = 2 * usigma n`, with `usigma` the sum of divisors `d ∣ n` satisfying `gcd(d, n/d) = 1`. This matches OEIS A063880: numbers `k` such that `σ(k) = 2 * usigma(k)`. Equivalently, the unitary and non-unitary divisor sums are equal.

The extra `0 < n` is necessary. In Lean, `σ 0 = 0` and `usigma 0 = 0`, so the equality holds at `0` unless positivity is required. The sequence is a list of positive terms, so this is not a loophole.

Nonvacuity: the file already proves `A 108`, `A 540`, `A 756`, and `IsPrimitiveTerm 108`.

The congruence `n % 216 = 108` is exactly `n ≡ 108 (mod 216)`. Independently, this is equivalent to `n ≡ 4 (mod 8)` and `27 ∣ n`, i.e. `padicValNat 2 n = 2` and `3 ≤ padicValNat 3 n` for `n ≠ 0`. That equivalence is proved in this worker's Lean file. It does not by itself prove the conjecture.

`IsPrimitiveTerm n` is primitivity in `{n | A n}` with respect to divisibility: `n ∈ A` and no proper divisor of `n` is in `A`. That matches Eldar's OEIS comment.

## OEIS A063880

- URL: https://oeis.org/A063880
- Internal: https://oeis.org/A063880/internal
- Related: https://oeis.org/A097702, https://oeis.org/A097703, https://oeis.org/A276378, https://oeis.org/A034448
- Direct fetch of oeis.org from this VM on 2026-09-13 returned Cloudflare 403/challenge HTML. Content below is from web-search snapshots of the live pages on 2026-09-12/13, including the internal `%I #39 Aug 31 2024 04:33:09` record.

Comments used:

- Ralf Stephan, 7 Jul 2003: terms so far are `≡ 108 (mod 216)`, confirmed to `10^7` by Robert G. Wilson v.
- Amiram Eldar, 30 Sep 2019: equivalent to equal unitary and non-unitary divisor sums.
- Amiram Eldar, 31 Aug 2024: primitives are powerful; other terms are `m * s` with `m` primitive and `s` squarefree coprime to `m`; only primitive below `10^18` is `108`; if there are no other primitives then `a(n) = 108 * A276378(n)`.

A097702 is `(A063880(n) - 108)/216`. Eldar (31 Aug 2024) proves: *if* `m = 216k + 108` is in A063880, then `2k+1` is squarefree and coprime to 6. That is the implication from the congruence plus the ratio formula, not a proof that every A063880 term is `≡ 108 (mod 216)`. The page still records that integrality of A097702 is conjectural (checked to `10^6`).

Editability: unknown. The public page is STATUS approved, last revision #39 on 2024-08-31. Unauthenticated/Cloudflare-blocked fetch does not show a pending draft or an edit form. This is not a novelty criterion.

## DeepMind formal-conjectures

- Added in PR #1877, commit `fcd975e61bcc4e3438b1ea86be7385a0f0263d43`, 2026-01-28, resolving issue #1455.
- The theorems remain `sorry` / `research open` on that commit and on this pin.
- GitHub code search for later proofs of A063880/63880 in `google-deepmind/formal-conjectures` did not return a proof PR. Other OEIS proof issues (#4252, #5027, #5028) are unrelated sequences.

## AlphaProof Nexus and Epoch

- https://github.com/google-deepmind/alphaproof-nexus-results README: the repo contains only successful AlphaProof Nexus proofs. Unauthenticated GitHub code search for `63880` in that repo returned no paths. README maps attempted OEIS problems to the `auto_oeis` branch of formal-conjectures; this worker did not find an A063880 success file.
- Epoch LeanOpenProblems / LeanOpenProblems-results: GitHub code search for `A063880` / `63880` returned no hits in this session.

## Other literature

- MathOverflow hits on unitary perfect numbers (`σ*(n) = 2n`) and related σ/σ* identities are a different equation. No exact proof of `σ(n) = 2 usigma(n) ⇒ n ≡ 108 (mod 216)` was found.
- arXiv hits on bounds for `σ*` and unitary perfect numbers (e.g. 0910.2798, 1312.4615, 2605.20475) do not resolve A063880.
- Public c5-k4 (`Kuberwastaken/c5-k4`) is instructed as already having searched powerful cores. This worker did not repeat that search and does not claim uniqueness of 108 or the primitive decomposition as new.

## Novelty conclusion

No public exact proof or disproof of the frozen theorems was found in the sources checked above. That is not an exhaustive literature clearance. Primitive decomposition and the “only primitive below 10^18 is 108” computation are already known and are not claimed as a new resolution.

Partial lemmas, finite leftover enumerations, and Eldar’s conditional comments are not a new resolution.
