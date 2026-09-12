# A076141 literature and novelty audit

Worker: cursor-03. Target: `OeisA76141.conjecture`. Audit date: 2026-09-12.

## Frozen statement

- Source: `FormalConjectures/OEIS/76141.lean`
- SHA-256 (working tree and assignment pin): `7954f35f38ed7da506eefc949c1d401e99625a70406561413198c467e63d4c78`
- DeepMind pin cited by the public proof README: same SHA at Formal Conjectures commit `e13dd7284e72012a1616806d09cb6b8025e387af`
- Exact type compiled in this tree:

```text
OeisA76141.conjecture : ∀ (n : ℕ), OeisA76141.a n ≤ 1
```

Upstream body is `fun n => sorry`. `#print axioms` on that declaration includes `sorryAx`.

## Live OEIS

- Entry: https://oeis.org/A076141
- Internal/JSON: https://oeis.org/A076141/internal and https://oeis.org/search?q=id:A076141&fmt=json
- Retrieved 2026-09-12. JSON `revision` 21, `time` 2018-07-11T20:12:54-04:00. Keyword `nonn,base`. Offset 0. Author Reinhard Zumkeller, 2002-10-31.
- Name: number of times n occurs as a binary sub-pattern of n^2.
- Comment posing the problem: `is a(n)<=1 for all n?`
- Further comments: not multiplicative (`a(5)=0`, `a(29)=0`, `a(145)=1`); `a(n) <= 1` for `n ≤ 10^6` (Robert Israel, 2018-07-11).
- Programs: Maple `StringTools:-SearchAll` and PARI check every alignment. Both count overlapping starts, matching `List.tails.countP`.
- b-file: https://oeis.org/A076141/b076141.txt (n = 0..10000). Retrieved 2026-09-12.
- History page https://oeis.org/A076141/history returned 404. History coverage is therefore incomplete.
- Editability: unknown. No login. Public JSON has no draft field. Page status is approved. This is not a novelty criterion.

Related OEIS, not the assigned theorem:

- https://oeis.org/A018826 numbers n whose binary word is a substring of that of n^2. Existence, not multiplicity.
- https://oeis.org/A136510 smallest k>1 such that n appears in n^k in binary. The comment `A136510(A018826(n))=2` is the existence statement, not a proof that A076141 is at most 1.
- A018826 construction `x^2 ≡ 8x+1 (mod 2^m)` produces some positive terms; it does not bound multiplicity.

## Formal Conjectures / DeepMind

- File added in google-deepmind/formal-conjectures commit `1bb238f2be` (2026-08-20), “Add more conjectures from AutoOeis (#5016)”.
- Issues/PR search for A076141 / 76141 / OeisA76141 on 2026-09-12 found one relevant item: open PR https://github.com/google-deepmind/formal-conjectures/pull/5088 “Mark OEIS A076141 as solved” (2026-08-21). No review comments. Upstream statement is still `research open` on the frozen commit.
- No AlphaProof Nexus OEIS output named A076141: https://github.com/google-deepmind/alphaproof-nexus-results (APNOutputs/OEIS listing, 2026-09-12).

## Epoch

Three public runs of `oeis_a076141_conjecture` exist. None is an accepted proof. Failed attempts are not a novelty proof.

- Isolated target: https://github.com/epoch-research/LeanOpenProblems/blob/main/apn/data/oeis/Isolated/oeis_a076141_conjecture.lean
- ant: https://github.com/epoch-research/LeanOpenProblems-results/tree/main/runs/oeis-full-50usd-ant-j0j0g4uzligm1k41/oeis_a076141_conjecture — SafeVerify failed; `sorryAx`
- oai: https://github.com/epoch-research/LeanOpenProblems-results/tree/main/runs/oeis-full-50usd-oai-jajpvieznaevpoyg/oeis_a076141_conjecture — same `sorryAx` failure
- gdm: https://github.com/epoch-research/LeanOpenProblems-results/tree/main/runs/oeis-full-50usd-gdm-1s7vwp2si1ap0r6d/oeis_a076141_conjecture — compile_submission failed with unsolved goals after a long overlapping-match case analysis

## Public exact proof (stop condition)

Public repository: https://github.com/KitaKen1/oeis-a076141-binary-word

Cited commit: `b4e179767fa3041c43e019b559ee77e6737317aa`

Proof file: https://github.com/KitaKen1/oeis-a076141-binary-word/blob/b4e179767fa3041c43e019b559ee77e6737317aa/lean/OeisA76141FC.lean#L1229-L1253

Theorem:

```lean
theorem oeis_a76141_solved (n : ℕ) : OeisA76141.a n ≤ 1
```

This is the frozen proposition. It imports `FormalConjectures.OEIS.«76141»` and does not use `OeisA76141.conjecture`. The file has no `sorry`, `axiom`, `native_decide`, or `unsafe` tokens.

Kernel check in this worker tree (Lean `v4.33.1`, existing `FormalConjectures.OEIS.76141` olean):

```sh
lake env lean /tmp/OeisA76141FC.lean
```

Exit code 0. `#print axioms oeis_a76141_solved` reported `[propext, Classical.choice, Quot.sound]`. Warnings were unused-variable / tactic-style only.

The author’s pin is Lean v4.27.0 and Formal Conjectures `e13dd728…`. The target file SHA matches this batch’s pin.

PR 5088 only retags the upstream file and links that URL. It is open, not merged, and has no human review. The batch rule is to stop when an exact prior solution exists, not to reproduce it as a new result. Independent review is still required before a public “solved” claim.

## Other literature

Searches on 2026-09-12 (assertion, not only the ID):

- arXiv: “binary sub-pattern”, “A076141”, “substring of its square” / binary. Hits such as [arXiv:2203.05451](https://arxiv.org/abs/2203.05451) and [arXiv:math/0402458](https://arxiv.org/abs/math/0402458) concern digit sums of n and n^2, not infix multiplicity.
- MathOverflow API search for “n substring of n^2 binary”: no items.
- Kuberwastaken/c5-k4: no A076141 hit in a name listing / code search (rate-limited retry not exhaustive).
- OpenAlex citation blob in Epoch metadata for A076141: empty citations.

## Inaccessible or incomplete sources

- OEIS HTML history URL 404.
- Some OEIS HTML fetches hit Cloudflare; JSON/internal/b-file succeeded.
- arXiv API returned HTTP 429 on one query; browser/search snippets were used instead.
- GitHub code search returned HTTP 429 on some retries; PR/issue and raw-file fetches succeeded.

“No other match” means no other public solution was found in the sources above. It is not a proof that no other write-up exists.
