# Independent audit: Green66 known trivial bound

Date: 2026-09-13T02:45:20.387411+00:00

## Verdict

**PASS for independent candidate compilation and axiom closure.** `Green66TrivialBound.trivial_bound` is a proof of the exact frozen known quarter-power bound, with a single constant `C = 10` and threshold `X ≥ 1`. It does not solve the open Green66 fixed-constant `1/10` question. Classification: `novel_mathematics=false`, `known_mathematics_formalization`. No first-formalization priority is established.

**Exact-type machine check PASS.** The independent `ExactTypeAudit.lean` uses `Lean.Meta.isDefEq` on the original and candidate declaration types. It exited 0 with warnings-as-errors and printed `PASS: candidate type is definitionally equal to exact frozen theorem type`; the axiom closure was checked again.

## Inputs and reproducibility

- Frozen baseline: `a2f4a1bb12a28e04a969da78feefac7d1ce49565`.
- Worker seed: `486f35dcee50c2c32b98f946726adbd20f6a5fbf`.
- Fetched candidate tip: `85c399a1f05a3627ec5eea6884c9958e6f84d413`, branch `cursor/b01-cursor-07-r03-ceef`.
- Frozen source: `FormalConjectures/GreensOpenProblems/66.lean`.
- Source SHA256: `d38ab7e233260302ef58121037a02dc94866ddae820e9fc84308ce7264e07acb`.
- Candidate: `research/batches/b01/workers/cursor-07-r03/targets/Green66-trivial-bound/Green66.lean`.
- Candidate SHA256: `20e98a7695ed2327099ed3f3d46d6394aea552aa02354287eacf65d0bfb13929`.
- Scratch: `/Users/wentaoli/Research/cursor07-r03-green66-audit-5z9kl7ik`.

Both source and candidate were extracted directly from their immutable Git commits. `environment-checks.json` confirms no upstream source/support/toolchain/manifest change in the worker commit; seed-to-candidate edits are confined to its worker folder. Current upstream main source, retrieved afresh through GitHub API, has the same source hash.

The cache at `/Users/wentaoli/.codex/worktrees/1974/formal-conjectures` was used read-only. Toolchain, lakefile, manifest, utility/support sources and all nine manifest package HEADs match the frozen baseline. Mathlib revision is `0df444a360eaa60ab8c11dca51a86af692955474`. No worker-produced olean was reused, and no shared cache was written.

Reproduction from scratch:

```sh
export LEAN_NUM_THREADS=2
export LEAN_PATH="$(cat lean-path.txt)"
/Users/wentaoli/.elan/toolchains/leanprover--lean4---v4.33.1/bin/lean -o FormalConjectures/GreensOpenProblems/66.olean FormalConjectures/GreensOpenProblems/66.lean
/Users/wentaoli/.elan/toolchains/leanprover--lean4---v4.33.1/bin/lean -DwarningAsError=true -o research/batches/b01/workers/cursor-07-r03/targets/Green66-trivial-bound/Green66.olean research/batches/b01/workers/cursor-07-r03/targets/Green66-trivial-bound/Green66.lean
/Users/wentaoli/.elan/toolchains/leanprover--lean4---v4.33.1/bin/lean -DwarningAsError=true ExactTypeAudit.lean
```

All three final commands exited 0. `compile-0.log` preserves the two expected source `sorry` warnings; the original admitted source cannot be compiled with warnings-as-errors without those expected warnings becoming errors. The candidate used warnings-as-errors and exited 0. `compile-1.log` records:

```text
'Green66TrivialBound.trivial_bound' depends on axioms: [propext, Classical.choice, Quot.sound]
```

The complete transitive closure therefore excludes `sorryAx`, extra axioms, native-decision/compiler trust axioms, and admitted source-theorem dependence. The original source is used for the unchanged predicate, not as a proved result. Candidate disables only two style/unused-section lint options; no kernel checks are disabled. Cached Mathlib dependencies were not rebuilt from source. The first auditor-authored metaprogram wrapper had an API/context error and missing module docstring; this was corrected without any candidate change. Its log is retained as `exact-type-audit-first.log`; the successful final output is `exact-type-audit.log`.

## Exact type and mathematics

Both original and candidate have the proposition:

```lean
∃ C > (0 : ℝ), ∀ᶠ X : ℝ in Filter.atTop,
  ∃ n : ℕ, Green66.IsSumOfTwoSquares n ∧
    (n : ℝ) ∈ Set.Icc (X - C * X ^ (1 / 4 : ℝ)) X
```

`C` precedes the eventual real quantifier, so it is uniform in `X`. The exponent is real `rpow`; the interval is backward and closed; the sum-of-squares witnesses are natural numbers. No integer-only or forward-interval substitute is used. Small/negative `X` need not satisfy an eventual proposition, and threshold 1 is explicit.

For `X ≥ 1`, choose `u = floor(sqrt X)`, `R = X − u²`, `v = floor(sqrt R)`, `n = u²+v²`. The greatest-square inequalities imply `R ≥ 0`, `n ≤ X`, and `X−n < 2 sqrt R+1`. They also give `R < 2 sqrt X+1 ≤ 3 sqrt X`. Consequently `sqrt R ≤ sqrt 3 · sqrt(sqrt X) ≤ 2 X^(1/4)`, and `X^(1/4) ≥ 1`. Thus the gap is bounded by `5 X^(1/4)`, which in particular gives the chosen `10 X^(1/4)`. Every square-root multiplication, squaring, and rpow identity carries the relevant nonnegativity hypothesis. Perfect-square inputs and zero remainder are permitted.

The proof is mathematically sound as a generous uniform bound; it makes no optimal-constant claim. `proof.md` describes this argument and its quantifiers accurately. The code's original formalizer collective and Wentao Li credits are preserved, and it explicitly identifies the elementary mathematics as known rather than attributing discovery to Green or Wentao Li.

## Current bounded public-proof search

[Ben Green's primary problem list](https://people.maths.ox.ac.uk/greenbj/papers/open-problems.pdf), problem 66, printed page 32 / PDF index 31, explicitly records the known quarter-power bound and the successive-square argument. Thus this is prior mathematics, independent of whether the Lean library labels it solved.

Search results are saved in `public-search.json`, and relevant exact source/PR bodies are retained under `search-hits/`. Current all-state upstream issue/PR searches included `GreensOpenProblems/66`, `green_66`, and Bambah. Inspected:

- [PR4398](https://github.com/google-deepmind/formal-conjectures/pull/4398): the current statement formalization with `sorry` for both the open question and known bound.
- [PR1729](https://github.com/google-deepmind/formal-conjectures/pull/1729): an older statement draft, also admitted.
- [PR1847](https://github.com/google-deepmind/formal-conjectures/pull/1847): a related forward-interval Bambah–Chowla draft; all corresponding bounds use `sorry`, and its prose inaccurately calls some known implications open. It supplies no competing Lean proof.

Global exact-name code search found the source and an [awesome_theorems catalog row](https://github.com/weiyangzen/awesome_theorems/blob/32e5f75412a804463a0b0c6fff1362d4ab5275b3/Docs/catalog/v5/curation/frontier_theorem_reviews_v5_5/nonerdos_171_254.jsonl). The row was read: it catalogs known mathematics and grants no new-theorem credit; it cites no exact Lean proof artifact.

Equivalent-result checks:

- [LeanGenius Erdos222Problem.lean](https://github.com/rjwalters/lean-genius/blob/main/proofs/Proofs/Erdos222Problem.lean) was fetched and read. Its `bambah_chowla_upper_bound` is declared as an **axiom**, as is its indexed sum-of-squares sequence. Downstream theorems are not an admissible proof of this bound.
- Epoch's `oeis_275409_conjecture_0/Submission/Spec.lean`, exact blob `50edcd344d5fcbf633ba3fef760acca7fbd845f9`, was independently fetched and read. Lines 11938–11958 give a natural-number **forward O(sqrt X)** result, despite the Bambah–Chowla name. This is not an equivalent fourth-root result. Saved as `search-hits/Epoch-275409-Spec.lean`.
- Current code searches of Epoch results and AlphaProof Nexus results for `green_66` returned no matches. Global Bambah/Chowla searches found no additional relevant exact proof; Chowla hits concern unrelated problems. GitHub search is incomplete in principle and can miss known raw-file hits, so absence is not treated as a guarantee.
- Local pinned Mathlib search for Bambah, Chowla and two-square gap wording found no match. Its existing sum-of-two-squares and square-root lemmas provide ingredients, not an identified exact interval theorem.

No prior public exact/equivalent completed Lean proof was found in this bounded screen. We did not compile the axiom-based, admitted, or weaker unrelated files. There is no universal absence claim, no first-formalization guarantee, and no OEIS editability claim.

## Limitations and disposition

This audit concerns only `Green66.green_66.variants.trivial_bound`. The open `Green66.green_66` remains untouched and unproved by this work. Upstream source/support code and all worker artifacts were unchanged by the auditor; only scratch files were written. No PR, publication, or attribution of new mathematics follows from this audit.
