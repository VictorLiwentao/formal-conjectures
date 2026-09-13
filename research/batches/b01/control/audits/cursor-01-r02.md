# Independent audit: cursor-01-r02 / A109074

Audit date: 2026-09-13T02:14:03.498119+00:00

## Verdict

**PASS: independently verified Lean proof of the exact corrected frozen statement.** `A109074Proof.conjecture` compiled on Lean 4.33.1 with warnings treated as errors. Its complete transitive axiom closure is exactly `propext`, `Classical.choice`, `Quot.sound`. The natural-number division issue is explicitly resolved by a divisibility theorem and positivity; this is not merely a proof of an easier rational-product replacement.

Classification: `novel_mathematics=false`; known mathematics formalized. No prior public exact/equivalent Lean proof of the corrected statement was found in the bounded searches below. This does **not** establish first formalization or guarantee absence of unindexed/private/recent work. The old public counterexample concerns a different, subsequently corrected definition and shift.

## Immutable inputs and scope

- Candidate commit: `5e40973bec551bd85d8749fdc3b2c6b539130720`, fetched `origin/cursor/b01-cursor-01-r02-0918`.
- Worker seed: `1107856a264a066e316c3cba7b5339be475f6304`.
- Frozen upstream baseline: `a2f4a1bb12a28e04a969da78feefac7d1ce49565`.
- Frozen source: `FormalConjectures/OEIS/109074.lean`.
- Source SHA256: `cd5a2af1993d52ae29df9480d9304cbecae195e24d2ab51a45919806899cfd1e`.
- Candidate: `research/batches/b01/workers/cursor-01-r02/targets/A109074/A109074.lean`.
- Candidate SHA256: `59fee8b35957e320b4124f2120b98162b9078dcb723c8dc19b59dcd6142c1b57`.
- Live upstream `main` source read through GitHub API at audit time has the same SHA256 as the frozen source.
- Candidate-vs-seed changes are confined to its worker folder. Candidate-vs-baseline diff for `FormalConjectures`, `FormalConjecturesUtil`, `FormalConjecturesForMathlib`, `lean-toolchain`, `lake-manifest.json`, and `lakefile.toml` is empty.

## Independent compilation

Scratch directory: `/Users/wentaoli/Research/cursor01-r02-a109074-audit-hvlakk9b`.

The original source and candidate were extracted directly with `git show BASELINE:path` and `git show CANDIDATE:path`. The original module was freshly compiled into scratch; no admitted module olean from a worker was reused. Its single expected warning is preserved in `109074.log`. The candidate was then freshly elaborated against this scratch module, with warnings treated as errors. We reused compatible library oleans read-only from `/Users/wentaoli/.codex/worktrees/1974/formal-conjectures`; we did not rebuild all Mathlib dependencies or write to that cache.

Reproduction from the scratch directory:

```sh
export LEAN_NUM_THREADS=2
export LEAN_PATH="$(cat lean-path.txt)"
/Users/wentaoli/.elan/toolchains/leanprover--lean4---v4.33.1/bin/lean -o FormalConjectures/OEIS/109074.olean FormalConjectures/OEIS/109074.lean
/Users/wentaoli/.elan/toolchains/leanprover--lean4---v4.33.1/bin/lean -DwarningAsError=true research/batches/b01/workers/cursor-01-r02/targets/A109074/A109074.lean
```

Both commands exited 0. Candidate output, in `A109074.log`:

```text
'A109074Proof.conjecture' depends on axioms: [propext, Classical.choice, Quot.sound]
```

`lean-path.txt` puts scratch first and then the read-only cache and package library directories. `environment-checks.json` records that the toolchain, manifest, lakefile, every frozen utility/support source file, and all nine manifest package HEADs match the compatible cache. Mathlib revision is `0df444a360eaa60ab8c11dca51a86af692955474`.

## Exact statement and trust audit

The original namespace definitions are imported unchanged, rather than redeclared. The final theorem and the compiled explicit-type example are:

```lean
theorem A109074Proof.conjecture (n : ℕ) :
  OeisA109074.frac (n + 1) =
    (OeisA109074.b (n + 1) : ℚ) / (OeisA109074.b n : ℚ)
```

This is the same quantified type as `OeisA109074.conjecture`, including `n = 0`. The final proof does not use the original admitted conjecture: the complete axiom closure excludes `sorryAx`. It likewise excludes `Lean.trustCompiler` or any additional axiom; no candidate `native_decide`, new axioms, or modified source definitions are used. Some original source numerical examples use native decision procedures, but they are not in the candidate's dependency closure.

## Mathematical and division audit

Let `N(n)` be the product of `(6k−2)!(2k−1)!` for `1 ≤ k ≤ n`, and `D(n)` be `2^n` times the product of `(4k−1)!(4k−2)!`. The original `b n` is **natural division** `N(n)/D(n)`. Candidate `b_eq` is definitional equality to that exact expression.

The proof independently establishes `den_dvd_num : D(n) ∣ N(n)` for every `n`. It proves all factorial/product denominators nonzero, then derives `b_pos : 0 < b n`. Only after these steps does `b_cast_div` apply `Nat.cast_div`. Thus discarded remainders or rational division by zero cannot hide a gap.

Integrality is reduced to prime valuations via Legendre's factorial formula. The argument sums balance because `(6k−2)+(2k−1)=(4k−1)+(4k−2)` for the actual range `k ≥ 1`. For `p = 2`, simultaneous binary digit-sum bounds are proved by strong induction with even/odd recurrences. For odd prime powers `Q`, the floor-sum difference is decomposed into positive/negative residue counts, with `r = (2k−1) mod Q`. The involution `r ↦ Q−1−r` exchanges the relevant signs and preserves parity. The proof supplies the prefix inequalities and full-period identities; it does not assume an invalid termwise factorial divisibility inequality. Summing the floor bounds yields the required valuations.

Finally binomial expansion gives

`frac(n+1) = (6n+4)! (2n+1)! / (2 (4n+3)! (4n+2)!)`,

and product recurrences give precisely the same expression for `b(n+1)/b(n)`. All cancellations have nonzero hypotheses. The index shift, binomial denominators, factor `2`, and boundary `n = 0` agree with the frozen theorem.

This verifies the arithmetic product identity. The file does not formalize the entire combinatorial theorem that this product enumerates vertically symmetric alternating-sign matrices; that distinction should remain explicit in publication claims.

## Known mathematics and current public solution search

Primary mathematical evidence:

- [OEIS A109074](https://oeis.org/A109074) states the ratio conjecture involving A005156.
- [OEIS A005156](https://oeis.org/A005156/internal) identifies the VSASM sequence, credits Robbins and Kuperberg, and gives the same factorial product.
- [Razumov–Stroganov, arXiv:math-ph/0312071](https://arxiv.org/pdf/math-ph/0312071) gives the factorial product in equation (19), and immediately after equation (21) explicitly states the binomial ratio, crediting Robbins and its equivalence to Kuperberg's result. This is direct prior mathematical evidence, not merely numerical agreement.

Current searches used GitHub all-state issue/PR search, code search, repository search, live OEIS pages, the primary paper, and a local Mathlib text search. Raw query results and their hit URLs are preserved in `public-search.json`, `equivalent-search.json`, and `additional-pr-search.json`.

The all-state upstream searches for `109074`, `A005156`, and `134357` found the correction/discussion [PR 5231](https://github.com/google-deepmind/formal-conjectures/pull/5231), [issue 5024](https://github.com/google-deepmind/formal-conjectures/issues/5024), [issue 5225](https://github.com/google-deepmind/formal-conjectures/issues/5225), and an omnibus misformalization issue. None supplies a Lean proof of the corrected frozen target. Search details and read issue bodies are retained in scratch.

The strongest apparent prior Lean hit is [Kuberwastaken/c5-k4's Oeis109074Counterexample.lean](https://github.com/Kuberwastaken/c5-k4/blob/9ae8ed4872fa5c9955b3380c82dcda73de6630e3/lean/Oeis109074Counterexample.lean). Its matching research note was also read. It targets old upstream commit `b33d8678a28118c95d8d4f60b11faaf39ccff1e6`, where `b` was the Fuss–Catalan formula `choose(3n,n)/(2n+1)` and the shift was different. Its n=1 counterexample (1 versus 3) is valid for that old statement and unrelated to the corrected product theorem. The old counterexample was not recompiled because it proves no competing solution of the present statement.

Global code searches included the exact namespace, A005156, VSASM, vertically symmetric alternating sign, Kuperberg, Stroganov, and sequence numbers. Relevant namespace hits were the upstream admission and that old counterexample/cache. Remaining numeric/substring hits were in other problems or unrelated projects. Searches of Epoch `LeanOpenProblems-results` and DeepMind `alphaproof-nexus-results` found no corrected exact/equivalent proof; Epoch numeric hits belong to other named problem folders. A local Mathlib search for `alternating.sign.matrix|vertically.symmetric|Kuperberg|Stroganov|109074|005156|134357` returned no match at the pinned Mathlib revision.

Search absence is bounded evidence only. GitHub search does not establish universal absence of equivalent Lean work, particularly unindexed code or formulas described under other names. OEIS pending edits/editability remain unknown; no claim of editability is made.

## Attribution and remaining caveats

Candidate header and `proof.md` preserve `Copyright 2026 The Formal Conjectures Authors`, name the collective as original Lean formalizers, and credit Wentao Li for new proof development/write-up. They separately credit Robbins, Kuperberg and Razumov–Stroganov for prior mathematics, and disclose Cursor/Grok assistance. This is appropriate and does not claim new enumeration mathematics.

Minor non-blocking bibliography correction: worker `literature.md` calls Kuperberg's 2002 paper “Adv. Math.”; the primary Razumov–Stroganov bibliography gives **Annals of Mathematics 156 (2002), 835–866**. The proof itself and theorem status are unaffected. `proof.md`'s `candidate`/not-yet-independent wording accurately records the worker's pre-audit state; the independent verdict belongs in the coordinator audit record.

No worker, coordinator, upstream source, or shared cache was changed by this audit. No publication, PR, or first-formalization claim is authorized or implied by this report.

## Coordinator final documentation check

Final public tip `014dd479dea3dd68c172ce82371d8fc9c83b7644` corrects the Kuperberg bibliography to Annals of Mathematics 156 (2002), 835–866 and records independent review separately from worker self-review. Compared with independently audited `5e40973bec551bd85d8749fdc3b2c6b539130720`, only five Markdown/JSON documentation files changed; A109074.lean diff is empty. The live worker confirms no remaining goal or continuation timers and is stopped. No PR submitted.
