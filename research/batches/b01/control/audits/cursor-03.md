# Independent prior-solution audit: cursor-03 / A076141

Date: 2026-09-12. Reviewer: coordinator subagent `screen_arithmetic`.
Disposition: **TECHNICAL PASS — `prior_solution_found`; retire the target from new-research work.** The unmodified prior public proof independently compiled successfully with an allowlisted axiom closure. The additional exact-type wrapper elaborated and printed the same clean closure, but its strict command exited 1 solely because the temporary wrapper omitted a module docstring (details below).

## Scope and exact source

This audit concerns retirement of a research slot because of a prior public proof. It is not a new mathematical claim by this batch. The worker report was read from `origin/cursor/b01-cursor-03-91b3:research/batches/b01/workers/cursor-03/targets/A076141/literature.md`.

Frozen target: `FormalConjectures/OEIS/76141.lean`, namespace `OeisA76141`, declaration `conjecture`, at batch baseline `a2f4a1bb12a28e04a969da78feefac7d1ce49565`. Independently computed source SHA-256: `7954f35f38ed7da506eefc949c1d401e99625a70406561413198c467e63d4c78`, matching the assignment.

The intended statement is `∀ n : ℕ, OeisA76141.a n ≤ 1`. Here `a` counts all prefix matches over `binaryPattern (n ^ 2).tails`, so overlapping positions are included. The zero case uses the word `[0]`. No primality, positivity, nonoverlap, or termination assumption is present.

## Prior public evidence

- [Exact public proof](https://github.com/KitaKen1/oeis-a076141-binary-word/blob/b4e179767fa3041c43e019b559ee77e6737317aa/lean/OeisA76141FC.lean#L1229-L1253).
- [Pinned public commit](https://github.com/KitaKen1/oeis-a076141-binary-word/commit/b4e179767fa3041c43e019b559ee77e6737317aa), GitHub API author/committer date `2026-08-21T14:35:11Z`.
- [Upstream PR 5088](https://github.com/google-deepmind/formal-conjectures/pull/5088), created `2026-08-21T14:54:44Z`, open and unmerged at this audit. It links the exact theorem and credits KitaKen1 (Kenta Kitamura), with disclosed Codex assistance.

I independently downloaded the raw file at that commit, rather than relying on the worker's downloaded copy. It has 1,255 lines and SHA-256 `98c14f27728c9ce1779fa45567770ee25608c1180b9a03ad697d87241e04a7e0`.

At line 1229 it declares:

```lean
theorem oeis_a76141_solved (n : ℕ) : OeisA76141.a n ≤ 1 := by
  ...
```

The sole import is the exact upstream OEIS module. No redefinition of `OeisA76141.a` or `binaryPattern` occurs. The proof explicitly handles `n = 0`; for positive n it extracts two ordered matching positions, converts them into overlapping binary blocks, derives a periodicity identity and contradictory integer block constraints. The helper hypotheses are derived inside the final proof; none remains as a final assumption.

A lexical search found no `sorry`, `axiom`, `native_decide`, or `unsafe` token and no reference to `OeisA76141.conjecture` in the downloaded proof. This lexical inspection supplements, and does not replace, the dependency-closure axiom check.

## Independent compilation and exact-type check

Temporary audit directory: `/tmp/cursor03-independent-audit-frny9zkq`.
Lean binary: `/Users/wentaoli/.elan/toolchains/leanprover--lean4---v4.33.1/bin/lean`.
`LEAN_NUM_THREADS=2`. Dependencies were read only from `/Users/wentaoli/.codex/worktrees/1974/formal-conjectures/.lake`; all nine package Git hashes independently matched the coordinator's `lake-manifest.json`. The cached utility source and toolchain also matched the coordinator. The temporary audit directory is first on `LEAN_PATH`, followed by the cached main library and each package's build library; the exact path is recorded in `reproduction.json` in the temporary directory.

The frozen target source was copied into the isolated directory and compiled there, then the byte-identical public proof was compiled there. No `lake build`, package update, active worktree source mutation, or shared-cache write was performed.

With the recorded environment and temporary directory as cwd, the exact compiler invocations were:

```text
/Users/wentaoli/.elan/toolchains/leanprover--lean4---v4.33.1/bin/lean -o /tmp/cursor03-independent-audit-frny9zkq/FormalConjectures/OEIS/76141.olean /tmp/cursor03-independent-audit-frny9zkq/FormalConjectures/OEIS/76141.lean
/Users/wentaoli/.elan/toolchains/leanprover--lean4---v4.33.1/bin/lean -o /tmp/cursor03-independent-audit-frny9zkq/OeisA76141FC.olean /tmp/cursor03-independent-audit-frny9zkq/OeisA76141FC.lean
/Users/wentaoli/.elan/toolchains/leanprover--lean4---v4.33.1/bin/lean -DwarningAsError=true /tmp/cursor03-independent-audit-frny9zkq/ExactTypeAudit.lean
```

Full logs are `target-compile.log`, `public-proof-compile.log`, and `exact-type-compile.log` in that temporary directory. The decisive outputs are preserved below because temporary files are not permanent batch artifacts.


The frozen target compiled with exit code 0 (only the expected warning for its original admitted conjecture). The unmodified public proof compiled with exit code 0. Warnings concerned only unused variables and tactic style. Its printed dependency closure is exactly:

```text
'oeis_a76141_solved' depends on axioms: [propext, Classical.choice, Quot.sound]
```

Thus the imported `sorry` theorem and the module's `native_decide` test lemmas do not contaminate the final proof. No `sorryAx` or `Lean.trustCompiler` appears in the final closure.

A separate exact-type wrapper was checked with warnings treated as errors:

```lean
import OeisA76141FC

#check @OeisA76141.conjecture
#check @oeis_a76141_solved

theorem cursor03_exact_type_audit : type_of% @OeisA76141.conjecture :=
  oeis_a76141_solved

#print axioms OeisA76141.conjecture
#print axioms oeis_a76141_solved
#print axioms cursor03_exact_type_audit
```

The `type_of%` expression uses the original declaration solely to extract its proposition, not its proof body. The separate check printed:

```text
OeisA76141.conjecture : ∀ (n : ℕ), OeisA76141.a n ≤ 1
oeis_a76141_solved : ∀ (n : ℕ), OeisA76141.a n ≤ 1
'OeisA76141.conjecture' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
'oeis_a76141_solved' depends on axioms: [propext, Classical.choice, Quot.sound]
'cursor03_exact_type_audit' depends on axioms: [propext, Classical.choice, Quot.sound]
```

The wrapper theorem therefore elaborated against the exact original type and its closure excluded `sorryAx`. **The strict wrapper command itself exited 1**, because `-DwarningAsError=true` promoted the missing module-docstring style warning to an error. No type error, unsolved goal, or proof-dependency error was reported. This ancillary style failure is not represented as a clean standalone compile. The unmodified public proof's separate exit-0 compilation and exact type/axiom output already establish the retirement criterion.

## Status interpretation

An open upstream label or unmerged PR does not negate an exact prior proof. The independently reproduced public proof establishes the exact frozen proposition with no extra hypotheses and only the allowed axioms. The appropriate target status is `prior_solution_found`, not a new `candidate_proof` or new mathematical resolution by this batch. No PR, push, OEIS edit, or author communication was performed.
