# Independent audit: cursor-01 / A237271

Audit date: 2026-09-13 UTC. Auditor: a separate Codex audit agent; no worker proof edits.

## Revision and exact target

- Worker commit: `21ab4c4e7022292d2fabc9d30a08252a410fd547` on `cursor/b01-cursor-01-8a28`.
- Frozen source commit: `a2f4a1bb12a28e04a969da78feefac7d1ce49565`.
- Proof: `research/batches/b01/workers/cursor-01/targets/A237271/A237271.lean`.
- Proof SHA-256: `835bd9ec5019dff7c03ccbdb4d42eddcef904897b25c275913841a9368f09b06`.
- Source: `FormalConjectures/OEIS/237271.lean`.
- Source SHA-256: `4f5f9875d35bc3f009af89444945296942a5967d1f8af20a4a102460227da11b`.

The target is exactly

```lean
∀ (k : ℕ), IsCarmichael k → 3 ≤ OeisA237271.a k
```

The candidate declaration is `OeisA237271.Cursor01.observation_carmichael`.
It uses the upstream `a` and `IsCarmichael` definitions without redefining or weakening them.
The worker adds a stronger theorem for every odd composite and derives the exact target.
The source/utility/dependency files have no diff from the frozen source commit. Changes
relative to coordination seed `238f78bdd5701ae4c97a0d70d4e22e2d45770d7a`
are restricted to `research/batches/b01/workers/cursor-01/`.

## Mathematical and source audit

[OEIS A237271](https://oeis.org/A237271/internal), retrieved independently on this audit,
records Omar E. Pol's October 21, 2025 finite empirical Carmichael observation.
The frozen Lean proposition is its unrestricted generalization. The divisor counting
definition matches Amiram Eldar's December 22, 2024 Mathematica program on the page.
The public page does not expose authenticated pending edit status; editability is unknown.

`IsCarmichael` quantifies over coprime positive bases; `Nat.FermatPsp` includes
compositeness. It does not have the earlier impossible all-nonzero-residue hypothesis.
Carmichael numbers are odd composites: use base 1 for compositeness; for an even
Carmichael number use base k−1 to force k to divide 2, a contradiction.
For an odd composite, the increasing divisor list has at least three entries.
Its first consecutive pair and last consecutive pair are distinct. Both contribute
to `a`: the first starts at 1, the last ends at k and starts at a proper divisor.
Thus the count is at least two. This argument is sound and has no extra target hypothesis.

The upstream source module contains unrelated `sorry` declarations and native-decided
small tests. That alone does not taint this proof: the final theorem's transitive axioms
must exclude those declarations. The proof source has no admissions or native decisions
and does not apply the upstream admitted target or `conjecture_2`.

## Independent compilation

Status: **INDEPENDENTLY VERIFIED exact Lean proof**, classified as known mathematics
with a newly developed Lean proof. The attribution correction in `7a2f94d8` is accepted.

Fresh source-module compile: exit 0, six expected warnings for the frozen repository's
admitted statements. Fresh candidate compile: exit 0 with `-DwarningAsError=true`, no
warnings. The exact-type `example` inside the candidate compiled. Output:

```text
'OeisA237271.Cursor01.observation_carmichael' depends on axioms: [propext, Classical.choice, Quot.sound]
'OeisA237271.Cursor01.a_ge_three_of_odd_composite' depends on axioms: [propext, Classical.choice, Quot.sound]
observation_carmichael : ∀ (k : ℕ), IsCarmichael k → 3 ≤ a k
```

This full transitive axiom closure excludes `sorryAx`, native/compiler axioms, and
custom axioms. The proof is not circular through the admitted upstream target.
Candidate output is retained in scratch `A237271.log`; source output in `237271.log`.
The separate source-only `type_audit.lean` command also completed with exit 0,
printing the exact frozen type. Its output is retained in scratch `type_audit.log`.
All three stages of the isolated audit pipeline finished successfully.

Isolated scratch directory: `/Users/wentaoli/Research/cursor01-audit-xuzpu_d5`.
The three Lean files were extracted with `git show <worker-commit>:<file>`.
The source module is freshly compiled to an olean in that isolated directory;
the worker proof and type audit are then independently elaborated with warnings as errors.
The first source-module attempt also used warnings as errors and failed solely because the
unchanged upstream statement contains known admissions; its six messages are retained in
`237271-first-warnings-as-errors.log`. Repeating that source compilation with ordinary
warning handling is appropriate; transitive axiom checks on the candidate are decisive.
No existing worker directory, source, shared cache, or dependency was modified.

Read-only cache: `/Users/wentaoli/.codex/worktrees/1974/formal-conjectures`.
Its utility and `FormalConjecturesForMathlib` source contents match the frozen baseline
(`git diff <frozen-commit> -- <those paths> lean-toolchain lake-manifest.json` is empty).
All nine dependency checkout HEADs match `lake-manifest.json`, including Mathlib
`0df444a360eaa60ab8c11dca51a86af692955474`.

Reproduction uses `LEAN_NUM_THREADS=2`, with `LEAN_PATH` consisting, in order, of the
scratch directory, the cache's `.lake/build/lib/lean`, and each cache
`.lake/packages/<package>/.lake/build/lib/lean`. The exact value is retained in
`scratch/lean-path.txt`. The binary is
`/Users/wentaoli/.elan/toolchains/leanprover--lean4---v4.33.1/bin/lean`.
From the scratch directory run:

```sh
lean FormalConjectures/OEIS/237271.lean -o FormalConjectures/OEIS/237271.olean
lean -DwarningAsError=true research/batches/b01/workers/cursor-01/targets/A237271/A237271.lean
lean -DwarningAsError=true research/batches/b01/workers/cursor-01/targets/A237271/type_audit.lean
```

## Prior proof, novelty, and credit

[DeepMind PR #5447](https://github.com/google-deepmind/formal-conjectures/pull/5447),
opened September 10, 2026 by GitHub user `j2d9w5xtjn-png`, already contains the same
odd-composite argument and Carmichael oddness argument. It explicitly describes a Lean
formalization as future work. The PR was open with no comments at this audit.
This is **formalization of known mathematics**, not a new mathematical discovery.

Independently retrieved upstream `237271.lean` has the same SHA-256 as the frozen file;
it still labels the target open and leaves it `sorry`. A GitHub issue search for the
exact declaration found only #4974, #4987, and #5447. No earlier exact Lean proof was
identified in these checks. This is bounded negative evidence, not a guarantee of global
formalization priority; the worker's wider literature audit was reviewed but not every
external artifact in it was rebuilt in this independent audit.

The existing header correctly retains The Formal Conjectures Authors' copyright and
Wentao Li's development credit. However, `proof.md` only mentions the number #5447,
without its author or link, and starts with “New proof development and write-up”.
Before publication, explicitly credit the prior informal argument to the linked PR and
its author, describe Wentao Li's work as Lean proof implementation/formalization, and
retain AI assistance disclosure. Do not credit Wentao Li with first discovery of the math.
This attribution/documentation correction is separate from kernel proof validity.

The worker subsequently fixed this gap in commit
`7a2f94d822d3bdef3aceaa1fafc54ed99e828b8c`. Independent `git diff` inspection confirms
that the Lean file differs only inside its initial copyright/attribution block comment;
all imports, definitions, statements, tactics, and audit commands are unchanged.
Its revised SHA-256 is
`4315ca7c9c058fd9beeb35bbf7bc66c6f1f8b4bc81b12d4aa3222baea296591e`.
The revised header and `proof.md` explicitly name and link the prior informal proof,
retain collective formalization credit and Wentao Li's Lean development credit,
and explicitly disclaim new mathematical discovery. The attribution issue is resolved
in this revision. The fresh elaboration described above is on the original commit's
mathematically identical Lean contents; the comment-only revision was not rebuilt.
