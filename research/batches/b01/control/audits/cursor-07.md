# Independent audit: cursor-07 / WOWII31

Audit date: 2026-09-13 UTC. Worker and coordinator files/caches were not modified.

## Candidate verdict

**Independent compilation PASS.** Exact frozen proposition is proved by
`WOWII31.conjecture31`. `novel_mathematics=false`; `first_formalization=false`. This is known mathematics. A prior public Lean proof was
also found independently; do not classify the worker artifact as the first formalization.

Worker commit: `54991f4be3792b20410a15dd905991d3c08a127b`.
Frozen baseline: `a2f4a1bb12a28e04a969da78feefac7d1ce49565`.
Worker proof path: `research/batches/b01/workers/cursor-07/targets/WOWII31/WOWII31.lean`.
Proof SHA-256: `6a6902d2bac9f7f65cda0df8c6e9e487779ee4705e8fafbf3b39bd0fd428860f`.
Source path: `FormalConjectures/WrittenOnTheWallII/GraphConjecture31.lean`.
Source SHA-256: `0c49c9a24c81a764e8bed251442f4e5cbda0ec7b22da2a1fcb04cb3ad02d8092`.
The live upstream file retrieved during this audit has the same source SHA-256.

The original declaration is `WrittenOnTheWallII.GraphConjecture31.conjecture31`.
Its exact type, also present as a successfully compiled example in the candidate, is:

```lean
∀ {α : Type*} [Fintype α] [DecidableEq α] [Nontrivial α]
    (G : SimpleGraph α) [DecidableRel G.Adj], G.Connected →
      2 * (G.radius.toNat : ℤ) - 1 ≤ (SimpleGraph.path G : ℤ)
```

The candidate imports only `FormalConjecturesUtil`; it does not import or apply
the admitted source theorem. It defines no replacement radius/path/induced-path
invariant and introduces no additional target assumptions. Its actual transitive axiom
output from fresh elaboration is:

```text
'WOWII31.conjecture31' depends on axioms: [propext, Classical.choice, Quot.sound]
```

Thus there is no sorry dependency, native-decision/compiler axiom, or custom axiom.
Fresh compile exit code is 0 with warnings treated as errors. Two cosmetic linters
are locally disabled in the candidate (unusedSectionVars and moduleDocstring),
which does not alter proof checking or the theorem's type.

## Reproduction

Scratch directory: `/Users/wentaoli/Research/cursor07-wowii31-audit-n5t83vyh`.
Proof and source bytes were extracted using `git show <worker-commit>:<path>`.
`LEAN_NUM_THREADS=2`. The exact `LEAN_PATH` is retained in `lean-path.txt`:
scratch directory first, then read-only cache `.lake/build/lib/lean` and each
`.lake/packages/<package>/.lake/build/lib/lean` under
`/Users/wentaoli/.codex/worktrees/1974/formal-conjectures`.
The utility and library source contents in that cache checkout have no differences
from the frozen baseline. All nine dependency checkout hashes match the frozen
manifest; Mathlib is `0df444a360eaa60ab8c11dca51a86af692955474`.

Using binary `/Users/wentaoli/.elan/toolchains/leanprover--lean4---v4.33.1/bin/lean`
from the scratch directory:

```sh
lean -DwarningAsError=true research/batches/b01/workers/cursor-07/targets/WOWII31/WOWII31.lean
```

Log: `WOWII31.log`. A full library rebuild was unnecessary: the target was freshly
elaborated against existing unchanged pinned library oleans. The standalone worker
source-only type print file was read but not rebuilt; the compiled candidate example
and independent source inspection establish the type match.

`git diff --name-only 238f78bdd5701ae4c97a0d70d4e22e2d45770d7a <worker-commit>`
contains only files under `research/batches/b01/workers/cursor-07/`.
No frozen source, library definition, dependency, or toolchain changes are present.

## Mathematical meaning and credits

The actual `SimpleGraph.path` definition counts vertices in a largest induced path.
`isInducedPath` requires distinct vertices and adjacency exactly between consecutive
positions. Radius is finite for the finite connected graphs in the theorem, so
`radius.toNat` faithfully represents it. The proof covers small radius before using
induction and vertex deletion. The `[Nontrivial α]` source assumption is retained,
although the internal theorem is stronger.

The frozen source docstring incorrectly describes average distance and cites a
1988 paper. The candidate correctly identifies and avoids that prose error.
[PR #4567](https://github.com/google-deepmind/formal-conjectures/pull/4567)
proposes the documentation correction without changing the Lean signature.

Independently read the primary paper
[Erdős–Saks–Sós, Maximum induced trees in graphs](https://www.renyi.hu/~p_erdos/1986-08.pdf),
Theorem 2.2, pages 64–65. It gives this induced-path bound and explicitly credits
Fan Chung's proof. The candidate follows its induction, radius-decreasing connected
vertex deletion, and two-geodesic construction. Where an extra first-vertex edge
occurs, removing the common starting vertex yields the requisite induced path.
This is a faithful formalization of that known result.

Collective Formal Conjectures copyright and Wentao Li's development credit are
retained; Chung and Erdős–Saks–Sós are clearly credited, and `proof.md` discloses AI
assistance. The phrase “New proof development” should be understood as this worker's
implementation work, not mathematical discovery or first formalization.

## Earlier exact Lean proof missed by worker screening

Independent GitHub issue search for `GraphConjecture31` found
[PR #4658](https://github.com/google-deepmind/formal-conjectures/pull/4658),
created July 28, 2026. It links a prior Lean formalization by Kenta Kitamura/KitaKen1:

[Immutable prior proof](https://github.com/KitaKen1/wowii-graph-conjecture-31-lean/blob/a948e9fc07e11b786aee8dadb1376b4d938454d6/lean/GraphConjecture31.lean).

Prior commit: `a948e9fc07e11b786aee8dadb1376b4d938454d6`.
Prior proof SHA-256: `318726153a99ac7ea26c1d970a51c4e1413f11ebc0087acfeac59cc51035b7c2`.
It imports only Mathlib, reproduces the same two invariant definitions (formatting
and local variable names differ), and proves the exact source theorem signature.
No `sorry`, `admit`, custom `axiom`, or `native_decide` occurs in the prior proof source.

The prior project's own pin is Lean/Mathlib 4.33.0-rc1; that toolchain is not installed
locally. An independent compatibility check passed against the available frozen
4.33.1 libraries, with the source unchanged except for appended `#print axioms` and
`#check` commands. Its source is `prior/lean/GraphConjecture31.lean`, audit copy
`prior/PriorAudit.lean`, and output `prior/PriorAudit.log` in the scratch directory.
First prior audit reached the exact theorem and printed allowed axioms, but exited 1
solely due to five style lints introduced in the newer toolchain (`haveILetI`).
Its full log is preserved as `prior/PriorAudit-first-style-errors.log`.
The repeat command disables only this cosmetic linter, retains warnings-as-errors,
and enables full-name printing for the axiom list:

```sh
lean -DwarningAsError=true -Dlinter.style.haveILetI=false prior/PriorAudit.lean
```

Prior final compile result: **PASS, exit 0**. Output:

```text
'WrittenOnTheWallII.GraphConjecture31.conjecture31' depends on axioms: [propext, Classical.choice, Quot.sound]
WrittenOnTheWallII.GraphConjecture31.conjecture31.{u} {α : Type u} [Fintype α] [DecidableEq α] [Nontrivial α]
  (G : SimpleGraph α) [DecidableRel G.Adj] (h : G.Connected) : 2 * ↑G.radius.toNat - 1 ≤ ↑G.path
```

No proof terms or definitions of the earlier artifact were edited. The only audit-file
addition is diagnostic commands; the cosmetic-linter command-line setting affects no
kernel content. This validates the earlier artifact on Lean 4.33.1, not a fresh run on
its own 4.33.0-rc1 pin. The two standalone invariant definition bodies were compared
with frozen upstream and agree up to formatting, local binder names, and placement
of the same Classical scope. No formal transport wrapper was compiled; the source
comparison establishes that both propositions concern the same invariants.

The worker's literature statement “No exact public Lean proof ... was found” missed
this directly indexed public PR. Correct `literature.md`, `STATUS.json`, and handoff
classification to acknowledge this prior formalization. The independent technical
validity of the new worker proof does not establish novelty.

## Follow-up attribution revision

The worker corrected its attribution and prior-solution records in
`20a7d73f546ff2a012ca56724fdc8a834537eafb`. Independent diff inspection confirms
that the Lean changes from the audited candidate are confined to the initial header
and module docstring. Proof terms, imports, definitions, and exact-type example are
unchanged. Revised proof SHA-256:
`761cac80413e3d86fb2620a37c99dd7692a5b3f5e6b66b338011cc535d85d217`.
The revised header names Kenta Kitamura's earlier formalization, links the immutable
artifact, and calls Wentao Li's work a later implementation, explicitly not a first
formalization. The prior-proof attribution issue is resolved. This comments-only
revision was not unnecessarily recompiled. Worker status still says the independent
prior audit is pending because it predates completion of this audit; the coordinator
can now record both independent compilation passes and retire this duplicate target.

## Coordinator follow-up

Worker correction commit `20a7d73f` changes the proof file only in copyright/attribution comments and the module docstring. The proof body is unchanged. It now credits Kenta Kitamura and explicitly disclaims first formalization. Browser confirmed no active goal and no continuation subscriptions before replacement.
