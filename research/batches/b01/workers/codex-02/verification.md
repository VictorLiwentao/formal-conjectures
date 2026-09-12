# Verification record

Date: 2026-09-12 UTC. Lean: `leanprover/lean4:v4.33.1`.
Worker branch: `codex/b01-codex-02`.

## Scope and environment

The runtime lives in `research/batches/b01/workers/codex-02/cache/runtime`.
It uses a private copy-on-write copy of the compatible local `.lake` cache;
source links point to this worktree. Build outputs stay in the worker directory.
`LEAN_NUM_THREADS=2` was set on local Lean jobs. No full default build, clean,
update, dependency-pin change, or upstream-source edit was performed.

## Commands and results

From the repository root:

```sh
python3 research/batches/b01/control/check_assignments.py --repo . --worker codex-02 --against 238f78bdd5701ae4c97a0d70d4e22e2d45770d7a
LEAN_NUM_THREADS=2 lake --dir research/batches/b01/workers/codex-02/cache/runtime --wfail build 'FormalConjectures.OEIS.«3161»' 'FormalConjectures.OEIS.«3162»'
```

Both passed. Lake built the required shared imports and the two requested problem
modules, then reported successful completion. The original problem placeholders
are unchanged; building them is not a proof of their conjectures.

For each target `A003161` and `A003162`, the source compile command is:

```sh
LEAN_NUM_THREADS=2 LEAN_PATH="$PWD" lake --dir research/batches/b01/workers/codex-02/cache/runtime env lean -DwarningAsError=true -o research/batches/b01/workers/codex-02/targets/A003161/A003161.olean research/batches/b01/workers/codex-02/targets/A003161/A003161.lean
```

Substitute `A003162` in both file paths for the second command.
Both target proof files compiled successfully with warnings treated as errors.
Final axiom output:

```text
'B01Codex02.cancel_two' depends on axioms: [propext, Classical.choice, Quot.sound]
'B01Codex02.raw_transfer' depends on axioms: [propext, Classical.choice, Quot.sound]
'B01Codex02.normalized_transfer' depends on axioms: [propext, Classical.choice, Quot.sound]
```

The separate exact-type audit passed with exit code 0. Its command was:

```sh
LEAN_NUM_THREADS=2 LEAN_PATH="$PWD" lake --dir research/batches/b01/workers/codex-02/cache/runtime env lean -DwarningAsError=true research/batches/b01/workers/codex-02/ExactTypeAudit.lean
```

Its output was:

```text
PASS: both Tower conclusions are definitionally equal to the full frozen theorem types.
'B01Codex02.RawStatement' depends on axioms: [propext, Classical.choice, Quot.sound]
'B01Codex02.NormalizedStatement' depends on axioms: [propext, Classical.choice, Quot.sound]
'B01Codex02.raw_transfer' depends on axioms: [propext, Classical.choice, Quot.sound]
'B01Codex02.normalized_transfer' depends on axioms: [propext, Classical.choice, Quot.sound]
```

The first two A003161 attempts failed during the natural/integer GCD conversion;
see [scratch-failures.md](scratch-failures.md). Failed-run axiom outputs are not
accepted. The successful run above contains no `sorryAx` or compiler-trust axiom.

```sh
python3 research/batches/b01/workers/codex-02/experiments.py
bash -n research/batches/b01/workers/codex-02/setup.sh research/batches/b01/workers/codex-02/verify.sh
git diff --cached --check
```

These passed. Exact arithmetic output is in [experiments.json](experiments.json):
499 admissible parameter triples, four congruences per triple, and exact
normalization checks on `N=1..200` and all larger sequence inputs used by the grid.
No random sampling, floats, native Lean evaluation, or trusted-computation shortcut
was used. Script syntax was checked; `verify.sh` reproduces the constituent
commands and has not been separately rerun end to end.

## What this establishes

The mathematical source mapping is recorded in
[formalization-audit.md](formalization-audit.md) and
[literature-reduction.md](literature-reduction.md).
The conditional Lean theorems have explicit hypotheses for the published inputs.
Their axiom lists do not turn those hypotheses into proved theorems. No source
`conjecture` proof or `a_is_integer` proof is used. The axiom reports audit the
complete transitive dependency closures of the compiled certificates.

A complete Lean formalization of the identities and Coster inputs is not supplied.
Neither assignment is marked `independently_verified`. A fresh reviewer must
check the source reduction before any public claim of a new resolution.
