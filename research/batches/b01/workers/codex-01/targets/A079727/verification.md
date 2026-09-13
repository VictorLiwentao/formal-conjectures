# A079727 verification record

Status: partial supporting proofs. No exact conjecture proof or disproof is
claimed. Self-review and kernel checks do not constitute independent review.

## Environment and frozen source

- Branch: `codex/b01-codex-01`.
- Source baseline: `a2f4a1bb12a28e04a969da78feefac7d1ce49565`.
- Coordinator seed: `238f78bdd5701ae4c97a0d70d4e22e2d45770d7a`.
- Lean: `leanprover/lean4:v4.33.1`.
- Source `FormalConjectures/OEIS/79727.lean` SHA-256:
  `5731cb2c5f91fe20862071d6d7f3331d164277c2107a38d53bbad359a43029c3`.
- Dependency pins, source files, control files and global configuration are
  unchanged. All tracked changes are below this worker's directory.
- The worktree had no package cache. Existing packages were copied using
  independent APFS clones, not writable symlinks to another worker's cache.
  Lean commands used `LEAN_NUM_THREADS=2`. No `lake update`, `lake clean`, or
  full default project build was run.

## Reproduction

From the repository root:

```bash
bash research/batches/b01/workers/codex-01/verify.sh
```

The script first runs the assignment/hash/path guard, then:

```bash
LEAN_NUM_THREADS=2 lake --wfail build 'FormalConjectures.OEIS.«79727»'
```

It compiles each of the eight current proof/audit files from source with:

```bash
LEAN_NUM_THREADS=2 lake env lean -DwarningAsError=true -o OUTPUT.olean SOURCE.lean
```

The outputs are in the worktree's `.lake/build/lib/lean` tree, so dependent
research imports resolve without editing the Lake project. Source/log pairs:

| Source | Log |
|---|---|
| `A079727.lean` | `lean.log` |
| `Reductions.lean` | `reductions.log` |
| `Bilinear.lean` | `bilinear.log` |
| `PolynomialKernel.lean` | `polynomial_kernel.log` |
| `BlockSummation.lean` | `block_summation.log` |
| `ProductReduction.lean` | `product_reduction.log` |
| `PowerSeriesCoefficients.lean` | `power_series_coefficients.log` |
| `ExactTypeAudit.lean` | `exact_type_audit.log` |

The current log for each file is the successful compilation, not a claim
that initial attempts compiled. The rejected parsing attempt is preserved
separately as `.lean.txt`, with its failure log, and is deliberately excluded.
It is not an accepted proof artifact.

## Exact types and dependency closure

The separate `ExactTypeAudit.lean` command reads the source constant types and
checks definitional equality for all relevant reductions. Its log prints the
four complete frozen types. The C1 equivalence has an explicit, unproved
endpoint hypothesis; the C4 implications have explicit, unproved block or
odd-multiple hypotheses. Those hypotheses are not hidden as axioms.

Each new supporting theorem is accompanied by `#print axioms`. The logs show
only subsets of `{propext, Classical.choice, Quot.sound}`. This command checks
the complete dependency closure, including imported helpers used by the proof.
The script verifies every printed set, checks the absence of warnings/errors,
and screens active source for forbidden proof shortcuts. Importing the frozen
module brings its original `sorry` theorems into the environment, but they are
not dependencies of the proved supporting declarations.

## Deterministic experiments

The same script reruns:

```bash
python3 research/batches/b01/workers/codex-01/targets/A079727/experiments.py --bound 503
python3 research/batches/b01/workers/codex-01/targets/A079727/polynomial_screen.py
python3 research/batches/b01/workers/codex-01/targets/A079727/legendre_screen.py --bound 101
python3 research/batches/b01/workers/codex-01/targets/A079727/validate_experiments.py
```

Outputs are checked in as JSONL; `experiment_validation.log` summarizes them.
The screens use exact integer arithmetic or modular arithmetic that only
inverts prime units. The first screen cross-checks its recurrence against
exact integer sums. Bounds, root selection, and lifts are explicit in source.
These programs have no role in constructing the Lean proof terms.

## Formalization audit

The complete sum includes `k=0` and `k=n`. The admissible prime predicate is
nonvacuous (`3`, `5`, `13`), and excludes `2` and `7`. Products use finite sets,
so factors are distinct; the empty set gives the benign value `n=1`.
The subtraction in the frozen big-product notation is outside the product.
The checked `{3,13}` index is 19. There is no identified statement mismatch.

The characteristic-`p` argument explicitly retains the possible degree-`p`
term of a polynomial with zero derivative. The `p^3` tail proof is not used
as a `p^4` tail proof. The formal-group argument remains conditional on
geometric facts not established in this work. See `proof.md` for the exact
boundary between proved statements and the proposed mathematical routes.

## Checkpoint result

The complete reproduction script exited 0 on 2026-09-13 UTC. All eight
source compilations passed with warnings treated as errors. All 31 printed
axiom checks (27 distinct supporting theorems, with four repeated checks in
the type audit) passed. The assignment guard and all deterministic screens
also passed. `../../verification_summary.log` records the final audit line.
