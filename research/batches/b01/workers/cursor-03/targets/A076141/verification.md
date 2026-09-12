# A076141 verification

## Environment

- Worker branch: `cursor/b01-cursor-03-91b3`
- Coordination seed: `238f78bdd5701ae4c97a0d70d4e22e2d45770d7a`
- Frozen upstream source commit: `a2f4a1bb12a28e04a969da78feefac7d1ce49565`
- Lean toolchain file: `leanprover/lean4:v4.33.1`
- `LEAN_NUM_THREADS=2`
- Assignment guard: `python3 research/batches/b01/control/check_assignments.py --repo . --worker cursor-03` → PASS, pinned hashes match.

## Source SHA

```sh
sha256sum FormalConjectures/OEIS/76141.lean
```

```text
7954f35f38ed7da506eefc949c1d401e99625a70406561413198c467e63d4c78  FormalConjectures/OEIS/76141.lean
```

Matches `assignments.json`.

## Exact-type audit (this tree)

```sh
LEAN_NUM_THREADS=2 lake env lean research/batches/b01/workers/cursor-03/targets/A076141/A076141.lean
```

Exit code 0. Compiler output:

```text
OeisA76141.conjecture : ∀ (n : ℕ), OeisA76141.a n ≤ 1
theorem OeisA76141.conjecture : ∀ (n : ℕ), OeisA76141.a n ≤ 1 :=
fun n => sorry
'OeisA76141.conjecture' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
```

Also `decide`-closed examples: `binaryPattern 0 = [0]`, `binaryPattern 1 = [1]`, `a 0 = 1`, `a 1 = 1`, `a 2 = 1`, `a 3 = 0`, `a 27 = 1`. No `native_decide` in the audit file.

## Prior proof kernel check

Downloaded https://raw.githubusercontent.com/KitaKen1/oeis-a076141-binary-word/b4e179767fa3041c43e019b559ee77e6737317aa/lean/OeisA76141FC.lean

Token scan: no `sorry`, `axiom`, `native_decide`, `ofReduceBool`, `trustCompiler`, `unsafe`, or `admit`.

```sh
LEAN_NUM_THREADS=2 lake env lean /tmp/OeisA76141FC.lean
```

Exit code 0 on this tree. Final line:

```text
'oeis_a76141_solved' depends on axioms: [propext, Classical.choice, Quot.sound]
```

No `sorryAx`. Unused-variable warnings only. The theorem type is `OeisA76141.a n ≤ 1`, using the imported frozen `a`, not the sorry `conjecture`.

This is a kernel check of a third-party file. It is not an independent human audit and does not license a new public claim by this worker.

## Deterministic experiments (unverified as a proof)

```sh
python3 research/batches/b01/workers/cursor-03/targets/A076141/experiments/count_occurrences.py
```

Overlapping Python counter matches the OEIS prefix of length 104, including a(0)=1, a(27)=1, a(145)=1. No n ≤ 200000 with a(n) ≥ 2. Separate loop: no n ≤ 10^6 with a(n) ≥ 2; max = 1. Suffix identity n^2 ≡ n (mod 2^{bitlen n}) has no solutions for 2 ≤ n < 5000. These checks are numerical, not a formal proof.

## Formalization notes used in the audit

- Overlap is counted.
- Zero is `[0]`.
- Leading zeros are not part of `binaryPattern` for n > 0.
- Two disjoint k-bit windows cannot fit in a square of bit length ≤ 2k except the impossible concatenation n‖n.

## What remains

Upstream is still `research open`. PR 5088 is open. OEIS still asks the question. This worker stops at `prior_solution_found`.
