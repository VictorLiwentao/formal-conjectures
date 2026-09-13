# Verification

Worker: `cursor-07-r03`
Target: `Green66-trivial-bound`
Declaration proved: `Green66TrivialBound.trivial_bound`
Frozen declaration: `Green66.green_66.variants.trivial_bound`
Classification: known_mathematics_formalization.
This is not a resolution of open Green problem 66 with constant `1/10`.
Self-review cannot set `independently_verified`.

## Source pin

```
d38ab7e233260302ef58121037a02dc94866ddae820e9fc84308ce7264e07acb  FormalConjectures/GreensOpenProblems/66.lean
```

Matches assignments.json and the worker prompt.
Lean: `leanprover/lean4:v4.33.1`.
Coordination seed: `486f35dcee50c2c32b98f946726adbd20f6a5fbf`.
Working tree edits are confined to
`research/batches/b01/workers/cursor-07-r03/`.

```
python3 research/batches/b01/control/check_assignments.py --repo . --worker cursor-07-r03 --against 486f35dcee50c2c32b98f946726adbd20f6a5fbf
PASS: 9 distinct workers, 15 declarations, 16 reserved sequence IDs, 4 exclusive source prefixes; pinned hashes match.
```

## Formalization audit

- Quantifier order: one `C > 0`, then `∀ᶠ X : ℝ in atTop`.
- Uniform constant `C = 10`, independent of `X`.
- Eventual threshold `X ≥ 1` covers small and negative `X`.
- Interval is closed `Set.Icc`, so `n = X` is allowed.
- Witnesses are natural squares via frozen `IsSumOfTwoSquares`.
- Exponent is real `rpow` `1/4`, identified with `√(√X)`.
- The admitted source theorems are imported only for the definition
  and for `#check`. `#print axioms` of the candidate has no `sorryAx`.
- No `native_decide`, extra axioms, or `Lean.trustCompiler`.

## Frozen source compile

Command:

```sh
LEAN_NUM_THREADS=2 lake env lean FormalConjectures/GreensOpenProblems/66.lean
```

Exit 0. Expected `sorry` warnings only:

```
FormalConjectures/GreensOpenProblems/66.lean:38:8: warning: declaration uses `sorry`
FormalConjectures/GreensOpenProblems/66.lean:49:8: warning: declaration uses `sorry`
```

## Candidate compile, warnings as errors

Command:

```sh
LEAN_NUM_THREADS=2 lake env lean -DwarningAsError=true research/batches/b01/workers/cursor-07-r03/targets/Green66-trivial-bound/Green66.lean
```

Exit 0. Output:

```
'Green66TrivialBound.trivial_bound' depends on axioms: [propext, Classical.choice, Quot.sound]
Green66.green_66.variants.trivial_bound :
  ∃ C > 0, ∀ᶠ (X : ℝ) in atTop, ∃ n, Green66.IsSumOfTwoSquares n ∧ ↑n ∈ Set.Icc (X - C * X ^ (1 / 4)) X
Green66TrivialBound.trivial_bound :
  ∃ C > 0, ∀ᶠ (X : ℝ) in atTop, ∃ n, Green66.IsSumOfTwoSquares n ∧ ↑n ∈ Set.Icc (X - C * X ^ (1 / 4)) X
```

Axiom closure is exactly `{propext, Classical.choice, Quot.sound}`.

## Exact-type audit

Command:

```sh
LEAN_NUM_THREADS=2 lake env lean -DwarningAsError=true research/batches/b01/workers/cursor-07-r03/targets/Green66-trivial-bound/Green66_audit.lean
```

Exit 0. Frozen type:

```
Green66.green_66.variants.trivial_bound :
  ∃ C > 0, ∀ᶠ (X : ℝ) in atTop, ∃ n, Green66.IsSumOfTwoSquares n ∧ ↑n ∈ Set.Icc (X - C * X ^ (1 / 4)) X
theorem Green66.green_66.variants.trivial_bound : ∃ C > 0,
  ∀ᶠ (X : ℝ) in atTop, ∃ n, Green66.IsSumOfTwoSquares n ∧ ↑n ∈ Set.Icc (X - C * X ^ (1 / 4)) X :=
sorry
```

The pretty-printed types of the frozen sorry theorem and of
`Green66TrivialBound.trivial_bound` are identical. The candidate file
also contains an `example` with the frozen type ascription.

## Proof file hash

Recorded after the candidate Lean source was frozen for this
verification pass:

```
20e98a7695ed2327099ed3f3d46d6394aea552aa02354287eacf65d0bfb13929  research/batches/b01/workers/cursor-07-r03/targets/Green66-trivial-bound/Green66.lean
```

Candidate commit: `f4d1e76875486f24946ad6ffda9942de602cfa09`.
