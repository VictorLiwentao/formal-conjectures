# Verification: A237271 corrected Carmichael observation

UTC: 2026-09-12T23:32:49Z
Worker branch: `cursor/b01-cursor-01-8a28`
Coordination seed: `238f78bdd5701ae4c97a0d70d4e22e2d45770d7a`
Frozen source commit: `a2f4a1bb12a28e04a969da78feefac7d1ce49565`
Lean: `leanprover/lean4:v4.33.1`

## Frozen source hash

```
sha256sum FormalConjectures/OEIS/237271.lean
4f5f9875d35bc3f009af89444945296942a5967d1f8af20a4a102460227da11b  FormalConjectures/OEIS/237271.lean
```

Matches `assignments.json`.

## Formalization audit

Separately compiled `type_audit.lean` (does not import the worker proof):

```
OeisA237271.observation_carmichael : ∀ (k : ℕ), IsCarmichael k → 3 ≤ OeisA237271.a k
theorem OeisA237271.observation_carmichael : ∀ (k : ℕ), IsCarmichael k → 3 ≤ OeisA237271.a k :=
fun k hk => sorry
```

The worker proof file contains

```
example : ∀ (k : ℕ), IsCarmichael k → 3 ≤ OeisA237271.a k :=
  observation_carmichael
```

That example compiled, so the candidate has the frozen type. The original declaration remains `sorry` in the frozen file, which this worker is not allowed to edit.

Quantifiers, `IsCarmichael` via coprime Fermat pseudoprimes, compositeness from `FermatPsp`, and `a`'s consecutive-divisor `countP` match the intended observation. The statement is nonvacuous (`isCarmichael_561` exists in the library). The stronger odd-composite lemma is not a loophole.

## Commands

```sh
export LEAN_NUM_THREADS=2
lake --wfail build 'FormalConjectures.OEIS.«237271»'
lake env lean -DwarningAsError=true research/batches/b01/workers/cursor-01/targets/A237271/A237271.lean
lake env lean -DwarningAsError=true research/batches/b01/workers/cursor-01/targets/A237271/type_audit.lean
python3 research/batches/b01/control/check_assignments.py --repo . --worker cursor-01 --against 238f78bdd5701ae4c97a0d70d4e22e2d45770d7a
python3 research/batches/b01/workers/cursor-01/targets/A237271/experiments/odd_composite_check.py
```

## Results

`lake --wfail build 'FormalConjectures.OEIS.«237271»'`: success.

`lake env lean -DwarningAsError=true` on the proof file: success, no warnings.

```
'OeisA237271.Cursor01.observation_carmichael' depends on axioms: [propext, Classical.choice, Quot.sound]
'OeisA237271.Cursor01.a_ge_three_of_odd_composite' depends on axioms: [propext, Classical.choice, Quot.sound]
observation_carmichael : ∀ (k : ℕ), IsCarmichael k → 3 ≤ a k
```

No `sorryAx`, `Lean.ofReduceBool`, `Lean.trustCompiler`, or added axioms.

Assignment guard: PASS. Only `research/batches/b01/workers/cursor-01/` is modified.

Finite experiment (unverified as a proof): every odd composite `< 20000` has `a n ≥ 3`; the ten Carmichael numbers `< 30000` have `a`-values `5,6,4,6,6,6,7,7,8,6`; odd primes have `a p = 2`; several even composites have `a n = 1`.

## Dependency audit

Imported `FormalConjectures.OEIS.«237271»` only for `a` and the ambient `IsCarmichael`. The proof does not apply `OeisA237271.observation_carmichael`, `conjecture_2`, or any other `sorry` theorem. `IsCarmichael` is a definition in `FormalConjecturesForMathlib` (no `sorry`). `Nat.FermatPsp` and divisor/list lemmas are Mathlib.

## Status

`candidate_proof`. Self-review cannot set `independently_verified`.
