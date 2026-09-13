# Verification — A109074 / `cursor-01-r02`

## Commands

Source hash (must match the prompt):

```bash
sha256sum FormalConjectures/OEIS/109074.lean
```

Observed: `cd5a2af1993d52ae29df9480d9304cbecae195e24d2ab51a45919806899cfd1e`

Compile the worker proof (not a lake target; file lives outside `FormalConjectures/`):

```bash
export LEAN_NUM_THREADS=2
lake env lean -DwarningAsError=true research/batches/b01/workers/cursor-01-r02/targets/A109074/A109074.lean
```

2026-09-13T01:59:47Z: exit 0. Output:

```
'A109074Proof.conjecture' depends on axioms: [propext, Classical.choice, Quot.sound]
```

No `sorryAx`, `native_decide`, extra axioms, or `Lean.trustCompiler`.

Assignment scope:

```bash
python3 research/batches/b01/control/check_assignments.py --repo . --worker cursor-01-r02
python3 research/batches/b01/control/check_assignments.py --repo . --worker cursor-01-r02 --against 1107856a264a066e316c3cba7b5339be475f6304
```

Both: PASS.

Numerical checks (supporting only; not a proof):

```bash
python3 research/batches/b01/workers/cursor-01-r02/targets/A109074/experiments/check_ratio.py
python3 research/batches/b01/workers/cursor-01-r02/targets/A109074/experiments/check_invariants.py
```

`check_ratio.py`: `b n` integral through `n=11`; frozen ratios match through `n=9`; 2-adic prefix minimum `0` through `n=200`.

`check_invariants.py`: `P,R,U` nonnegative on `[0,4096)`; odd-step deltas nonnegative; odd-prime digit-sum prefixes nonnegative for `p=3,5,7,11,13` through `n=800`.

## Exact-type audit

Frozen `OeisA109074.conjecture`:

```lean
theorem conjecture (n : ℕ) :
    frac (n + 1) = (b (n + 1) : ℚ) / (b n : ℚ)
```

Worker theorem `A109074Proof.conjecture` has this type, compiled separately. The file also contains

```lean
example : ∀ n : ℕ, frac (n + 1) = (b (n + 1) : ℚ) / (b n : ℚ) :=
  conjecture
```

Do not use `OeisA109074.conjecture` (`sorry`) as a proof. The import is definitions only. `#print axioms` does not include `sorryAx`.

`native_decide` appears only in the upstream tests `a_0`–`a_4`. The worker file does not depend on those theorems.

## Formalization audit

- Quantifier: all `n : ℕ`, including `n=0` (`frac 1 = b 1 / b 0 = 1/1`).
- `b` remains Nat division. Integrality is `den_dvd_num`; positivity is `b_pos`; then `b_cast_div`.
- Empty products: `b 0 = 1`.
- Indexing matches PR #5231, not the old Fuss–Catalan source.
- `frac n` need not be an integer (`frac 3 = 26/3`). The theorem is a rational identity.

Self-review recorded `candidate_proof` only and cannot set `independently_verified`.

Coordinator independent audit **PASSED** for exact commit `5e40973bec551bd85d8749fdc3b2c6b539130720`: source/candidate compile exit 0, exact type matches, full allowed axioms, integrality/positivity verified. Known mathematics; no earlier corrected exact Lean proof found in checked sources. The coordinator report will be `research/batches/b01/control/audits/cursor-01-r02.md` on the coordinator branch.
