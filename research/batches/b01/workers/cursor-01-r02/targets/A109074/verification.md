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
lake env lean research/batches/b01/workers/cursor-01-r02/targets/A109074/A109074.lean
```

2026-09-13T00:50Z class compile: exit 0 with one `sorry` warning, on `digitSum_ineq` for odd primes.

`--wfail` is not claimed. A `sorry` warning would fail CI-style `--wfail`.

Assignment scope:

```bash
python3 research/batches/b01/control/check_assignments.py --repo . --worker cursor-01-r02
python3 research/batches/b01/control/check_assignments.py --repo . --worker cursor-01-r02 --against 1107856a264a066e316c3cba7b5339be475f6304
```

Numerical checks (supporting only):

```bash
python3 research/batches/b01/workers/cursor-01-r02/targets/A109074/experiments/check_ratio.py
python3 research/batches/b01/workers/cursor-01-r02/targets/A109074/experiments/check_invariants.py
```

`check_ratio.py`: `b n` integral through `n=11`; frozen ratios match through `n=9`; 2-adic prefix minimum `0` through `n=200`.

`check_invariants.py`: `P,R,U` nonnegative on `[0,4096)`; odd-step deltas nonnegative; odd-prime digit-sum prefixes nonnegative for `p=3,5,7,11,13` through `n=800`.

## Exact-type audit (not a completion)

Frozen:

```lean
theorem conjecture (n : ℕ) :
    frac (n + 1) = (b (n + 1) : ℚ) / (b n : ℚ)
```

Worker theorem `A109074Proof.conjecture` has this type. It must **not** be treated as proved while `digitSum_ineq` uses `sorry`.

Do not use `OeisA109074.conjecture` (sorry) as a proof. Import is definitions only.

`native_decide` appears only in the upstream tests `a_0`–`a_4`. The worker file does not depend on those theorems.

`#print axioms A109074Proof.conjecture` is **not** claimed. It would currently include `sorryAx`.

## Formalization audit

- Quantifier: all `n : ℕ`, including `n=0` (`frac 1 = b 1 / b 0 = 1/1`)
- `b` remains Nat division; no silent rational replacement
- Empty products: `b 0 = 1`
- Nonvacuity: `b n > 0` is proved from `den_dvd_num`, which is still conditional on odd primes
- Indexing matches PR #5231, not the old Fuss–Catalan source
