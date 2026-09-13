# HANDOFF — cursor-04 / A135508

Worker: cursor-04
Exclusive target: `OeisA135508.conjecture` (`FormalConjectures/OEIS/135508.lean`)
Branch: `cursor/a135508-lcm-primes-770d`
(Cloud required `cursor/<name>-770d`; this is the actual branch.)

Do not start duplicate work on this declaration. Cursor-07 owns non-OEIS discovery; do not enter that scope.

## Status

`partial`. Frozen conjecture unproved. No prior exact solution found in the checked sources (`literature.md`). Statement matches McEachen; not defective. Cloitre Cor. 6.6 is conditional on `C₁` and is not a batch resolution.

## Reproduce

```bash
git checkout cursor/a135508-lcm-primes-770d
sha256sum FormalConjectures/OEIS/135508.lean
# expect 3814549cee8601c96c59b923d7ece1c4b26a59b0fd134f49a93cbbc38e914b0b

LEAN_NUM_THREADS=2 lake --wfail build 'FormalConjectures.OEIS.«135508»'
LEAN_NUM_THREADS=2 lake env lean research/batches/b01/workers/cursor-04/targets/A135508/A135508.lean
LEAN_NUM_THREADS=2 lake env lean research/batches/b01/workers/cursor-04/targets/A135508/type_audit.lean

python3 research/batches/b01/control/check_assignments.py --repo . --worker cursor-04 --against 238f78bdd5701ae4c97a0d70d4e22e2d45770d7a
```

## What is proved (research file only)

- Closed form of `a`, dichotomy at primes, first-entry criterion `p | x(p-1) ↔ a(p-3)=p-2` for `p ≥ 5`.
- McEachen for `p=2,3`, all primes `p ≥ 7` with `p ≡ 2 (mod 3)`, and several injected-factor families (`5,7,11,13,19`).
- Unconditional twin inhibition for pairs with smaller member `≥ 11` (Cloitre 6.3 without `C₁`).

## Gap

See `proof.md`. Remaining McEachen primes need a first-entry bound for some factor of `p-2`. Finite scans to `n=50000` and injector checks for `q ≤ 5000` are not a proof.

## Commit SHA

Research commit: `b407cc93665d8b44c0d43fcb651b38857cf839a2`
Branch: `cursor/a135508-lcm-primes-770d`
