# HANDOFF — cursor-04 / A135508

Worker: cursor-04
Exclusive target: `OeisA135508.conjecture` (`FormalConjectures/OEIS/135508.lean`)
Branch: `cursor/a135508-lcm-primes-770d`
(Cloud required `cursor/<name>-770d`; this is the actual branch.)

Do not start duplicate work on this declaration. Cursor-07 owns non-OEIS discovery; do not enter that scope.

## Status

`partial`. Frozen conjecture unproved. No prior exact solution found in the checked sources (`literature.md`). Statement matches McEachen; not defective. Cloitre Cor. 6.6 is conditional on `C₁` and is not a batch resolution.

Cloitre Prop. 6.5 is now proved in the research file as `a_two_four_pow`. That is not McEachen.

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
- McEachen for `p=2,3`, all primes `p ≥ 7` with `p ≡ 2 (mod 3)`, and injected-factor families (`5,7,11,13,17,19,23`).
- Unconditional twin inhibition for pairs with smaller member `≥ 11` (Cloitre 6.3 without `C₁`).
- Cloitre 2-adic staircase `a(2·4^k-1)=2` for every `k`.
- Remaining-class reduction: a factor `q ≡ 2 (mod 3)` of `p-2`, the bound `q(q+2) ≤ p-2` on the least prime factor, prime and coprime injectors.
- Remaining McEachen when `lpf(p-2) ≤ 23` (`conjecture_of_minFac_le_twentythree`).
- `not_q_dvd_x_le`: such a `q ≥ 7` does not divide `x n` for `0 < n ≤ q`.
- Even `k` and `k ≡ 1 (mod 3)` cannot give prime injectors; remaining candidates are `k ≡ 5 (mod 6)`.
- `conjecture_of_cases` is the frozen type plus an injector hypothesis on the remaining class.

## Gap

See `proof.md`. Remaining McEachen primes need a first-entry bound for some factor of `p-2`. Dirichlet, Linnik `L=5`, and the usual GRH bound do not give `r ≤ q(q+2)-1`. Finite scans to `n=40000` and injector checks for `q ≤ 5000` are not a proof.

## Commit SHA

Research commit: pending after this commit
Branch: `cursor/a135508-lcm-primes-770d`
