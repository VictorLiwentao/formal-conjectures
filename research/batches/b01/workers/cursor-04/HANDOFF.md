# HANDOFF — cursor-04 / A135508

Worker: cursor-04
Exclusive target: `OeisA135508.conjecture` (`FormalConjectures/OEIS/135508.lean`)
Branch: `cursor/a135508-lcm-primes-770d`
(Cloud required `cursor/<name>-770d`; this is the actual branch.)

Do not start duplicate work on this declaration. Cursor-07 owns non-OEIS discovery; do not enter that scope.

## Status

`partial`. Frozen conjecture unproved. No prior exact solution found in the checked sources (`literature.md`). Statement matches McEachen; not defective. Cloitre Cor. 6.6 is conditional on `C₁` and is not a batch resolution. The implication itself is `conjecture_of_C1` (no `sorryAx`).

`conjecture_of_square_window` proves the frozen type *assuming* every prime `q ≥ 5` divides `x(q(q+2)-1)`. The window hypothesis is not proved. Miller–Rabin found no window failures for primes `q ≡ 2 (mod 3)` up to `2000000` (worst first `k = 311` at `q = 1944791`).

The remaining sufficient arithmetic condition is now `conjecture_of_exists_factor_injector`: some prime factor `q` of `p-2` has a prime injector with `k ≤ (p-2)/q`. Existence is not proved.

An elementary Chebyshev product bound on leftover candidates, using Mathlib `θ(x) ≤ (log 4) x`, does not close at leftover `q ≥ 113` (`experiments/chebyshev_gap.py`).

First-entry of leftover least factors `163`, `167`, `179`, `227` is proved. That is not `∀p`. New leftover least factors at `p < 400000` include `251` (`k=35`) and `389` (`k=29`); those first-entries are now proved as well.

## Reproduce

```bash
git checkout cursor/a135508-lcm-primes-770d
sha256sum FormalConjectures/OEIS/135508.lean
# expect 3814549cee8601c96c59b923d7ece1c4b26a59b0fd134f49a93cbbc38e914b0b

LEAN_NUM_THREADS=2 lake --wfail build 'FormalConjectures.OEIS.«135508»'
LEAN_NUM_THREADS=2 lake env lean -DwarningAsError=true research/batches/b01/workers/cursor-04/targets/A135508/A135508.lean
LEAN_NUM_THREADS=2 lake env lean research/batches/b01/workers/cursor-04/targets/A135508/type_audit.lean

python3 research/batches/b01/control/check_assignments.py --repo . --worker cursor-04 --against 238f78bdd5701ae4c97a0d70d4e22e2d45770d7a
```

## What is proved (research file only)

See `proof.md` for the full list. New in this continuation:

- `k_mul_sub_two_le_of_cofactor`, `conjecture_of_factor_k_le_cofactor`, `conjecture_of_exists_factor_injector`: remaining McEachen if some factor of `p-2` has a prime injector inside the actual McEachen window `k ≤ (p-2)/q`.
- `q_dvd_x_add_eight_window_of_sq_sub_two`, `q_dvd_x_add_eight_window_of_add_six`: leftover polynomial candidates `k = q` and `k = q+6`. Primality not proved.
- First-entry `163 | x 4073`, `167 | x 2837`, `179 | x 3041`, `227 | x 6581`, `251 | x 8783`, `389 | x 11279`, and remaining McEachen when those are `lpf(p-2)`.

Previously: mod-3 family, minFac `≤ 107` or larger-twin least factor, square-window and add-eight packaging, Dirichlet unbounded injectors, Cloitre 6.5 / 6.7, twin inhibition, 3-adic barriers through `a 14`.

## Gap

See `proof.md`. Remaining McEachen primes have `lpf(p-2) ≥ 113` not a larger twin and not among `{163,167,179,227,251,389}`, and need a first-entry bound. Dirichlet, Linnik `L=5`, GRH, and the elementary Chebyshev product bound do not give `r ≤ q(q+2)-1`. Finite scans are not a proof.

## Commit SHA

Research commit: `a3035adf`
Branch: `cursor/a135508-lcm-primes-770d`
