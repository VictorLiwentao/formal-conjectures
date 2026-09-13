# HANDOFF — cursor-04 / A135508

Worker: cursor-04
Exclusive target: `OeisA135508.conjecture` (`FormalConjectures/OEIS/135508.lean`)
Branch: `cursor/a135508-lcm-primes-770d`
(Cloud required `cursor/<name>-770d`; this is the actual branch.)

Do not start duplicate work on this declaration. Cursor-07 owns non-OEIS discovery; do not enter that scope.

## Status

`partial`. Frozen conjecture unproved. No prior exact solution found in the checked sources (`literature.md`). Statement matches McEachen; not defective. Cloitre Cor. 6.6 is conditional on `C₁` and is not a batch resolution. The implication itself is `conjecture_of_C1` (no `sorryAx`).

`conjecture_of_square_window` proves the frozen type *assuming* every prime `q ≥ 5` divides `x(q(q+2)-1)`. The window hypothesis is not proved. Miller–Rabin found no window failures for primes `q ≡ 2 (mod 3)` up to `2000000` (worst first `k = 311` at `q = 1944791`).

The remaining sufficient arithmetic condition is `conjecture_of_exists_factor_injector`: some prime factor `q` of `p-2` has a prime injector with `k ≤ (p-2)/q`. Existence is not proved.

Complementary factors `r ≡ 1 (mod 3)` inject at `k ≡ 1 (mod 6)`, `k ≥ 7` (`conjecture_of_remaining_mod_one_k`). Type B remaining numbers (every prime factor `≡ 2 (mod 3)`) satisfy `lpf^2 ≤ (p-2)/lpf` and `lpf^3 + 2 ≤ p`. After the `lpf ≤ 149` family, Type B leftover needs `lpf ≥ 157`, hence `p ≥ 157^3 + 2`.

An elementary Chebyshev product bound on leftover candidates, using Mathlib `θ(x) ≤ (log 4) x`, does not close at leftover `q ≥ 157` (`experiments/chebyshev_gap.py`).

Remaining McEachen is proved when `lpf(p-2) ≤ 149` or that least factor is a larger twin (`conjecture_of_minFac_le_one_hundred_forty_nine_or_twin`). First-entry of `113` (`k=5`), `127` (`k=7`), `131`, `137`, `149`, `163`, `167`, `179`, `227`, `251` and `389` is proved. That is not `∀p`.

A Type B scan to `p < 2000000` found exactly one leftover example, `p = 113^3 + 2`, now covered by `113 ∣ x 563`.

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

- Cube lemma: odd composite `n ≡ 2 (mod 3)` with `n < lpf^3` has a prime factor `≡ 1 (mod 3)`.
- Complementary `k ≡ 1 (mod 6)` packaging, including `k=7`.
- Type B cofactor window `k ≤ lpf^2` and size bound `lpf^3 + 2 ≤ p`.
- First-entry `113 | x 563`, `127 | x 887`, `131 | x 653`, `137 | x 683`, `149 | x 743`.
- Remaining McEachen when `lpf(p-2) ≤ 149` or a larger-twin least factor.

Previously: mod-3 family, minFac `≤ 107` or larger-twin least factor, square-window and add-eight packaging, Dirichlet unbounded injectors, Cloitre 6.5 / 6.7, twin inhibition, 3-adic barriers through `a 14`, first-entry of `163`, `167`, `179`, `227`, `251`, `389`.

## Gap

See `proof.md`. Remaining McEachen primes have `lpf(p-2) ≥ 157` not a larger twin and not among `{163,167,179,227,251,389}`, and need a first-entry bound. Dirichlet, Linnik `L=5`, GRH, and the elementary Chebyshev product bound do not give `r ≤ q(q+2)-1`. Finite scans are not a proof.

## Commit SHA

Research commit: `5f1b23f6`
Branch: `cursor/a135508-lcm-primes-770d`
