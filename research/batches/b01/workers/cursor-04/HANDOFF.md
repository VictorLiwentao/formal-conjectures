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

Remaining Type A numbers (`p-2 < lpf^3`) have prime cofactor (`remaining_type_A_cofactor_prime`). If the least factor is `≡ 2 (mod 3)`, that cofactor is `≡ 1 (mod 3)`, and McEachen follows from primality of `7r-2` (`conjecture_of_remaining_type_A_mod_two_seven`). If the least factor is `≡ 1 (mod 3)`, that cofactor is `≡ 2 (mod 3)`, and McEachen follows from primality of `5r-2` (`conjecture_of_remaining_type_A_mod_one_five`). Primality is not proved.

Complementary factors `r ≡ 1 (mod 3)` inject at `k ≡ 1 (mod 6)`, `k ≥ 7` (`conjecture_of_remaining_mod_one_k`). Type B remaining numbers (every prime factor `≡ 2 (mod 3)`) satisfy `lpf^2 ≤ (p-2)/lpf` and `lpf^3 + 2 ≤ p`. After the `lpf ≤ 239` family, leftover Type B needs a non-twin least factor `≡ 2 (mod 3)` at least `257`, hence `p ≥ 257^3 + 2`.

An elementary Chebyshev product bound on leftover candidates, using Mathlib `θ(x) ≤ (log 4) x`, does not close at leftover `q ≥ 257` (`experiments/chebyshev_gap.py`). First-order Bonferroni/Mertens is not a `∀q` proof (`experiments/bonferroni.py`).

Remaining McEachen is proved when `lpf(p-2) ≤ 239` or that least factor is a larger twin (`conjecture_of_minFac_le_two_hundred_thirty_nine_or_twin`). First-entry of `211` (`k=13`), `223` (`k=7`), `233` and `239` (both `k=5`) is proved, together with the earlier families including `227`. That is not `∀p`.

A leftover scan to `p < 5000000` with `lpf ≥ 157` found 14783 primes, zero Type A cofactor failures, and zero McEachen-window gaps (`experiments/type_a_gaps.py`). The unique Lean Type B leftover in that range is `p = 167^2 · 179 + 2 = 4992133`, already covered by `167` and `179`. Finite scans are not a proof.

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

- Type A dual: cofactor `≡ 2 (mod 3)` when `lpf ≡ 1 (mod 3)`, packaged through `5r-2`.
- First-entry `211 | x 2741`, `223 | x 1559`, `233 | x 1163`, `239 | x 1193`.
- Remaining McEachen when `lpf(p-2) ≤ 239` or a larger-twin least factor.

Previously: Type A leftover is semiprime, cube / complementary / Type B structure, minFac `≤ 197` or larger-twin least factor, square-window and add-eight packaging, Dirichlet unbounded injectors, Cloitre 6.5 / 6.7, twin inhibition, 3-adic barriers through `a 14`, first-entry of `113`, `127`, `131`, `137`, `149`, `157`, `163`, `167`, `173`, `179`, `191`, `197`, `227`, `251`, `389`.

## Gap

See `proof.md`. Remaining McEachen primes have `lpf(p-2) ≥ 251` not a larger twin and not among `{251,389}`, and need a first-entry bound. The next leftover non-twin least factor is `257`. Dirichlet, Linnik `L=5`, GRH, Chebyshev, and first-order Bonferroni do not give `r ≤ q(q+2)-1`. Finite scans are not a proof.

## Commit SHA

Research commit: (filled after commit)
Branch: `cursor/a135508-lcm-primes-770d`
