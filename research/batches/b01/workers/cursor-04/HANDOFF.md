# HANDOFF — cursor-04 / A135508

Worker: cursor-04
Exclusive target: `OeisA135508.conjecture` (`FormalConjectures/OEIS/135508.lean`)
Branch: `cursor/a135508-lcm-primes-770d`
(Cloud required `cursor/<name>-770d`; this is the actual branch.)

Do not start duplicate work on this declaration. Cursor-07 owns non-OEIS discovery; do not enter that scope.

## Status

`partial`. Frozen conjecture still unproved after the compiled `401` family. No prior exact solution found in the checked sources (`literature.md`). Statement matches McEachen; not defective. Cloitre Cor. 6.6 is conditional on `C₁` and is not a batch resolution. The implication itself is `conjecture_of_C1` (no `sorryAx`). Partial lemmas, finite scans, and conditional Type A injectors are not a resolution.

`conjecture_of_square_window` proves the frozen type *assuming* every prime `q ≥ 5` divides `x(q(q+2)-1)`. The window hypothesis is not proved. Miller–Rabin found no window failures for primes `q ≡ 2 (mod 3)` up to `2000000` (worst first `k = 311` at `q = 1944791`).

The remaining sufficient arithmetic condition is `conjecture_of_exists_factor_injector`: some prime factor `q` of `p-2` has a prime injector with `k ≤ (p-2)/q`. Existence is not proved.

McEachen at `p ≥ 5` is equivalent to `gcd(x(p-3), p-2) > 1` (`a_eq_self_iff_gcd_gt_one`). Primes `q ≡ 2 (mod 3)` never first-enter at the primitive index `q-2` (`not_first_entry_k_one_of_mod_two`). A fully smooth composite shift does not inject `q ≠ 3` (`not_first_entry_of_gcd_eq_self`). Those identities isolate leftover first-entry as existence of a prime `kq-2` in the square window.

Remaining Type A numbers (`p-2 < lpf^3`) have prime cofactor (`remaining_type_A_cofactor_prime`). If the least factor is `≡ 2 (mod 3)`, that cofactor is `≡ 1 (mod 3)`, and McEachen follows from primality of `7r-2` (`conjecture_of_remaining_type_A_mod_two_seven`). If the least factor is `≡ 1 (mod 3)`, that cofactor is `≡ 2 (mod 3)`, and McEachen follows from primality of `5r-2` (`conjecture_of_remaining_type_A_mod_one_five`). Primality is not proved.

Complementary factors `r ≡ 1 (mod 3)` inject at `k ≡ 1 (mod 6)`, `k ≥ 7` (`conjecture_of_remaining_mod_one_k`). Type B remaining numbers (every prime factor `≡ 2 (mod 3)`) satisfy `lpf^2 ≤ (p-2)/lpf` and `lpf^3 + 2 ≤ p`. After the `lpf ≤ 401` family, leftover Type B needs a non-twin least factor `≡ 2 (mod 3)` at least `419`, hence `p ≥ 419^3 + 2`.

An elementary Chebyshev product bound on leftover candidates, using Mathlib `θ(x) ≤ (log 4) x`, does not close at leftover `q ≥ 409` (`experiments/chebyshev_gap.py`). First-order Bonferroni/Mertens is not a `∀q` proof (`experiments/bonferroni.py`).

Remaining McEachen is proved when `lpf(p-2) ≤ 401` or that least factor is a larger twin (`conjecture_of_minFac_le_four_hundred_one_or_twin`). First-entry of `397` (`k=7`, index `2777`) and `401` (`k=5`, index `2003`) is proved, together with the `389` cutoff and the earlier families. The Euclid first-entry criterion, the index identity `n+1 = g(kq-2)`, and the `30`/`210` stock bounds are proved; leftover least factors remain coprime to `210` (`gcd_two_hundred_ten_eq_one_of_minFac`). Square-obstruction lemmas are proved: `5q-2` and `7q-2` are never squares; an odd composite other than a prime square meets its least-factor window; a coprime odd composite whose least factor has entered must be that square; a composite in the square window has least factor `< q`; `kq-2` is never a square when `q ≡ 5,7 (mod 8)`; admissible `k ≡ 5 (mod 6)` in the window satisfies `k ≤ q`. That is not `∀p`.

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

Confirm in the research compile: no `error:`, no `sorryAx`, and

```
#print axioms conjecture_of_minFac_le_four_hundred_one_or_twin
#print axioms a_eq_self_iff_gcd_gt_one
#print axioms not_first_entry_k_one_of_mod_two
#print axioms eq_sq_of_coprime_odd_composite
#print axioms not_eq_sq_kq_sub_two_of_mod_eight
#print axioms minFac_lt_q_of_composite_window
```

## What is proved (research file only)

See `proof.md` for the full list. New in this continuation:

- McEachen at `p ≥ 5` iff `gcd(x(p-3), p-2) > 1`.
- Primitive `k = 1` is never a first-entry of a prime `q ≡ 2 (mod 3)`.
- Fully smooth composite shifts do not inject `q ≠ 3`.
- A composite below `q²` has least factor `< q`.
- First-entry of `397` (`k=7`) and `401` (`k=5`), remaining McEachen when `lpf(p-2) ≤ 401` or a larger-twin least factor.
- `5q-2` and `7q-2` are never squares. An odd composite other than a prime square meets its least-factor window. A coprime odd composite whose least factor has entered is that square. Composites in the square window have least factor `< q`. If `q ≡ 5,7 (mod 8)` then no `kq-2` is a square. Admissible `k ≡ 5 (mod 6)` in the square window satisfies `k ≤ q`.

Previously: g-1 first-entry criterion, first-entry of `307` through `389`, Euclid index identity, `210`-stock coprimality, Type A dual `5r-2`, square-window and add-eight packaging, Dirichlet unbounded injectors, Cloitre 6.5 / 6.7, twin inhibition, 3-adic barriers through `a 14`.

## Gap

See `proof.md`. Remaining McEachen primes have `lpf(p-2) ≥ 409` not a larger twin, and need a first-entry bound. The next leftover non-twin least factor is `409`. Dirichlet, Linnik `L=5`, GRH, Chebyshev, first-order Bonferroni, Euclid packaging, the `g(kq-2)` index identity, k=1 blockage, fully smooth blocking, the `210` stock, and the compiled square-obstruction lemmas do not give `r ≤ q(q+2)-1`. Finite scans are not a proof.

## Commit SHA

Research commit: `69c6e08554248f43c600105eada1cc27c8b92c83`
Branch: `cursor/a135508-lcm-primes-770d`
