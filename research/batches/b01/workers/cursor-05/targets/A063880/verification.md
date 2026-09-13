# A063880 verification

Worker: cursor-05. Incomplete session. No candidate proof or disproof is claimed.

## Source pin

```text
sha256sum FormalConjectures/OEIS/63880.lean
b50d00e13735613cbe37bd3a25c19130874e8f036ca2a0e3c1aceb177a33c683  FormalConjectures/OEIS/63880.lean
```

Matches the assignment hash.

## Assignment guard

```text
python3 research/batches/b01/control/check_assignments.py --repo . --worker cursor-05
python3 research/batches/b01/control/check_assignments.py --repo . --worker cursor-05 --against 238f78bdd5701ae4c97a0d70d4e22e2d45770d7a
```

Both: PASS.

## Lean compile of the worker file

Command:

```text
LEAN_NUM_THREADS=2 lake env lean -DwarningAsError=true research/batches/b01/workers/cursor-05/targets/A063880/A063880.lean
```

Result on 2026-09-13T02:24Z: exit code 0, no warnings, no `sorry` declaration in this file.

This is **not** a compile of the frozen theorems. The frozen `sorry` theorems in `FormalConjectures/OEIS/63880.lean` were not used as proof steps.

New lemmas compiled in this checkpoint include `not_seven_sigma_eq_ten_usigma_five_thirteen_nineteen`, `five_seven_pow_ge_three_mul_overshoot`, `not_seven_sigma_eq_ten_usigma_five_sq_seven_pow_ge_four`, and `not_seven_sigma_eq_ten_usigma_five_fourth_seven_sq`.

No `#print axioms` audit of a completed target theorem exists, because those theorems are not proved.

Exact types of the frozen declarations, copied from the source file:

```text
theorem mod_216_of_a {n : ℕ} (h : A n) : n % 216 = 108
theorem unique_primitive_108 {n : ℕ} (h : IsPrimitiveTerm n) : n = 108
```

## Experiments

```text
python3 research/batches/b01/workers/cursor-05/targets/A063880/experiments/abundancy_enum.py
```

Exact `Fraction` one- and two-prime leftover fills. Output: empty except the known `3^3` for leftover `10/7`. Explicitly unverified as a proof. Three-or-more-prime fills are not covered.

`experiments/leftover_search.py` is a broader recursive search. It is explicitly unverified and was not used as evidence of emptiness: a first run did not finish in a bounded time.

```text
python3 research/batches/b01/workers/cursor-05/targets/A063880/experiments/case_tree.py
```

Exact `Fraction` ω=1 and ω=2 leftover classification. Only one-prime hit: `3^3` for leftover `10/7`. ω=2 empty on the listed leftovers. Explicitly unverified as a proof of emptiness for ω≥3.

```text
python3 research/batches/b01/workers/cursor-05/targets/A063880/experiments/omega3_ten_seven.py
```

Exact `Fraction` ω=3 search for leftover `10/7` with primes `≥ 5`. Output: no hits; stops at `p = 7` because `{7,11,13}` has cap below leftover. Explicitly unverified as a proof. ω≥4 is not covered.

```text
python3 research/batches/b01/workers/cursor-05/targets/A063880/experiments/omega3_five_triples.py
```

Exact `Fraction` map of leftover `10/7` triples that include `5`. Used only to choose Lean case splits. Explicitly unverified as a proof.

## Formalization audit

See `literature.md`. The Lean `A` matches OEIS A063880 on positive integers. The congruence and primitive-uniqueness statements match the OEIS comments. No statement defect was found that would make a loophole proof a solution of the intended conjecture.

## Axioms

Not applicable to a completed target. Proved lemmas in `A063880.lean` were not axiom-printed in this checkpoint; they compile under the standard Mathlib environment.
