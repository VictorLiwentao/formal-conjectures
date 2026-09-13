# Handoff — cursor-06 / A108866

## Branch

- Branch: `cursor/b01-cursor-06-a108866-efe4`
- Seed: `codex/b01-coordination` at `9b2350d25b9387afdb446a5cf70e54b1aa0fdcec`
- Frozen source: `a2f4a1bb12a28e04a969da78feefac7d1ce49565`
- Source SHA-256: `afa95297bd177a882fb72b03f32f1da68ecae58d9126981567562462b73266f8`

## Reproduction

```sh
python3 research/batches/b01/control/check_assignments.py --repo . --worker cursor-06
python3 research/batches/b01/control/check_assignments.py --repo . --worker cursor-06 --against 9b2350d25b9387afdb446a5cf70e54b1aa0fdcec
LEAN_NUM_THREADS=2 lake --wfail build 'FormalConjectures.OEIS.«108866»'
LEAN_NUM_THREADS=2 lake env lean -DwarningAsError=true research/batches/b01/workers/cursor-06/targets/A108866/A108866.lean
python3 research/batches/b01/workers/cursor-06/targets/A108866/experiments/scan_beyond_c5k4.py
python3 research/batches/b01/workers/cursor-06/targets/A108866/experiments/padic_converse.py
```

Final math commit SHA: `876b864f06ca1e4922ea4dcd8a7ce164c1f232ee`.

## Status

Partial. Kernel-checked so far:

- even-composite converse `not_n_sq_dvd_num_of_even`
- odd identity `ratExpression_eq_two_mul_n_sum_choose_sq`
- prime direction `n_sq_dvd_num_of_prime`
- odd valuation formula `padicValRat_ratExpression_of_odd_prime`
- converse criteria `not_n_sq_dvd_num_of_odd_inner_lt`, `not_n_sq_dvd_num_of_inner_le_denom`
- Fermat split `q_mul_ratExpression_sub_eq_fermat_add`
- `not_dvd_den_ratExpression_of_lt`
- `padicValRat_ratExpression_mul_eq_neg_one` and `not_n_sq_dvd_num_of_mul_odd_primes` (`n=mq`, prime `q`, `1<m<q`, `q ∤ T(m).num`)
- LTE recurrence `padicValRat_ratExpression_mul_of_val_lt_one` and `not_n_sq_dvd_num_of_val_pred`
- unique multiple `padicValRat_ratExpression_eq_neg_one_of_unique` and `not_n_sq_dvd_num_of_unique_prime_mul`
- unequal-valuation split `padicValRat_ratExpression_mul_eq_min_sub_one`
- truncated harmonic `padicValRat_ratExpression_eq_neg_pow_of_trunc` and `not_n_sq_dvd_num_of_trunc` (`p^e ≤ m < p^{e+1}`, `p ∤ m`, `L(m/p^e) ≠ 0` in `𝔽_p`)
- `Nat.log` form `padicValRat_ratExpression_eq_neg_log_of_trunc` and `not_n_sq_dvd_num_of_log`
- `L(2) ≠ 0` form `padicValRat_ratExpression_eq_neg_one_of_two_mul` and `not_n_sq_dvd_num_of_two_mul`
- reduction `conjecture_of_odd_composite_converse`

Axioms `{propext, Classical.choice, Quot.sound}` on the printed theorems. Full odd converse open. No PR. No OEIS edit. Not the frozen iff.

Run URL: https://cursor.com/agents/bc-c701d4c6-5791-456d-bec8-130a051cefe4
