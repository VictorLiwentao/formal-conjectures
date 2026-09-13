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
python3 research/batches/b01/workers/cursor-06/targets/A108866/experiments/remaining_odd.py
python3 research/batches/b01/workers/cursor-06/targets/A108866/experiments/prime_power_leading.py
python3 research/batches/b01/workers/cursor-06/targets/A108866/experiments/leading_mod_p2.py
python3 research/batches/b01/workers/cursor-06/targets/A108866/experiments/combo_coeff_fp.py
```

Final math commit SHA: `accb6ab2`.

## Status

Partial. Kernel-checked so far:

- even-composite converse `not_n_sq_dvd_num_of_even`
- odd identity `ratExpression_eq_two_mul_n_sum_choose_sq`
- prime direction `n_sq_dvd_num_of_prime`
- truncated harmonic `L ≠ 0` criterion
- exact converse at `n=9,25,27,49`
- powers of 3: `not_n_sq_dvd_num_of_three_pow`
- `n=3 p^e` for primes `p≥5`: `not_n_sq_dvd_num_of_three_mul_pow`
- rest product `C ≡ C0` with valuation gap at least 2
- `v_p(U0)≥1` and `v_p(U)=v_p(U0)` if `v_p(U0)<2`
- converse at `n=p^e` if `v_p(U0)=1`: `not_n_sq_dvd_num_of_prime_pow_of_leading`
- `v_p(U0)=1` if `p^2` does not divide `oddInnerNum p`
- all `n=5^e` for `e≥2`: `not_n_sq_dvd_num_of_five_pow`
- all `n=p^e` for `p ∈ {11,13,17,19,23,29,31}` and `e≥2`
- pairing `inv_pair_zmod` in `ZMod (p^2)`
- Wolstenholme for `H_{p-1}` in `ZMod (p^2)`: `harmonic_pred_eq_zero_zmod`
- `v_p(H_{p-1})≥2` in `ℚ`: `two_le_padicValRat_harmonic_pred`
- square pairing `inv_sq_pair_zmod` and half-range split `inv_sq_sum_eq_two_half_add_p`
- odd inverse-square identity `inv_sq_odd_eq_seven_eight`
- combo coefficient `odd_combo_eq_p_mul_coeff` and simplified form `(7/4)c + 2 S3 - τ`
- `v_p(U0)=1` iff that coefficient is nonzero in `𝔽_p`
- cube pairing `k^{-3}+(p-k)^{-3}=-3p k^{-4}`
- Fermat lift `k^{p-1}=1+p c` and `k^{-2}=k^{p-3}(1-p c)`
- `v_7(U0)=2`: `padicValRat_oddLeadingSum0_seven`
- `v_7(T(49))=2`: `padicValRat_ratExpression_forty_nine`
- `C(p-1,a-1) ≡ 1 - p H_{a-1}` in `ZMod (p^2)` for odd `a`
- `¬ p^2 ∣ oddInnerNum p` iff the odd unit sum is nonzero in `ZMod (p^2)`
- reduction `conjecture_of_odd_composite_converse`

Axioms `{propext, Classical.choice, Quot.sound}` on the printed theorems. Full odd converse open. No PR. No OEIS edit. Not the frozen iff.

Run URL: https://cursor.com/agents/bc-c701d4c6-5791-456d-bec8-130a051cefe4
