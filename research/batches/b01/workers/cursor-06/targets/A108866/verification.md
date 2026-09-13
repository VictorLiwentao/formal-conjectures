# Verification — A108866

Incomplete. No independently verified full proof or disproof.

## Frozen type

See `FormalConjectures/OEIS/108866.lean`:

```
theorem conjecture {n : ℕ} (hn : n > 3) :
    (ratExpression n).num ≡ 0 [ZMOD (n^2 : ℤ)] ↔ n.Prime
```

SHA-256: `afa95297bd177a882fb72b03f32f1da68ecae58d9126981567562462b73266f8`.
Confirmed on the working tree by `sha256sum FormalConjectures/OEIS/108866.lean`.

## Kernel-checked lemmas (not the full iff)

Command:

```
LEAN_NUM_THREADS=2 lake env lean -DwarningAsError=true research/batches/b01/workers/cursor-06/targets/A108866/A108866.lean
```

Exit code 0, no warnings.

`#print axioms` on 2026-09-13:

```
'OeisA108866.not_n_sq_dvd_num_of_even' depends on axioms: [propext, Classical.choice, Quot.sound]
'OeisA108866.ratExpression_eq_two_mul_n_sum_choose_sq' depends on axioms: [propext, Classical.choice, Quot.sound]
'OeisA108866.n_sq_dvd_num_of_prime' depends on axioms: [propext, Classical.choice, Quot.sound]
'OeisA108866.padicValRat_ratExpression_of_odd_prime' depends on axioms: [propext, Classical.choice, Quot.sound]
'OeisA108866.not_n_sq_dvd_num_of_odd_inner_lt' depends on axioms: [propext, Classical.choice, Quot.sound]
'OeisA108866.not_n_sq_dvd_num_of_inner_le_denom' depends on axioms: [propext, Classical.choice, Quot.sound]
```

Additional converse helpers compiled in the same file: `oddInnerNum_ne_zero`, `four_le_padicValNat_oddDenom`, `q_mul_ratExpression_sub_eq_sum`, `q_mul_ratExpression_sub_eq_fermat_add`, `q_dvd_two_pow_mul_sub`, `one_le_padicValRat_two_pow_mul_sub`, `not_dvd_den_ratExpression_of_lt`.

Kernel-checked square-free fragment, axioms `{propext, Classical.choice, Quot.sound}`:

```
'OeisA108866.padicValRat_ratExpression_mul_eq_neg_one'
'OeisA108866.not_n_sq_dvd_num_of_mul_odd_primes'
```

Kernel-checked LTE recurrence and unique-multiple fragment, same axioms, `#print axioms` on 2026-09-13:

```
'OeisA108866.padicValRat_ratExpression_mul_of_val_lt_one'
'OeisA108866.not_n_sq_dvd_num_of_val_pred'
'OeisA108866.padicValRat_ratExpression_eq_neg_one_of_unique'
'OeisA108866.not_n_sq_dvd_num_of_unique_prime_mul'
'OeisA108866.padicValRat_ratExpression_mul_eq_min_sub_one'
```

These cover additional `n=mq` with `v_q(T(m))<1`, and `n=mp` when `p≤m<2p` and `p∤m`. The file still does not prove the frozen iff.

Kernel-checked truncated harmonic criterion, same axioms, `#print axioms` on 2026-09-13:

```
'OeisA108866.twoHarmonicTrunc_two_ne_zero'
'OeisA108866.twoHarmonicTrunc_one_ne_zero'
'OeisA108866.padicValRat_ratExpression_eq_neg_pow_of_trunc'
'OeisA108866.not_n_sq_dvd_num_of_trunc'
'OeisA108866.padicValRat_ratExpression_eq_neg_log_of_trunc'
'OeisA108866.not_n_sq_dvd_num_of_log'
'OeisA108866.padicValRat_ratExpression_eq_neg_one_of_two_mul'
'OeisA108866.not_n_sq_dvd_num_of_two_mul'
```

If `p^e ≤ m < p^{e+1}`, `p ∤ m`, and `L(m/p^e) ≠ 0` in `𝔽_p`, then `v_p(T(m)) = -e`, so the converse holds at `n=mp`. This is not the frozen iff.

Exact type of the prime-direction theorem, from `#print OeisA108866.n_sq_dvd_num_of_prime`:

```
theorem OeisA108866.n_sq_dvd_num_of_prime : ∀ {p : ℕ},
  Nat.Prime p → p > 3 → (ratExpression p).num ≡ 0 [ZMOD ↑p ^ 2]
```

Exact type of the even converse, from `#print OeisA108866.not_n_sq_dvd_num_of_even`:

```
theorem OeisA108866.not_n_sq_dvd_num_of_even : ∀ {n : ℕ},
  n > 3 → Even n → ¬(OeisA108866.ratExpression n).num ≡ 0 [ZMOD ↑n ^ 2]
```

The file does not import or use `OeisA108866.conjecture` as a proof.

Source module build:

```
LEAN_NUM_THREADS=2 lake --wfail build 'FormalConjectures.OEIS.«108866»'
```

Assignments:

```
python3 research/batches/b01/control/check_assignments.py --repo . --worker cursor-06
```

PASS.

## Experiments

c5-k4 already scanned `n=4..4000` (do not repeat as novelty). Scripts: `experiments/scan_beyond_c5k4.py` and `experiments/padic_converse.py` (p-adic valuations for prime powers, Fermat psp, and `n=pq`; experimental only).
