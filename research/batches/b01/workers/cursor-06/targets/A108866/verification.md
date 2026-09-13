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

Kernel-checked powers of 3, same axioms, `#print axioms` on 2026-09-13:

```
'OeisA108866.not_n_sq_dvd_num_of_three_pow'
```

For `e≥2`, `v_3(T(3^e))=2-e<2e`. This covers `n=9,27,81,...` structurally.

Kernel-checked `n=3 p^e` for primes `p≥5`, same axioms, `#print axioms` on 2026-09-13:

```
'OeisA108866.not_n_sq_dvd_num_of_three_mul_pow'
```

For `e≥1`, `v_p(T(3 p^e))=-e<2e`. Compile log: `/opt/cursor/artifacts/a108866_lean_wfail_threemulpow.log`, exit 0, no `sorryAx`.

Leading-binomial product lemmas for the remaining `p^e` case (`p≥5`, `e≥2`) are in the same file:
`choose_pow_pred_eq_prod_Icc`, `prod_mul_pow_pred_eq_choose_pred`,
`choose_pow_pred_eq_mul_rest`. They give
`C(p^e-1, a p^{e-1}-1) = C(p-1, a-1) * (rest product)` exactly.

Kernel-checked rest-product congruence, same axioms, `#print axioms` on 2026-09-13:

```
'OeisA108866.eq_or_two_le_padicValRat_choose_sub'
'OeisA108866.eq_or_two_le_padicValRat_leading_sub'
'OeisA108866.padicValRat_leading_eq_of_lt'
```

Compile log: `/opt/cursor/artifacts/a108866_lean_wfail_leading.log`, exit 0, no `sorryAx`.
Either `C=C0` or `v_p(C-C0)≥2`. If `v_p(U0)<2` then `v_p(U)=v_p(U0)`.

Kernel-checked prime-power converse under `v_p(U0)=1`, same axioms, `#print axioms` on 2026-09-13:

```
'OeisA108866.one_le_padicValRat_oddLeadingSum0'
'OeisA108866.padicValRat_inner_prime_pow_of_leading'
'OeisA108866.not_n_sq_dvd_num_of_prime_pow_of_leading'
```

Compile log: `/opt/cursor/artifacts/a108866_lean_wfail_layer.log`, exit 0, no `sorryAx`.
If `v_p(U0)=1` then `v_p(T(p^e))=3-e<2e`. Evaluating `v_p(U0)=1` exactly is not yet kernel-checked.
The file still does not prove the frozen iff.

Kernel-checked `p^e` converse when `p^2` does not divide `oddInnerNum p`, plus all powers of 5, same axioms, `#print axioms` on 2026-09-13:

```
'OeisA108866.not_n_sq_dvd_num_of_prime_pow'
'OeisA108866.not_n_sq_dvd_num_of_five_pow'
'OeisA108866.choose_pred_eq_one_sub_harmonic_zmod'
'OeisA108866.oddInnerNum_zmod_sq_harmonic'
'OeisA108866.not_pow_dvd_oddInnerNum_iff'
```

Compile log: `/opt/cursor/artifacts/a108866_lean_wfail_primepow_inner.log`, exit 0, no `sorryAx`.
`oddInnerNum 5 = 960` by `norm_num` after unfolding, not `native_decide`.
`decide` on the `ZMod (p^2)` unit sum for `p=11,13` stuck on `ZMod.inv`; do not use `native_decide`.

Kernel-checked `p^e` converse for `p ∈ {11,13,17,19,23,29,31}` by unfolding `oddInnerNum`, same axioms, `#print axioms` on 2026-09-13:

```
'OeisA108866.inv_pair_zmod'
'OeisA108866.harmonic_pred_eq_zero_zmod'
'OeisA108866.not_n_sq_dvd_num_of_eleven_pow'
'OeisA108866.not_n_sq_dvd_num_of_thirteen_pow'
'OeisA108866.not_n_sq_dvd_num_of_seventeen_pow'
'OeisA108866.not_n_sq_dvd_num_of_nineteen_pow'
'OeisA108866.not_n_sq_dvd_num_of_twenty_three_pow'
'OeisA108866.not_n_sq_dvd_num_of_twenty_nine_pow'
'OeisA108866.not_n_sq_dvd_num_of_thirty_one_pow'
```

Compile log: `/opt/cursor/artifacts/a108866_lean_wfail_wolstenholme.log`, exit 0, no `sorryAx`.

Kernel-checked square pairing, rational Wolstenholme, and `v_7(U0)=2`, same axioms, `#print axioms` on 2026-09-13:

```
'OeisA108866.inv_sq_pair_zmod'
'OeisA108866.two_le_padicValRat_harmonic_pred'
'OeisA108866.inv_sq_sum_eq_two_half_add_p'
'OeisA108866.padicValRat_oddLeadingSum0_seven'
```

Compile log: `/opt/cursor/artifacts/a108866_lean_wfail_pairing4.log`, exit 0, no `sorryAx`.
This is not the frozen iff.

Kernel-checked exact evaluations `n=9,25,27,49` and packaging lemmas remain in the same file, same axioms.

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

c5-k4 already scanned `n=4..4000` (do not repeat as novelty). Scripts: `experiments/scan_beyond_c5k4.py`, `experiments/padic_converse.py`, `experiments/remaining_odd.py`, and `experiments/prime_power_leading.py` (leading binomial sum `U` for `T(p^e)`; experimental only).
