# Verification

## Commands

From the repository root, Lean 4.33.1, `LEAN_NUM_THREADS=2`:

```bash
sha256sum FormalConjectures/OEIS/135508.lean
# 3814549cee8601c96c59b923d7ece1c4b26a59b0fd134f49a93cbbc38e914b0b

lake --wfail build 'FormalConjectures.OEIS.«135508»'

LEAN_NUM_THREADS=2 lake env lean research/batches/b01/workers/cursor-04/targets/A135508/A135508.lean
LEAN_NUM_THREADS=2 lake env lean research/batches/b01/workers/cursor-04/targets/A135508/type_audit.lean

python3 research/batches/b01/control/check_assignments.py --repo . --worker cursor-04
python3 research/batches/b01/control/check_assignments.py --repo . --worker cursor-04 --against 238f78bdd5701ae4c97a0d70d4e22e2d45770d7a
```

Experiments (not proofs):

```bash
python3 research/batches/b01/workers/cursor-04/targets/A135508/experiments/scan_structure.py
python3 research/batches/b01/workers/cursor-04/targets/A135508/experiments/first_entry_bound.py
python3 research/batches/b01/workers/cursor-04/targets/A135508/experiments/injector_bound.py
python3 research/batches/b01/workers/cursor-04/targets/A135508/experiments/injector_mod.py
python3 research/batches/b01/workers/cursor-04/targets/A135508/experiments/first_entry_shape.py
python3 research/batches/b01/workers/cursor-04/targets/A135508/experiments/injector_window.py
python3 research/batches/b01/workers/cursor-04/targets/A135508/experiments/window_miller.py 1000000
python3 research/batches/b01/workers/cursor-04/targets/A135508/experiments/cofactor_seven.py
python3 research/batches/b01/workers/cursor-04/targets/A135508/experiments/paired_injectors.py
python3 research/batches/b01/workers/cursor-04/targets/A135508/experiments/leftover_injectors.py
```

No `lake clean`, `lake update`, or full default `lake build`.

## Exact frozen type (separately compiled)

`type_audit.lean` prints:

```
OeisA135508.conjecture : ∀ (p : ℕ), Nat.Prime p → ¬Nat.Prime (p - 2) → OeisA135508.a (p - 1) = p
```

The theorem body in the frozen file is `sorry`. The `rfl` tests `a_0`–`a_4` depend on no axioms.

## Axioms of proved research lemmas

Captured from `#print axioms` in `A135508.lean` on 2026-09-13:

```
conjecture_of_mod_three : propext, Classical.choice, Quot.sound
twin_pair_inhibition : propext, Classical.choice, Quot.sound
larger_twin_eq_one : propext, Classical.choice, Quot.sound
conjecture_of_factor_dvd_x : propext, Classical.choice, Quot.sound
conjecture_of_injected : propext, Classical.choice, Quot.sound
inhibition : propext, Quot.sound
conjecture_of_thirteen_dvd / eleven / nineteen / seven / five : propext, Classical.choice, Quot.sound
conjecture_two / conjecture_three : propext
a_two_four_pow / v2_x_ge_two / v2_x_two_four_pow_pred : propext, Classical.choice, Quot.sound
exists_prime_factor_mod_three / exists_remaining_factor / remaining_minFac_mul_add_two_le : propext, Classical.choice, Quot.sound
q_dvd_x_of_prime_injector / conjecture_of_prime_injector : propext, Classical.choice, Quot.sound
q_dvd_x_of_coprime_shift : propext, Quot.sound
not_q_dvd_x_le / not_q_dvd_x_self : propext, Classical.choice, Quot.sound
not_prime_kq_sub_two_of_even : propext, Quot.sound
not_prime_kq_sub_two_of_k_mod_one : propext, Classical.choice, Quot.sound
conjecture_of_five_prime_injector / remaining_injector / cases : propext, Classical.choice, Quot.sound
conjecture_of_seventeen_dvd / twentythree_dvd / twenty_nine_dvd : propext, Classical.choice, Quot.sound
conjecture_of_minFac_le_twentythree / twenty_nine / twenty_nine_or_twin : propext, Classical.choice, Quot.sound
conjecture_of_larger_twin_dvd / larger_twin_dvd_x : propext, Classical.choice, Quot.sound
q_dvd_x_of_prime_index / conjecture_of_prime_index : propext, Classical.choice, Quot.sound
cloitre_valuation_barrier / a_eq_prime_padic_succ : propext, Classical.choice, Quot.sound
conjecture_of_minFac_le_fifty_nine_or_twin / remaining_prime_le_fifty_nine : propext, Classical.choice, Quot.sound
conjecture_of_thirty_seven_dvd / forty_one / forty_seven / fifty_three / fifty_nine : propext, Classical.choice, Quot.sound
conjecture_of_minFac_entered / gcd_gt_one_of_composite_shift / two_dvd_x : propext, Classical.choice, Quot.sound (two_dvd_x: propext, Quot.sound)
conjecture_of_sixty_seven_dvd / seventy_one / seventy_nine / eighty_three / eighty_nine / ninety_seven / one_hundred_one : propext, Classical.choice, Quot.sound
conjecture_of_minFac_le_one_hundred_one_or_twin / remaining_prime_le_one_hundred_one : propext, Classical.choice, Quot.sound
exists_prime_index_injector / exists_prime_index_injector_mod_one / q_dvd_x_eventually / q_dvd_x_eventually_mod_one : propext, Classical.choice, Quot.sound
coprime_five_mul_sub_two / coprime_sub_two_six_mul : propext, Classical.choice, Quot.sound
nine_dvd_succ_of_three_dvd_a / not_three_dvd_a_of_not_nine : propext, Quot.sound
a_5 / twenty_seven_dvd_x : propext, Quot.sound
a_6 : propext, Classical.choice, Quot.sound
prime_dvd_a_padic / eighty_one_dvd_succ_of_three_dvd_a / not_three_dvd_a_of_not_eighty_one : propext, Classical.choice, Quot.sound
q_dvd_x_square_window_of_prime_index / conjecture_of_square_window : propext, Classical.choice, Quot.sound
conjecture_of_C1 / larger_twin_dvd_square_window / prime_of_no_prime_dvd_lt / q_dvd_x_square_window_of_exists / q_dvd_x_window_of_no_small_factor : propext, Classical.choice, Quot.sound
conjecture_of_cofactor_seven / seven_dvd_x_square_window : propext, Classical.choice, Quot.sound
five_dvd_x_square_window : propext, Quot.sound
k_mod_three_of_six_five / k_ge_five_of_mod_six_five : propext
two_hundred_forty_three_dvd_x / a_8 / a_7 / seven_hundred_twenty_nine_dvd_succ_of_three_dvd_a / not_three_dvd_a_of_not_seven_hundred_twenty_nine : propext, Classical.choice, Quot.sound
conjecture_of_minFac_seven / q_dvd_x_square_window_of_seven / seven_mul_sub_two_le_square : propext, Classical.choice, Quot.sound (square bound: propext)
five_mul_sub_two_le_square / eleven_mul_sub_two_le_square / thirteen_mul_sub_two_le_square / cofactor_injector_le / mul_mod_three_eq_two : propext
q_dvd_x_square_window_of_five / eleven / thirteen / conjecture_of_cofactor_five / conjecture_of_minFac_five / eleven / thirteen / conjecture_of_minFac_prime_index / conjecture_of_paired_injectors / seven_hundred_twenty_nine_dvd_x / two_thousand_one_hundred_eighty_seven_dvd_succ_of_three_dvd_a : propext, Classical.choice, Quot.sound
conjecture_of_add_two_overlap / conjecture_of_remaining_add_two_overlap : propext, Classical.choice, Quot.sound
a_9 : propext, Quot.sound
two_thousand_one_hundred_eighty_seven_dvd_x / six_thousand_five_hundred_sixty_one_dvd_succ_of_three_dvd_a : propext, Classical.choice, Quot.sound
one_hundred_seven_dvd_x_2459 / conjecture_of_one_hundred_seven_dvd / remaining_prime_eq_one_hundred_seven / conjecture_of_minFac_le_one_hundred_seven_or_twin : propext, Classical.choice, Quot.sound
a_11 / six_thousand_five_hundred_sixty_one_dvd_x / nineteen_thousand_six_hundred_eighty_three_dvd_succ_of_three_dvd_a : propext, Classical.choice, Quot.sound
k_mul_sub_two_le_square : propext
q_dvd_x_square_window_of_k_le / conjecture_of_minFac_k_le / q_dvd_x_square_window_of_seventeen / nineteen / twentythree / twentyfive / twenty_nine / sq_sub_two : propext, Classical.choice, Quot.sound
q_mod_six_five : propext, Quot.sound
dvd_x_succ_of_dvd_a_add_two : propext, Quot.sound
not_prime_dvd_x_succ / prime_dvd_a_add_two_of_first_entry / a_12 / a_13 / not_seven_dvd_x_thirteen / nineteen_thousand_six_hundred_eighty_three_dvd_x / fifty_nine_thousand_forty_nine_dvd_succ_of_three_dvd_a / three_pow_eleven_dvd_x / three_pow_twelve_dvd_succ_of_three_dvd_a : propext, Classical.choice, Quot.sound
a_14 : propext, Quot.sound
remaining_minFac_mul_add_eight_le / conjecture_of_minFac_entered_add_eight / q_dvd_x_add_eight_window_of_k_le / conjecture_of_minFac_k_le_add_eight / conjecture_of_minFac_mod_two_overlap_or_k_le_add_eight : propext, Classical.choice, Quot.sound
k_mul_sub_two_le_add_eight : propext
```

No `sorryAx`, `native_decide`, or `Lean.trustCompiler` on these declarations. `Classical.choice` enters through `Nat.find` in `exists_least_dvd` and through Mathlib `decide` instances. Full log: `experiments/a135508_axioms.log`. Recompiled 2026-09-13T04:47Z.

No `sorryAx`, `native_decide`, or `Lean.trustCompiler` on these declarations. `Classical.choice` enters through `Nat.find` in `exists_least_dvd` and through Mathlib `decide` instances. Full log: `experiments/a135508_axioms.log`.

## Formalization audit (summary)

See `literature.md`. Nonvacuous; indices match OEIS `a(n)` for `n ≥ 1`; `p=2,3` hold; dichotomy `a(p-1) ∈ {1,p}` is proved. Not a loophole proof.

## What is not claimed

The frozen `conjecture` is not proved. Partial lemmas, the twin theorems, and finite scans are not a resolution. Self-review is not `independently_verified`.
