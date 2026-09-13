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
python3 research/batches/b01/workers/cursor-04/targets/A135508/experiments/leftover_injectors.py 400000
python3 research/batches/b01/workers/cursor-04/targets/A135508/experiments/window_miller.py 2000000
python3 research/batches/b01/workers/cursor-04/targets/A135508/experiments/mod_one_factor.py 400000
python3 research/batches/b01/workers/cursor-04/targets/A135508/experiments/type_b.py 2000000
python3 research/batches/b01/workers/cursor-04/targets/A135508/experiments/type_a_gaps.py 5000000 157
python3 research/batches/b01/workers/cursor-04/targets/A135508/experiments/bonferroni.py
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
one_hundred_sixty_three_dvd_x_4073 / conjecture_of_one_hundred_sixty_three_dvd / one_hundred_sixty_seven_dvd_x_2837 / conjecture_of_one_hundred_sixty_seven_dvd / one_hundred_seventy_nine_dvd_x_3041 / conjecture_of_one_hundred_seventy_nine_dvd / two_hundred_twenty_seven_dvd_x_6581 / conjecture_of_two_hundred_twenty_seven_dvd : propext, Classical.choice, Quot.sound
k_mul_sub_two_le_of_cofactor : propext
conjecture_of_factor_k_le_cofactor / conjecture_of_exists_factor_injector / q_dvd_x_add_eight_window_of_sq_sub_two / q_dvd_x_add_eight_window_of_add_six / remaining_p_ge_one_hundred_sixty_three / conjecture_of_minFac_one_hundred_sixty_three / remaining_p_ge_one_hundred_sixty_seven / conjecture_of_minFac_one_hundred_sixty_seven / remaining_p_ge_one_hundred_seventy_nine / conjecture_of_minFac_one_hundred_seventy_nine / remaining_p_ge_two_hundred_twenty_seven / conjecture_of_minFac_two_hundred_twenty_seven / two_hundred_fifty_one_dvd_x_8783 / conjecture_of_two_hundred_fifty_one_dvd / remaining_p_ge_two_hundred_fifty_one / conjecture_of_minFac_two_hundred_fifty_one / three_hundred_eighty_nine_dvd_x_11279 / conjecture_of_three_hundred_eighty_nine_dvd / remaining_p_ge_three_hundred_eighty_nine / conjecture_of_minFac_three_hundred_eighty_nine : propext, Classical.choice, Quot.sound
one_hundred_thirteen_dvd_x_563 / conjecture_of_one_hundred_thirteen_dvd / remaining_p_ge_one_hundred_thirteen / conjecture_of_minFac_one_hundred_thirteen / one_hundred_twenty_seven_dvd_x_887 / conjecture_of_one_hundred_twenty_seven_dvd / remaining_p_ge_one_hundred_twenty_seven / conjecture_of_minFac_one_hundred_twenty_seven / one_hundred_thirty_one_dvd_x_653 / conjecture_of_one_hundred_thirty_one_dvd / remaining_p_ge_one_hundred_thirty_one / conjecture_of_minFac_one_hundred_thirty_one / one_hundred_thirty_seven_dvd_x_683 / conjecture_of_one_hundred_thirty_seven_dvd / remaining_p_ge_one_hundred_thirty_seven / conjecture_of_minFac_one_hundred_thirty_seven / one_hundred_forty_nine_dvd_x_743 / conjecture_of_one_hundred_forty_nine_dvd / remaining_p_ge_one_hundred_forty_nine / conjecture_of_minFac_one_hundred_forty_nine / remaining_prime_le_one_hundred_forty_nine / conjecture_of_minFac_le_one_hundred_forty_nine_or_twin : propext, Classical.choice, Quot.sound
remaining_p_sub_two_odd / remaining_div_ge_minFac / remaining_minFac_ge_seven_of_not_five / seven_le_div_of_minFac_seven / exists_prime_factor_mod_one_of_lt_cube / remaining_exists_mod_one_of_lt_cube / cube_le_of_all_prime_factors_mod_two / conjecture_of_remaining_mod_one_seven / conjecture_of_exists_mod_one_seven / conjecture_of_remaining_lt_cube_mod_one_seven / remaining_type_B_div_ge_sq / conjecture_of_remaining_type_B_k_le / remaining_type_B_p_ge / conjecture_of_remaining_mod_one_k / conjecture_of_exists_mod_one_k : propext, Classical.choice, Quot.sound
remaining_mod_one_factor_ge_seven / k_mul_sub_two_mod_of_six_one : propext, Quot.sound
k_mod_three_of_six_one / k_ge_seven_of_mod_six_one : propext
remaining_p_sub_two_gt_one / seven_mul_sub_two_ge_seven / two_le_seven_mul_of_ge_seven / five_le_of_seven_le / one_ne_two / zero_ne_two / one_lt_three / one_lt_five / one_lt_seven / four_le_seven / two_mod_three / five_mod_three : no extra axioms (or a subset of propext)
remaining_type_A_cofactor_prime / remaining_type_A_cofactor_mod_one / remaining_type_A_cofactor_mod_two / conjecture_of_remaining_type_A_mod_two_seven / conjecture_of_remaining_type_A_mod_one_five : propext, Classical.choice, Quot.sound
one_hundred_fifty_seven_dvd_x_1097 / conjecture_of_one_hundred_fifty_seven_dvd / remaining_p_ge_one_hundred_fifty_seven / conjecture_of_minFac_one_hundred_fifty_seven / one_hundred_seventy_three_dvd_x_863 / conjecture_of_one_hundred_seventy_three_dvd / remaining_p_ge_one_hundred_seventy_three / conjecture_of_minFac_one_hundred_seventy_three / one_hundred_ninety_one_dvd_x_953 / conjecture_of_one_hundred_ninety_one_dvd / remaining_p_ge_one_hundred_ninety_one / conjecture_of_minFac_one_hundred_ninety_one / one_hundred_ninety_seven_dvd_x_983 / conjecture_of_one_hundred_ninety_seven_dvd / remaining_p_ge_one_hundred_ninety_seven / conjecture_of_minFac_one_hundred_ninety_seven / remaining_prime_le_one_hundred_seventy_three / remaining_prime_from_one_hundred_seventy_four_le_one_hundred_ninety_seven / remaining_prime_le_one_hundred_ninety_seven / conjecture_of_minFac_le_one_hundred_ninety_seven_or_twin : propext, Classical.choice, Quot.sound
two_hundred_eleven_dvd_x_2741 / conjecture_of_two_hundred_eleven_dvd / remaining_p_ge_two_hundred_eleven / conjecture_of_minFac_two_hundred_eleven / two_hundred_twenty_three_dvd_x_1559 / conjecture_of_two_hundred_twenty_three_dvd / remaining_p_ge_two_hundred_twenty_three / conjecture_of_minFac_two_hundred_twenty_three / two_hundred_thirty_three_dvd_x_1163 / conjecture_of_two_hundred_thirty_three_dvd / remaining_p_ge_two_hundred_thirty_three / conjecture_of_minFac_two_hundred_thirty_three / two_hundred_thirty_nine_dvd_x_1193 / conjecture_of_two_hundred_thirty_nine_dvd / remaining_p_ge_two_hundred_thirty_nine / conjecture_of_minFac_two_hundred_thirty_nine / remaining_prime_from_one_hundred_ninety_eight_le_two_hundred_eleven / remaining_prime_from_two_hundred_twelve_le_two_hundred_twenty_seven / remaining_prime_from_two_hundred_twenty_eight_le_two_hundred_thirty_nine / remaining_prime_from_one_hundred_ninety_eight_le_two_hundred_thirty_nine / conjecture_of_minFac_le_two_hundred_thirty_nine_or_twin / two_hundred_fifty_seven_dvd_x_1283 / conjecture_of_two_hundred_fifty_seven_dvd / remaining_p_ge_two_hundred_fifty_seven / conjecture_of_minFac_two_hundred_fifty_seven / remaining_prime_from_two_hundred_forty_le_two_hundred_fifty_seven / conjecture_of_minFac_le_two_hundred_fifty_seven_or_twin / two_hundred_sixty_three_dvd_x_6047 / conjecture_of_two_hundred_sixty_three_dvd / remaining_p_ge_two_hundred_sixty_three / conjecture_of_minFac_two_hundred_sixty_three / remaining_prime_from_two_hundred_fifty_eight_le_two_hundred_sixty_three / conjecture_of_minFac_le_two_hundred_sixty_three_or_twin / a_add_two_eq / two_hundred_sixty_nine_dvd_x_2957 / conjecture_of_two_hundred_sixty_nine_dvd / remaining_p_ge_two_hundred_sixty_nine / conjecture_of_minFac_two_hundred_sixty_nine / remaining_prime_from_two_hundred_sixty_four_le_two_hundred_sixty_nine / conjecture_of_minFac_le_two_hundred_sixty_nine_or_twin : propext, Classical.choice, Quot.sound (the 212–227 interval lemma depends only on propext; the 258–263 and 264–269 interval lemmas depend only on propext; `a_add_two_eq` depends on propext, Quot.sound)
a_add_two_mul_gcd / thirty_dvd_x / gcd_thirty_dvd_gcd_x : propext, Quot.sound
dvd_a_add_two_of_dvd_add / q_dvd_x_succ_of_dvd_add / first_entry_iff_dvd_add / conjecture_of_gcd_thirty / two_hundred_ten_dvd_x / gcd_two_hundred_ten_dvd_gcd_x / conjecture_of_gcd_two_hundred_ten : propext, Classical.choice, Quot.sound
two_hundred_seventy_seven_dvd_x_5261 / conjecture_of_two_hundred_seventy_seven_dvd / remaining_p_ge_two_hundred_seventy_seven / conjecture_of_minFac_two_hundred_seventy_seven / remaining_prime_from_two_hundred_seventy_le_two_hundred_seventy_seven / conjecture_of_minFac_le_two_hundred_seventy_seven_or_twin / two_hundred_eighty_one_dvd_x_3089 / conjecture_of_two_hundred_eighty_one_dvd / remaining_p_ge_two_hundred_eighty_one / conjecture_of_minFac_two_hundred_eighty_one / remaining_prime_from_two_hundred_seventy_eight_le_two_hundred_eighty_one / conjecture_of_minFac_le_two_hundred_eighty_one_or_twin : propext, Classical.choice, Quot.sound (the 278–281 interval lemma depends only on propext)
succ_eq_gcd_mul_kq_sub_two / exists_first_entry_index : propext, Quot.sound
gcd_two_hundred_ten_eq_one_of_minFac / two_hundred_ninety_three_dvd_x_3221 / conjecture_of_two_hundred_ninety_three_dvd / remaining_p_ge_two_hundred_ninety_three / conjecture_of_minFac_two_hundred_ninety_three / remaining_prime_from_two_hundred_eighty_two_le_two_hundred_ninety_three / conjecture_of_minFac_le_two_hundred_ninety_three_or_twin : propext, Classical.choice, Quot.sound
dvd_right_of_dvd_add / add_two_gcd_eq_of_kq_sub_two / eq_one_of_prime_dvd_pred / not_dvd_gcd_pred_of_mem : propext
succ_pred_kq_sub_two : propext, Quot.sound
odd_prime_dvd_two_mul / first_entry_iff_dvd_gcd_pred / q_dvd_x_of_gcd_eq_one_at_shift : propext, Classical.choice, Quot.sound
three_hundred_seven_dvd_x_3989 / conjecture_of_minFac_three_hundred_seven / three_hundred_eleven_dvd_x_1553 / conjecture_of_minFac_three_hundred_eleven / three_hundred_seventeen_dvd_x_1583 / conjecture_of_minFac_three_hundred_seventeen / three_hundred_thirty_one_dvd_x_6287 / conjecture_of_minFac_three_hundred_thirty_one / three_hundred_thirty_seven_dvd_x_2357 / conjecture_of_minFac_three_hundred_thirty_seven / three_hundred_forty_seven_dvd_x_1733 / conjecture_of_minFac_three_hundred_forty_seven / three_hundred_fifty_three_dvd_x_3881 / conjecture_of_minFac_three_hundred_fifty_three / three_hundred_fifty_nine_dvd_x_3947 / conjecture_of_minFac_three_hundred_fifty_nine / three_hundred_sixty_seven_dvd_x_6971 / conjecture_of_minFac_three_hundred_sixty_seven / three_hundred_seventy_three_dvd_x_2609 / conjecture_of_minFac_three_hundred_seventy_three / three_hundred_seventy_nine_dvd_x_9473 / conjecture_of_minFac_three_hundred_seventy_nine / three_hundred_eighty_three_dvd_x_1913 / conjecture_of_minFac_three_hundred_eighty_three / remaining_prime_from_two_hundred_ninety_four_le_three_hundred_seven / remaining_prime_from_three_hundred_eighty_four_le_three_hundred_eighty_nine / conjecture_of_minFac_le_three_hundred_eighty_nine_or_twin : propext, Classical.choice, Quot.sound (the 294–307 and 384–389 interval lemmas depend only on propext)
gcd_lt_q_of_dvd_pred / first_entry_k_one_iff_coprime / not_first_entry_of_gcd_eq_self / a_eq_self_iff_gcd_gt_one / not_first_entry_k_one_of_mod_two / minFac_lt_of_composite_lt_sq / gcd_gt_one_of_minFac_dvd_shift / three_hundred_ninety_seven_dvd_x_2777 / four_hundred_one_dvd_x_2003 / conjecture_of_minFac_le_four_hundred_one_or_twin : `propext, Classical.choice, Quot.sound` except `gcd_lt_q_of_dvd_pred` (`propext`) and the 390–397 / 398–401 interval lemmas (`propext` only). No `sorryAx`.
not_eq_sq_of_mod_five_three / not_eq_sq_of_mod_seven_five / sq_mod_eight / not_eq_sq_of_mod_eight / dvd_sq_add_two_of_eq_sq : `propext` (or a subset).
five_mul_sub_two_mod_five / not_eq_sq_five_mul_sub_two / seven_mul_sub_two_mod_seven / not_eq_sq_seven_mul_sub_two / five_mul_sub_two_odd / seven_mul_sub_two_odd / k_le_q_of_mod_six_five / k_mul_sub_two_le_sq_sub_two / two_dvd_mul_succ : `propext, Quot.sound`.
eq_minFac_sq_of_odd_composite_lt / minFac_mul_add_two_le_of_odd_composite_ne_sq / gcd_gt_one_of_odd_composite_ne_sq / eq_sq_of_coprime_odd_composite / five_mul_sub_two_minFac_window_le / gcd_gt_one_of_five_mul_sub_two_composite / seven_mul_sub_two_minFac_window_le / gcd_gt_one_of_seven_mul_sub_two_composite / minFac_lt_q_of_composite_window / not_eq_sq_kq_sub_two_of_mod_eight : `propext, Classical.choice, Quot.sound`. No `sorryAx`.
```

No `sorryAx`, `native_decide`, or `Lean.trustCompiler` on these declarations. `Classical.choice` enters through `Nat.find` in `exists_least_dvd` and through Mathlib `decide` instances. Full log: `experiments/a135508_axioms.log`. Recompiled 2026-09-13 09:49 UTC (square-obstruction continuation). The research compile had no `error:`, `warning:`, or `sorryAx`.

## Formalization audit (summary)

See `literature.md`. Nonvacuous; indices match OEIS `a(n)` for `n ≥ 1`; `p=2,3` hold; dichotomy `a(p-1) ∈ {1,p}` is proved. Not a loophole proof.

## What is not claimed

The frozen `conjecture` is not proved. Partial lemmas, the twin theorems, and finite scans are not a resolution. Self-review is not `independently_verified`.
