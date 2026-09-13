# Verification — A001818-C1 / `cursor-01-r04`

## Commands

```bash
sha256sum FormalConjectures/OEIS/1818.lean
export LEAN_NUM_THREADS=2
lake env lean -DwarningAsError=true research/batches/b01/workers/cursor-01-r04/targets/A001818-C1/A001818.lean
python3 research/batches/b01/control/check_assignments.py --repo . --worker cursor-01-r04 --against 7a37b78ee539aab88ebbb77a2579f838e9fcc7a6
```

Source SHA-256: `1e41db84e11a5adb981526a75330a597a13ceef8479eb4fb4ef832256496dffe`.
Toolchain: `leanprover/lean4:v4.33.1`. Dependencies unchanged.

## Exact-type audit

The worker definition `sunMatrix` is definitionally the frozen inline matrix: `sunMatrix_eq_frozen` is `rfl`. Integer exponents: `int_sub_val` is `rfl`, and `#eval ((0 : Fin 3).val - (1 : Fin 3).val : ℤ)` is `-1`.

`#check` ascribes `OeisA1818.conjecture1` to
`∀ n, 1 ≤ n → ∀ ζ, IsPrimitiveRoot ζ (2*n) → (sunMatrix n ζ).permanent = (a n : ℂ)`,
which type-checks. The original `a` is used. The admitted `OeisA1818.conjecture1` is not used as a proof.

## Current kernel-checked lemmas (not a C1 solution)

`lake env lean -DwarningAsError=true` exit 0. Axioms of the proved lemmas are a subset of `propext`, `Classical.choice`, `Quot.sound`. Including:

```
'A001818C1.conjecture1_of_one' depends on axioms: [propext, Classical.choice, Quot.sound]
'A001818C1.calogero_kernel_sum' depends on axioms: [propext, Classical.choice, Quot.sound]
'A001818C1.det_calogero' depends on axioms: [propext, Classical.choice, Quot.sound]
'A001818C1.prod_zeta_perm' depends on axioms: [propext, Classical.choice, Quot.sound]
'A001818C1.sunMatrix_sub_ones_off' depends on axioms: [propext, Classical.choice, Quot.sound]
'A001818C1.det_calogero_eq_signed_sum' depends on axioms: [propext, Classical.choice, Quot.sound]
'A001818C1.permanent_sunMatrix_sub_ones' depends on axioms: [propext, Classical.choice, Quot.sound]
'A001818C1.signed_derangement_inv_sum' depends on axioms: [propext, Classical.choice, Quot.sound]
'A001818C1.cycleEdgeWeight_formPerm_cons' depends on axioms: [propext, Classical.choice, Quot.sound]
'A001818C1.sum_cycleEdgeWeight_cons_rotate' depends on axioms: [propext, Classical.choice, Quot.sound]
'A001818C1.sum_cycleEdgeWeight_ncycles' depends on axioms: [propext, Classical.choice, Quot.sound]
'A001818C1.cycleEdgeWeight_zeta' depends on axioms: [propext, Classical.choice, Quot.sound]
'A001818C1.listing_support_univ' depends on axioms: [propext, Classical.choice, Quot.sound]
'A001818C1.listing_inv_one_sub_sum' depends on axioms: [propext, Classical.choice, Quot.sound]
'A001818C1.ncycleToListing_listingPerm' depends on axioms: [propext, Classical.choice, Quot.sound]
'A001818C1.listingPerm_ncycleToListing' depends on axioms: [propext, Classical.choice, Quot.sound]
'A001818C1.ncycle_inv_one_sub_sum' depends on axioms: [propext, Classical.choice, Quot.sound]
'A001818C1.cycleEdgeWeight_ofSubtype' depends on axioms: [propext, Classical.choice, Quot.sound]
'A001818C1.sum_cycleEdgeWeight_replace_cycle' depends on axioms: [propext, Classical.choice, Quot.sound]
'A001818C1.sign_of_cycleType_replicate_two' depends on axioms: [propext, Classical.choice, Quot.sound]
'A001818C1.derangement_long_cycle_or_replicate_two' depends on axioms: [propext, Classical.choice, Quot.sound]
'A001818C1.inv_one_sub_prod_of_univ' depends on axioms: [propext, Classical.choice, Quot.sound]
'A001818C1.involution_unsigned_eq_neg_signed' depends on axioms: [propext, Classical.choice, Quot.sound]
'A001818C1.inv_one_sub_replace_cycle' depends on axioms: [propext, Classical.choice, Quot.sound]
'A001818C1.remainder_support_eq_compl' depends on axioms: [propext, Classical.choice, Quot.sound]
'A001818C1.ofSubtype_mul_remainder' depends on axioms: [propext, Classical.choice, Quot.sound]
'A001818C1.longPoints_mul_listing' depends on axioms: [propext, Classical.choice, Quot.sound]
'A001818C1.sum_eq_sum_longKey' depends on axioms: [propext, Classical.choice, Quot.sound]
'A001818C1.longKey_of_listing' depends on axioms: [propext, Classical.choice, Quot.sound]
'A001818C1.eq_listing_of_longKey' depends on axioms: [propext, Classical.choice, Quot.sound]
'A001818C1.long_fiber_inv_one_sub' depends on axioms: [propext, Classical.choice, Quot.sound]
'A001818C1.long_cycle_inv_one_sub_sum' depends on axioms: [propext, Classical.choice, Quot.sound]
'A001818C1.long_fiber_signed_inv_one_sub' depends on axioms: [propext, Classical.choice, Quot.sound]
'A001818C1.long_cycle_signed_inv_one_sub_sum' depends on axioms: [propext, Classical.choice, Quot.sound]
'A001818C1.unsigned_derangement_inv_sum' depends on axioms: [propext, Classical.choice, Quot.sound]
'A001818C1.permanent_sunMatrix_sub_ones_eq_a' depends on axioms: [propext, Classical.choice, Quot.sound]
'A001818C1.cayleyWeight_inv' depends on axioms: [propext, Classical.choice, Quot.sound]
'A001818C1.prod_sunMatrix_eq_cayleyWeight' depends on axioms: [propext, Classical.choice, Quot.sound]
'A001818C1.permanent_sunMatrix_eq_sum_cayleyWeight' depends on axioms: [propext, Classical.choice, Quot.sound]
'A001818C1.cayleyWeight_reverse_odd_cycle' depends on axioms: [propext, Classical.choice, Quot.sound]
'A001818C1.reverseOddCycle_involutive' depends on axioms: [propext, Classical.choice, Quot.sound]
'A001818C1.sum_cayleyWeight_eq_sum_no_odd' depends on axioms: [propext, Classical.choice, Quot.sound]
'A001818C1.permanent_sunMatrix_eq_sum_no_odd' depends on axioms: [propext, Classical.choice, Quot.sound]
'A001818C1.one_add_cayleyWeight_swap' depends on axioms: [propext, Classical.choice, Quot.sound]
'A001818C1.cayleySum_fin_two_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
'A001818C1.cayleyWeight_ofSubtype' depends on axioms: [propext, Classical.choice, Quot.sound]
'A001818C1.oddLongPoints_mul_swap' depends on axioms: [propext, Classical.choice, Quot.sound]
'A001818C1.oddLongPoints_ofSubtype_nonempty_iff' depends on axioms: [propext, Classical.choice, Quot.sound]
'A001818C1.cayleySum_ofSubtype' depends on axioms: [propext, Classical.choice, Quot.sound]
'A001818C1.cayleySum_term_swap_ofSubtype' depends on axioms: [propext, Classical.choice, Quot.sound]
'A001818C1.sum_cayleySum_term_swap_ofSubtype' depends on axioms: [propext, Classical.choice, Quot.sound]
'A001818C1.cycleOf_eq_swap_of_card_two' depends on axioms: [propext, Classical.choice, Quot.sound]
'A001818C1.exists_eq_swap_mul_ofSubtype' depends on axioms: [propext, Classical.choice, Quot.sound]
'A001818C1.sum_fiber_swap_ofSubtype' depends on axioms: [propext, Classical.choice, Quot.sound]
'A001818C1.cayleySum_sigma2' depends on axioms: [propext, Classical.choice, Quot.sound]
'A001818C1.cayley_triple_identity' depends on axioms: [propext, Classical.choice, Quot.sound]
'A001818C1.cayleyWeight_formPerm' depends on axioms: [propext, Classical.choice, Quot.sound]
'A001818C1.cayleyWeight_formPerm_cons' depends on axioms: [propext, Classical.choice, Quot.sound]
'A001818C1.sum_fiber_fixed' depends on axioms: [propext, Classical.choice, Quot.sound]
'A001818C1.cayleySum_sigma1' depends on axioms: [propext, Classical.choice, Quot.sound]
'A001818C1.cayleySum_split' depends on axioms: [propext, Classical.choice, Quot.sound]
'A001818C1.cayleySum_eq_sigma1_add_sigma2_add' depends on axioms: [propext, Classical.choice, Quot.sound]
'A001818C1.cayleyWeight_cons_rotate_eq_neg_path' depends on axioms: [propext, Classical.choice, Quot.sound]
'A001818C1.sum_cayleyWeight_cons_rotate' depends on axioms: [propext, Classical.choice, Quot.sound]
'A001818C1.sum_cayleyWeight_listings_eq_of_eqOn_compl' depends on axioms: [propext, Classical.choice, Quot.sound]
'A001818C1.sum_cayleyWeight_hamiltonian_eq_of_eqOn_compl' depends on axioms: [propext, Classical.choice, Quot.sound]
'A001818C1.sum_cayleyWeight_hamiltonian_eq_of_injective' depends on axioms: [propext, Classical.choice, Quot.sound]
'A001818C1.sum_cayleyWeight_hamiltonian_eq_of_card_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
'A001818C1.sum_cayleyWeight_hamiltonian_subtype_eq_fin' depends on axioms: [propext, Classical.choice, Quot.sound]
'A001818C1.support_ofSubtype_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
'A001818C1.cayleyWeight_ofSubtype_finset' depends on axioms: [propext, Classical.choice, Quot.sound]
'A001818C1.cycleSupportEquiv' depends on axioms: [propext, Classical.choice, Quot.sound]
'A001818C1.sum_cayleyWeight_cycles_support' depends on axioms: [propext, Classical.choice, Quot.sound]
'A001818C1.hamiltonianCayleySum_eq_cayleyHamConst' depends on axioms: [propext, Classical.choice, Quot.sound]
'A001818C1.hamiltonianCayleySum_subtype_eq_cayleyHamConst' depends on axioms: [propext, Classical.choice, Quot.sound]
'A001818C1.card_powersetCard_mem' depends on axioms: [propext, Classical.choice, Quot.sound]
'A001818C1.sum_cayleyWeight_even_cycles_through' depends on axioms: [propext, Classical.choice, Quot.sound]
'A001818C1.cayleyHamConst_one' depends on axioms: [propext, Classical.choice, Quot.sound]
'A001818C1.oddLongPoints_isCycle' depends on axioms: [propext, Classical.choice, Quot.sound]
'A001818C1.cayleySum_term_isCycle' depends on axioms: [propext, Classical.choice, Quot.sound]
'A001818C1.sum_cayleyWeight_long_even_cycles_through' depends on axioms: [propext, Classical.choice, Quot.sound]
'A001818C1.signMatrix_one' depends on axioms: [propext, Classical.choice, Quot.sound]
'A001818C1.permanent_succ_column_zero' depends on axioms: [propext, Classical.choice, Quot.sound]
'A001818C1.permanent_signMatrixOf_minor_rev' depends on axioms: [propext, Classical.choice, Quot.sound]
'A001818C1.permanent_signMatrix' depends on axioms: [propext, Classical.choice, Quot.sound]
'A001818C1.cayleySumOn_pair' depends on axioms: [propext, Classical.choice, Quot.sound]
'A001818C1.evenCycleSumThrough_eq_binom' depends on axioms: [propext, Classical.choice, Quot.sound]
'A001818C1.cayleyWeight_cycleOf_mul_remainder' depends on axioms: [propext, Classical.choice, Quot.sound]
'A001818C1.cayleySum_eq_one_add_even_cycles_of_card_two' depends on axioms: [propext, Classical.choice, Quot.sound]
```

The complementary fibres (`cayleySum_fibre_remainder`, `cayleySum_complementary_eq_inner`) are proved. Geometric Cayley matrices tend to the transposed sign matrix, so on even size `cayleySum(cayleyPowZero)` tends to 0 (`tendsto_cayleySum_powZero`). Strong induction on even cardinality gives complementary cancellation and `cayleySum = 0` whenever some coordinate is zero (`cayleySum_eq_zero_fin`). Paper identity (3.9) is `identity_three_nine` / `identity_three_nine_tail`. Recurrence (4.8) is `cayleySum_eq_recurrence`.

Theorem 1.1 is `cayleySum_eq_matching`. The root-of-unity matching evaluation is `matchingSum_zeta`. The worker theorems `conjecture1` and `conjecture1_frozen` compile with exit 0.

```
'A001818C1.cayleySum_eq_matching' depends on axioms: [propext, Classical.choice, Quot.sound]
'A001818C1.matchingSum_zeta' depends on axioms: [propext, Classical.choice, Quot.sound]
'A001818C1.conjecture1' depends on axioms: [propext, Classical.choice, Quot.sound]
'A001818C1.conjecture1_frozen' depends on axioms: [propext, Classical.choice, Quot.sound]
```

No `sorryAx`, `native_decide`, or `Lean.trustCompiler`. The admitted source theorem is used only in a `#check` ascription, not as a proof. Self-review cannot mark independently verified.

## Boundary

- `n = 1`: primitive 2nd root is `-1`; matrix is `I_2`; permanent `1 = a 1`.
- Off-diagonal denominators: `ζ^{i-j} ≠ 1` for `i ≠ j` on `Fin N`.
- Calogero circulant eigenvalues `{N-1,N-3,…,1-N}`; product `(-1)^n a n`.
- `per(M-J)` expands over derangements only; `∏_i ζ^{σi-i} = 1`.
