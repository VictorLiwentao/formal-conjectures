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
conjecture_of_seventeen_dvd / twentythree_dvd : propext, Classical.choice, Quot.sound
```

No `sorryAx`, `native_decide`, or `Lean.trustCompiler` on these declarations. `Classical.choice` enters through `Nat.find` in `exists_least_dvd` and through Mathlib `decide` instances. Full log: `experiments/a135508_axioms.log`.

## Formalization audit (summary)

See `literature.md`. Nonvacuous; indices match OEIS `a(n)` for `n ≥ 1`; `p=2,3` hold; dichotomy `a(p-1) ∈ {1,p}` is proved. Not a loophole proof.

## What is not claimed

The frozen `conjecture` is not proved. Partial lemmas, the twin theorems, and finite scans are not a resolution. Self-review is not `independently_verified`.
