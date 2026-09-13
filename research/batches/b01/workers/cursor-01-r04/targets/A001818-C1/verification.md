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

`lake env lean -DwarningAsError=true` exit 0. Axioms of the proved lemmas:

```
'A001818C1.conjecture1_of_one' depends on axioms: [propext, Classical.choice, Quot.sound]
'A001818C1.zpow_sub_ne_one' depends on axioms: [propext, Classical.choice, Quot.sound]
'A001818C1.inv_one_sub_eq_sum' depends on axioms: [propext, Classical.choice, Quot.sound]
'A001818C1.denom_ne_zero' depends on axioms: [propext, Classical.choice, Quot.sound]
```

No `sorryAx`, `native_decide`, or `Lean.trustCompiler` in those lemmas. The general `n ≥ 1` identity is not yet proved.

## Boundary

- `n = 1`: primitive 2nd root is `-1`; matrix is `I_2`; permanent `1 = a 1`.
- Off-diagonal denominators: `ζ^{i-j} ≠ 1` for `i ≠ j` on `Fin N`.
