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
```

No `sorryAx`, `native_decide`, or `Lean.trustCompiler` in those lemmas. The general `n ≥ 1` identity is not yet proved.

## Boundary

- `n = 1`: primitive 2nd root is `-1`; matrix is `I_2`; permanent `1 = a 1`.
- Off-diagonal denominators: `ζ^{i-j} ≠ 1` for `i ≠ j` on `Fin N`.
- Calogero circulant eigenvalues `{N-1,N-3,…,1-N}`; product `(-1)^n a n`.
- `per(M-J)` expands over derangements only; `∏_i ζ^{σi-i} = 1`.
