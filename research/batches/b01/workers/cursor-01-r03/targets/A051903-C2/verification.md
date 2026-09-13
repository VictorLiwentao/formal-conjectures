# Verification — A051903-C2 / `cursor-01-r03`

## Commands

Source hash (must match the prompt):

```bash
sha256sum FormalConjectures/OEIS/51903.lean
```

Observed: `3a694eccc4bd92c14e28e609563bad0ecdfb8895f45c6de887b46fcfcd483db4`

Toolchain: Lean 4.33.1 (`leanprover/lean4:v4.33.1`). `lake-manifest.json` and dependencies were not changed.

Compile the worker proof (not a lake target; file lives outside `FormalConjectures/`):

```bash
export LEAN_NUM_THREADS=2
lake env lean -DwarningAsError=true research/batches/b01/workers/cursor-01-r03/targets/A051903-C2/A051903.lean
```

Assignment scope:

```bash
python3 research/batches/b01/control/check_assignments.py --repo . --worker cursor-01-r03
python3 research/batches/b01/control/check_assignments.py --repo . --worker cursor-01-r03 --against 1ee796fa5606a0027266111e53f9b6c5d11d62a6
```

Both: PASS. Changed paths are confined to `research/batches/b01/workers/cursor-01-r03/`.

## Exact-type audit

Frozen `OeisA51903.conjecture2`:

```lean
theorem conjecture2 :
    answer(sorry) ↔ ∃ n : ℕ, Odd n ∧ 1 < a n ∧ ∀ b : ℕ, b ^ n ≡ b ^ (a n) [MOD n]
```

Worker wrapper `A051903C2.conjecture2`:

```lean
theorem conjecture2 :
    answer(False) ↔ ∃ n : ℕ, Odd n ∧ 1 < a n ∧ ∀ b : ℕ, b ^ n ≡ b ^ (a n) [MOD n]
```

The only source-statement change is `answer(sorry)` to `answer(False)`. The original `a`, `Odd n`, `1 < a n`, and `∀ b` are unchanged. The file also contains

```lean
example :
    False ↔ ∃ n : ℕ, Odd n ∧ 1 < a n ∧ ∀ b : ℕ, b ^ n ≡ b ^ (a n) [MOD n] :=
  conjecture2
```

so the elaborated left-hand side is `False`, not the `answer(sorry) → True` placeholder.

Do not use `OeisA51903.conjecture2` (`sorry`) as a proof. The import is the definition `a` only.

`decide +native` appears only in the upstream tests `a_1`–`a_5`. The worker theorems do not depend on those tests.

Boundary checks in the proof, not native computation:

- `n = 0` is even, and `factorization 0 = 0`, so it is excluded by `Odd` and by `1 < a n`.
- `n = 1` is odd with `a 1 = 0`.
- `e ≥ 2` and odd `p ≥ 3` force `n ≥ p^e ≥ 9 > e`.

## Axioms and compile log

Worker proof SHA-256: `88417287b950e6e0fdde7387ffb624dc5185efea62e7075c917137018d10593c`.

Captured 2026-09-13T02:35:13Z, `lake env lean -DwarningAsError=true`, exit 0:

```
A051903C2.conjecture2 : False ↔ ∃ n, Odd n ∧ 1 < a n ∧ ∀ (b : ℕ), b ^ n ≡ b ^ a n [MOD n]
'A051903C2.no_odd_universal' depends on axioms: [propext, Classical.choice, Quot.sound]
'A051903C2.conjecture2' depends on axioms: [propext, Classical.choice, Quot.sound]
```

No `sorryAx`, extra axioms, `native_decide`, or `Lean.trustCompiler`. Full command transcript: `targets/A051903-C2/compile.log`.

## Formalization audit

- The all-`b` condition is instantiated at `b = 1+p` and reduced modulo `p^e`; the quantifier is not weakened.
- Maximum exponent uses the original `primeFactorsList`/`count`/`foldr max` definition.
- `n > e` is proved before `n - e`.
- The prime is odd; the argument is not applied to even `n`.
- Order of `1+p` is Mathlib `ZMod.orderOf_one_add_prime`, not an extra axiom.
- C1 and C3 are not claimed.
- C2 asks for an odd example and is answered NO. The equivalent A327295 all-terms-even question is answered YES. C3 remains excluded.

Self-review records `candidate_proof` only and cannot set `independently_verified`. Coordinator independent audit is pending.
