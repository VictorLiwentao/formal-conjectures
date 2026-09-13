# A063880 proof notes

Worker: cursor-05. These notes describe an incomplete independent attempt. They are not a claimed proof of the frozen theorems.

## Frozen targets

Let `A n` mean `0 < n` and `σ(n) = 2 usigma(n)`.

1. `∀ {n : ℕ}, A n → n % 216 = 108`
2. `∀ {n : ℕ}, IsPrimitiveTerm n → n = 108`

Neither is proved in Lean in this worker tree. The original theorems in `FormalConjectures/OEIS/63880.lean` are not used as proof steps.

## What is proved here

In `A063880.lean`, compiled with `lake env lean -DwarningAsError=true`:

- `usigma` is coprime-multiplicative, with the prime-power formula `usigma (p^k) = 1 + p^k` for `k > 0`.
- For `n ≠ 0`, `usigma n` is the product of `1 + p^k` over the factorization.
- On squarefree `n`, unitary divisors are all divisors, so `usigma n = σ 1 n`.
- If `A m` and `s` is squarefree and coprime to `m`, then `A (m * s)`. This is an independent form of the textbook helper `a_of_primitive_mul_squarefree`, without primitivity and without using that helper’s `sorry`.
- `n % 216 = 108` iff `n % 8 = 4` and `27 ∣ n`.
- For `n ≠ 0`, that is equivalent to `padicValNat 2 n = 2` and `3 ≤ padicValNat 3 n`.
- Concrete values: `usigma 4 = 5`, `usigma 27 = 28`, `usigma 108 = 140`.
- If `4m` is in `A` and `m` is odd, then `7 σ(m) = 10 usigma(m)`.
- Under that leftover equation, `padicValNat 3 m < 4`. In particular `3^4` cannot divide the odd part.
- If also `padicValNat 3 m = 3`, then `σ` and `usigma` agree on the 3-free part of `m`.

These lemmas are infrastructure and partial case analysis. They do not decide the open statements.

## Intended remaining argument

Write `ρ(n) = σ(n)/usigma(n)` for `n > 0`. Then `A n` iff `ρ(n) = 2`. The function `ρ` is coprime-multiplicative, and `ρ(p) = 1`, so only prime powers with exponent at least 2 affect `ρ`. Let `K` be the squareful kernel of `n`. Then `A n` iff `ρ(K) = 2`.

The known kernel is `K = 4 * 27 = 108`, since `ρ(4) = 7/5` and `ρ(27) = 10/7`.

By the CRT lemma, the congruence holds for every `n` with `A n` if every such kernel satisfies `v₂(K) = 2` and `v₃(K) ≥ 3`. Uniqueness of the primitive 108 follows if that kernel is exactly 108, together with the known decomposition (which must be proved independently if used).

The primitive decomposition itself is already known and is not claimed as new.

## Finite leftover experiments (not a proof)

For `n = 2^a * m` with `m` odd, the leftover is `2 / ρ(2^a)`. In particular:

- `a ≤ 1`: leftover `2` (odd squareful kernel)
- `a = 2`: leftover `10/7`
- `a = 3`: leftover `6/5`
- `a = 4`: leftover `34/31`

The script `experiments/abundancy_enum.py` does exact `Fraction` one- and two-prime fills. It found no fills other than the known `3^3` for leftover `10/7`. Empty one/two-prime searches are **not** a proof: three or more primes remain, and last-prime bounds grow when leftover is close to 1.

A broader recursive search (`experiments/leftover_search.py`) was written and is explicitly unverified. A first run did not return in a bounded time and was stopped.

## Gaps

- No Lean proof that `ρ(K) = 2` forces `v₂ = 2` and `v₃ ≥ 3`.
- No Lean proof that the only squareful kernel is 108.
- No independent proof yet of `powerful_of_isPrimitiveTerm` or `exists_primitive_of_a`.
- Odd kernels (`leftover 2`) and high `2`-powers are not ruled out by a complete finite case tree in Lean.

A claimed completion still requires the exact frozen types, a sorry-free compile, and `#print axioms` in `{propext, Classical.choice, Quot.sound}`.
