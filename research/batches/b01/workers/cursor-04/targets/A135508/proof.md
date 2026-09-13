# A135508 research note

Copyright 2026 The Formal Conjectures Authors.
Copyright 2026 Wentao Li.
Original Lean formalization: The Formal Conjectures Authors.
New proof development and write-up: Wentao Li.

AI assistance: Cursor Grok 4.6 Extra (cloud worker cursor-04), used for literature search, experiments, and Lean development. This note is not a claimed complete proof of `OeisA135508.conjecture`.

## Frozen target

```
OeisA135508.conjecture :
  ∀ (p : ℕ), Nat.Prime p → ¬Nat.Prime (p - 2) → OeisA135508.a (p - 1) = p
```

The frozen file is unchanged and still ends in `sorry`. Research lemmas import definitions and the `rfl` tests only. They do not use the `sorry` theorem.

## Closed form (proved)

For `n > 0`:

- `a n = (n+1) / gcd(x n, n+1)`
- `x (n+1) = x n * (a n + 2)`
- `a n ∣ n+1`
- `m ≤ n` implies `x m ∣ x n` (for `m > 0`)

For prime `p`: `a (p-1) = 1 ∨ a (p-1) = p`, and `a (p-1) = 1 ↔ p ∣ x (p-1)`.

For prime `p ≥ 5`: `p ∣ x (p-1) ↔ a (p-3) = p-2`.
Hence McEachen at `p` is equivalent to `gcd(x (p-3), p-2) > 1`, i.e. some prime factor of `p-2` already divides `x` by index `p-3`.

## Unconditional McEachen cases (proved)

1. `p = 2` and `p = 3`.
2. Every prime `p ≥ 7` with `p ≡ 2 (mod 3)` (equivalently `3 ∣ p-2`). Reason: `a 3 = 1` forces `3 ∣ x n` for all `n ≥ 4`, and `4 ≤ p-3`.
3. `5 ∣ p-2` and `p ≥ 7`. Reason: `a 2 = 3` forces `5 ∣ x n` for `n ≥ 3`.
4. Injected factors of `r+2` for primes `r ≥ 7`, `r ≡ 2 (mod 3)`:
   - `7 ∣ x n` for `n ≥ 47` (`47+2 = 49`), hence McEachen if `7 ∣ p-2` and `p ≥ 50`.
   - `13 ∣ x n` for `n ≥ 11`, hence McEachen if `13 ∣ p-2` and `p ≥ 14`.
   - `19 ∣ x n` for `n ≥ 17`.
   - `11 ∣ x n` for `n ≥ 53`.
   - `17 ∣ x n` for `n ≥ 83` (`5·17-2 = 83` prime).
   - `23 ∣ x n` for `n ≥ 113` (`5·23-2 = 113` prime).
   The general form is `conjecture_of_injected` / `conjecture_of_prime_injector` / `conjecture_of_five_prime_injector`.
5. Remaining primes with `lpf(p-2) ≤ 23` (`conjecture_of_minFac_le_twentythree`). The window `q(q+2) ≤ p-2` supplies the entry-index bounds.

## Twin primes without `C₁` (proved)

Cloitre’s inhibition lemma is unconditional: `a(p-1)=p` implies `a(p+1)=1`.

The smaller member of any twin pair `≥ 11` is `≡ 2 (mod 3)`. Combined with the mod-3 theorem, this gives Cloitre Proposition 6.3 **without** hypothesis `C₁`:

- `twin_pair_inhibition`: `p ≥ 11` prime and `p+2` prime ⇒ `a(p-1)=p` and `a(p+1)=1`.
- `larger_twin_eq_one`: larger twin `q ≥ 13` satisfies `a(q-1)=1`.

The pair `(5,7)` remains the unique exception among twins: `5 ≡ 2 (mod 3)` but `5 < 7`, and `a 4 = 1 ≠ 5`.

This is not McEachen (McEachen excludes `p-2` prime). It is the twin-detection half of Cloitre’s Hypothesis 6.11, now unconditional for `q ≥ 13`.

## Remaining gap (not proved)

The leftover primes are `p ≡ 1 (mod 3)` with `p-2` composite and `lpf(p-2) ≥ 29`. Then `p-2 ≡ 2 (mod 3)`, so some prime factor `q` of `p-2` is `≡ 2 (mod 3)` (`exists_remaining_factor`). If `q = 5` we are done. If `q ≥ 11`, the mod-3 theorem gives `a(q-1)=q`, so `q` does **not** divide `x(q-1)`. One needs a later injection: some index `r ≤ p-3` with `q ∣ a(r-1)+2`.

If `r` itself is a prime `≡ 2 (mod 3)`, then `r ≡ -2 (mod q)` and `r ≤ p-3` suffices (`q_dvd_x_of_prime_injector`, `conjecture_of_prime_injector`). For `lpf(p-2)=q` one has `p-2 ≥ q(q+2)` (`remaining_minFac_mul_add_two_le`). The square `p = q^2+2` is never an odd prime for `q > 3`. So a prime

`r = kq - 2 ≤ q(q+2)-1` with `k ≡ 2 (mod 3)` and `r ≥ 7`

would finish McEachen. Even `k` makes `kq-2` even (`not_prime_kq_sub_two_of_even`). If `k ≡ 1 (mod 3)` then `3 ∣ kq-2`, hence composite for `q ≥ 11` (`not_prime_kq_sub_two_of_k_mod_one`). The only prime-injector candidates are therefore `k ≡ 5 (mod 6)`. Existence of such an `r` is a Linnik-type statement in a fixed residue class modulo `6q`. Mathlib has Dirichlet’s theorem (`Nat.forall_exists_prime_gt_and_eq_mod`), which gives infinitely many primes in that class but no bound `r ≤ q(q+2)-1`. Current Linnik exponents (`L = 5`) are larger than `2`. Even the usual GRH bound is larger than `q^2` by a log factor. The bound was **not** assumed.

`conjecture_of_cases` splits the frozen type into `p=2`, `p=3`, `p ≡ 2 (mod 3)`, or a remaining injector. `not_q_dvd_x_le` proves that a prime `q ≡ 2 (mod 3)` with `q ≥ 7` does not divide `x n` for `0 < n ≤ q`.

Composite injection is also available: if `gcd(x(kq-3), kq-2)=1`, then `q` enters even when `kq-2` is composite (`q_dvd_x_of_coprime_shift`). When `kq-2` is prime the gcd is 1 by the mod-3 theorem. No uniform proof that some `k` in range has gcd `1` was obtained.

Deterministic experiments (`injector_bound.py`, `injector_mod.py`): for every prime `q ≡ 2 (mod 3)` with `11 ≤ q ≤ 5000`, a `k ≡ 5 (mod 6)` injector exists with `k ≤ q+2` (worst `k = 89` at `q = 4271`). A factorization scan to `n = 40000` found no McEachen failure and no composite `a(n)`. Finite checks are not a resolution.

Cloitre’s route (assume `C₁`, then Theorem 6.2) was not used. `C₁` is stronger than McEachen and remains open.

## 2-adic staircase (Cloitre 6.5, proved)

Proved: `v2(gcd)`, `v2(a n)`, `v2(x(n+1))`, odd-increment stability, dyadic blocks `exists_block`, the block formula `v2(x n) = 2 k + 2` on `2·4^k ≤ n ≤ 2·4^{k+1}-1` (`v2_x_ge_two`), and Cloitre’s identity `a(2·4^k-1)=2` for every `k` (`a_two_four_pow`). This is Cloitre Proposition 6.5 in Lean indexing. It does not by itself prove McEachen.

## Methods that did not finish the exact type

- Brute-force evaluation of `x n` (values explode; factorization tracking of `a n` is used instead).
- Claiming Cloitre Cor. 6.6 (needs `C₁`).
- Proving `q ∣ x(q^2-1)` in full generality (Epoch’s closest attempt; still open).
- Using `native_decide` or the frozen `sorry`.
- Using Mathlib Dirichlet without a Linnik bound.
- Using GRH or current Linnik `L=5` as if they implied `r ≤ q(q+2)-1`. They do not.

## Status

Partial lemmas only. The exact frozen proposition is not proved or disproved.
