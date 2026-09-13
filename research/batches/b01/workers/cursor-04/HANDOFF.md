# HANDOFF — cursor-04 / A135508

Worker: cursor-04
Exclusive target: `OeisA135508.conjecture` (`FormalConjectures/OEIS/135508.lean`)
Branch: `cursor/a135508-lcm-primes-770d`
(Cloud required `cursor/<name>-770d`; this is the actual branch.)

Do not start duplicate work on this declaration. Cursor-07 owns non-OEIS discovery; do not enter that scope.

## Status

`partial`. Frozen conjecture unproved. No prior exact solution found in the checked sources (`literature.md`). Statement matches McEachen; not defective. Cloitre Cor. 6.6 is conditional on `C₁` and is not a batch resolution. The implication itself is now `conjecture_of_C1` (no `sorryAx`).

Cloitre Prop. 6.5 is proved in the research file as `a_two_four_pow`. That is not McEachen.

Dirichlet existence of some prime injector is proved (`exists_prime_index_injector`, `q_dvd_x_eventually`). That does not bound the injector by `q(q+2)-1` and is not a resolution.

`conjecture_of_square_window` proves the frozen type *assuming* every prime `q ≥ 5` divides `x(q(q+2)-1)`. The window hypothesis is not proved. Miller–Rabin found no window failures for primes `q ≡ 2 (mod 3)` up to `1000000`.

If `n ≥ 7` and `3 ∣ a n` then `729 ∣ n+1`. If `n ≥ 9` then `2187 ∣ n+1`. If `n ≥ 10` then `6561 ∣ n+1`, using `a 9 = 1`. If `n ≥ 12` then `19683 ∣ n+1`, using `a 11 = 1`. If `n ≥ 13` then `59049 ∣ n+1`, using `a 12 = 1`. If `n ≥ 14` then `531441 ∣ n+1`, using `a 13 = 7`. Those are not McEachen. Also `a 12 = 1`, `a 13 = 7`, `a 14 = 1`.

Remaining McEachen holds if some prime injector of `lpf(p-2)` has `k ≤ q+2` (`conjecture_of_minFac_k_le`). Existence of such a `k` is the square-window gap. For `q ≡ 2 (mod 3)` one has `q ≡ 5 (mod 6)`, so `k = q` is admissible; primality of `q²-2` is sufficient, not necessary.

Remaining McEachen holds if one of `5q-2`, `7q-2`, `5s-2`, `7s-2` is prime (`conjecture_of_paired_injectors`). A scan of remaining primes `p < 200000` found 332 of 466 covered by that pairing. That is a proper subfamily, not a `∀p` proof.

`leftover_injectors.py`: all 466 leftover remaining primes `p < 200000` have some prime-factor injector inside the actual McEachen window `k ≤ (p-2)/r`. That is a finite check, not a counterexample and not a proof.

McEachen also holds when `gcd(q+2, p-2) > 1` for a prime `q ≡ 2 (mod 3)` (`conjecture_of_add_two_overlap`). That overlap is rare among leftover primes.

A first-order union bound on injector candidates `k ≡ 5 (mod 6)`, `k ≤ q` is negative. Mathlib Selberg is an upper-bound sieve only. That does not finish the window.

## Reproduce

```bash
git checkout cursor/a135508-lcm-primes-770d
sha256sum FormalConjectures/OEIS/135508.lean
# expect 3814549cee8601c96c59b923d7ece1c4b26a59b0fd134f49a93cbbc38e914b0b

LEAN_NUM_THREADS=2 lake --wfail build 'FormalConjectures.OEIS.«135508»'
LEAN_NUM_THREADS=2 lake env lean research/batches/b01/workers/cursor-04/targets/A135508/A135508.lean
LEAN_NUM_THREADS=2 lake env lean research/batches/b01/workers/cursor-04/targets/A135508/type_audit.lean

python3 research/batches/b01/control/check_assignments.py --repo . --worker cursor-04 --against 238f78bdd5701ae4c97a0d70d4e22e2d45770d7a
```

## What is proved (research file only)

- Closed form of `a`, dichotomy at primes, first-entry criterion `p | x(p-1) ↔ a(p-3)=p-2` for `p ≥ 5`.
- McEachen for `p=2,3` and all primes `p ≥ 7` with `p ≡ 2 (mod 3)`.
- Injected-factor families (`5,7,11,13,17,19,23,29,37,41,47,53,59,67,71,79,83,89,97,101,107`) and remaining McEachen when `lpf(p-2) ≤ 107` or a larger-twin least factor.
- McEachen when some prime factor of `p-2` is a larger twin `≥ 13` (`conjecture_of_larger_twin_dvd`). Combined: `conjecture_of_minFac_le_one_hundred_one_or_twin`.
- Tight remaining reduction `conjecture_of_minFac_entered`: it is enough that `lpf(p-2)` divides `x` by index `q(q+2)-1`.
- Composite shifts are not coprime injectors once that least factor has entered (`gcd_gt_one_of_composite_shift`).
- General prime-index injector `q_dvd_x_of_prime_index` (the index need only be `≡ 2 (mod 3)`).
- Dirichlet: some (unbounded) prime injector `kq-2 ≡ 2 (mod 3)` exists for every prime `q ≡ 2 (mod 3)` (`k ≡ 5 (mod 6)`) and every prime `q ≡ 1 (mod 3)` with `q ≥ 7` (`k ≡ 1 (mod 6)`). Hence those primes eventually divide `x`.
- If `n ≥ 3` and `3 ∣ a n`, then `9 ∣ n+1`. If `n ≥ 6`, then `81 ∣ n+1`. If `n ≥ 7`, then `729 ∣ n+1`. If `n ≥ 9`, then `2187 ∣ n+1`. If `n ≥ 10`, then `6561 ∣ n+1`. If `n ≥ 12`, then `19683 ∣ n+1`. If `n ≥ 13`, then `59049 ∣ n+1`. If `n ≥ 14`, then `531441 ∣ n+1`. Also `a 6 = 7`, `a 7 = 2`, `a 8 = 1`, `a 9 = 1`, `a 11 = 1`, `a 12 = 1`, `a 13 = 7`, `a 14 = 1`, `243 ∣ x n` for `n ≥ 7`, `729 ∣ x n` for `n ≥ 9`, `2187 ∣ x n` for `n ≥ 10`, `6561 ∣ x n` for `n ≥ 12`, `19683 ∣ x n` for `n ≥ 13`, `177147 ∣ x n` for `n ≥ 14`.
- First-entry: `dvd_x_succ_of_dvd_a_add_two`, `not_prime_dvd_x_succ`, `prime_dvd_a_add_two_of_first_entry`.
- Square-window packaging: `k_mul_sub_two_le_square`, `q_dvd_x_square_window_of_k_le`, `conjecture_of_minFac_k_le`. Existence of `k ≤ q+2` is not proved.
- `q_mod_six_five`: remaining `q ≡ 2 (mod 3)` are `≡ 5 (mod 6)`. `q_dvd_x_square_window_of_sq_sub_two` if `q²-2` is prime.
- Square-window instances `k = 17,19,23,25,29`.
- `conjecture_of_add_two_overlap` / `conjecture_of_remaining_add_two_overlap`: McEachen if some prime `q ≡ 2 (mod 3)` has `gcd(q+2, p-2) > 1`.
- `conjecture_of_square_window`: frozen type follows from `q ∣ x(q(q+2)-1)` for every prime `q ≥ 5`. Hypothesis not proved. Window holds for `q=5`, `q=7`, and larger twins.
- `prime_of_no_prime_dvd_lt` / `q_dvd_x_window_of_no_small_factor`: for `q ≡ 2 (mod 3)`, a `k ≡ 5 (mod 6)` with `k ≤ q` and no prime factor of `kq-2` below `q` is a prime injector in the window.
- `conjecture_of_C1`: Cloitre Cor. 6.6 as an implication from `C₁` on positive indices. Not a resolution.
- `conjecture_of_cofactor_seven`: remaining McEachen if a cofactor `s ≡ 1 (mod 3)` of `p-2` has `7s-2` prime and the complementary factor is at least `7`.
- `conjecture_of_cofactor_five`: remaining McEachen if a cofactor `s ≡ 2 (mod 3)` has `5s-2` prime and the complementary factor is at least `5`.
- `conjecture_of_minFac_five` / `eleven` / `thirteen` / `seven`: remaining McEachen if the corresponding `k·lpf(p-2)-2` is a prime in the square window.
- `conjecture_of_paired_injectors`: remaining McEachen if one of `5q-2`, `7q-2`, `5s-2`, `7s-2` is prime.
- Cloitre 6.7 as `cloitre_valuation_barrier`.
- Unconditional twin inhibition for pairs with smaller member `≥ 11` (Cloitre 6.3 without `C₁`).
- Cloitre 2-adic staircase `a(2·4^k-1)=2` for every `k`.
- Remaining-class reduction: a factor `q ≡ 2 (mod 3)` of `p-2`, the bound `q(q+2) ≤ p-2`, prime and coprime injectors.
- `not_q_dvd_x_le`: such a `q ≥ 7` does not divide `x n` for `0 < n ≤ q`.
- Even `k` and `k ≡ 1 (mod 3)` cannot give prime injectors for `q ≡ 2 (mod 3)`; remaining candidates are `k ≡ 5 (mod 6)`.
- `conjecture_of_cases` is the frozen type plus an injector hypothesis on the remaining class.

## Gap

See `proof.md`. Remaining McEachen primes have `lpf(p-2) ≥ 113` not a larger twin, and need a first-entry bound. Dirichlet, Linnik `L=5`, and the usual GRH bound do not give `r ≤ q(q+2)-1`. Finite scans are not a proof.

## Commit SHA

Research commit: `aeb3add3`
Branch: `cursor/a135508-lcm-primes-770d`
