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
- `σ 1 n = usigma n` iff `n` is squarefree, for `n > 0`. Combined with the previous item, `v₃(m) = 3` on leftover `10/7` forces the 3-free part of `m` to be squarefree.
- CRT plus the two valuations is recorded as `mod_216_of_A_of_valuations`: if `A n`, `v₂(n) = 2`, and `v₃(n) ≥ 3`, then `n % 216 = 108`. This is not yet the frozen theorem, because those valuations are not forced.
- If leftover `10/7` has `v₃ = 2`, the 3-free part `t` satisfies `91 σ(t) = 100 usigma(t)`. On that equation, `v₅(t) < 2`, `v₇(t) < 2`, and `v₁₁(t) < 3`. If also `v₁₁(t) = 2`, the 11-free part is not squarefree, and `v₁₃` of that part is `< 2`. After `11^2`, every prime `13 ≤ p ≤ 113` has `v_p < 2` on leftover `12200/12103`, and every `p ≥ 127` has cap `p/(p-1) ≤ 127/126 < 12200/12103`.
- If `8m` is in `A` with `m` odd (so `v₂ = 3`), then `5 σ(m) = 6 usigma(m)` and `v₃(m) < 2`. In particular `9` cannot divide the odd part of a term with `v₂ = 3`. Also `v₅(m) < 3`. If `v₅(m) = 2`, the 5-free part is not squarefree.
- If `A n` and `v₂(n) ≥ 3`, then `v₃(n) < 2`. Equivalently, `9` cannot divide such an `n`. This uses `ρ(8)ρ(9) = 13/6 > 2` and monotonicity in the two exponents.
- Leftover `6/5` cannot be a single prime power times a squarefree factor: `5^2` undershoots, `5^k` for `k ≥ 3` overshoots, primes `≥ 7` have cap `≤ 7/6 < 6/5`, and `3^k` for `k ≥ 2` overshoots.
- Every prime `p ≥ 5` undershoots leftover `10/7`: `ρ(p^k) < p/(p-1) ≤ 5/4 < 10/7`. So leftover `10/7` cannot be a single prime power `p^k` with `p ≥ 5` times a squarefree coprime factor.
- Caps: `{5,11}` and `{7,11}` cannot reach `10/7`. The only two-prime cap product that can reach `10/7` without `3` is `{5,7}`. Algebraically `ρ(125)ρ(343) > 10/7`. The rays `ρ(25)ρ(7^k)` and `ρ(5^k)ρ(49)` stay strictly below `10/7`.
- `ρ(p^a)` is strictly increasing in the exponent `a ≥ 1`. This is used to lift the `{5,7}` overshoot from exponents `(3,3)` to all `a,b ≥ 3`.
- Leftover `10/7` cannot be two squareful primes `p < q` both at least `5` times a squarefree coprime factor. The cases are `{5,7}` (undershoot on the axes, overshoot for `a,b ≥ 3`), `{5,q}` with `q ≥ 11` (cap `5/4 · 11/10 = 11/8 < 10/7`), and `{p,q}` with `p ≥ 7` and `q ≥ 11` (cap `7/6 · 11/10 = 77/60 < 10/7`).
- Three squareful primes all at least `7` cannot fill leftover `10/7`. The Euler-product cap is at most `7/6 · 11/10 · 13/12 = 1001/720 < 10/7`.
- Leftover `10/7` ω=3 with a factor `5` is constrained: `{5^2, 7^2, p^k}` undershoots for every `p ≥ 23`; Euler-product caps kill `{5,11,p}` for `p ≥ 29`, `{5,13,p}` for `p ≥ 23`, and `{5,17,p}` for `p ≥ 19`; the squares `{5,7,11}`, `{5,7,13}`, `{5,7,17}`, and `{5,7,19}` overshoot, so every exponent triple `≥ 2` overshoots for those four last primes.
- `ρ(25) cap(11) cap(q) < 10/7` for every `q ≥ 13`, so `{5^2, 11^b, q^c}` undershoots. Combined with the overshoots `ρ(125)ρ(121)ρ(13^2)` and `ρ(125)ρ(121)ρ(17^2)`, the triples `{5,11,13}` and `{5,11,17}` cannot fill leftover `10/7`. The triple `{5,11,19}` is also closed: `a=2` undershoots by the same cap, `{5^3,11^2,19^c}` undershoots, `{5^3,11^b,19^c}` with `b≥3` overshoots from `(3,3,2)`, and `a≥4` overshoots from `(4,2,2)`.
- `{5,11,23}` is closed: `a=2` and `a=3` undershoot, `{5^a,11^2,23^c}` undershoots for every `a`, and `a≥4` with `b≥3` overshoots from `(4,3,2)`. `{5,13,17}` is closed by a similar split on the 5-exponent.
- `{5,13,19}` is closed. `a≤4` undershoots (including `ρ(625) cap(13) cap(19)`), `{5^a,13^b,361}` undershoots, `{5^a,2197,6859}` undershoots, `{5^5,2197,19^c}` undershoots, `a≥6` with `b=3` and `c≥4` overshoots from `(6,3,4)`, and `a≥5` with `b≥4` and `c≥3` overshoots from `(5,4,3)`.
- `{5^3, 7^2, p^k}` with `k≥2` cannot fill leftover `10/7` for any prime `p≥23`: squares overshoot on `23≤p≤79`, `{5^3,7^2,83^2}` undershoots while `k≥3` overshoots, and Euler caps kill `p≥89`. `{5^2, 7^3, p^k}` is likewise closed: squares overshoot on `23≤p≤31`, and caps kill `p≥37`.
- `{5^a, 7^b}` with `a,b ≥ 3` already overshoots leftover `10/7`, so any extra positive factor still overshoots. This includes every ω≥3 kernel containing `5^a 7^b` with both exponents at least 3.
- `{5^2, 7^b, p^k}` with `b≥4` cannot fill leftover `10/7` for `p≥23` and `k≥2`: squares overshoot on `23≤p≤31`, the prime `p=37` undershoots only at `(b,k)=(4,2)` and `(5,2)` and overshoots from `(4,3)` and `(6,2)`, and `ρ(25) cap(7) cap(p)` kills `p≥41`.
- `{5^4, 7^2, p^k}` cannot fill leftover `10/7` for `p≥23` and `k≥2`: squares overshoot on `23≤p≤223`, and `ρ(625) ρ(49) cap(p)` kills `p≥227`.
- `{5^5, 7^2, p^k}` and `{5^6, 7^2, p^k}` are closed the same way, with square/cap splits at `337/347` and `383/389`. For `a≥7`, squares `{5^7,7^2,p^2}` overshoot on `p≤389`, the prime `p=397` undershoots only at `a=7,k=2` and overshoots from `(7,2,3)` and `(8,2,2)`, and `ρ(5^a) ρ(49) cap(p)` kills every `p≥401`.
- `{5^a, 7^b, p^k}` with `p ≥ 11` and `a,b,k ≥ 2` cannot fill leftover `10/7`. This is `not_seven_sigma_eq_ten_usigma_five_seven_prime`.
- An extra positive factor cannot repair an overshoot of leftover `10/7`. In particular every kernel containing `5^a 7^b 11^c` with `a,b,c≥2` overshoots, including ω≥4 supersets of `{5,7,11}`.
- Leftover `6/5` is impossible on a squarefree odd part: `5 σ = 6 usigma` and `σ = usigma` force `5 = 6`.
- Leftover `6/5` cannot be two squareful primes `p < q` both at least `5` times a squarefree coprime factor (`not_five_sigma_of_two_sq_primes`). The cases are: two primes `≥ 11` (Euler cap `11/10 · 13/12 < 6/5`); `{5^a, q^k}` with `q ≥ 7` (`a ≥ 3` overshoots from `5^3`, squares `{5^2, q^2}` overshoot for `7 ≤ q ≤ 151`, and `ρ(25) cap(q)` undershoots for `q ≥ 157`); `{7^a, q^k}` with `q ≥ 11` (squares overshoot for `11 ≤ q ≤ 17`, `{7,19}` undershoots only at exponents `(2,2)` and overshoots otherwise, `{7^2, q}` undershoots for `q ≥ 23` by `ρ(49) cap(q)`, `{7^a, q}` with `a ≥ 3` overshoots for `q ≤ 31` from `{7^3, q^2}`, and Euler `7/6 · q/(q-1)` undershoots for `q ≥ 37`). Combined with the unique-squareful-prime lemma, leftover `6/5` is closed at ω≤2.
- If `8m` is in `A` with `m` odd, the same two-prime obstruction applies to `m` (`not_A_of_eight_mul_two_sq_primes`).
- `{5^a, 7^b}` with `a,b ≥ 2` overshoots leftover `6/5` even after an extra positive factor, so every ω≥3 kernel containing both squareful primes `5` and `7` overshoots.
- `{11^2, 13^2, p^k}` cannot fill leftover `6/5` for primes `p ≥ 17` and `k ≥ 2`. Squares overshoot for `17 ≤ p ≤ 43`, and `ρ(121) ρ(169) cap(p)` undershoots for `p ≥ 47`. If also `p ≤ 43`, every exponent triple `a,b,k ≥ 2` overshoots.
- Leftover `6/5` on an arbitrary `m` cannot be three squareful primes `11,13,p` with `p ≥ 17` times a squarefree coprime factor (`not_five_sigma_of_three_sq_primes_eleven_thirteen`). The family is closed.
- `{13, 17, p}` cannot fill leftover `6/5` for any third prime `p ≥ 19`. The family is glued (`not_five_sigma_of_three_sq_primes_thirteen_seventeen`).
- `{11, 19, p}` cannot fill leftover `6/5` for any third prime `p ≥ 23`. The family is glued (`not_five_sigma_of_three_sq_primes_eleven_nineteen`).
- `{5^2, q^b, r^c}` undershoots leftover `6/5` for `313 ≤ q < r` (`five_sigma_lt_six_usigma_five_sq_two_large`), and that case is glued when `v_5=2`.
- `{11, 17, p}` cannot fill leftover `6/5` for any third prime `p ≥ 19`. The family is glued to an arbitrary `m` (`not_five_sigma_of_three_sq_primes_eleven_seventeen`).
- `{7^a, q^b, r^c}` undershoots leftover `6/5` for `71 ≤ q < r` (`not_five_sigma_of_three_sq_primes_seven_two_large`). Euler `7/6 · q/(q-1) · r/(r-1)` is at most `6/5` on that rectangle.
- `{7^a, q^b, r^c}` overshoots leftover `6/5` whenever `11 ≤ q ≤ 17` (`not_five_sigma_of_three_sq_primes_seven_q_le_seventeen`). The two-prime squares `{7^2, q^2}` already overshoot, and an extra positive factor cannot repair that.
- `{7, 19, r}` cannot fill leftover `6/5` for any third prime `r ≥ 23`. The family is glued (`not_five_sigma_of_three_sq_primes_seven_nineteen`). Squares overshoot for `23 ≤ r ≤ 7237`; `{7^3, 19^2}` and `{7^2, 19^3}` already overshoot without `r`; and `ρ(49) ρ(361) cap(r)` undershoots for `r ≥ 7243`.
- `{7, 23, r}` cannot fill leftover `6/5` for any third prime `r ≥ 29`. The family is glued (`not_five_sigma_of_three_sq_primes_seven_twenty_three`).
- Three squareful primes `11 ≤ p < q < r` with `q ≥ 23` undershoot leftover `6/5` (`not_five_sigma_of_three_sq_primes_ge_eleven_twenty_three`). Three squareful primes `13 ≤ p < q < r` with `q ≥ 19` likewise undershoot (`not_five_sigma_of_three_sq_primes_ge_thirteen_nineteen`).
- Leftover `10/7` on an arbitrary `m` cannot be three squareful primes `7 ≤ p < q < r` times a squarefree coprime factor (`not_seven_sigma_of_three_sq_primes_ge_seven`).
- Leftover `10/7` on an arbitrary `m` cannot be three squareful primes `5,7,r` with `r ≥ 11` times a squarefree coprime factor (`not_seven_sigma_of_three_sq_primes_five_seven`).
- Leftover `10/7` on an arbitrary `m` cannot be three squareful primes `5 < q < r` with `11 ≤ q` times a squarefree coprime factor (`not_seven_sigma_of_three_sq_primes_five`). Together with the two previous glues, leftover `10/7` is closed at ω=3.
- Leftover `10/7` on an arbitrary `m` cannot be four squareful primes `7 ≤ p < q < r < s` with `s ≥ 41` times a squarefree coprime factor (`not_seven_sigma_of_four_sq_primes_ge_seven`). The Euler-product cap is at most `7/6 · 11/10 · 13/12 · 41/40 < 10/7`. Remaining leftover `10/7` ω=4 includes last prime `17 ≤ s ≤ 37` and kernels that contain `5`.

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

The script `experiments/case_tree.py` classifies leftovers `10/7`, `100/91`, `6/5`, `34/31`, `22/21`, `130/127`, and odd leftover `2`. It reports: the only one-prime fill among these is `3^3` for `10/7`; all listed two-prime searches returned empty with no `INCOMPLETE` flag on the ω=2 last-prime bound. Three-or-more-prime fills are not thereby excluded. This is **not** a proof.

A broader recursive search (`experiments/leftover_search.py`) was written and is explicitly unverified. A first run did not return in a bounded time and was stopped.

The script `experiments/omega3_ten_seven.py` searches leftover `10/7` for three primes `≥ 5` using last-prime bounds. It reported no hits and stopped at `p = 7` because `{7,11,13}` already has cap below `10/7`. This is **not** a proof. In particular it does not cover ω≥4, and it is not the Lean ω=3-with-`5` case analysis.

## Gaps

- No Lean proof that `ρ(K) = 2` forces `v₂ = 2` and `v₃ ≥ 3`.
- No Lean proof that the only squareful kernel is 108.
- No independent proof yet of `powerful_of_isPrimitiveTerm` or `exists_primitive_of_a`.
- Odd kernels (`leftover 2`) and the remaining `v₂ ≥ 3` leftovers (`6/5` with ω≥3, `34/31`, …) are not ruled out by a complete finite case tree in Lean.
- Leftover `10/7` ω=3 is closed on an arbitrary `m`. Leftover `10/7` ω=4 with four primes `≥ 7` and last prime `≥ 41` is glued. Remaining leftover `10/7` work is ω=4 with last prime `≤ 37` or a factor `5`, ω≥5, leftover `100/91`, leftover `2`, and leftover `6/5` with ω≥3.
- Leftover `6/5` is closed for ω≤2 (squarefree, unique squareful prime, and two squareful primes `≥ 5`). ω≥3 remains except: every kernel containing squareful `5` and `7` overshoots; `{11,13,p}` is glued for every `p ≥ 17`; `{11,17,p}` is glued for every `p ≥ 19`; `{13,17,p}` is glued for every `p ≥ 19`; `{11,19,p}` is glued for every `p ≥ 23`; `{5^2,q,r}` is glued for `313 ≤ q < r`; `{7,q,r}` is glued for `11 ≤ q ≤ 23` and for `71 ≤ q < r`; every triple `11 ≤ p < q < r` with `q ≥ 23` is glued; every triple `13 ≤ p < q < r` with `q ≥ 19` is glued. Remaining triples include `{7,q,r}` with `29 ≤ q < 71` and `{5,q,r}` with `q < 313`.
- Leftover `100/91` after `11^2` still allows ω≥2 with primes `≥ 127`. Without `11^2`, the smallest squareful prime may be `≥ 13`.

A claimed completion still requires the exact frozen types, a sorry-free compile, and `#print axioms` in `{propext, Classical.choice, Quot.sound}`.
