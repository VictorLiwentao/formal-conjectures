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
- `a n + 2 = (n+1 + 2 gcd(x n, n+1)) / gcd(x n, n+1)` (`a_add_two_eq`)
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
   - `29 ∣ x n` for `n ≥ 317` (`11·29-2 = 317` prime).
   - `37 ∣ x n` for `n ≥ 257` (`7·37-2 = 257` prime).
   - `41 ∣ x n` for `n ≥ 449` (`11·41-2 = 449` prime).
   - `47 ∣ x n` for `n ≥ 233` (`5·47-2 = 233` prime).
   - `53 ∣ x n` for `n ≥ 263`.
   - `59 ∣ x n` for `n ≥ 293`.
   - `67 ∣ x n` for `n ≥ 467` (`7·67-2 = 467` prime).
   - `71 ∣ x n` for `n ≥ 353` (`5·71-2 = 353` prime).
   - `79 ∣ x n` for `n ≥ 1499` (`19·79-2 = 1499` prime).
   - `83 ∣ x n` for `n ≥ 911`.
   - `89 ∣ x n` for `n ≥ 443`.
   - `97 ∣ x n` for `n ≥ 677`.
   - `101 ∣ x n` for `n ≥ 503`.
   - `107 ∣ x n` for `n ≥ 2459` (`23·107-2 = 2459` prime).
   - `113 ∣ x n` for `n ≥ 563` (`5·113-2 = 563` prime).
   - `127 ∣ x n` for `n ≥ 887` (`7·127-2 = 887` prime).
   - `131 ∣ x n` for `n ≥ 653`.
   - `137 ∣ x n` for `n ≥ 683`.
   - `149 ∣ x n` for `n ≥ 743`.
   - `157 ∣ x n` for `n ≥ 1097` (`7·157-2 = 1097` prime).
   - `163 ∣ x n` for `n ≥ 4073` (`25·163-2 = 4073` prime).
   - `167 ∣ x n` for `n ≥ 2837` (`17·167-2 = 2837` prime).
   - `173 ∣ x n` for `n ≥ 863`.
   - `179 ∣ x n` for `n ≥ 3041` (`17·179-2 = 3041` prime).
   - `191 ∣ x n` for `n ≥ 953`.
   - `197 ∣ x n` for `n ≥ 983`.
   - `211 ∣ x n` for `n ≥ 2741` (`13·211-2 = 2741` prime).
   - `223 ∣ x n` for `n ≥ 1559` (`7·223-2 = 1559` prime).
   - `233 ∣ x n` for `n ≥ 1163`.
   - `239 ∣ x n` for `n ≥ 1193`.
   - `257 ∣ x n` for `n ≥ 1283`.
   - `263 ∣ x n` for `n ≥ 6047` (`23·263-2 = 6047` prime).
   - `269 ∣ x n` for `n ≥ 2957` (`11·269-2 = 2957` prime).
   - `277 ∣ x n` for `n ≥ 5261` (`19·277-2 = 5261` prime).
   - `281 ∣ x n` for `n ≥ 3089` (`11·281-2 = 3089` prime).
   - `227 ∣ x n` for `n ≥ 6581` (`29·227-2 = 6581` prime).
   - `251 ∣ x n` for `n ≥ 8783` (`35·251-2 = 8783` prime).
   - `389 ∣ x n` for `n ≥ 11279` (`29·389-2 = 11279` prime).
   The general form is `conjecture_of_injected` / `conjecture_of_prime_injector` / `conjecture_of_prime_index` / `conjecture_of_five_prime_injector`.
5. Remaining primes with `lpf(p-2) ≤ 29` (`conjecture_of_minFac_le_twenty_nine`), `lpf(p-2) ≤ 59` or a larger-twin least factor (`conjecture_of_minFac_le_fifty_nine_or_twin`), `lpf(p-2) ≤ 101` or a larger-twin least factor (`conjecture_of_minFac_le_one_hundred_one_or_twin`), `lpf(p-2) ≤ 107` or a larger-twin least factor (`conjecture_of_minFac_le_one_hundred_seven_or_twin`), `lpf(p-2) ≤ 149` or a larger-twin least factor (`conjecture_of_minFac_le_one_hundred_forty_nine_or_twin`), `lpf(p-2) ≤ 197` or a larger-twin least factor (`conjecture_of_minFac_le_one_hundred_ninety_seven_or_twin`), `lpf(p-2) ≤ 239` or a larger-twin least factor (`conjecture_of_minFac_le_two_hundred_thirty_nine_or_twin`), `lpf(p-2) ≤ 257` or a larger-twin least factor (`conjecture_of_minFac_le_two_hundred_fifty_seven_or_twin`), `lpf(p-2) ≤ 263` or a larger-twin least factor (`conjecture_of_minFac_le_two_hundred_sixty_three_or_twin`), `lpf(p-2) ≤ 269` or a larger-twin least factor (`conjecture_of_minFac_le_two_hundred_sixty_nine_or_twin`), `lpf(p-2) ≤ 277` or a larger-twin least factor (`conjecture_of_minFac_le_two_hundred_seventy_seven_or_twin`), and `lpf(p-2) ≤ 281` or a larger-twin least factor (`conjecture_of_minFac_le_two_hundred_eighty_one_or_twin`). The leftover threshold `281` enters at `k=11`. If `1 < gcd(p-2, 30)` and `p ≥ 7`, McEachen holds (`conjecture_of_gcd_thirty`). If `1 < gcd(p-2, 210)` and `p ≥ 50`, McEachen holds (`conjecture_of_gcd_two_hundred_ten`). Leftover least factors remain coprime to `210`.

## Twin primes without `C₁` (proved)

Cloitre’s inhibition lemma is unconditional: `a(p-1)=p` implies `a(p+1)=1`.

The smaller member of any twin pair `≥ 11` is `≡ 2 (mod 3)`. Combined with the mod-3 theorem, this gives Cloitre Proposition 6.3 **without** hypothesis `C₁`:

- `twin_pair_inhibition`: `p ≥ 11` prime and `p+2` prime ⇒ `a(p-1)=p` and `a(p+1)=1`.
- `larger_twin_eq_one`: larger twin `q ≥ 13` satisfies `a(q-1)=1`.

The pair `(5,7)` remains the unique exception among twins: `5 ≡ 2 (mod 3)` but `5 < 7`, and `a 4 = 1 ≠ 5`.

This is not McEachen (McEachen excludes `p-2` prime). It is the twin-detection half of Cloitre’s Hypothesis 6.11, now unconditional for `q ≥ 13`.

## Remaining gap (not proved)

The leftover primes are `p ≡ 1 (mod 3)` with `p-2` composite, `lpf(p-2) ≥ 293`, and that least factor not a larger twin and not among the explicit family `389`. The next non-twin leftover least factor is `293`. Then `p-2 ≡ 2 (mod 3)`, so some prime factor `q` of `p-2` is `≡ 2 (mod 3)` (`exists_remaining_factor`). If `q = 5` we are done. If `q ≥ 11`, the mod-3 theorem gives `a(q-1)=q`, so `q` does **not** divide `x(q-1)`. One needs a later injection: some index `r ≤ p-3` with `q ∣ a(r-1)+2`.

If `q` has not entered `x n`, then `q ∣ x(n+1)` if and only if `q ∣ n+1+2g` (`first_entry_iff_dvd_add`). That Euclid criterion does not by itself produce an in-window index for leftover `q ≥ 293`. The `30`-stock and `210`-stock lower bounds package the primes `2,3,5,7`; leftover least factors are coprime to `210`.

`conjecture_of_minFac_entered` records the tight remaining reduction: McEachen holds once `lpf(p-2)` divides `x` by index `q(q+2)-1`. `gcd_gt_one_of_composite_shift` shows that an odd composite `kq-2 ≡ 2 (mod 3)` is not a coprime injector once that least factor has already entered by its own square-window. Together these isolate the remaining gap as existence of a prime injector `kq-2 ≤ q(q+2)-1`, not a defect in the first-entry algebra.

`q_dvd_x_of_prime_index` injects any factor of `p-2` at a prime `kq-2 ≡ 2 (mod 3)`, including factors `≡ 1 (mod 3)` that are not twins. Cloitre Lemma 6.7 is now `cloitre_valuation_barrier`. If `3 ∣ n+1` and `n ≥ 4` then `gcd(x n, n+1) > 1`. If `n ≥ 3` and `3 ∣ a n`, then `9 ∣ n+1` (`nine_dvd_succ_of_three_dvd_a`). If `n ≥ 6` and `3 ∣ a n`, then `81 ∣ n+1` (`eighty_one_dvd_succ_of_three_dvd_a`), using `a 5 = 1` and `27 ∣ x 6`. If `n ≥ 7` and `3 ∣ a n`, then `729 ∣ n+1` (`seven_hundred_twenty_nine_dvd_succ_of_three_dvd_a`), using `a 6 = 7` so that `243 ∣ x n` for `n ≥ 7`, and `a 8 = 1`. If `n ≥ 9` and `3 ∣ a n`, then `2187 ∣ n+1`. These are C1 fragments for the prime 3, not remaining McEachen.

Dirichlet is now in the research file, still without a window bound. `exists_prime_index_injector` produces a prime `r = kq-2` with `k ≡ 5 (mod 6)` and `r ≡ 2 (mod 3)` for every prime `q ≡ 2 (mod 3)`, `q ≥ 5`. `exists_prime_index_injector_mod_one` does the same for `q ≡ 1 (mod 3)`, `q ≥ 7`, with `k ≡ 1 (mod 6)`. Hence every such `q` eventually divides `x` (`q_dvd_x_eventually`, `q_dvd_x_eventually_mod_one`). That is not McEachen: the frozen type needs the injector at or before index `p-3`, and the tight remaining case needs `r ≤ q(q+2)-1`.

`conjecture_of_square_window` packages the remaining exact reduction: if every prime `q ≥ 5` divides `x(q(q+2)-1)`, the frozen statement follows from `conjecture_of_minFac_entered` plus the mod-3 family and `p=2,3`. The hypothesis is not proved. A prime injector in the window is sufficient (`q_dvd_x_square_window_of_prime_index`, `q_dvd_x_square_window_of_exists`). Larger twins already meet the window (`larger_twin_dvd_square_window`). So do `q=5` and `q=7` (`five_dvd_x_square_window`, `seven_dvd_x_square_window`).

For `q ≡ 2 (mod 3)` and `k ≤ q` with `k ≡ 5 (mod 6)`, primality of `kq-2` is equivalent to having no prime factor `< q` (`prime_of_no_prime_dvd_lt`, since `kq-2 < q²`). That is `q_dvd_x_window_of_no_small_factor`. A first-order union bound on those residue classes is negative (`|A| ≈ q/6` candidates versus `∑_{p<q} |A|/p ≈ (q/6) log log q` hits), so this does not give an elementary existence proof. Mathlib’s Selberg sieve is an upper bound only.

Cloitre Corollary 6.6 is now `conjecture_of_C1`: the assumption `∀ n>0, a n = 1 ∨ (a n).Prime` implies the frozen type. That implication is not an assumption of `C₁`, and it is not a resolution.

If `p-2 = q s` with `q ≥ 7` and `s ≡ 1 (mod 3)` and `7s-2` prime, then McEachen holds (`conjecture_of_cofactor_seven`). If `s ≡ 2 (mod 3)` and `5s-2` prime, then McEachen holds (`conjecture_of_cofactor_five`). If `5·lpf(p-2)-2` is prime, remaining McEachen holds (`conjecture_of_minFac_five`); this applies to least factors `≡ 2 (mod 3)`. If `7·lpf(p-2)-2` is prime, remaining McEachen holds (`conjecture_of_minFac_seven`); this applies to least factors `≡ 1 (mod 3)`. The four disjuncts are packaged as `conjecture_of_paired_injectors`. A scan of remaining primes `p < 200000` found 466 such primes, of which 332 are covered by that pairing. The first uncovered example is `(p,q,s)=(17443,107,163)`. These are proper subfamilies, not a `∀p` proof.

If `n ≥ 9` and `3 ∣ a n`, then `2187 ∣ n+1` (`two_thousand_one_hundred_eighty_seven_dvd_succ_of_three_dvd_a`), using `a 8 = 1` so that `729 ∣ x n` for `n ≥ 9`. If `n ≥ 10` and `3 ∣ a n`, then `6561 ∣ n+1`, using `a 9 = 1` so that `2187 ∣ x n` for `n ≥ 10`. If `n ≥ 12` and `3 ∣ a n`, then `19683 ∣ n+1`, using `a 11 = 1` so that `6561 ∣ x n` for `n ≥ 12`. If `n ≥ 13` and `3 ∣ a n`, then `59049 ∣ n+1`, using `a 12 = 1` so that `19683 ∣ x n` for `n ≥ 13`. If `n ≥ 14` and `3 ∣ a n`, then `531441 ∣ n+1`, using `a 13 = 7` so that `177147 ∣ x n` for `n ≥ 14`. These are C1 fragments for the prime 3, not remaining McEachen.

The first-entry mechanism is now explicit: `dvd_x_succ_of_dvd_a_add_two`, `not_prime_dvd_x_succ`, and `prime_dvd_a_add_two_of_first_entry`. Using that chain, `7` does not divide `x 13`, so `a 13 = 7`. Also `a 12 = 1` (`13 ∣ x 12`) and `a 14 = 1` (`15 ∣ x 14`).

Any injector with `k ≤ q+2` lies in the square window (`k_mul_sub_two_le_square`, `q_dvd_x_square_window_of_k_le`). Remaining McEachen follows if some prime injector of `lpf(p-2)` has `k ≤ q+2` (`conjecture_of_minFac_k_le`). This does not prove existence of such a `k`. For `q ≡ 2 (mod 3)` one has `q ≡ 5 (mod 6)` (`q_mod_six_five`), so `k = q` is an admissible residue; primality of `q²-2` is sufficient (`q_dvd_x_square_window_of_sq_sub_two`) but not necessary. Square-window lemmas for `k = 17,19,23,25,29` are instances of `k ≤ q+2`.

The actual McEachen window for a factor `q` of `p-2` is `k ≤ (p-2)/q` (`k_mul_sub_two_le_of_cofactor`, `conjecture_of_factor_k_le_cofactor`, `conjecture_of_exists_factor_injector`). That is the remaining sufficient arithmetic condition. Existence is not proved.

An odd composite `n ≡ 2 (mod 3)` with `n < lpf(n)^3` has a prime factor `≡ 1 (mod 3)` (`exists_prime_factor_mod_one_of_lt_cube`). Remaining `p-2` below that cube therefore cannot be supported only by primes `≡ 2 (mod 3)` (`remaining_exists_mod_one_of_lt_cube`, `cube_le_of_all_prime_factors_mod_two`). The complementary injector of any such factor `r` with `k ≡ 1 (mod 6)` and `k ≥ 7` fits once `k ≤ (p-2)/r` (`conjecture_of_remaining_mod_one_k`). In particular `k=7` fits once `5 ∤ p-2` (`remaining_div_ge_minFac`, `conjecture_of_remaining_mod_one_seven`). Primality of `kr-2` is not proved.

Type B remaining numbers (every prime factor `≡ 2 (mod 3)`) satisfy `lpf^2 ≤ (p-2)/lpf` and `lpf^3 + 2 ≤ p` (`remaining_type_B_div_ge_sq`, `remaining_type_B_p_ge`). Remaining Type A numbers (`p-2 < lpf^3`) have prime cofactor `(p-2)/lpf` (`remaining_type_A_cofactor_prime`). If the least factor is `≡ 2 (mod 3)`, that cofactor is `≡ 1 (mod 3)` (`remaining_type_A_cofactor_mod_one`), so McEachen follows from primality of `7r-2` (`conjecture_of_remaining_type_A_mod_two_seven`). If the least factor is `≡ 1 (mod 3)`, that cofactor is `≡ 2 (mod 3)` (`remaining_type_A_cofactor_mod_two`), so McEachen follows from primality of `5r-2` (`conjecture_of_remaining_type_A_mod_one_five`). Primality of those complementary injectors is not proved.

After the `lpf ≤ 281` family, leftover Type B needs a non-twin least factor `≥ 293` that is `≡ 2 (mod 3)`, and `p ≥ 293^3 + 2`. Remaining McEachen in Type B follows if some injector of the least factor has `k ≤ lpf^2` (`conjecture_of_remaining_type_B_k_le`). Existence of that prime is not proved.

After overlap `q+2 ∣ p-2` is excluded, a remaining least factor `q ≡ 2 (mod 3)` satisfies `p-2 ≥ q(q+8)` (`remaining_minFac_mul_add_eight_le`). First-entry by index `q(q+8)-1` is then enough (`conjecture_of_minFac_entered_add_eight`). An injector with `k ≤ q+8` fills that window (`conjecture_of_minFac_k_le_add_eight`, `conjecture_of_minFac_mod_two_overlap_or_k_le_add_eight`). The extra candidate `k = q+6` is packaged as `q_dvd_x_add_eight_window_of_add_six`; `k = q` is `q_dvd_x_add_eight_window_of_sq_sub_two`. Primality of those values is not proved.

First-entry of leftover least factors `113` (`k=5`, index `563`), `127` (`k=7`, index `887`), `131` (`k=5`, index `653`), `137` (`k=5`, index `683`), `149` (`k=5`, index `743`), `157` (`k=7`, index `1097`), `163` (`k=25`, index `4073`), `167` (`k=17`, index `2837`), `173` (`k=5`, index `863`), `179` (`k=17`, index `3041`), `191` (`k=5`, index `953`), `197` (`k=5`, index `983`), `211` (`k=13`, index `2741`), `223` (`k=7`, index `1559`), `227` (`k=29`, index `6581`), `233` (`k=5`, index `1163`), `239` (`k=5`, index `1193`), `251` (`k=35`, index `8783`), `257` (`k=5`, index `1283`), `263` (`k=23`, index `6047`), `269` (`k=11`, index `2957`), `277` (`k=19`, index `5261`), `281` (`k=11`, index `3089`) and `389` (`k=29`, index `11279`) is proved, and remaining McEachen follows for those least factors and for every remaining prime with `lpf(p-2) ≤ 281` or a larger-twin least factor (`conjecture_of_minFac_le_two_hundred_eighty_one_or_twin`). That is not `∀p`. After this cutoff the leftover least factor is at least `293`.

McEachen also holds if some prime `q ≡ 2 (mod 3)` with `q ≤ p-3` satisfies `gcd(q+2, p-2) > 1` (`conjecture_of_add_two_overlap`, `conjecture_of_remaining_add_two_overlap`). Then a factor of `q+2` already divides `x q` and divides `p-2`. Among leftover primes `p < 200000` this overlap is rare (5 of 466). It is a proper subfamily.

If `r` itself is a prime `≡ 2 (mod 3)`, then `r ≡ -2 (mod q)` and `r ≤ p-3` suffices (`q_dvd_x_of_prime_injector`, `conjecture_of_prime_injector`). For `lpf(p-2)=q` one has `p-2 ≥ q(q+2)` (`remaining_minFac_mul_add_two_le`). The square `p = q^2+2` is never an odd prime for `q > 3`. So a prime

`r = kq - 2 ≤ q(q+2)-1` with `k ≡ 2 (mod 3)` and `r ≥ 7`

would finish McEachen for a factor `q ≡ 2 (mod 3)`. Even `k` makes `kq-2` even (`not_prime_kq_sub_two_of_even`). If `k ≡ 1 (mod 3)` then `3 ∣ kq-2`, hence composite for `q ≥ 11` (`not_prime_kq_sub_two_of_k_mod_one`). The only prime-injector candidates for such `q` are therefore `k ≡ 5 (mod 6)`. For a factor `r ≡ 1 (mod 3)` that is not a twin, the usable indices are primes `kr-2 ≡ 2 (mod 3)`, typically `k ≡ 1 (mod 6)` (`q_dvd_x_of_prime_index`). Existence of such an index below `q(q+2)-1` is a Linnik-type statement. Current Linnik exponents (`L = 5`) are larger than `2`. Even the usual GRH bound is larger than `q^2` by a log factor. The bound was **not** assumed.

`conjecture_of_cases` splits the frozen type into `p=2`, `p=3`, `p ≡ 2 (mod 3)`, or a remaining injector. `not_q_dvd_x_le` proves that a prime `q ≡ 2 (mod 3)` with `q ≥ 7` does not divide `x n` for `0 < n ≤ q`.

Composite injection is also available: if `gcd(x(kq-3), kq-2)=1`, then `q` enters even when `kq-2` is composite (`q_dvd_x_of_coprime_shift`). When `kq-2` is prime the gcd is 1 by the mod-3 theorem. A scan of first entries for primes `11 ≤ q ≤ 4000` up to `n = 30000` found **no** composite `kq-2` first entries: every recorded first entry was a prime injector. That scan is not a proof, but it indicates that composites in the window do not remove the Linnik barrier.

Deterministic experiments (`injector_bound.py`, `injector_mod.py`, `first_entry_shape.py`, `injector_window.py`, `window_miller.py`, `paired_injectors.py`, `leftover_injectors.py`, `chebyshev_gap.py`, `mod_one_factor.py`, `type_b.py`, `type_a_gaps.py`, `bonferroni.py`): for every prime `q ≡ 2 (mod 3)` with `11 ≤ q ≤ 30000`, a `k ≡ 5 (mod 6)` injector exists with `k ≤ q+2` (trial division). Miller–Rabin to `q ≤ 2000000` found **no** square-window or add-eight-window failures; the worst first `k` in that range was `311` at `q = 1944791`. An exact factorization scan to `n = 40000` found no McEachen failure (`3612` checked). For leftover remaining primes `p < 5000000` with `lpf(p-2) ≥ 157` (14783 such primes), Type A cofactors were prime in every case (0 failures of `remaining_type_A_cofactor_prime`), and **no** McEachen-window injector gap was found (worst covering `k = 83` at `p = 1664053`). There were 117 cube-size leftovers `p-2 ≥ lpf^3`; only one had every prime factor `≡ 2 (mod 3)`, namely `p = 167^2 · 179 + 2 = 4992133`, already covered by the proved `167` and `179` families. First-order Bonferroni/Mertens on square-window candidates is not a `∀q` proof: some small `q` have `∑ |A_p| < |A|` (e.g. 131, 149, 173) but 113, 157, 191, 197, 227, 251, 389, 1009, 5003 do not. Unsifted candidates remain positive (e.g. `q = 5003`: 154 of 834). Finite checks are not a resolution.

Cloitre’s route (assume `C₁`, then Theorem 6.2) is recorded as the implication `conjecture_of_C1`. `C₁` is stronger than McEachen and remains open.

## 2-adic staircase (Cloitre 6.5, proved)

Proved: `v2(gcd)`, `v2(a n)`, `v2(x(n+1))`, odd-increment stability, dyadic blocks `exists_block`, the block formula `v2(x n) = 2 k + 2` on `2·4^k ≤ n ≤ 2·4^{k+1}-1` (`v2_x_ge_two`), and Cloitre’s identity `a(2·4^k-1)=2` for every `k` (`a_two_four_pow`). This is Cloitre Proposition 6.5 in Lean indexing. It does not by itself prove McEachen.

## Methods that did not finish the exact type

- Brute-force evaluation of `x n` (values explode; factorization tracking of `a n` is used instead).
- Claiming Cloitre Cor. 6.6 (needs `C₁`).
- Proving `q ∣ x(q^2-1)` in full generality (Epoch’s closest attempt; still open).
- Using `native_decide` or the frozen `sorry`.
- Using Mathlib Dirichlet without a Linnik bound. The file now proves unbounded injectors; that still does not give `r ≤ q(q+2)-1`.
- Using GRH or current Linnik `L=5` as if they implied `r ≤ q(q+2)-1`. They do not.
- Treating `conjecture_of_square_window` or `conjecture_of_C1` as a proof of the frozen type. They are reductions, not a window bound and not a proof of `C₁`.
- Using a first-order sieve union bound on `k ≡ 5 (mod 6)`, `k ≤ q`. The count is negative.
- Treating `conjecture_of_paired_injectors` as a `∀p` proof. It is a proper subfamily.
- Treating a leftover scan with no McEachen-window gap as a proof. It is a finite check.
- Treating `conjecture_of_add_two_overlap` as a `∀p` proof. It needs `gcd(q+2, p-2) > 1`.
- Treating `conjecture_of_minFac_k_le` as a `∀p` proof. It needs a prime injector with `k ≤ q+2`.
- Treating `conjecture_of_minFac_k_le_add_eight` as a `∀p` proof. It needs a prime injector with `k ≤ q+8` after overlap is excluded.
- Treating `a 12 = 1`, `a 13 = 7`, `a 14 = 1`, or the 3-adic lifts `59049` and `531441` as remaining McEachen.
- Using Mathlib Chebyshev `θ(x) ≤ (log 4) x` on the product of leftover candidates `kq-2`. The resulting smoothness contradiction does not close at leftover `q ≥ 113` (`chebyshev_gap.py`).
- Treating first-entry of `163`, `167`, `179`, `227`, `277`, or `281` as a `∀p` proof. Those are explicit leftover minFac families.
- Treating `conjecture_of_gcd_thirty` / `conjecture_of_gcd_two_hundred_ten` as leftover McEachen. Those package the entered `30`/`210` stock; leftover least factors are coprime to `210`.
- Treating `first_entry_iff_dvd_add` as a window bound. It is the Euclid first-entry criterion, not existence of an in-window index.
- Treating `conjecture_of_remaining_mod_one_seven` / `exists_prime_factor_mod_one_of_lt_cube` / `conjecture_of_remaining_mod_one_k` / `conjecture_of_remaining_type_B_k_le` as a `∀p` proof. The cube forces a complementary residue class below `lpf^3` and a square cofactor in Type B; it does not prove the injector is prime.
- Treating `conjecture_of_minFac_le_one_hundred_forty_nine_or_twin` or `conjecture_of_minFac_le_one_hundred_ninety_seven_or_twin` as a `∀p` proof. Those lift the leftover cutoff from `107` to `149` and then to `197`.
- Treating `remaining_type_A_cofactor_prime` / `conjecture_of_remaining_type_A_mod_two_seven` as a `∀p` proof. Type A leftover is semiprime; primality of an in-window injector is not proved.
- Using a first-order Bonferroni count on leftover APs as a `∀q` proof. The harmonic sum diverges, and the exact count already fails for several leftover `q` (`bonferroni.py`).

## Status

Partial lemmas only. The exact frozen proposition is not proved or disproved. After the compiled `281` family the leftover least factor is `≥ 293`. This is not a resolution of the frozen type.
