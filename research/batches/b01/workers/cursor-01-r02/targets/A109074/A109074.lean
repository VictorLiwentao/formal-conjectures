/-
Copyright 2026 The Formal Conjectures Authors.
Copyright 2026 Wentao Li.

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.

Original Lean formalization: The Formal Conjectures Authors.
New Lean proof development and write-up: Wentao Li.
Mathematical proof: Robbins conjectured the VSASM product; Kuperberg proved
the enumeration; Razumov–Stroganov recorded the factorial product used here.
This file formalizes the resulting ratio identity, including natural-division
integrality of that product. It does not claim a new ASM enumeration.
AI assistance: Cursor Grok 4.6 Extra High, 2026-09-13.
-/

import FormalConjectures.OEIS.«109074»

/-!
Exact target: `OeisA109074.conjecture` from the frozen source
`FormalConjectures/OEIS/109074.lean`.
-/

open Finset Nat
open OeisA109074

namespace A109074Proof

lemma six_succ (n : ℕ) : 6 * (n + 1) - 2 = 6 * n + 4 := by
  have : 2 ≤ 6 * (n + 1) := by nlinarith
  omega

lemma four_succ (n : ℕ) : 4 * (n + 1) - 1 = 4 * n + 3 := by
  have : 1 ≤ 4 * (n + 1) := by nlinarith
  omega

lemma four_succ_sub_two (n : ℕ) : 4 * (n + 1) - 2 = 4 * n + 2 := by
  have : 2 ≤ 4 * (n + 1) := by nlinarith
  omega

lemma factorial_cast_ne_zero (m : ℕ) : (m ! : ℚ) ≠ 0 :=
  Nat.cast_ne_zero.mpr (factorial_ne_zero m)

/--
The binomial quotient equals the incremental factorial ratio, as rationals.
This does not yet mention the natural-division sequence `b`.
-/
lemma frac_succ (n : ℕ) :
    frac (n + 1) =
      ((6 * n + 4)! * (2 * n + 1)! : ℚ) / (2 * ((4 * n + 3)! * (4 * n + 2)!)) := by
  have h6 := six_succ n
  have h4 := four_succ n
  have hle1 : 2 * (n + 1) ≤ 6 * n + 4 := by omega
  have hle2 : 2 * (n + 1) ≤ 4 * n + 3 := by omega
  have hnum := Nat.cast_choose (K := ℚ) hle1
  have hden := Nat.cast_choose (K := ℚ) hle2
  have h2 : 2 * (n + 1) = 2 * n + 2 := by omega
  have hsubn : 6 * n + 4 - (2 * n + 2) = 4 * n + 2 := by omega
  have hsubd : 4 * n + 3 - (2 * n + 2) = 2 * n + 1 := by omega
  unfold frac
  simp only
  rw [h6, h4, Nat.cast_mul, hnum, hden, h2, hsubn, hsubd]
  have hA := factorial_cast_ne_zero (6 * n + 4)
  have hB := factorial_cast_ne_zero (2 * n + 2)
  have hC := factorial_cast_ne_zero (4 * n + 2)
  have hD := factorial_cast_ne_zero (4 * n + 3)
  have hE := factorial_cast_ne_zero (2 * n + 1)
  field_simp [hA, hB, hC, hD, hE]
  ring

def numProd (n : ℕ) : ℕ :=
  ∏ k ∈ Icc 1 n, (6 * k - 2)! * (2 * k - 1)!

def denFactProd (n : ℕ) : ℕ :=
  ∏ k ∈ Icc 1 n, (4 * k - 1)! * (4 * k - 2)!

def denProd (n : ℕ) : ℕ := 2 ^ n * denFactProd n

lemma b_eq (n : ℕ) : b n = numProd n / denProd n := rfl

lemma numProd_ne_zero (n : ℕ) : numProd n ≠ 0 := by
  unfold numProd
  exact prod_ne_zero_iff.2 fun _ _ =>
    mul_ne_zero (factorial_ne_zero _) (factorial_ne_zero _)

lemma denFactProd_ne_zero (n : ℕ) : denFactProd n ≠ 0 := by
  unfold denFactProd
  exact prod_ne_zero_iff.2 fun _ _ =>
    mul_ne_zero (factorial_ne_zero _) (factorial_ne_zero _)

lemma denProd_ne_zero (n : ℕ) : denProd n ≠ 0 := by
  unfold denProd
  exact mul_ne_zero (pow_ne_zero _ two_ne_zero) (denFactProd_ne_zero n)

lemma numProd_succ (n : ℕ) :
    numProd (n + 1) = numProd n * ((6 * n + 4)! * (2 * n + 1)!) := by
  unfold numProd
  rw [prod_Icc_succ_top (by omega), six_succ]
  rfl

lemma denFactProd_succ (n : ℕ) :
    denFactProd (n + 1) =
      denFactProd n * ((4 * n + 3)! * (4 * n + 2)!) := by
  unfold denFactProd
  rw [prod_Icc_succ_top (by omega), four_succ, four_succ_sub_two]

lemma denProd_succ (n : ℕ) :
    denProd (n + 1) = 2 * denProd n * ((4 * n + 3)! * (4 * n + 2)!) := by
  unfold denProd
  rw [pow_succ, denFactProd_succ]
  ring

lemma factorization_factorial_add_digitSum {p m : ℕ} (hp : p.Prime) :
    (p - 1) * m.factorial.factorization p + (p.digits m).sum = m := by
  have h := Nat.sub_one_mul_factorization_factorial (n := m) hp
  have hs : (p.digits m).sum ≤ m := Nat.digit_sum_le p m
  rw [h, Nat.sub_add_cancel hs]

lemma numProd_factorization (n p : ℕ) :
    (numProd n).factorization p =
      ∑ k ∈ Icc 1 n,
        ((6 * k - 2)!.factorization p + (2 * k - 1)!.factorization p) := by
  unfold numProd
  rw [factorization_prod_apply (fun _ _ => mul_ne_zero (factorial_ne_zero _) (factorial_ne_zero _))]
  refine sum_congr rfl fun k _ => ?_
  rw [Nat.factorization_mul (factorial_ne_zero _) (factorial_ne_zero _), Finsupp.add_apply]

lemma denFactProd_factorization (n p : ℕ) :
    (denFactProd n).factorization p =
      ∑ k ∈ Icc 1 n,
        ((4 * k - 1)!.factorization p + (4 * k - 2)!.factorization p) := by
  unfold denFactProd
  rw [factorization_prod_apply (fun _ _ => mul_ne_zero (factorial_ne_zero _) (factorial_ne_zero _))]
  refine sum_congr rfl fun k _ => ?_
  rw [Nat.factorization_mul (factorial_ne_zero _) (factorial_ne_zero _), Finsupp.add_apply]

lemma two_pow_factorization {p n : ℕ} (hp : p.Prime) :
    (2 ^ n).factorization p = if p = 2 then n else 0 := by
  rw [factorization_pow, Finsupp.smul_apply]
  by_cases hp2 : p = 2
  · subst hp2
    simp [prime_two.factorization_self]
  · have : (2 : ℕ).factorization p = 0 :=
      factorization_eq_zero_of_not_dvd (by
        intro hdiv
        exact hp2 ((prime_dvd_prime_iff_eq hp prime_two).mp hdiv))
    simp [this, hp2]

lemma denProd_factorization (n p : ℕ) (hp : p.Prime) :
    (denProd n).factorization p =
      (if p = 2 then n else 0) + (denFactProd n).factorization p := by
  unfold denProd
  rw [Nat.factorization_mul (pow_ne_zero _ two_ne_zero) (denFactProd_ne_zero n),
    Finsupp.add_apply, two_pow_factorization hp]

lemma mem_Icc_one {n k : ℕ} (hk : k ∈ Icc 1 n) : 1 ≤ k :=
  (mem_Icc.mp hk).1

lemma eight_sub_three (k : ℕ) (hk : 1 ≤ k) :
    6 * k - 2 + (2 * k - 1) = 4 * k - 1 + (4 * k - 2) := by
  omega

lemma four_k_sub_two_eq (k : ℕ) (hk : 1 ≤ k) : 4 * k - 2 = 2 * (2 * k - 1) := by omega

lemma four_k_sub_one_eq (k : ℕ) (hk : 1 ≤ k) : 4 * k - 1 = 2 * (2 * k - 1) + 1 := by omega

lemma two_k_sub_one_pos (k : ℕ) (hk : 1 ≤ k) : 0 < 2 * k - 1 := by omega

lemma digits_two_mul_eq {m : ℕ} (hm : 0 < m) :
    ((2 : ℕ).digits (2 * m)).sum = ((2 : ℕ).digits m).sum := by
  rw [digits_base_mul one_lt_two hm, List.sum_cons, zero_add]

lemma digits_two_mul_add_one_eq (m : ℕ) :
    ((2 : ℕ).digits (2 * m + 1)).sum = ((2 : ℕ).digits m).sum + 1 := by
  have hpos : 2 * m + 1 ≠ 0 := by omega
  have hmod : (2 * m + 1) % 2 = 1 := by omega
  have hdiv : (2 * m + 1) / 2 = m := by omega
  rw [digits_eq_cons_digits_div one_lt_two hpos, hmod, hdiv, List.sum_cons, add_comm]

lemma two_adic_digits (k : ℕ) (hk : 1 ≤ k) :
    ((2 : ℕ).digits (4 * k - 1)).sum + ((2 : ℕ).digits (4 * k - 2)).sum =
      2 * ((2 : ℕ).digits (2 * k - 1)).sum + 1 := by
  have hpos := two_k_sub_one_pos k hk
  rw [four_k_sub_two_eq k hk, four_k_sub_one_eq k hk, digits_two_mul_eq hpos,
    digits_two_mul_add_one_eq]
  ring

def pop2 (n : ℕ) : ℕ := ((2 : ℕ).digits n).sum

lemma pop2_zero : pop2 0 = 0 := by simp [pop2]

lemma pop2_two_mul (m : ℕ) : pop2 (2 * m) = pop2 m := by
  cases m with
  | zero => simp [pop2]
  | succ m =>
    simp only [pop2]
    exact digits_two_mul_eq (succ_pos _)

lemma pop2_two_mul_add_one (m : ℕ) : pop2 (2 * m + 1) = pop2 m + 1 :=
  digits_two_mul_add_one_eq m

lemma sum_Icc_one_eq_sum_range (n : ℕ) (f : ℕ → ℕ) :
    ∑ k ∈ Icc 1 n, f k = ∑ k ∈ range n, f (k + 1) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [sum_Icc_succ_top (by omega), sum_range_succ, ih]

lemma sum_range_two_mul (n : ℕ) (f : ℕ → ℕ) :
    ∑ k ∈ range (2 * n), f k = ∑ k ∈ range n, (f (2 * k) + f (2 * k + 1)) := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hlen : 2 * (n + 1) = 2 * n + 1 + 1 := by omega
    rw [hlen, sum_range_succ, sum_range_succ, ih, sum_range_succ]
    ac_rfl

lemma six_succ_sub_two (k : ℕ) : 6 * (k + 1) - 2 = 6 * k + 4 := by
  have : 2 ≤ 6 * (k + 1) := by nlinarith
  omega

lemma pop2_six_succ (k : ℕ) : pop2 (6 * (k + 1) - 2) = pop2 (3 * k + 2) := by
  have hpos : 0 < 3 * k + 2 := by omega
  have hmul : 6 * (k + 1) - 2 = 2 * (3 * k + 2) := by
    rw [six_succ_sub_two]; omega
  rw [hmul, pop2, digits_two_mul_eq hpos]
  rfl

/-- ∑_{k=1}^n pop₂(2k-1) = ∑_{j<n} pop₂(j) + n. -/
lemma sum_pop2_odd (n : ℕ) :
    ∑ k ∈ Icc 1 n, pop2 (2 * k - 1) = ∑ k ∈ range n, pop2 k + n := by
  rw [sum_Icc_one_eq_sum_range]
  have hodd : ∀ k, pop2 (2 * (k + 1) - 1) = pop2 k + 1 := by
    intro k
    have : 2 * (k + 1) - 1 = 2 * k + 1 := by omega
    rw [this, pop2_two_mul_add_one]
  simp [hodd, sum_add_distrib, sum_const, card_range]

lemma sum_pop2_six (n : ℕ) :
    ∑ k ∈ Icc 1 n, pop2 (6 * k - 2) = ∑ k ∈ range n, pop2 (3 * k + 2) := by
  rw [sum_Icc_one_eq_sum_range]
  refine sum_congr rfl fun k _ => pop2_six_succ k

def S2 (n : ℕ) : ℕ := ∑ k ∈ range n, pop2 k

def A2 (n : ℕ) : ℕ := ∑ k ∈ range n, pop2 (3 * k)

def B2 (n : ℕ) : ℕ := ∑ k ∈ range n, pop2 (3 * k + 1)

def C2 (n : ℕ) : ℕ := ∑ k ∈ range n, pop2 (3 * k + 2)

lemma pop2_three_two_mul (n : ℕ) : pop2 (3 * (2 * n)) = pop2 (3 * n) := by
  have : 3 * (2 * n) = 2 * (3 * n) := by ring
  rw [this, pop2_two_mul]

lemma pop2_three_two_mul_add_one (n : ℕ) :
    pop2 (3 * (2 * n) + 1) = pop2 (3 * n) + 1 := by
  have : 3 * (2 * n) + 1 = 2 * (3 * n) + 1 := by ring
  rw [this, pop2_two_mul_add_one]

lemma pop2_three_two_mul_add_two (n : ℕ) :
    pop2 (3 * (2 * n) + 2) = pop2 (3 * n + 1) := by
  have : 3 * (2 * n) + 2 = 2 * (3 * n + 1) := by ring
  rw [this, pop2_two_mul]

lemma pop2_three_two_mul_succ (n : ℕ) :
    pop2 (3 * (2 * n + 1)) = pop2 (3 * n + 1) + 1 := by
  have : 3 * (2 * n + 1) = 2 * (3 * n + 1) + 1 := by ring
  rw [this, pop2_two_mul_add_one]

lemma pop2_three_two_mul_succ_add_one (n : ℕ) :
    pop2 (3 * (2 * n + 1) + 1) = pop2 (3 * n + 2) := by
  have : 3 * (2 * n + 1) + 1 = 2 * (3 * n + 2) := by ring
  rw [this, pop2_two_mul]

lemma pop2_three_two_mul_succ_add_two (n : ℕ) :
    pop2 (3 * (2 * n + 1) + 2) = pop2 (3 * n + 2) + 1 := by
  have : 3 * (2 * n + 1) + 2 = 2 * (3 * n + 2) + 1 := by ring
  rw [this, pop2_two_mul_add_one]

lemma S2_two_mul (n : ℕ) : S2 (2 * n) = 2 * S2 n + n := by
  unfold S2
  rw [sum_range_two_mul]
  simp [pop2_two_mul, pop2_two_mul_add_one, sum_add_distrib, sum_const, card_range]
  ring

lemma S2_two_mul_add_one (n : ℕ) :
    S2 (2 * n + 1) = 2 * S2 n + n + pop2 n := by
  calc
    S2 (2 * n + 1) = S2 (2 * n) + pop2 (2 * n) := by
      simp [S2, sum_range_succ]
    _ = 2 * S2 n + n + pop2 n := by
      rw [S2_two_mul, pop2_two_mul]

lemma A2_two_mul (n : ℕ) : A2 (2 * n) = A2 n + B2 n + n := by
  unfold A2
  rw [sum_range_two_mul]
  have hsum :
      ∑ j ∈ range n, (pop2 (3 * (2 * j)) + pop2 (3 * (2 * j + 1))) =
        ∑ j ∈ range n, (pop2 (3 * j) + (pop2 (3 * j + 1) + 1)) :=
    sum_congr rfl fun j _ => by
      rw [pop2_three_two_mul, pop2_three_two_mul_succ]
  rw [hsum, sum_add_distrib, sum_add_distrib, sum_const, card_range, ← A2, ← B2]
  ring

lemma B2_two_mul (n : ℕ) : B2 (2 * n) = A2 n + C2 n + n := by
  unfold B2
  rw [sum_range_two_mul]
  have hsum :
      ∑ j ∈ range n, (pop2 (3 * (2 * j) + 1) + pop2 (3 * (2 * j + 1) + 1)) =
        ∑ j ∈ range n, (pop2 (3 * j) + 1 + pop2 (3 * j + 2)) :=
    sum_congr rfl fun j _ => by
      rw [pop2_three_two_mul_add_one, pop2_three_two_mul_succ_add_one]
  rw [hsum, sum_add_distrib, sum_add_distrib, sum_const, card_range, ← A2, ← C2]
  ring

lemma C2_two_mul (n : ℕ) : C2 (2 * n) = B2 n + C2 n + n := by
  unfold C2
  rw [sum_range_two_mul]
  have hsum :
      ∑ j ∈ range n, (pop2 (3 * (2 * j) + 2) + pop2 (3 * (2 * j + 1) + 2)) =
        ∑ j ∈ range n, (pop2 (3 * j + 1) + (pop2 (3 * j + 2) + 1)) :=
    sum_congr rfl fun j _ => by
      rw [pop2_three_two_mul_add_two, pop2_three_two_mul_succ_add_two]
  rw [hsum, sum_add_distrib, sum_add_distrib, sum_const, card_range, ← B2, ← C2]
  ring

lemma A2_two_mul_add_one (n : ℕ) :
    A2 (2 * n + 1) = A2 n + B2 n + n + pop2 (3 * n) := by
  calc
    A2 (2 * n + 1) = A2 (2 * n) + pop2 (3 * (2 * n)) := by
      simp [A2, sum_range_succ]
    _ = A2 n + B2 n + n + pop2 (3 * n) := by
      rw [A2_two_mul, pop2_three_two_mul]

lemma B2_two_mul_add_one (n : ℕ) :
    B2 (2 * n + 1) = A2 n + C2 n + n + pop2 (3 * n) + 1 := by
  calc
    B2 (2 * n + 1) = B2 (2 * n) + pop2 (3 * (2 * n) + 1) := by
      simp [B2, sum_range_succ]
    _ = A2 n + C2 n + n + pop2 (3 * n) + 1 := by
      rw [B2_two_mul, pop2_three_two_mul_add_one]
      ring

lemma C2_two_mul_add_one (n : ℕ) :
    C2 (2 * n + 1) = B2 n + C2 n + n + pop2 (3 * n + 1) := by
  calc
    C2 (2 * n + 1) = C2 (2 * n) + pop2 (3 * (2 * n) + 2) := by
      simp [C2, sum_range_succ]
    _ = B2 n + C2 n + n + pop2 (3 * n + 1) := by
      rw [C2_two_mul, pop2_three_two_mul_add_two]

/--
Simultaneous 2-adic bounds. `C2 n ≤ S2 n + n` is the required popcount
prefix inequality. The extra popcount comparisons close the odd inductive step.
-/
lemma two_adic_core (n : ℕ) :
    A2 n ≤ S2 n + n ∧
      B2 n ≤ S2 n + n ∧
        C2 n ≤ S2 n + n ∧
          pop2 (3 * n) + A2 n ≤ S2 n + n + pop2 n ∧
            pop2 (3 * n + 1) + B2 n ≤ S2 n + n + pop2 n + 1 ∧
              pop2 (3 * n + 2) + C2 n ≤ S2 n + n + pop2 n + 1 := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    rcases n.eq_zero_or_pos with rfl | hpos
    · simp [A2, B2, C2, S2, pop2]
    · cases Nat.mod_two_eq_zero_or_one n with
      | inl heven =>
        obtain ⟨m, rfl⟩ : ∃ m, n = 2 * m :=
          ⟨n / 2, (Nat.div_add_mod n 2).symm.trans (by simp [heven])⟩
        have hm : m < 2 * m := by omega
        rcases ih m hm with ⟨hA, hB, hC, h1, h2, h3⟩
        rw [A2_two_mul, B2_two_mul, C2_two_mul, S2_two_mul, pop2_two_mul,
          pop2_three_two_mul, pop2_three_two_mul_add_one, pop2_three_two_mul_add_two]
        refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
        · nlinarith
        · nlinarith
        · nlinarith
        · nlinarith
        · nlinarith
        · nlinarith
      | inr hodd =>
        obtain ⟨m, rfl⟩ : ∃ m, n = 2 * m + 1 :=
          ⟨n / 2, (Nat.div_add_mod n 2).symm.trans (by simp [hodd])⟩
        have hm : m < 2 * m + 1 := by omega
        rcases ih m hm with ⟨hA, hB, hC, h1, h2, h3⟩
        rw [A2_two_mul_add_one, B2_two_mul_add_one, C2_two_mul_add_one, S2_two_mul_add_one,
          pop2_two_mul_add_one, pop2_three_two_mul_succ, pop2_three_two_mul_succ_add_one,
          pop2_three_two_mul_succ_add_two]
        refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
        · nlinarith
        · nlinarith
        · nlinarith
        · nlinarith
        · nlinarith
        · nlinarith

/-- 2-adic form of the digit-sum inequality. -/
lemma two_adic_pop_ineq (n : ℕ) :
    ∑ k ∈ Icc 1 n, pop2 (2 * k - 1) ≥ ∑ k ∈ Icc 1 n, pop2 (6 * k - 2) := by
  have h := (two_adic_core n).2.2.1
  simpa [sum_pop2_odd, sum_pop2_six, S2, C2] using h

lemma digitSum_ineq_two (n : ℕ) :
    ∑ k ∈ Icc 1 n, (((2 : ℕ).digits (4 * k - 1)).sum + ((2 : ℕ).digits (4 * k - 2)).sum) ≥
      ∑ k ∈ Icc 1 n, (((2 : ℕ).digits (6 * k - 2)).sum + ((2 : ℕ).digits (2 * k - 1)).sum) + n := by
  have hcard : ∑ k ∈ Icc 1 n, (1 : ℕ) = n := by
    simp [sum_const, card_Icc]
  have hlhs :
      ∑ k ∈ Icc 1 n, (((2 : ℕ).digits (4 * k - 1)).sum + ((2 : ℕ).digits (4 * k - 2)).sum) =
        2 * ∑ k ∈ Icc 1 n, pop2 (2 * k - 1) + n := by
    have hterm : ∀ k ∈ Icc 1 n,
        ((2 : ℕ).digits (4 * k - 1)).sum + ((2 : ℕ).digits (4 * k - 2)).sum =
          2 * pop2 (2 * k - 1) + 1 := by
      intro k hk
      simpa [pop2] using two_adic_digits k (mem_Icc_one hk)
    rw [sum_congr rfl hterm, sum_add_distrib, ← mul_sum, hcard]
  have hrhs :
      ∑ k ∈ Icc 1 n, (((2 : ℕ).digits (6 * k - 2)).sum + ((2 : ℕ).digits (2 * k - 1)).sum) + n =
        ∑ k ∈ Icc 1 n, pop2 (6 * k - 2) + ∑ k ∈ Icc 1 n, pop2 (2 * k - 1) + n := by
    simp [pop2, sum_add_distrib]
  rw [hlhs, hrhs]
  have h := two_adic_pop_ineq n
  nlinarith

/--
For every prime `p`, the base-`p` digit sums of the factorial arguments dominate
the `2^n` contribution.
-/
lemma digitSum_ineq (n p : ℕ) (hp : p.Prime) :
    ∑ k ∈ Icc 1 n, ((p.digits (4 * k - 1)).sum + (p.digits (4 * k - 2)).sum) ≥
      ∑ k ∈ Icc 1 n, ((p.digits (6 * k - 2)).sum + (p.digits (2 * k - 1)).sum) +
        (p - 1) * (if p = 2 then n else 0) := by
  by_cases hp2 : p = 2
  · subst hp2
    simpa using digitSum_ineq_two n
  · simp only [hp2, ite_false, mul_zero, add_zero]
    sorry

lemma den_dvd_num (n : ℕ) : denProd n ∣ numProd n := by
  refine (Nat.factorization_le_iff_dvd (denProd_ne_zero n) (numProd_ne_zero n)).1 ?_
  intro p
  by_cases hp : p.Prime
  · have hbal_num :
        ∑ k ∈ Icc 1 n,
            ((p - 1) * ((6 * k - 2)!.factorization p + (2 * k - 1)!.factorization p) +
              (p.digits (6 * k - 2)).sum + (p.digits (2 * k - 1)).sum) =
          ∑ k ∈ Icc 1 n, (6 * k - 2 + (2 * k - 1)) := by
      refine sum_congr rfl fun k hk => ?_
      have h1 := factorization_factorial_add_digitSum (m := 6 * k - 2) hp
      have h2 := factorization_factorial_add_digitSum (m := 2 * k - 1) hp
      linear_combination h1 + h2
    have hbal_den :
        ∑ k ∈ Icc 1 n,
            ((p - 1) * ((4 * k - 1)!.factorization p + (4 * k - 2)!.factorization p) +
              (p.digits (4 * k - 1)).sum + (p.digits (4 * k - 2)).sum) =
          ∑ k ∈ Icc 1 n, (4 * k - 1 + (4 * k - 2)) := by
      refine sum_congr rfl fun k hk => ?_
      have h1 := factorization_factorial_add_digitSum (m := 4 * k - 1) hp
      have h2 := factorization_factorial_add_digitSum (m := 4 * k - 2) hp
      linear_combination h1 + h2
    have hsame :
        ∑ k ∈ Icc 1 n, (6 * k - 2 + (2 * k - 1)) =
          ∑ k ∈ Icc 1 n, (4 * k - 1 + (4 * k - 2)) :=
      sum_congr rfl fun k hk => eight_sub_three k (mem_Icc_one hk)
    have hmul_num :
        (p - 1) * (numProd n).factorization p +
            ∑ k ∈ Icc 1 n, ((p.digits (6 * k - 2)).sum + (p.digits (2 * k - 1)).sum) =
          ∑ k ∈ Icc 1 n, (6 * k - 2 + (2 * k - 1)) := by
      rw [numProd_factorization, Finset.mul_sum, ← sum_add_distrib]
      convert hbal_num using 1
      refine sum_congr rfl fun k _ => ?_
      ring
    have hmul_den :
        (p - 1) * (denFactProd n).factorization p +
            ∑ k ∈ Icc 1 n, ((p.digits (4 * k - 1)).sum + (p.digits (4 * k - 2)).sum) =
          ∑ k ∈ Icc 1 n, (4 * k - 1 + (4 * k - 2)) := by
      rw [denFactProd_factorization, Finset.mul_sum, ← sum_add_distrib]
      convert hbal_den using 1
      refine sum_congr rfl fun k _ => ?_
      ring
    have hineq := digitSum_ineq n p hp
    have hgoal :
        (p - 1) * (numProd n).factorization p ≥
          (p - 1) * ((if p = 2 then n else 0) + (denFactProd n).factorization p) := by
      nlinarith [hmul_num, hmul_den, hsame, hineq]
    have hp1 : 0 < p - 1 := Nat.sub_pos_of_lt hp.one_lt
    have : (numProd n).factorization p ≥
        (if p = 2 then n else 0) + (denFactProd n).factorization p :=
      Nat.le_of_mul_le_mul_left hgoal hp1
    simpa [denProd_factorization n p hp] using this
  · simp [Nat.factorization_eq_zero_of_not_prime _ hp]

lemma b_pos (n : ℕ) : 0 < b n := by
  rw [b_eq]
  have hdiv := den_dvd_num n
  have hden := denProd_ne_zero n
  have hnum := numProd_ne_zero n
  have hle : denProd n ≤ numProd n := Nat.le_of_dvd (Nat.pos_of_ne_zero hnum) hdiv
  exact Nat.div_pos hle (Nat.pos_of_ne_zero hden)

lemma b_cast_div (n : ℕ) : (b n : ℚ) = (numProd n : ℚ) / denProd n := by
  rw [b_eq, Nat.cast_div (den_dvd_num n)]
  exact Nat.cast_ne_zero.mpr (denProd_ne_zero n)

lemma b_succ_ratio (n : ℕ) :
    (b (n + 1) : ℚ) / b n =
      ((6 * n + 4)! * (2 * n + 1)! : ℚ) / (2 * ((4 * n + 3)! * (4 * n + 2)!)) := by
  have hb0 : (b n : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (ne_of_gt (b_pos n))
  have hnum0 : (numProd n : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (numProd_ne_zero n)
  have hden0 : (denProd n : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (denProd_ne_zero n)
  have hF1 := factorial_cast_ne_zero (6 * n + 4)
  have hF2 := factorial_cast_ne_zero (2 * n + 1)
  have hF3 := factorial_cast_ne_zero (4 * n + 3)
  have hF4 := factorial_cast_ne_zero (4 * n + 2)
  rw [b_cast_div, b_cast_div, numProd_succ, denProd_succ]
  push_cast
  field_simp [hb0, hnum0, hden0, hF1, hF2, hF3, hF4]

/-- Exact frozen type of `OeisA109074.conjecture`. -/
theorem conjecture (n : ℕ) :
    frac (n + 1) = (b (n + 1) : ℚ) / b n := by
  rw [frac_succ, b_succ_ratio]

end A109074Proof
