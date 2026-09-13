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

/-- `+1` class of the floor increment \(d(r,Q)\). -/
def deltaPos (Q r : ℕ) : Prop := Q ≤ 3 * r + 1 ∧ 2 * r + 1 < Q

/-- `-1` class of the floor increment \(d(r,Q)\). -/
def deltaNeg (Q r : ℕ) : Prop := Q ≤ 2 * r ∧ 3 * r + 1 < 2 * Q

instance {Q r : ℕ} : Decidable (deltaPos Q r) := by
  dsimp [deltaPos]
  infer_instance

instance {Q r : ℕ} : Decidable (deltaNeg Q r) := by
  dsimp [deltaNeg]
  infer_instance

lemma odd_pos_of {Q : ℕ} (h : Odd Q) : 0 < Q := by
  rcases h with ⟨k, rfl⟩
  omega

lemma deltaPos_lt_deltaNeg {Q r₁ r₂ : ℕ} (hp : deltaPos Q r₁) (hn : deltaNeg Q r₂) :
    r₁ < r₂ := by
  have := hp.2
  have := hn.1
  omega

lemma not_deltaPos_and_deltaNeg {Q r : ℕ} : ¬(deltaPos Q r ∧ deltaNeg Q r) := by
  intro ⟨hp, hn⟩
  exact (lt_irrefl r) (deltaPos_lt_deltaNeg hp hn)

lemma invol_lt {Q r : ℕ} (_hQ : 0 < Q) (hr : r < Q) : Q - 1 - r < Q := by omega

lemma invol_invol {Q r : ℕ} (_hQ : 0 < Q) (hr : r < Q) : Q - 1 - (Q - 1 - r) = r := by omega

lemma odd_invol {Q r : ℕ} (hQ : Odd Q) (hr : r < Q) (hro : Odd r) :
    Odd (Q - 1 - r) := by
  rcases hQ with ⟨k, rfl⟩
  rcases hro with ⟨m, rfl⟩
  have : m < k := by omega
  refine ⟨k - m - 1, ?_⟩
  omega

lemma even_invol {Q r : ℕ} (hQ : Odd Q) (hr : r < Q) (hrev : Even r) :
    Even (Q - 1 - r) := by
  rcases hQ with ⟨k, rfl⟩
  rcases hrev with ⟨m, hm⟩
  refine ⟨k - m, ?_⟩
  omega

lemma deltaPos_iff_invol {Q r : ℕ} (hQ : 0 < Q) (hr : r < Q) :
    deltaPos Q r ↔ deltaNeg Q (Q - 1 - r) := by
  unfold deltaPos deltaNeg
  have : Q - 1 - r < Q := invol_lt hQ hr
  constructor <;> intro h <;> omega

lemma div_eq_one {a b : ℕ} (h0 : 0 < b) (hle : b ≤ a) (hlt : a < 2 * b) : a / b = 1 := by
  rw [Nat.div_eq_sub_div h0 hle, Nat.div_eq_of_lt (by omega)]

lemma floor_inc_eq (Q r : ℕ) (hQ : 0 < Q) (hr : r < Q) :
    (3 * r + 1) / Q + (if deltaNeg Q r then 1 else 0) =
      (2 * r + 1) / Q + (2 * r) / Q + (if deltaPos Q r then 1 else 0) := by
  by_cases hp : deltaPos Q r
  · have hnp : ¬ deltaNeg Q r := fun hn => not_deltaPos_and_deltaNeg ⟨hp, hn⟩
    rw [if_neg hnp, if_pos hp]
    have hlt2 : 2 * r + 1 < Q := hp.2
    have h2r : 2 * r < Q := by omega
    have h3 : Q ≤ 3 * r + 1 := hp.1
    have h3lt : 3 * r + 1 < 2 * Q := by omega
    rw [Nat.div_eq_of_lt hlt2, Nat.div_eq_of_lt h2r, div_eq_one hQ h3 h3lt]
  · by_cases hn : deltaNeg Q r
    · rw [if_pos hn, if_neg hp]
      have h2 : Q ≤ 2 * r := hn.1
      have h2lt : 2 * r < 2 * Q := by omega
      have h21 : Q ≤ 2 * r + 1 := by omega
      have h21lt : 2 * r + 1 < 2 * Q := by omega
      have h3 : Q ≤ 3 * r + 1 := by omega
      have h3lt : 3 * r + 1 < 2 * Q := hn.2
      rw [div_eq_one hQ h2 h2lt, div_eq_one hQ h21 h21lt, div_eq_one hQ h3 h3lt]
    · rw [if_neg hn, if_neg hp]
      by_cases hsmall : 2 * r + 1 < Q
      · have h3lt : 3 * r + 1 < Q := by
          unfold deltaPos at hp
          omega
        rw [Nat.div_eq_of_lt hsmall, Nat.div_eq_of_lt (by omega : 2 * r < Q),
          Nat.div_eq_of_lt h3lt]
      · by_cases hbig : Q ≤ 2 * r
        · have h3ge : 2 * Q ≤ 3 * r + 1 := by
            unfold deltaNeg at hn
            omega
          have h2lt : 2 * r < 2 * Q := by omega
          have h21 : Q ≤ 2 * r + 1 := by omega
          have h21lt : 2 * r + 1 < 2 * Q := by omega
          have hle : Q ≤ 3 * r + 1 := by omega
          have h2eq : (2 * r) / Q = 1 := div_eq_one hQ hbig h2lt
          have h21eq : (2 * r + 1) / Q = 1 := div_eq_one hQ h21 h21lt
          have h3two : (3 * r + 1) / Q = 2 := by
            rw [Nat.div_eq_sub_div hQ hle, div_eq_one hQ (by omega) (by omega)]
          omega
        · have : 2 * r + 1 = Q := by omega
          have h2r : 2 * r < Q := by omega
          have h3 : Q ≤ 3 * r + 1 := by omega
          have h3lt : 3 * r + 1 < 2 * Q := by omega
          rw [this, Nat.div_self hQ, Nat.div_eq_of_lt h2r, div_eq_one hQ h3 h3lt]

def posCount (Q n : ℕ) : ℕ :=
  #{k ∈ Icc 1 n | deltaPos Q ((2 * k - 1) % Q)}

def negCount (Q n : ℕ) : ℕ :=
  #{k ∈ Icc 1 n | deltaNeg Q ((2 * k - 1) % Q)}

lemma posCount_zero (Q : ℕ) : posCount Q 0 = 0 := by simp [posCount]

lemma negCount_zero (Q : ℕ) : negCount Q 0 = 0 := by simp [negCount]

lemma card_pos_odd_eq_neg_odd (Q : ℕ) (hQ : Odd Q) :
    #{r ∈ range Q | deltaPos Q r ∧ Odd r} = #{r ∈ range Q | deltaNeg Q r ∧ Odd r} := by
  have hpos : 0 < Q := odd_pos_of hQ
  refine card_nbij' (fun r => Q - 1 - r) (fun r => Q - 1 - r) ?maps ?maps' ?linv ?rinv
  · intro r hr
    have hmem := (mem_filter.mp (by exact hr))
    -- `hr` is already a Finset membership after coercion
    have hrQ : r < Q := by
      have : r ∈ (range Q).filter (fun r => deltaPos Q r ∧ Odd r) := hr
      exact mem_range.mp (mem_filter.mp this).1
    have hpred := (mem_filter.mp (show r ∈ (range Q).filter (fun r => deltaPos Q r ∧ Odd r) from hr)).2
    exact mem_filter.mpr ⟨mem_range.mpr (invol_lt hpos hrQ),
      (deltaPos_iff_invol hpos hrQ).mp hpred.1, odd_invol hQ hrQ hpred.2⟩
  · intro r hr
    have hrQ : r < Q := by
      have : r ∈ (range Q).filter (fun r => deltaNeg Q r ∧ Odd r) := hr
      exact mem_range.mp (mem_filter.mp this).1
    have hpred := (mem_filter.mp (show r ∈ (range Q).filter (fun r => deltaNeg Q r ∧ Odd r) from hr)).2
    have hr' : Q - 1 - r < Q := invol_lt hpos hrQ
    refine mem_filter.mpr ⟨mem_range.mpr hr', ?_, odd_invol hQ hrQ hpred.2⟩
    exact (deltaPos_iff_invol hpos hr').mpr (by simpa [invol_invol hpos hrQ] using hpred.1)
  · intro r hr
    have hrQ : r < Q := by
      have : r ∈ (range Q).filter (fun r => deltaPos Q r ∧ Odd r) := hr
      exact mem_range.mp (mem_filter.mp this).1
    exact invol_invol hpos hrQ
  · intro r hr
    have hrQ : r < Q := by
      have : r ∈ (range Q).filter (fun r => deltaNeg Q r ∧ Odd r) := hr
      exact mem_range.mp (mem_filter.mp this).1
    exact invol_invol hpos hrQ

lemma card_pos_even_eq_neg_even (Q : ℕ) (hQ : Odd Q) :
    #{r ∈ range Q | deltaPos Q r ∧ Even r} = #{r ∈ range Q | deltaNeg Q r ∧ Even r} := by
  have hpos : 0 < Q := odd_pos_of hQ
  refine card_nbij' (fun r => Q - 1 - r) (fun r => Q - 1 - r) ?maps ?maps' ?linv ?rinv
  · intro r hr
    have hrQ : r < Q := by
      have : r ∈ (range Q).filter (fun r => deltaPos Q r ∧ Even r) := hr
      exact mem_range.mp (mem_filter.mp this).1
    have hpred := (mem_filter.mp (show r ∈ (range Q).filter (fun r => deltaPos Q r ∧ Even r) from hr)).2
    exact mem_filter.mpr ⟨mem_range.mpr (invol_lt hpos hrQ),
      (deltaPos_iff_invol hpos hrQ).mp hpred.1, even_invol hQ hrQ hpred.2⟩
  · intro r hr
    have hrQ : r < Q := by
      have : r ∈ (range Q).filter (fun r => deltaNeg Q r ∧ Even r) := hr
      exact mem_range.mp (mem_filter.mp this).1
    have hpred := (mem_filter.mp (show r ∈ (range Q).filter (fun r => deltaNeg Q r ∧ Even r) from hr)).2
    have hr' : Q - 1 - r < Q := invol_lt hpos hrQ
    refine mem_filter.mpr ⟨mem_range.mpr hr', ?_, even_invol hQ hrQ hpred.2⟩
    exact (deltaPos_iff_invol hpos hr').mpr (by simpa [invol_invol hpos hrQ] using hpred.1)
  · intro r hr
    have hrQ : r < Q := by
      have : r ∈ (range Q).filter (fun r => deltaPos Q r ∧ Even r) := hr
      exact mem_range.mp (mem_filter.mp this).1
    exact invol_invol hpos hrQ
  · intro r hr
    have hrQ : r < Q := by
      have : r ∈ (range Q).filter (fun r => deltaNeg Q r ∧ Even r) := hr
      exact mem_range.mp (mem_filter.mp this).1
    exact invol_invol hpos hrQ

lemma odd_add_one_div_two (Q : ℕ) (hQ : Odd Q) : (Q + 1) / 2 = Q / 2 + 1 := by
  rcases hQ with ⟨k, rfl⟩
  omega

lemma two_mul_mid_sub_one (Q : ℕ) (hQ : Odd Q) : 2 * ((Q + 1) / 2) - 1 = Q := by
  rcases hQ with ⟨k, rfl⟩
  omega

lemma le_mid_sub_one_of_odd {Q k : ℕ} (hQ : Odd Q) (hk : 1 ≤ k)
    (h : 2 * k - 1 < Q) : k ≤ (Q + 1) / 2 - 1 := by
  rcases hQ with ⟨a, rfl⟩
  omega

lemma residue_period_shift {Q q j : ℕ} (_hQ : 0 < Q) (hj : 1 ≤ j) :
    (2 * (q * Q + j) - 1) % Q = (2 * j - 1) % Q := by
  have h1 : 1 ≤ 2 * j := by omega
  have h2 : 1 ≤ 2 * (q * Q + j) := by omega
  have hsum : 2 * (q * Q + j) - 1 = (2 * j - 1) + Q * (2 * q) := by
    zify [h1, h2]
    ring
  rw [hsum, Nat.add_mul_mod_self_left]

lemma Icc_union_split {a b c : ℕ} (h1 : a ≤ b + 1) (h2 : b ≤ c) :
    Icc a c = Icc a b ∪ Icc (b + 1) c := by
  ext x
  simp [mem_union, mem_Icc]
  omega

lemma disjoint_Icc_succ (a b c : ℕ) :
    Disjoint (Icc a b) (Icc (b + 1) c) := by
  refine disjoint_left.2 ?_
  intro x ha hb
  simp [mem_Icc] at ha hb
  omega

lemma succ_mul_eq (q Q : ℕ) : (q + 1) * Q = q * Q + Q := by ring

lemma filter_delta_card_block (P : ℕ → Prop) [DecidablePred P] (Q q : ℕ) (hQ : 0 < Q) :
    #{k ∈ Icc (q * Q + 1) ((q + 1) * Q) | P ((2 * k - 1) % Q)} =
      #{j ∈ Icc 1 Q | P ((2 * j - 1) % Q)} := by
  have hsucc := succ_mul_eq q Q
  refine card_nbij' (fun k => k - q * Q) (fun j => q * Q + j) ?_ ?_ ?_ ?_
  · intro k hk
    have hk' := mem_filter.mp (show k ∈ (Icc (q * Q + 1) ((q + 1) * Q)).filter
        (fun k => P ((2 * k - 1) % Q)) from hk)
    have hI := mem_Icc.mp hk'.1
    have hle : q * Q ≤ k := le_trans (Nat.le_add_right (q * Q) 1) hI.1
    have hj1 : 1 ≤ k - q * Q := Nat.le_sub_of_add_le' hI.1
    have hj2 : k - q * Q ≤ Q :=
      Nat.sub_le_iff_le_add'.mpr (hsucc ▸ hI.2)
    have hk_eq : k = q * Q + (k - q * Q) := by
      rw [add_comm, Nat.sub_add_cancel hle]
    have hres : (2 * k - 1) % Q = (2 * (k - q * Q) - 1) % Q := by
      have h := residue_period_shift (Q := Q) (q := q) (j := k - q * Q) hQ hj1
      rwa [← hk_eq] at h
    refine mem_filter.mpr ⟨mem_Icc.mpr ⟨hj1, hj2⟩, hres ▸ hk'.2⟩
  · intro j hj
    have hj' := mem_filter.mp (show j ∈ (Icc 1 Q).filter
        (fun j => P ((2 * j - 1) % Q)) from hj)
    have hI := mem_Icc.mp hj'.1
    have hres : (2 * (q * Q + j) - 1) % Q = (2 * j - 1) % Q :=
      residue_period_shift hQ hI.1
    refine mem_filter.mpr ⟨mem_Icc.mpr ⟨Nat.add_le_add_left hI.1 _, hsucc ▸
        Nat.add_le_add_left hI.2 _⟩, hres ▸ hj'.2⟩
  · intro k hk
    have hk' := mem_filter.mp (show k ∈ (Icc (q * Q + 1) ((q + 1) * Q)).filter
        (fun k => P ((2 * k - 1) % Q)) from hk)
    have hI := mem_Icc.mp hk'.1
    have hle : q * Q ≤ k := le_trans (Nat.le_add_right (q * Q) 1) hI.1
    change q * Q + (k - q * Q) = k
    rw [add_comm, Nat.sub_add_cancel hle]
  · intro j _hj
    exact Nat.add_sub_cancel_left (q * Q) j

lemma filter_delta_card_rem (P : ℕ → Prop) [DecidablePred P] (Q q s : ℕ)
    (hQ : 0 < Q) :
    #{k ∈ Icc (q * Q + 1) (q * Q + s) | P ((2 * k - 1) % Q)} =
      #{j ∈ Icc 1 s | P ((2 * j - 1) % Q)} := by
  refine card_nbij' (fun k => k - q * Q) (fun j => q * Q + j) ?_ ?_ ?_ ?_
  · intro k hk
    have hk' := mem_filter.mp (show k ∈ (Icc (q * Q + 1) (q * Q + s)).filter
        (fun k => P ((2 * k - 1) % Q)) from hk)
    have hI := mem_Icc.mp hk'.1
    have hle : q * Q ≤ k := le_trans (Nat.le_add_right (q * Q) 1) hI.1
    have hj1 : 1 ≤ k - q * Q := Nat.le_sub_of_add_le' hI.1
    have hj2 : k - q * Q ≤ s := Nat.sub_le_iff_le_add'.mpr hI.2
    have hk_eq : k = q * Q + (k - q * Q) := by
      rw [add_comm, Nat.sub_add_cancel hle]
    have hres : (2 * k - 1) % Q = (2 * (k - q * Q) - 1) % Q := by
      have h := residue_period_shift (Q := Q) (q := q) (j := k - q * Q) hQ hj1
      rwa [← hk_eq] at h
    refine mem_filter.mpr ⟨mem_Icc.mpr ⟨hj1, hj2⟩, hres ▸ hk'.2⟩
  · intro j hj
    have hj' := mem_filter.mp (show j ∈ (Icc 1 s).filter
        (fun j => P ((2 * j - 1) % Q)) from hj)
    have hI := mem_Icc.mp hj'.1
    have hres : (2 * (q * Q + j) - 1) % Q = (2 * j - 1) % Q :=
      residue_period_shift hQ hI.1
    refine mem_filter.mpr ⟨mem_Icc.mpr ⟨Nat.add_le_add_left hI.1 _,
        Nat.add_le_add_left hI.2 _⟩, hres ▸ hj'.2⟩
  · intro k hk
    have hk' := mem_filter.mp (show k ∈ (Icc (q * Q + 1) (q * Q + s)).filter
        (fun k => P ((2 * k - 1) % Q)) from hk)
    have hI := mem_Icc.mp hk'.1
    have hle : q * Q ≤ k := le_trans (Nat.le_add_right (q * Q) 1) hI.1
    change q * Q + (k - q * Q) = k
    rw [add_comm, Nat.sub_add_cancel hle]
  · intro j _hj
    exact Nat.add_sub_cancel_left (q * Q) j

lemma count_mul_self (P : ℕ → Prop) [DecidablePred P] (Q q : ℕ) (hQ : 0 < Q) :
    #{k ∈ Icc 1 (q * Q) | P ((2 * k - 1) % Q)} =
      q * #{j ∈ Icc 1 Q | P ((2 * j - 1) % Q)} := by
  induction q with
  | zero => simp
  | succ q ih =>
    have hsucc := succ_mul_eq q Q
    have hsplit : Icc 1 ((q + 1) * Q) =
        Icc 1 (q * Q) ∪ Icc (q * Q + 1) ((q + 1) * Q) := by
      rw [hsucc]
      exact Icc_union_split (Nat.le_add_left 1 _) (Nat.le_add_right _ _)
    have hdisj : Disjoint (Icc 1 (q * Q)) (Icc (q * Q + 1) ((q + 1) * Q)) := by
      rw [hsucc]
      exact disjoint_Icc_succ 1 (q * Q) (q * Q + Q)
    rw [hsplit, filter_union,
      card_union_of_disjoint
        (Disjoint.mono (filter_subset _ _) (filter_subset _ _) hdisj), ih,
      filter_delta_card_block P Q q hQ]
    ring

lemma count_mul_add (P : ℕ → Prop) [DecidablePred P] (Q q s : ℕ) (hQ : 0 < Q) :
    #{k ∈ Icc 1 (q * Q + s) | P ((2 * k - 1) % Q)} =
      q * #{j ∈ Icc 1 Q | P ((2 * j - 1) % Q)} +
        #{j ∈ Icc 1 s | P ((2 * j - 1) % Q)} := by
  have hsplit : Icc 1 (q * Q + s) =
      Icc 1 (q * Q) ∪ Icc (q * Q + 1) (q * Q + s) :=
    Icc_union_split (Nat.le_add_left 1 _) (Nat.le_add_right _ _)
  have hdisj := disjoint_Icc_succ 1 (q * Q) (q * Q + s)
  rw [hsplit, filter_union,
    card_union_of_disjoint
      (Disjoint.mono (filter_subset _ _) (filter_subset _ _) hdisj),
    count_mul_self P Q q hQ, filter_delta_card_rem P Q q s hQ]

lemma posCount_mul_add (Q q s : ℕ) (hQ : 0 < Q) :
    posCount Q (q * Q + s) = q * posCount Q Q + posCount Q s :=
  count_mul_add (deltaPos Q) Q q s hQ

lemma negCount_mul_add (Q q s : ℕ) (hQ : 0 < Q) :
    negCount Q (q * Q + s) = q * negCount Q Q + negCount Q s :=
  count_mul_add (deltaNeg Q) Q q s hQ

lemma not_deltaPos_zero (Q : ℕ) : ¬ deltaPos Q 0 := by
  intro h
  unfold deltaPos at h
  omega

lemma not_deltaNeg_zero (Q : ℕ) : ¬ deltaNeg Q 0 := by
  intro h
  unfold deltaNeg at h
  omega

lemma card_filter_odd_add_even (s : Finset ℕ) (P : ℕ → Prop) [DecidablePred P] :
    #{x ∈ s | P x} = #{x ∈ s | P x ∧ Odd x} + #{x ∈ s | P x ∧ Even x} := by
  have h := card_filter_add_card_filter_not (s := s.filter P) (p := Odd)
  simpa [filter_filter, Nat.not_odd_iff_even] using h.symm

lemma two_mul_sub_one_odd {k : ℕ} (hk : 1 ≤ k) : Odd (2 * k - 1) := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le hk
  exact ⟨m, by omega⟩

lemma two_mul_sub_one_lt_of_lt_mid {Q k n : ℕ} (hQ : Odd Q)
    (hk : 1 ≤ k) (hkn : k ≤ n) (hn : n < (Q + 1) / 2) : 2 * k - 1 < Q := by
  rcases hQ with ⟨a, rfl⟩
  omega

lemma two_mul_div_two_add_one {r : ℕ} (hr : Odd r) : 2 * (r / 2 + 1) - 1 = r := by
  rcases hr with ⟨m, rfl⟩
  omega

lemma two_mul_sub_one_le {k n : ℕ} (hk : 1 ≤ k) (hkn : k ≤ n) :
    2 * k - 1 ≤ 2 * n - 1 := by
  omega

lemma div_two_add_one_two_mul {k : ℕ} (hk : 1 ≤ k) : (2 * k - 1) / 2 + 1 = k := by
  omega


lemma two_mul_div_two_even {r : ℕ} (hr : Even r) : 2 * (r / 2) = r := by
  rcases hr with ⟨t, ht⟩
  omega

lemma even_div_two_le {r m : ℕ} (hr : Even r) (hle : r ≤ 2 * m) : r / 2 ≤ m := by
  rcases hr with ⟨t, ht⟩
  omega

lemma two_mul_mid_mod (Q : ℕ) (hQ : Odd Q) :
    (2 * ((Q + 1) / 2) - 1) % Q = 0 := by
  rw [two_mul_mid_sub_one Q hQ, Nat.mod_self]

lemma two_pred_mid (Q : ℕ) (hQ : Odd Q) :
    2 * ((Q + 1) / 2 - 1) - 1 = Q - 2 := by
  rcases hQ with ⟨a, rfl⟩
  omega

lemma odd_le_sub_two {Q r : ℕ} (hQ : Odd Q) (hr : r < Q) (ho : Odd r) : r ≤ Q - 2 := by
  rcases hQ with ⟨a, rfl⟩
  rcases ho with ⟨m, rfl⟩
  omega

lemma mid_pos (Q : ℕ) (hQ : Odd Q) : 0 < (Q + 1) / 2 := by
  rcases hQ with ⟨a, rfl⟩
  omega

lemma mid_le_self (Q : ℕ) (hQ : Odd Q) : (Q + 1) / 2 ≤ Q := by
  rcases hQ with ⟨a, rfl⟩
  omega

lemma two_mul_sub_one_mod_gt_mid {Q k : ℕ} (hQ : Odd Q)
    (hk : (Q + 1) / 2 < k) (hkQ : k ≤ Q) :
    (2 * k - 1) % Q = 2 * (k - (Q + 1) / 2) := by
  rcases hQ with ⟨a, rfl⟩
  have hQpos : 0 < 2 * a + 1 := by omega
  have hge : 2 * a + 1 ≤ 2 * k - 1 := by omega
  have hlt : 2 * k - 1 < 2 * (2 * a + 1) := by omega
  have hdiv : (2 * k - 1) / (2 * a + 1) = 1 := div_eq_one hQpos hge hlt
  have hmod := Nat.div_add_mod (2 * k - 1) (2 * a + 1)
  rw [hdiv, mul_one] at hmod
  have hrem : (2 * k - 1) % (2 * a + 1) = 2 * k - 1 - (2 * a + 1) := by omega
  have hsub : 2 * k - 1 - (2 * a + 1) = 2 * (k - (a + 1)) := by omega
  have hmid : (2 * a + 1 + 1) / 2 = a + 1 := by omega
  rw [hrem, hsub, hmid]

lemma even_inv_residue (Q r : ℕ) (hQ : Odd Q) (hr : Even r) (hrQ : r < Q) :
    (2 * ((Q + 1) / 2 + r / 2) - 1) % Q = r := by
  rcases hQ with ⟨a, rfl⟩
  rcases hr with ⟨t, ht⟩
  have hsum : 2 * ((2 * a + 1 + 1) / 2 + r / 2) - 1 = (2 * a + 1) + r := by omega
  have : (2 * a + 1) + r = r + (2 * a + 1) * 1 := by ring
  rw [hsum, this, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hrQ]

lemma card_delta_odd_prefix_le (Q bound : ℕ) (hQ : Odd Q) :
    #{r ∈ range Q | deltaNeg Q r ∧ Odd r ∧ r ≤ bound} ≤
      #{r ∈ range Q | deltaPos Q r ∧ Odd r ∧ r ≤ bound} := by
  let sNeg := (range Q).filter (fun r => deltaNeg Q r ∧ Odd r ∧ r ≤ bound)
  let sPos := (range Q).filter (fun r => deltaPos Q r ∧ Odd r ∧ r ≤ bound)
  by_cases hne : sNeg.Nonempty
  · obtain ⟨r0, hr0⟩ := hne
    have hr0' := mem_filter.mp hr0
    have hsub : (range Q).filter (fun r => deltaPos Q r ∧ Odd r) ⊆ sPos := by
      intro r hs
      have hs' := mem_filter.mp hs
      have hlt : r < r0 := deltaPos_lt_deltaNeg hs'.2.1 hr0'.2.1
      exact mem_filter.mpr ⟨hs'.1, hs'.2.1, hs'.2.2, le_trans (le_of_lt hlt) hr0'.2.2.2⟩
    have hle1 : #{r ∈ range Q | deltaPos Q r ∧ Odd r} ≤ #sPos := card_le_card hsub
    have hle2 : #sNeg ≤ #{r ∈ range Q | deltaNeg Q r ∧ Odd r} := by
      refine card_le_card ?_
      intro r hr
      have hr' := mem_filter.mp hr
      exact mem_filter.mpr ⟨hr'.1, hr'.2.1, hr'.2.2.1⟩
    calc
      #sNeg ≤ #{r ∈ range Q | deltaNeg Q r ∧ Odd r} := hle2
      _ = #{r ∈ range Q | deltaPos Q r ∧ Odd r} := (card_pos_odd_eq_neg_odd Q hQ).symm
      _ ≤ #sPos := hle1
  · have hsempty : sNeg = ∅ := Finset.not_nonempty_iff_eq_empty.mp hne
    change #sNeg ≤ #sPos
    rw [hsempty]
    exact Nat.zero_le _

lemma card_delta_even_prefix_le (Q bound : ℕ) (hQ : Odd Q) :
    #{r ∈ range Q | deltaNeg Q r ∧ Even r ∧ r ≤ bound} ≤
      #{r ∈ range Q | deltaPos Q r ∧ Even r ∧ r ≤ bound} := by
  let sNeg := (range Q).filter (fun r => deltaNeg Q r ∧ Even r ∧ r ≤ bound)
  let sPos := (range Q).filter (fun r => deltaPos Q r ∧ Even r ∧ r ≤ bound)
  by_cases hne : sNeg.Nonempty
  · obtain ⟨r0, hr0⟩ := hne
    have hr0' := mem_filter.mp hr0
    have hsub : (range Q).filter (fun r => deltaPos Q r ∧ Even r) ⊆ sPos := by
      intro r hs
      have hs' := mem_filter.mp hs
      have hlt : r < r0 := deltaPos_lt_deltaNeg hs'.2.1 hr0'.2.1
      exact mem_filter.mpr ⟨hs'.1, hs'.2.1, hs'.2.2, le_trans (le_of_lt hlt) hr0'.2.2.2⟩
    have hle1 : #{r ∈ range Q | deltaPos Q r ∧ Even r} ≤ #sPos := card_le_card hsub
    have hle2 : #sNeg ≤ #{r ∈ range Q | deltaNeg Q r ∧ Even r} := by
      refine card_le_card ?_
      intro r hr
      have hr' := mem_filter.mp hr
      exact mem_filter.mpr ⟨hr'.1, hr'.2.1, hr'.2.2.1⟩
    calc
      #sNeg ≤ #{r ∈ range Q | deltaNeg Q r ∧ Even r} := hle2
      _ = #{r ∈ range Q | deltaPos Q r ∧ Even r} := (card_pos_even_eq_neg_even Q hQ).symm
      _ ≤ #sPos := hle1
  · have hsempty : sNeg = ∅ := Finset.not_nonempty_iff_eq_empty.mp hne
    change #sNeg ≤ #sPos
    rw [hsempty]
    exact Nat.zero_le _

lemma posCount_eq_odd_bound (Q n : ℕ) (hQ : Odd Q) (hn : n < (Q + 1) / 2) :
    posCount Q n = #{r ∈ range Q | deltaPos Q r ∧ Odd r ∧ r ≤ 2 * n - 1} := by
  unfold posCount
  refine card_nbij' (fun k => 2 * k - 1) (fun r => r / 2 + 1) ?_ ?_ ?_ ?_
  · intro k hk
    have hk' := mem_filter.mp (show k ∈ (Icc 1 n).filter
        (fun k => deltaPos Q ((2 * k - 1) % Q)) from hk)
    have hI := mem_Icc.mp hk'.1
    have hlt := two_mul_sub_one_lt_of_lt_mid hQ hI.1 hI.2 hn
    have hmod : (2 * k - 1) % Q = 2 * k - 1 := Nat.mod_eq_of_lt hlt
    refine mem_filter.mpr ⟨mem_range.mpr hlt, ?_, two_mul_sub_one_odd hI.1,
      two_mul_sub_one_le hI.1 hI.2⟩
    · change deltaPos Q (2 * k - 1)
      rw [← hmod]
      exact hk'.2
  · intro r hr
    have hr' := mem_filter.mp (show r ∈ (range Q).filter
        (fun r => deltaPos Q r ∧ Odd r ∧ r ≤ 2 * n - 1) from hr)
    have hodd := hr'.2.2.1
    have hk_eq := two_mul_div_two_add_one hodd
    have hk1 : 1 ≤ r / 2 + 1 := Nat.le_add_left 1 _
    have hk2 : r / 2 + 1 ≤ n := by
      rcases hodd with ⟨m, rfl⟩
      omega
    have hmod : (2 * (r / 2 + 1) - 1) % Q = r := by
      rw [hk_eq, Nat.mod_eq_of_lt (mem_range.mp hr'.1)]
    refine mem_filter.mpr ⟨mem_Icc.mpr ⟨hk1, hk2⟩, ?_⟩
    · rw [hmod]; exact hr'.2.1
  · intro k hk
    have hk' := mem_filter.mp (show k ∈ (Icc 1 n).filter
        (fun k => deltaPos Q ((2 * k - 1) % Q)) from hk)
    exact div_two_add_one_two_mul (mem_Icc.mp hk'.1).1
  · intro r hr
    have hr' := mem_filter.mp (show r ∈ (range Q).filter
        (fun r => deltaPos Q r ∧ Odd r ∧ r ≤ 2 * n - 1) from hr)
    exact two_mul_div_two_add_one hr'.2.2.1

lemma negCount_eq_odd_bound (Q n : ℕ) (hQ : Odd Q) (hn : n < (Q + 1) / 2) :
    negCount Q n = #{r ∈ range Q | deltaNeg Q r ∧ Odd r ∧ r ≤ 2 * n - 1} := by
  unfold negCount
  refine card_nbij' (fun k => 2 * k - 1) (fun r => r / 2 + 1) ?_ ?_ ?_ ?_
  · intro k hk
    have hk' := mem_filter.mp (show k ∈ (Icc 1 n).filter
        (fun k => deltaNeg Q ((2 * k - 1) % Q)) from hk)
    have hI := mem_Icc.mp hk'.1
    have hlt := two_mul_sub_one_lt_of_lt_mid hQ hI.1 hI.2 hn
    have hmod : (2 * k - 1) % Q = 2 * k - 1 := Nat.mod_eq_of_lt hlt
    refine mem_filter.mpr ⟨mem_range.mpr hlt, ?_, two_mul_sub_one_odd hI.1,
      two_mul_sub_one_le hI.1 hI.2⟩
    · change deltaNeg Q (2 * k - 1)
      rw [← hmod]
      exact hk'.2
  · intro r hr
    have hr' := mem_filter.mp (show r ∈ (range Q).filter
        (fun r => deltaNeg Q r ∧ Odd r ∧ r ≤ 2 * n - 1) from hr)
    have hodd := hr'.2.2.1
    have hk_eq := two_mul_div_two_add_one hodd
    have hk1 : 1 ≤ r / 2 + 1 := Nat.le_add_left 1 _
    have hk2 : r / 2 + 1 ≤ n := by
      rcases hodd with ⟨m, rfl⟩
      omega
    have hmod : (2 * (r / 2 + 1) - 1) % Q = r := by
      rw [hk_eq, Nat.mod_eq_of_lt (mem_range.mp hr'.1)]
    refine mem_filter.mpr ⟨mem_Icc.mpr ⟨hk1, hk2⟩, ?_⟩
    · rw [hmod]; exact hr'.2.1
  · intro k hk
    have hk' := mem_filter.mp (show k ∈ (Icc 1 n).filter
        (fun k => deltaNeg Q ((2 * k - 1) % Q)) from hk)
    exact div_two_add_one_two_mul (mem_Icc.mp hk'.1).1
  · intro r hr
    have hr' := mem_filter.mp (show r ∈ (range Q).filter
        (fun r => deltaNeg Q r ∧ Odd r ∧ r ≤ 2 * n - 1) from hr)
    exact two_mul_div_two_add_one hr'.2.2.1

lemma posCount_eq_even_bound (Q n : ℕ) (hQ : Odd Q)
    (hn1 : (Q + 1) / 2 ≤ n) (hn2 : n ≤ Q) :
    #{k ∈ Icc ((Q + 1) / 2 + 1) n | deltaPos Q ((2 * k - 1) % Q)} =
      #{r ∈ range Q | deltaPos Q r ∧ Even r ∧ r ≤ 2 * (n - (Q + 1) / 2)} := by
  refine card_nbij' (fun k => (2 * k - 1) % Q)
      (fun r => (Q + 1) / 2 + r / 2) ?_ ?_ ?_ ?_
  · intro k hk
    have hk' := mem_filter.mp (show k ∈ (Icc ((Q + 1) / 2 + 1) n).filter
        (fun k => deltaPos Q ((2 * k - 1) % Q)) from hk)
    have hI := mem_Icc.mp hk'.1
    have hk1 : (Q + 1) / 2 < k := Nat.lt_of_succ_le hI.1
    have hkQ : k ≤ Q := le_trans hI.2 hn2
    have hres := two_mul_sub_one_mod_gt_mid hQ hk1 hkQ
    have hle : 2 * (k - (Q + 1) / 2) ≤ 2 * (n - (Q + 1) / 2) :=
      Nat.mul_le_mul_left 2 (Nat.sub_le_sub_right hI.2 _)
    refine mem_filter.mpr ⟨mem_range.mpr (Nat.mod_lt _ (odd_pos_of hQ)), hk'.2, ?_, ?_⟩
    · change Even ((2 * k - 1) % Q)
      rw [hres]
      exact even_two_mul _
    · change (2 * k - 1) % Q ≤ 2 * (n - (Q + 1) / 2)
      rw [hres]
      exact hle
  · intro r hr
    have hr' := mem_filter.mp (show r ∈ (range Q).filter
        (fun r => deltaPos Q r ∧ Even r ∧ r ≤ 2 * (n - (Q + 1) / 2)) from hr)
    have hE := hr'.2.2.1
    have hrQ := mem_range.mp hr'.1
    have hmod := even_inv_residue Q r hQ hE hrQ
    have hr0 : r ≠ 0 := fun h0 => not_deltaPos_zero Q (h0 ▸ hr'.2.1)
    have hk1 : (Q + 1) / 2 + 1 ≤ (Q + 1) / 2 + r / 2 := by
      have : 1 ≤ r / 2 := by
        rcases hE with ⟨t, ht⟩
        omega
      exact Nat.add_le_add_left this _
    have hk2 : (Q + 1) / 2 + r / 2 ≤ n := by
      have : (Q + 1) / 2 + r / 2 ≤ (Q + 1) / 2 + (n - (Q + 1) / 2) :=
        Nat.add_le_add_left (even_div_two_le hE hr'.2.2.2) _
      rwa [Nat.add_sub_cancel' hn1] at this
    refine mem_filter.mpr ⟨mem_Icc.mpr ⟨hk1, hk2⟩, ?_⟩
    · rw [hmod]; exact hr'.2.1
  · intro k hk
    have hk' := mem_filter.mp (show k ∈ (Icc ((Q + 1) / 2 + 1) n).filter
        (fun k => deltaPos Q ((2 * k - 1) % Q)) from hk)
    have hI := mem_Icc.mp hk'.1
    have hk1 : (Q + 1) / 2 < k := Nat.lt_of_succ_le hI.1
    have hkQ : k ≤ Q := le_trans hI.2 hn2
    have hle : (Q + 1) / 2 ≤ k := le_of_lt hk1
    change (Q + 1) / 2 + ((2 * k - 1) % Q) / 2 = k
    rw [two_mul_sub_one_mod_gt_mid hQ hk1 hkQ]
    have : 2 * (k - (Q + 1) / 2) / 2 = k - (Q + 1) / 2 := by omega
    rw [this, add_comm, Nat.sub_add_cancel hle]
  · intro r hr
    have hr' := mem_filter.mp (show r ∈ (range Q).filter
        (fun r => deltaPos Q r ∧ Even r ∧ r ≤ 2 * (n - (Q + 1) / 2)) from hr)
    exact even_inv_residue Q r hQ hr'.2.2.1 (mem_range.mp hr'.1)

lemma negCount_eq_even_bound (Q n : ℕ) (hQ : Odd Q)
    (hn1 : (Q + 1) / 2 ≤ n) (hn2 : n ≤ Q) :
    #{k ∈ Icc ((Q + 1) / 2 + 1) n | deltaNeg Q ((2 * k - 1) % Q)} =
      #{r ∈ range Q | deltaNeg Q r ∧ Even r ∧ r ≤ 2 * (n - (Q + 1) / 2)} := by
  refine card_nbij' (fun k => (2 * k - 1) % Q)
      (fun r => (Q + 1) / 2 + r / 2) ?_ ?_ ?_ ?_
  · intro k hk
    have hk' := mem_filter.mp (show k ∈ (Icc ((Q + 1) / 2 + 1) n).filter
        (fun k => deltaNeg Q ((2 * k - 1) % Q)) from hk)
    have hI := mem_Icc.mp hk'.1
    have hk1 : (Q + 1) / 2 < k := Nat.lt_of_succ_le hI.1
    have hkQ : k ≤ Q := le_trans hI.2 hn2
    have hres := two_mul_sub_one_mod_gt_mid hQ hk1 hkQ
    have hle : 2 * (k - (Q + 1) / 2) ≤ 2 * (n - (Q + 1) / 2) :=
      Nat.mul_le_mul_left 2 (Nat.sub_le_sub_right hI.2 _)
    refine mem_filter.mpr ⟨mem_range.mpr (Nat.mod_lt _ (odd_pos_of hQ)), hk'.2, ?_, ?_⟩
    · change Even ((2 * k - 1) % Q)
      rw [hres]
      exact even_two_mul _
    · change (2 * k - 1) % Q ≤ 2 * (n - (Q + 1) / 2)
      rw [hres]
      exact hle
  · intro r hr
    have hr' := mem_filter.mp (show r ∈ (range Q).filter
        (fun r => deltaNeg Q r ∧ Even r ∧ r ≤ 2 * (n - (Q + 1) / 2)) from hr)
    have hE := hr'.2.2.1
    have hrQ := mem_range.mp hr'.1
    have hmod := even_inv_residue Q r hQ hE hrQ
    have hr0 : r ≠ 0 := fun h0 => not_deltaNeg_zero Q (h0 ▸ hr'.2.1)
    have hk1 : (Q + 1) / 2 + 1 ≤ (Q + 1) / 2 + r / 2 := by
      have : 1 ≤ r / 2 := by
        rcases hE with ⟨t, ht⟩
        omega
      exact Nat.add_le_add_left this _
    have hk2 : (Q + 1) / 2 + r / 2 ≤ n := by
      have : (Q + 1) / 2 + r / 2 ≤ (Q + 1) / 2 + (n - (Q + 1) / 2) :=
        Nat.add_le_add_left (even_div_two_le hE hr'.2.2.2) _
      rwa [Nat.add_sub_cancel' hn1] at this
    refine mem_filter.mpr ⟨mem_Icc.mpr ⟨hk1, hk2⟩, ?_⟩
    · rw [hmod]; exact hr'.2.1
  · intro k hk
    have hk' := mem_filter.mp (show k ∈ (Icc ((Q + 1) / 2 + 1) n).filter
        (fun k => deltaNeg Q ((2 * k - 1) % Q)) from hk)
    have hI := mem_Icc.mp hk'.1
    have hk1 : (Q + 1) / 2 < k := Nat.lt_of_succ_le hI.1
    have hkQ : k ≤ Q := le_trans hI.2 hn2
    have hle : (Q + 1) / 2 ≤ k := le_of_lt hk1
    change (Q + 1) / 2 + ((2 * k - 1) % Q) / 2 = k
    rw [two_mul_sub_one_mod_gt_mid hQ hk1 hkQ]
    have : 2 * (k - (Q + 1) / 2) / 2 = k - (Q + 1) / 2 := by omega
    rw [this, add_comm, Nat.sub_add_cancel hle]
  · intro r hr
    have hr' := mem_filter.mp (show r ∈ (range Q).filter
        (fun r => deltaNeg Q r ∧ Even r ∧ r ≤ 2 * (n - (Q + 1) / 2)) from hr)
    exact even_inv_residue Q r hQ hr'.2.2.1 (mem_range.mp hr'.1)

lemma posCount_mid (Q : ℕ) (hQ : Odd Q) :
    posCount Q ((Q + 1) / 2) = #{r ∈ range Q | deltaPos Q r ∧ Odd r} := by
  have hn : (Q + 1) / 2 - 1 < (Q + 1) / 2 := Nat.sub_lt (mid_pos Q hQ) (by decide)
  have hmid1 : (Q + 1) / 2 - 1 + 1 = (Q + 1) / 2 := Nat.sub_add_cancel (mid_pos Q hQ)
  have hsplit : Icc 1 ((Q + 1) / 2) =
      Icc 1 ((Q + 1) / 2 - 1) ∪ Icc ((Q + 1) / 2) ((Q + 1) / 2) := by
    rw [← hmid1]
    exact Icc_union_split (Nat.le_add_left 1 _) (Nat.sub_le _ _)
  have hdisj : Disjoint (Icc 1 ((Q + 1) / 2 - 1)) (Icc ((Q + 1) / 2) ((Q + 1) / 2)) := by
    have h := disjoint_Icc_succ 1 ((Q + 1) / 2 - 1) ((Q + 1) / 2)
    rwa [hmid1] at h
  have hsing : Icc ((Q + 1) / 2) ((Q + 1) / 2) = {(Q + 1) / 2} := by
    ext x
    simp [mem_singleton]
  unfold posCount
  rw [hsplit, filter_union,
    card_union_of_disjoint (Disjoint.mono (filter_subset _ _) (filter_subset _ _) hdisj)]
  have h0 : #{k ∈ Icc ((Q + 1) / 2) ((Q + 1) / 2) | deltaPos Q ((2 * k - 1) % Q)} = 0 := by
    rw [hsing, filter_singleton, two_mul_mid_mod Q hQ]
    simp [not_deltaPos_zero]
  have hodd := posCount_eq_odd_bound Q ((Q + 1) / 2 - 1) hQ hn
  have hfilter :
      (range Q).filter (fun r => deltaPos Q r ∧ Odd r ∧ r ≤ Q - 2) =
        (range Q).filter (fun r => deltaPos Q r ∧ Odd r) := by
    ext r
    constructor
    · intro hr
      have hr' := mem_filter.mp hr
      exact mem_filter.mpr ⟨hr'.1, hr'.2.1, hr'.2.2.1⟩
    · intro hr
      have hr' := mem_filter.mp hr
      exact mem_filter.mpr ⟨hr'.1, hr'.2.1, hr'.2.2,
        odd_le_sub_two hQ (mem_range.mp hr'.1) hr'.2.2⟩
  rw [h0, add_zero, ← posCount, hodd, two_pred_mid Q hQ, hfilter]

lemma negCount_mid (Q : ℕ) (hQ : Odd Q) :
    negCount Q ((Q + 1) / 2) = #{r ∈ range Q | deltaNeg Q r ∧ Odd r} := by
  have hn : (Q + 1) / 2 - 1 < (Q + 1) / 2 := Nat.sub_lt (mid_pos Q hQ) (by decide)
  have hmid1 : (Q + 1) / 2 - 1 + 1 = (Q + 1) / 2 := Nat.sub_add_cancel (mid_pos Q hQ)
  have hsplit : Icc 1 ((Q + 1) / 2) =
      Icc 1 ((Q + 1) / 2 - 1) ∪ Icc ((Q + 1) / 2) ((Q + 1) / 2) := by
    rw [← hmid1]
    exact Icc_union_split (Nat.le_add_left 1 _) (Nat.sub_le _ _)
  have hdisj : Disjoint (Icc 1 ((Q + 1) / 2 - 1)) (Icc ((Q + 1) / 2) ((Q + 1) / 2)) := by
    have h := disjoint_Icc_succ 1 ((Q + 1) / 2 - 1) ((Q + 1) / 2)
    rwa [hmid1] at h
  have hsing : Icc ((Q + 1) / 2) ((Q + 1) / 2) = {(Q + 1) / 2} := by
    ext x
    simp [mem_singleton]
  unfold negCount
  rw [hsplit, filter_union,
    card_union_of_disjoint (Disjoint.mono (filter_subset _ _) (filter_subset _ _) hdisj)]
  have h0 : #{k ∈ Icc ((Q + 1) / 2) ((Q + 1) / 2) | deltaNeg Q ((2 * k - 1) % Q)} = 0 := by
    rw [hsing, filter_singleton, two_mul_mid_mod Q hQ]
    simp [not_deltaNeg_zero]
  have hodd := negCount_eq_odd_bound Q ((Q + 1) / 2 - 1) hQ hn
  have hfilter :
      (range Q).filter (fun r => deltaNeg Q r ∧ Odd r ∧ r ≤ Q - 2) =
        (range Q).filter (fun r => deltaNeg Q r ∧ Odd r) := by
    ext r
    constructor
    · intro hr
      have hr' := mem_filter.mp hr
      exact mem_filter.mpr ⟨hr'.1, hr'.2.1, hr'.2.2.1⟩
    · intro hr
      have hr' := mem_filter.mp hr
      exact mem_filter.mpr ⟨hr'.1, hr'.2.1, hr'.2.2,
        odd_le_sub_two hQ (mem_range.mp hr'.1) hr'.2.2⟩
  rw [h0, add_zero, ← negCount, hodd, two_pred_mid Q hQ, hfilter]

lemma even_bound_full (Q : ℕ) (hQ : Odd Q) :
    2 * (Q - (Q + 1) / 2) = Q - 1 := by
  rcases hQ with ⟨a, rfl⟩
  omega

lemma filter_even_le_pred (Q : ℕ) (P : ℕ → Prop) [DecidablePred P] :
    (range Q).filter (fun r => P r ∧ Even r ∧ r ≤ Q - 1) =
      (range Q).filter (fun r => P r ∧ Even r) := by
  ext r
  constructor
  · intro hr
    have hr' := mem_filter.mp hr
    exact mem_filter.mpr ⟨hr'.1, hr'.2.1, hr'.2.2.1⟩
  · intro hr
    have hr' := mem_filter.mp hr
    exact mem_filter.mpr ⟨hr'.1, hr'.2.1, hr'.2.2,
      Nat.le_sub_one_of_lt (mem_range.mp hr'.1)⟩

lemma posCount_period_eq_card (Q : ℕ) (hQ : Odd Q) :
    posCount Q Q = #{r ∈ range Q | deltaPos Q r} := by
  have hsplit : Icc 1 Q = Icc 1 ((Q + 1) / 2) ∪ Icc ((Q + 1) / 2 + 1) Q :=
    Icc_union_split (Nat.le_add_left 1 _) (mid_le_self Q hQ)
  have hdisj := disjoint_Icc_succ 1 ((Q + 1) / 2) Q
  unfold posCount
  rw [hsplit, filter_union,
    card_union_of_disjoint (Disjoint.mono (filter_subset _ _) (filter_subset _ _) hdisj)]
  have heven := posCount_eq_even_bound Q Q hQ (mid_le_self Q hQ) le_rfl
  rw [← posCount, posCount_mid Q hQ, heven, even_bound_full Q hQ,
    filter_even_le_pred Q (deltaPos Q)]
  exact (card_filter_odd_add_even (range Q) (deltaPos Q)).symm

lemma negCount_period_eq_card (Q : ℕ) (hQ : Odd Q) :
    negCount Q Q = #{r ∈ range Q | deltaNeg Q r} := by
  have hsplit : Icc 1 Q = Icc 1 ((Q + 1) / 2) ∪ Icc ((Q + 1) / 2 + 1) Q :=
    Icc_union_split (Nat.le_add_left 1 _) (mid_le_self Q hQ)
  have hdisj := disjoint_Icc_succ 1 ((Q + 1) / 2) Q
  unfold negCount
  rw [hsplit, filter_union,
    card_union_of_disjoint (Disjoint.mono (filter_subset _ _) (filter_subset _ _) hdisj)]
  have heven := negCount_eq_even_bound Q Q hQ (mid_le_self Q hQ) le_rfl
  rw [← negCount, negCount_mid Q hQ, heven, even_bound_full Q hQ,
    filter_even_le_pred Q (deltaNeg Q)]
  exact (card_filter_odd_add_even (range Q) (deltaNeg Q)).symm

lemma posCount_period_eq_negCount_period (Q : ℕ) (hQ : Odd Q) :
    posCount Q Q = negCount Q Q := by
  rw [posCount_period_eq_card Q hQ, negCount_period_eq_card Q hQ,
    card_filter_odd_add_even (range Q) (deltaPos Q),
    card_filter_odd_add_even (range Q) (deltaNeg Q),
    card_pos_odd_eq_neg_odd Q hQ, card_pos_even_eq_neg_even Q hQ]

lemma posCount_ge_negCount_of_lt (Q n : ℕ) (hQ : Odd Q) (hn : n < Q) :
    negCount Q n ≤ posCount Q n := by
  by_cases h1 : n < (Q + 1) / 2
  · rw [posCount_eq_odd_bound Q n hQ h1, negCount_eq_odd_bound Q n hQ h1]
    exact card_delta_odd_prefix_le Q (2 * n - 1) hQ
  · have hn1 : (Q + 1) / 2 ≤ n := Nat.le_of_not_gt h1
    have hn2 : n ≤ Q := le_of_lt hn
    have hsplit : Icc 1 n = Icc 1 ((Q + 1) / 2) ∪ Icc ((Q + 1) / 2 + 1) n :=
      Icc_union_split (Nat.le_add_left 1 _) hn1
    have hdisj := disjoint_Icc_succ 1 ((Q + 1) / 2) n
    unfold posCount negCount
    rw [hsplit, filter_union,
      card_union_of_disjoint (Disjoint.mono (filter_subset _ _) (filter_subset _ _) hdisj),
      filter_union,
      card_union_of_disjoint (Disjoint.mono (filter_subset _ _) (filter_subset _ _) hdisj)]
    have hmidP : #{k ∈ Icc 1 ((Q + 1) / 2) | deltaPos Q ((2 * k - 1) % Q)} =
        #{r ∈ range Q | deltaPos Q r ∧ Odd r} := by
      simpa [posCount] using posCount_mid Q hQ
    have hmidN : #{k ∈ Icc 1 ((Q + 1) / 2) | deltaNeg Q ((2 * k - 1) % Q)} =
        #{r ∈ range Q | deltaNeg Q r ∧ Odd r} := by
      simpa [negCount] using negCount_mid Q hQ
    rw [hmidP, hmidN, posCount_eq_even_bound Q n hQ hn1 hn2,
      negCount_eq_even_bound Q n hQ hn1 hn2, card_pos_odd_eq_neg_odd Q hQ]
    have := card_delta_even_prefix_le Q (2 * (n - (Q + 1) / 2)) hQ
    nlinarith

lemma posCount_ge_negCount (Q n : ℕ) (hQ : Odd Q) :
    negCount Q n ≤ posCount Q n := by
  have hpos := odd_pos_of hQ
  have hs : n % Q < Q := Nat.mod_lt n hpos
  have hdecomp : n = n / Q * Q + n % Q := by
    rw [Nat.mul_comm]
    exact (Nat.div_add_mod n Q).symm
  rw [hdecomp, posCount_mul_add Q (n / Q) (n % Q) hpos,
    negCount_mul_add Q (n / Q) (n % Q) hpos,
    posCount_period_eq_negCount_period Q hQ]
  have := posCount_ge_negCount_of_lt Q (n % Q) hQ hs
  nlinarith

lemma six_eq_three_odd (k : ℕ) (hk : 1 ≤ k) : 6 * k - 2 = 3 * (2 * k - 1) + 1 := by
  omega

lemma three_mul_div (Q q r : ℕ) (hQ : 0 < Q) :
    (3 * (Q * q + r) + 1) / Q = 3 * q + (3 * r + 1) / Q := by
  have : 3 * (Q * q + r) + 1 = (3 * r + 1) + Q * (3 * q) := by ring
  rw [this, Nat.add_mul_div_left _ _ hQ]
  ac_rfl

lemma two_mul_div (Q q r : ℕ) (hQ : 0 < Q) :
    (2 * (Q * q + r)) / Q = 2 * q + (2 * r) / Q := by
  have : 2 * (Q * q + r) = (2 * r) + Q * (2 * q) := by ring
  rw [this, Nat.add_mul_div_left _ _ hQ]
  ac_rfl

lemma two_mul_add_one_div (Q q r : ℕ) (hQ : 0 < Q) :
    (2 * (Q * q + r) + 1) / Q = 2 * q + (2 * r + 1) / Q := by
  have : 2 * (Q * q + r) + 1 = (2 * r + 1) + Q * (2 * q) := by ring
  rw [this, Nat.add_mul_div_left _ _ hQ]
  ac_rfl

lemma floor_term (Q k : ℕ) (hQ : 0 < Q) (hk : 1 ≤ k) :
    (6 * k - 2) / Q + (2 * k - 1) / Q +
        (if deltaNeg Q ((2 * k - 1) % Q) then 1 else 0) =
      (4 * k - 1) / Q + (4 * k - 2) / Q +
        (if deltaPos Q ((2 * k - 1) % Q) then 1 else 0) := by
  set q := (2 * k - 1) / Q
  set r := (2 * k - 1) % Q
  have hm : 2 * k - 1 = Q * q + r := (Nat.div_add_mod (2 * k - 1) Q).symm
  have hr : r < Q := Nat.mod_lt _ hQ
  have h6div : (6 * k - 2) / Q = 3 * q + (3 * r + 1) / Q := by
    rw [six_eq_three_odd k hk, hm]
    exact three_mul_div Q q r hQ
  have h41div : (4 * k - 1) / Q = 2 * q + (2 * r + 1) / Q := by
    rw [four_k_sub_one_eq k hk, hm]
    exact two_mul_add_one_div Q q r hQ
  have h42div : (4 * k - 2) / Q = 2 * q + (2 * r) / Q := by
    rw [four_k_sub_two_eq k hk, hm]
    exact two_mul_div Q q r hQ
  have hinc := floor_inc_eq Q r hQ hr
  rw [h6div, h41div, h42div]
  nlinarith [hinc]

lemma posCount_eq_sum_boole (Q n : ℕ) :
    posCount Q n =
      ∑ k ∈ Icc 1 n, if deltaPos Q ((2 * k - 1) % Q) then 1 else 0 := by
  unfold posCount
  exact (sum_boole (fun k => deltaPos Q ((2 * k - 1) % Q)) (Icc 1 n)).symm

lemma negCount_eq_sum_boole (Q n : ℕ) :
    negCount Q n =
      ∑ k ∈ Icc 1 n, if deltaNeg Q ((2 * k - 1) % Q) then 1 else 0 := by
  unfold negCount
  exact (sum_boole (fun k => deltaNeg Q ((2 * k - 1) % Q)) (Icc 1 n)).symm

lemma floor_ineq_odd_mod (Q n : ℕ) (hQ : Odd Q) :
    ∑ k ∈ Icc 1 n, ((4 * k - 1) / Q + (4 * k - 2) / Q) ≤
      ∑ k ∈ Icc 1 n, ((6 * k - 2) / Q + (2 * k - 1) / Q) := by
  have hterm :
      ∑ k ∈ Icc 1 n,
          ((6 * k - 2) / Q + (2 * k - 1) / Q +
            if deltaNeg Q ((2 * k - 1) % Q) then 1 else 0) =
        ∑ k ∈ Icc 1 n,
          ((4 * k - 1) / Q + (4 * k - 2) / Q +
            if deltaPos Q ((2 * k - 1) % Q) then 1 else 0) :=
    sum_congr rfl fun k hk => floor_term Q k (odd_pos_of hQ) (mem_Icc_one hk)
  simp only [sum_add_distrib] at hterm ⊢
  rw [← posCount_eq_sum_boole, ← negCount_eq_sum_boole] at hterm
  have hpos := posCount_ge_negCount Q n hQ
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
    let b := log p (6 * n) + 1
    have hb {m : ℕ} (hm : m ≤ 6 * n) : log p m < b :=
      (log_mono_right hm).trans_lt (Nat.lt_succ_self _)
    have hval {m : ℕ} (hm : m ≤ 6 * n) :
        m.factorial.factorization p = ∑ i ∈ Ico 1 b, m / p ^ i :=
      factorization_factorial hp (hb hm)
    have hle6 {k : ℕ} (hk : k ∈ Icc 1 n) : 6 * k - 2 ≤ 6 * n := by
      have := mem_Icc.mp hk
      omega
    have hle2 {k : ℕ} (hk : k ∈ Icc 1 n) : 2 * k - 1 ≤ 6 * n := by
      have := mem_Icc.mp hk
      omega
    have hle41 {k : ℕ} (hk : k ∈ Icc 1 n) : 4 * k - 1 ≤ 6 * n := by
      have := mem_Icc.mp hk
      omega
    have hle42 {k : ℕ} (hk : k ∈ Icc 1 n) : 4 * k - 2 ≤ 6 * n := by
      have := mem_Icc.mp hk
      omega
    have hnum :
        ∑ k ∈ Icc 1 n,
            ((6 * k - 2)!.factorization p + (2 * k - 1)!.factorization p) =
          ∑ i ∈ Ico 1 b, ∑ k ∈ Icc 1 n,
            ((6 * k - 2) / p ^ i + (2 * k - 1) / p ^ i) := by
      have h1 : ∑ k ∈ Icc 1 n,
          ((6 * k - 2)!.factorization p + (2 * k - 1)!.factorization p) =
          ∑ k ∈ Icc 1 n, ((∑ i ∈ Ico 1 b, (6 * k - 2) / p ^ i) +
            ∑ i ∈ Ico 1 b, (2 * k - 1) / p ^ i) :=
        sum_congr rfl fun k hk => by rw [hval (hle6 hk), hval (hle2 hk)]
      rw [h1, sum_add_distrib,
        Finset.sum_comm (s := Icc 1 n) (t := Ico 1 b),
        Finset.sum_comm (s := Icc 1 n) (t := Ico 1 b),
        ← sum_add_distrib]
      exact sum_congr rfl fun _ _ => (sum_add_distrib).symm
    have hden :
        ∑ k ∈ Icc 1 n,
            ((4 * k - 1)!.factorization p + (4 * k - 2)!.factorization p) =
          ∑ i ∈ Ico 1 b, ∑ k ∈ Icc 1 n,
            ((4 * k - 1) / p ^ i + (4 * k - 2) / p ^ i) := by
      have h1 : ∑ k ∈ Icc 1 n,
          ((4 * k - 1)!.factorization p + (4 * k - 2)!.factorization p) =
          ∑ k ∈ Icc 1 n, ((∑ i ∈ Ico 1 b, (4 * k - 1) / p ^ i) +
            ∑ i ∈ Ico 1 b, (4 * k - 2) / p ^ i) :=
        sum_congr rfl fun k hk => by rw [hval (hle41 hk), hval (hle42 hk)]
      rw [h1, sum_add_distrib,
        Finset.sum_comm (s := Icc 1 n) (t := Ico 1 b),
        Finset.sum_comm (s := Icc 1 n) (t := Ico 1 b),
        ← sum_add_distrib]
      exact sum_congr rfl fun _ _ => (sum_add_distrib).symm
    have hvle :
        ∑ k ∈ Icc 1 n,
            ((4 * k - 1)!.factorization p + (4 * k - 2)!.factorization p) ≤
          ∑ k ∈ Icc 1 n,
            ((6 * k - 2)!.factorization p + (2 * k - 1)!.factorization p) := by
      rw [hnum, hden]
      refine Finset.sum_le_sum fun i _ => ?_
      have hodd : Odd (p ^ i) := Odd.pow (n := i) (hp.odd_of_ne_two hp2)
      exact floor_ineq_odd_mod (p ^ i) n hodd
    have hbal_num :
        ∑ k ∈ Icc 1 n,
            ((p - 1) * ((6 * k - 2)!.factorization p + (2 * k - 1)!.factorization p) +
              ((p.digits (6 * k - 2)).sum + (p.digits (2 * k - 1)).sum)) =
          ∑ k ∈ Icc 1 n, (6 * k - 2 + (2 * k - 1)) := by
      refine sum_congr rfl fun k _ => ?_
      have hA := factorization_factorial_add_digitSum (m := 6 * k - 2) hp
      have hB := factorization_factorial_add_digitSum (m := 2 * k - 1) hp
      linear_combination hA + hB
    have hbal_den :
        ∑ k ∈ Icc 1 n,
            ((p - 1) * ((4 * k - 1)!.factorization p + (4 * k - 2)!.factorization p) +
              ((p.digits (4 * k - 1)).sum + (p.digits (4 * k - 2)).sum)) =
          ∑ k ∈ Icc 1 n, (4 * k - 1 + (4 * k - 2)) := by
      refine sum_congr rfl fun k _ => ?_
      have hA := factorization_factorial_add_digitSum (m := 4 * k - 1) hp
      have hB := factorization_factorial_add_digitSum (m := 4 * k - 2) hp
      linear_combination hA + hB
    have hsum_eq :
        ∑ k ∈ Icc 1 n, (6 * k - 2 + (2 * k - 1)) =
          ∑ k ∈ Icc 1 n, (4 * k - 1 + (4 * k - 2)) :=
      sum_congr rfl fun k hk => eight_sub_three k (mem_Icc_one hk)
    have hnum' :
        (p - 1) * ∑ k ∈ Icc 1 n,
            ((6 * k - 2)!.factorization p + (2 * k - 1)!.factorization p) +
          ∑ k ∈ Icc 1 n,
            ((p.digits (6 * k - 2)).sum + (p.digits (2 * k - 1)).sum) =
          ∑ k ∈ Icc 1 n, (6 * k - 2 + (2 * k - 1)) := by
      rw [Finset.mul_sum, ← sum_add_distrib]
      convert hbal_num using 1
    have hden' :
        (p - 1) * ∑ k ∈ Icc 1 n,
            ((4 * k - 1)!.factorization p + (4 * k - 2)!.factorization p) +
          ∑ k ∈ Icc 1 n,
            ((p.digits (4 * k - 1)).sum + (p.digits (4 * k - 2)).sum) =
          ∑ k ∈ Icc 1 n, (4 * k - 1 + (4 * k - 2)) := by
      rw [Finset.mul_sum, ← sum_add_distrib]
      convert hbal_den using 1
    have htot :
        (p - 1) * ∑ k ∈ Icc 1 n,
            ((6 * k - 2)!.factorization p + (2 * k - 1)!.factorization p) +
          ∑ k ∈ Icc 1 n,
            ((p.digits (6 * k - 2)).sum + (p.digits (2 * k - 1)).sum) =
          (p - 1) * ∑ k ∈ Icc 1 n,
            ((4 * k - 1)!.factorization p + (4 * k - 2)!.factorization p) +
          ∑ k ∈ Icc 1 n,
            ((p.digits (4 * k - 1)).sum + (p.digits (4 * k - 2)).sum) := by
      rw [hnum', hden', hsum_eq]
    have hvle' := Nat.mul_le_mul_left (p - 1) hvle
    have hcmp :
        (p - 1) * ∑ k ∈ Icc 1 n,
              ((4 * k - 1)!.factorization p + (4 * k - 2)!.factorization p) +
            ∑ k ∈ Icc 1 n,
              ((p.digits (6 * k - 2)).sum + (p.digits (2 * k - 1)).sum) ≤
          (p - 1) * ∑ k ∈ Icc 1 n,
              ((6 * k - 2)!.factorization p + (2 * k - 1)!.factorization p) +
            ∑ k ∈ Icc 1 n,
              ((p.digits (6 * k - 2)).sum + (p.digits (2 * k - 1)).sum) :=
      Nat.add_le_add_right hvle' _
    have hcmp' :
        (p - 1) * ∑ k ∈ Icc 1 n,
              ((4 * k - 1)!.factorization p + (4 * k - 2)!.factorization p) +
            ∑ k ∈ Icc 1 n,
              ((p.digits (4 * k - 1)).sum + (p.digits (4 * k - 2)).sum) ≥
          (p - 1) * ∑ k ∈ Icc 1 n,
              ((4 * k - 1)!.factorization p + (4 * k - 2)!.factorization p) +
            ∑ k ∈ Icc 1 n,
              ((p.digits (6 * k - 2)).sum + (p.digits (2 * k - 1)).sum) := by
      rw [← htot]
      exact hcmp
    exact Nat.le_of_add_le_add_left hcmp'

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
    frac (n + 1) = (b (n + 1) : ℚ) / (b n : ℚ) := by
  rw [frac_succ, b_succ_ratio]

example : ∀ n : ℕ, frac (n + 1) = (b (n + 1) : ℚ) / (b n : ℚ) :=
  conjecture

#print axioms conjecture

end A109074Proof
