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
New proof development and write-up: Wentao Li.
-/

import FormalConjectures.OEIS.«108866»
import Mathlib.NumberTheory.Padics.PadicVal.Basic
import Mathlib.Data.Nat.Log

/-!
Partial development for OEIS A108866.

This file does not use `OeisA108866.conjecture`. It proves that an even
`n > 3` never satisfies the congruence. The prime direction and the
odd-composite converse are not proved here.
-/

open Finset

namespace OeisA108866

private instance : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩

lemma ratExpression_of_pos {n : ℕ} (hn : 0 < n) :
    ratExpression n =
      (-2 : ℚ) / n + ∑ i ∈ range n, (2 : ℚ) ^ (i + 1) / (i + 1) := by
  simp [ratExpression, hn]

lemma term_nonneg (i : ℕ) : 0 ≤ (2 : ℚ) ^ (i + 1) / (i + 1) :=
  div_nonneg (pow_nonneg (by norm_num) _) (by exact_mod_cast Nat.zero_le (i + 1))

lemma term_pos (i : ℕ) : 0 < (2 : ℚ) ^ (i + 1) / (i + 1) :=
  div_pos (pow_pos (by norm_num) _) (by exact_mod_cast Nat.succ_pos i)

lemma sum_terms_pos {n : ℕ} (hn : 0 < n) :
    0 < ∑ i ∈ range n, (2 : ℚ) ^ (i + 1) / (i + 1) :=
  sum_pos (fun _ _ => term_pos _) (nonempty_range_iff.mpr (Nat.pos_iff_ne_zero.mp hn))

lemma two_le_sum_terms {n : ℕ} (hn : 0 < n) :
    (2 : ℚ) ≤ ∑ i ∈ range n, (2 : ℚ) ^ (i + 1) / (i + 1) := by
  have h0 : 0 ∈ range n := mem_range.mpr hn
  have := single_le_sum (fun i _ => term_nonneg i) h0
  simpa using this

lemma ratExpression_pos {n : ℕ} (hn : 1 < n) : 0 < ratExpression n := by
  have hn0 : 0 < n := Nat.zero_lt_of_lt hn
  have hsum := two_le_sum_terms hn0
  have hdiv : (-2 : ℚ) / n > -2 := by
    have hn1 : (1 : ℚ) < n := by exact_mod_cast hn
    have hnpos : 0 < (n : ℚ) := Nat.cast_pos.mpr hn0
    have hinv : (n : ℚ)⁻¹ < 1 := (inv_lt_one_iff₀).2 (Or.inr hn1)
    have : -2 * (n : ℚ)⁻¹ > -2 := by nlinarith
    simpa [div_eq_mul_inv] using this
  rw [ratExpression_of_pos hn0]
  nlinarith

lemma ratExpression_eq_partial {n : ℕ} (hn : 1 < n) :
    ratExpression n =
      ∑ i ∈ range (n - 1), (2 : ℚ) ^ (i + 1) / (i + 1) +
        ((2 : ℚ) ^ n - 2) / n := by
  have hn0 : 0 < n := Nat.zero_lt_of_lt hn
  have hna : n - 1 + 1 = n := Nat.sub_add_cancel (Nat.one_le_of_lt hn)
  rw [ratExpression_of_pos hn0, ← hna, sum_range_succ]
  have hcast : ((n - 1 : ℕ) : ℚ) + 1 = n := by exact_mod_cast hna
  simp [hcast, sub_eq_add_neg, div_eq_mul_inv, add_comm, add_left_comm]
  ring

lemma padicValRat_two_self : padicValRat 2 2 = 1 :=
  padicValRat.self (by decide : 1 < 2)

lemma padicValRat_two_pow (k : ℕ) : padicValRat 2 ((2 : ℚ) ^ k) = k := by
  rw [padicValRat.pow, padicValRat_two_self, mul_one]

lemma two_pow_eq_two_mul_pow {n : ℕ} (hn : 1 ≤ n) :
    2 ^ n = 2 * 2 ^ (n - 1) := by
  calc
    2 ^ n = 2 ^ (n - 1 + 1) := by rw [Nat.sub_add_cancel hn]
    _ = 2 ^ (n - 1) * 2 := pow_succ _ _
    _ = 2 * 2 ^ (n - 1) := mul_comm _ _

lemma padicValRat_two_pow_div {k : ℕ} (hk : 0 < k) :
    padicValRat 2 ((2 : ℚ) ^ k / k) = (k : ℤ) - padicValNat 2 k := by
  have hk0 : (k : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.pos_iff_ne_zero.mp hk)
  have h2 : (2 : ℚ) ^ k ≠ 0 := pow_ne_zero _ (by norm_num)
  rw [padicValRat.div h2 hk0, padicValRat_two_pow, padicValRat.of_nat]

lemma k_lt_two_pow_pred {k : ℕ} (hk : 3 ≤ k) : k < 2 ^ (k - 1) := by
  induction k, hk using Nat.le_induction with
  | base => decide
  | succ k hk ih =>
    have hk1 : 1 ≤ k := by omega
    have hpow : 2 ^ k = 2 * 2 ^ (k - 1) := two_pow_eq_two_mul_pow hk1
    have h2k : 2 * k < 2 ^ k := by
      rw [hpow]
      exact Nat.mul_lt_mul_of_pos_left ih (by decide)
    have hk1le : k + 1 ≤ 2 * k := by omega
    have : k + 1 < 2 ^ k := Nat.lt_of_le_of_lt hk1le h2k
    simpa [Nat.add_one_sub_one] using this

lemma two_le_k_sub_padicValNat_two {k : ℕ} (hk : 3 ≤ k) :
    2 ≤ k - padicValNat 2 k := by
  have hk0 : k ≠ 0 := by omega
  have hlog : padicValNat 2 k ≤ Nat.log 2 k := padicValNat_le_nat_log k
  have hlt : Nat.log 2 k < k - 1 :=
    Nat.log_lt_of_lt_pow hk0 (k_lt_two_pow_pred hk)
  omega

lemma two_le_padicValRat_two_pow_div {k : ℕ} (hk : 3 ≤ k) :
    2 ≤ padicValRat 2 ((2 : ℚ) ^ k / k) := by
  have hkpos : 0 < k := by omega
  have hle : padicValNat 2 k ≤ k :=
    (padicValNat_le_nat_log (p := 2) k).trans (Nat.log_le_self 2 k)
  rw [padicValRat_two_pow_div hkpos, ← Int.natCast_sub hle]
  exact_mod_cast (two_le_k_sub_padicValNat_two hk)

lemma two_le_padicValRat_sum_range {m : ℕ} (hm : 2 ≤ m) :
    2 ≤ padicValRat 2 (∑ i ∈ range m, (2 : ℚ) ^ (i + 1) / (i + 1)) := by
  induction m, hm using Nat.le_induction with
  | base =>
    have hsum : ∑ i ∈ range 2, (2 : ℚ) ^ (i + 1) / (i + 1) = 4 := by
      simp [sum_range_succ]
      norm_num
    rw [hsum]
    have : (4 : ℚ) = (2 : ℚ) ^ 2 := by norm_num
    rw [this, padicValRat_two_pow]
    norm_cast
  | succ m hm ih =>
    rw [sum_range_succ]
    have hden : (m : ℚ) + 1 = ((m + 1 : ℕ) : ℚ) := (Nat.cast_succ m).symm
    rw [hden]
    have hterm : 2 ≤ padicValRat 2 ((2 : ℚ) ^ (m + 1) / ((m + 1 : ℕ) : ℚ)) :=
      two_le_padicValRat_two_pow_div (by omega : 3 ≤ m + 1)
    have hsum0 :
        ∑ i ∈ range m, (2 : ℚ) ^ (i + 1) / (i + 1) +
            (2 : ℚ) ^ (m + 1) / ((m + 1 : ℕ) : ℚ) ≠ 0 := by
      have hpos : 0 < ∑ i ∈ range (m + 1), (2 : ℚ) ^ (i + 1) / (i + 1) :=
        sum_terms_pos (Nat.succ_pos m)
      rw [sum_range_succ, hden] at hpos
      exact ne_of_gt hpos
    have hmin := padicValRat.min_le_padicValRat_add (p := 2) hsum0
    exact le_trans (le_min ih hterm) hmin

lemma two_le_padicValRat_two_harmonic_partial {n : ℕ} (hn : 2 < n) :
    2 ≤ padicValRat 2 (∑ i ∈ range (n - 1), (2 : ℚ) ^ (i + 1) / (i + 1)) := by
  have hm : 2 ≤ n - 1 := by omega
  exact two_le_padicValRat_sum_range hm

lemma two_pow_sub_two_eq {n : ℕ} (hn : 1 ≤ n) :
    2 ^ n - 2 = 2 * (2 ^ (n - 1) - 1) := by
  have hpow := two_pow_eq_two_mul_pow hn
  have hle : 1 ≤ 2 ^ (n - 1) := Nat.one_le_pow _ _ (by decide)
  rw [hpow, Nat.mul_sub, mul_one]

lemma padicValNat_two_two_pow_sub_two {n : ℕ} (hn : 2 ≤ n) :
    padicValNat 2 (2 ^ n - 2) = 1 := by
  have hn1 : 1 ≤ n := by omega
  have hne : 2 ^ (n - 1) - 1 ≠ 0 := by
    have : 1 < 2 ^ (n - 1) :=
      Nat.one_lt_pow (by omega : n - 1 ≠ 0) (by decide)
    exact Nat.sub_ne_zero_of_lt this
  rw [two_pow_sub_two_eq hn1, padicValNat.mul (by decide) hne, padicValNat_self]
  have hodd : ¬ 2 ∣ 2 ^ (n - 1) - 1 := by
    have hpowpos : 1 ≤ 2 ^ (n - 1) := Nat.one_le_pow _ _ (by decide)
    have he : Even (2 ^ (n - 1)) := Nat.even_pow.mpr ⟨even_two, by omega⟩
    have : ¬ Even (2 ^ (n - 1) - 1) := by
      rw [Nat.even_sub hpowpos]
      simp [he]
    exact mt even_iff_two_dvd.mpr this
  simp [padicValNat.eq_zero_of_not_dvd hodd]

lemma two_pow_n_ne_two {n : ℕ} (hn : 2 ≤ n) : (2 : ℚ) ^ n ≠ 2 := by
  have : (2 : ℕ) < 2 ^ n := by
    have : 2 ^ 1 < 2 ^ n := Nat.pow_lt_pow_right (by decide) (by omega : 1 < n)
    simpa using this
  exact_mod_cast (ne_of_gt this)

lemma nat_cast_two_pow_sub_two {n : ℕ} (hn : 2 ≤ n) :
    ((2 ^ n - 2 : ℕ) : ℚ) = (2 : ℚ) ^ n - 2 := by
  have hle : 2 ≤ 2 ^ n := by
    have : 2 ^ 1 ≤ 2 ^ n := Nat.pow_le_pow_right (by decide) (by omega : 1 ≤ n)
    simpa using this
  rw [Nat.cast_sub hle, Nat.cast_pow]
  simp

lemma padicValRat_two_fermat_term {n : ℕ} (hn : 2 ≤ n) :
    padicValRat 2 (((2 : ℚ) ^ n - 2) / n) = 1 - padicValNat 2 n := by
  have hn0 : n ≠ 0 := by omega
  have hnum : (2 : ℚ) ^ n - 2 ≠ 0 := sub_ne_zero.mpr (two_pow_n_ne_two hn)
  have hden : (n : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hn0
  rw [padicValRat.div hnum hden, ← nat_cast_two_pow_sub_two hn, padicValRat.of_nat,
    padicValRat.of_nat, padicValNat_two_two_pow_sub_two hn]
  simp

lemma not_two_dvd_num_of_padicValRat_two_le_zero {q : ℚ} (hq : q ≠ 0)
    (hval : padicValRat 2 q ≤ 0) : ¬ (2 : ℤ) ∣ q.num := by
  intro hdiv
  have hnumA : 2 ∣ q.num.natAbs := Int.natCast_dvd.mp hdiv
  have hnum0 : q.num.natAbs ≠ 0 := Int.natAbs_ne_zero.mpr (Rat.num_ne_zero.mpr hq)
  have hvaln : 1 ≤ padicValNat 2 q.num.natAbs :=
    one_le_padicValNat_of_dvd hnum0 hnumA
  have hden : ¬ 2 ∣ q.den := by
    intro hd
    have hg : 2 ∣ Nat.gcd q.num.natAbs q.den := Nat.dvd_gcd hnumA hd
    have hgcd : Nat.gcd q.num.natAbs q.den = 1 := q.reduced
    omega
  have hden0 : padicValNat 2 q.den = 0 := padicValNat.eq_zero_of_not_dvd hden
  have : (0 : ℤ) < padicValRat 2 q := by
    rw [padicValRat_def, padicValInt]
    simp [hden0]
    exact_mod_cast hvaln
  exact (not_le_of_gt this) hval

lemma padicValRat_two_ratExpression_even {n : ℕ} (hn : n > 3) (he : Even n) :
    padicValRat 2 (ratExpression n) ≤ 0 := by
  have hn1 : 1 < n := by omega
  have hn2 : 2 < n := by omega
  have hnle : 2 ≤ n := by omega
  rw [ratExpression_eq_partial hn1]
  set S := ∑ i ∈ range (n - 1), (2 : ℚ) ^ (i + 1) / (i + 1)
  set Fterm := ((2 : ℚ) ^ n - 2) / n
  have hSval : 2 ≤ padicValRat 2 S := two_le_padicValRat_two_harmonic_partial hn2
  have hFval : padicValRat 2 Fterm = 1 - padicValNat 2 n :=
    padicValRat_two_fermat_term hnle
  have hvn : 1 ≤ padicValNat 2 n :=
    one_le_padicValNat_of_dvd (by omega) (even_iff_two_dvd.mp he)
  have hFlt : padicValRat 2 Fterm ≤ 0 := by
    rw [hFval]
    have : (1 : ℤ) - (padicValNat 2 n : ℤ) ≤ 0 := by
      have : 1 ≤ (padicValNat 2 n : ℤ) := by exact_mod_cast hvn
      omega
    exact this
  have hSne : S ≠ 0 :=
    ne_of_gt (sum_terms_pos (by omega : 0 < n - 1))
  have hFne : Fterm ≠ 0 :=
    div_ne_zero (sub_ne_zero.mpr (two_pow_n_ne_two hnle)) (Nat.cast_ne_zero.mpr (by omega))
  have hTne : S + Fterm ≠ 0 :=
    (ratExpression_eq_partial hn1 ▸ ne_of_gt (ratExpression_pos hn1))
  have hneval : padicValRat 2 S ≠ padicValRat 2 Fterm := by
    intro h
    have hge : 2 ≤ padicValRat 2 Fterm := by simpa [h] using hSval
    have hlt : padicValRat 2 Fterm < 2 := lt_of_le_of_lt hFlt (by decide : (0 : ℤ) < 2)
    exact (not_le_of_gt hlt) hge
  have hmin := padicValRat.add_eq_min hTne hSne hFne hneval
  rw [hmin]
  exact min_le_of_right_le hFlt

theorem not_n_sq_dvd_num_of_even {n : ℕ} (hn : n > 3) (he : Even n) :
    ¬ (ratExpression n).num ≡ 0 [ZMOD (n ^ 2 : ℤ)] := by
  intro h
  have hq0 : ratExpression n ≠ 0 := ne_of_gt (ratExpression_pos (by omega))
  have hval : padicValRat 2 (ratExpression n) ≤ 0 :=
    padicValRat_two_ratExpression_even hn he
  have hnot : ¬ (2 : ℤ) ∣ (ratExpression n).num :=
    not_two_dvd_num_of_padicValRat_two_le_zero hq0 hval
  have hdiv : (n ^ 2 : ℤ) ∣ (ratExpression n).num := Int.modEq_zero_iff_dvd.mp h
  have h2n : (2 : ℤ) ∣ (n : ℤ) := by
    exact_mod_cast (even_iff_two_dvd.mp he)
  have h2sq : (2 : ℤ) ∣ (n : ℤ) ^ 2 := dvd_pow h2n (by decide)
  exact hnot (h2sq.trans (by simpa using hdiv))

end OeisA108866
