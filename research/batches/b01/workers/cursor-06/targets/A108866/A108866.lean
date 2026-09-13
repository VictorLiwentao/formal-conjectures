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
import Mathlib.Algebra.Polynomial.Derivative
import Mathlib.Algebra.Polynomial.Eval.Coeff
import Mathlib.Algebra.Ring.GeomSum
import Mathlib.Data.Nat.Choose.Sum

/-!
Partial development for OEIS A108866.

This file does not use `OeisA108866.conjecture`. It proves that an even
`n > 3` never satisfies the congruence, and the Komatsu–Sury odd
identity for `T(n)`. The prime direction and the odd-composite converse
are not proved here.
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

/- Komatsu–Sury Lemma 2, specialised at `x = -2`. -/

open Polynomial

/-- Left-hand polynomial in Komatsu–Sury Lemma 2. -/
noncomputable def altHarmonicPoly (n : ℕ) : ℚ[X] :=
  ∑ i ∈ range n, C ((-1 : ℚ) ^ i / (i + 1)) * X ^ (i + 1)

/-- Main right-hand polynomial in Komatsu–Sury Lemma 2, without the constant. -/
noncomputable def binomAltHarmonicPoly (n : ℕ) : ℚ[X] :=
  ∑ i ∈ range n,
    C ((n.choose (i + 1) : ℚ) * (-1 : ℚ) ^ i / (i + 1)) * (X + 1) ^ (i + 1)

lemma C_neg_one_pow_mul_X_pow (i : ℕ) :
    C ((-1 : ℚ) ^ i) * X ^ i = (-X : ℚ[X]) ^ i := by
  have h1 : (-1 : ℚ[X]) = C (-1) := by simp
  refine Eq.symm ?_
  calc
    (-X : ℚ[X]) ^ i = ((-1 : ℚ[X]) * X) ^ i := by simp
    _ = (-1 : ℚ[X]) ^ i * X ^ i := mul_pow _ _ _
    _ = C (-1) ^ i * X ^ i := by rw [h1]
    _ = C ((-1 : ℚ) ^ i) * X ^ i := by rw [C_pow]

lemma derivative_altHarmonicPoly (n : ℕ) :
    derivative (altHarmonicPoly n) = ∑ i ∈ range n, (-X : ℚ[X]) ^ i := by
  unfold altHarmonicPoly
  rw [derivative_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  have hi : (i + 1 : ℚ) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero i
  rw [derivative_C_mul_X_pow, Nat.add_one_sub_one, Nat.cast_succ]
  have : ((-1 : ℚ) ^ i / (i + 1)) * (i + 1) = (-1 : ℚ) ^ i := by
    field_simp [hi]
  rw [this, C_neg_one_pow_mul_X_pow]

lemma geom_sum_neg_X (n : ℕ) (hn : Odd n) :
    (∑ i ∈ range n, (-X : ℚ[X]) ^ i) * (1 + X) = 1 + X ^ n := by
  have h := geom_sum_mul_neg (-X : ℚ[X]) n
  have h1 : (1 : ℚ[X]) - (-X) = 1 + X := by ring
  rw [h1] at h
  have : (1 : ℚ[X]) - (-X) ^ n = 1 + X ^ n := by
    rw [neg_pow, hn.neg_one_pow]
    ring
  rwa [this] at h

lemma one_add_X_ne_zero : (1 + X : ℚ[X]) ≠ 0 := by
  intro h
  have := congr_arg (eval (0 : ℚ)) h
  simp at this

lemma mul_derivative_altHarmonicPoly (n : ℕ) (hn : Odd n) :
    (1 + X) * derivative (altHarmonicPoly n) = 1 + X ^ n := by
  rw [derivative_altHarmonicPoly, mul_comm]
  exact geom_sum_neg_X n hn

lemma X_pow_binomial (n : ℕ) :
    (X : ℚ[X]) ^ n =
      ∑ m ∈ range (n + 1),
        C ((n.choose m : ℚ) * (-1 : ℚ) ^ (n - m)) * (X + 1) ^ m := by
  have hbase : ((X + 1 : ℚ[X]) + (-1)) ^ n = X ^ n := by
    have : (X + 1 + (-1 : ℚ[X])) = X := by ring
    rw [this]
  rw [← hbase, add_pow]
  refine Finset.sum_congr rfl fun m _ => ?_
  have hneg : (-1 : ℚ[X]) ^ (n - m) = C ((-1 : ℚ) ^ (n - m)) := by
    have : (-1 : ℚ[X]) = C (-1) := by simp
    rw [this, C_pow]
  rw [hneg, ← C_eq_natCast]
  simp
  ring

lemma neg_one_pow_pred {m : ℕ} (hm : 0 < m) :
    (-1 : ℚ) ^ (m - 1) = - ((-1) ^ m) := by
  have : (-1 : ℚ) ^ m = (-1) ^ (m - 1) * (-1) := by
    rw [← pow_succ, Nat.sub_add_cancel hm]
  rw [this]
  ring

lemma neg_one_pow_sub_eq {n m : ℕ} (hn : Odd n) (hm : m ≤ n) (hm0 : 0 < m) :
    (-1 : ℚ) ^ (n - m) = (-1) ^ (m - 1) := by
  have hmul : (-1 : ℚ) ^ (n - m) * (-1) ^ m = (-1) ^ n := by
    rw [← pow_add, Nat.sub_add_cancel hm]
  have hsq : ((-1 : ℚ) ^ m) ^ 2 = 1 := by simp [← pow_mul]
  have hprod : (-1 : ℚ) ^ (n - m) = (-1) ^ n * (-1) ^ m := by
    calc
      (-1 : ℚ) ^ (n - m) = (-1) ^ (n - m) * ((-1) ^ m) ^ 2 := by rw [hsq, mul_one]
      _ = ((-1) ^ (n - m) * (-1) ^ m) * (-1) ^ m := by ring
      _ = (-1) ^ n * (-1) ^ m := by rw [hmul]
  rw [hprod, hn.neg_one_pow, neg_one_pow_pred hm0]
  ring

lemma X_pow_add_one_eq (n : ℕ) (hn : Odd n) :
    (X : ℚ[X]) ^ n + 1 =
      ∑ i ∈ range n, C ((n.choose (i + 1) : ℚ) * (-1 : ℚ) ^ i) * (X + 1) ^ (i + 1) := by
  have hbin := X_pow_binomial n
  have h0 : C ((n.choose 0 : ℚ) * (-1 : ℚ) ^ (n - 0)) * (X + 1) ^ 0 = -1 := by
    simp [hn.neg_one_pow]
  have hsum :
      (X : ℚ[X]) ^ n =
        -1 + ∑ i ∈ range n,
          C ((n.choose (i + 1) : ℚ) * (-1 : ℚ) ^ (n - (i + 1))) * (X + 1) ^ (i + 1) := by
    rw [hbin, sum_range_succ', h0, add_comm]
  rw [hsum, add_comm, add_neg_cancel_left]
  refine Finset.sum_congr rfl fun i hi => ?_
  have him : i + 1 ≤ n := by
    have : i < n := mem_range.mp hi
    omega
  have hsign : (-1 : ℚ) ^ (n - (i + 1)) = (-1) ^ i := by
    simpa [Nat.add_one_sub_one] using neg_one_pow_sub_eq hn him (Nat.succ_pos i)
  rw [hsign]

lemma derivative_one_add_X : derivative (X + 1 : ℚ[X]) = 1 := by
  simp [derivative_add, derivative_X, derivative_one]

lemma derivative_binomAltHarmonicPoly (n : ℕ) :
    derivative (binomAltHarmonicPoly n) =
      ∑ i ∈ range n, C ((n.choose (i + 1) : ℚ) * (-1 : ℚ) ^ i) * (X + 1) ^ i := by
  unfold binomAltHarmonicPoly
  rw [derivative_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  have hi : (i + 1 : ℚ) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero i
  have hder : derivative ((X + 1 : ℚ[X]) ^ (i + 1)) =
      C (i + 1 : ℚ) * (X + 1) ^ i := by
    rw [derivative_pow, Nat.add_one_sub_one, derivative_one_add_X, mul_one, Nat.cast_succ]
  rw [derivative_C_mul, hder, ← mul_assoc, ← C_mul]
  have : ((n.choose (i + 1) : ℚ) * (-1 : ℚ) ^ i / (i + 1)) * (i + 1) =
      (n.choose (i + 1) : ℚ) * (-1 : ℚ) ^ i := by
    field_simp [hi]
  rw [this]

lemma mul_derivative_binomAltHarmonicPoly (n : ℕ) (hn : Odd n) :
    (1 + X) * derivative (binomAltHarmonicPoly n) = 1 + X ^ n := by
  rw [derivative_binomAltHarmonicPoly, mul_sum]
  have hX : (1 + X : ℚ[X]) = X + 1 := by ring
  have hsum :
      ∑ i ∈ range n,
          (1 + X) * (C ((n.choose (i + 1) : ℚ) * (-1 : ℚ) ^ i) * (X + 1) ^ i) =
        ∑ i ∈ range n,
          C ((n.choose (i + 1) : ℚ) * (-1 : ℚ) ^ i) * (X + 1) ^ (i + 1) := by
    refine Finset.sum_congr rfl fun i _ => ?_
    calc
      (1 + X) * (C ((n.choose (i + 1) : ℚ) * (-1 : ℚ) ^ i) * (X + 1) ^ i) =
          (X + 1) * (C ((n.choose (i + 1) : ℚ) * (-1 : ℚ) ^ i) * (X + 1) ^ i) := by
        rw [hX]
      _ = C ((n.choose (i + 1) : ℚ) * (-1 : ℚ) ^ i) * ((X + 1) * (X + 1) ^ i) := by
        ring
      _ = C ((n.choose (i + 1) : ℚ) * (-1 : ℚ) ^ i) * (X + 1) ^ (i + 1) := by
        rw [← pow_succ']
  rw [hsum]
  rw [add_comm (1 : ℚ[X]) (X ^ n)]
  exact (X_pow_add_one_eq n hn).symm

lemma derivative_altHarmonicPoly_eq_binom (n : ℕ) (hn : Odd n) :
    derivative (altHarmonicPoly n) = derivative (binomAltHarmonicPoly n) := by
  apply mul_left_cancel₀ one_add_X_ne_zero
  rw [mul_derivative_altHarmonicPoly n hn, mul_derivative_binomAltHarmonicPoly n hn]

lemma eval_altHarmonicPoly_zero (n : ℕ) : (altHarmonicPoly n).eval 0 = 0 := by
  unfold altHarmonicPoly
  rw [eval_finsetSum]
  refine Finset.sum_eq_zero fun i _ => ?_
  simp [pow_succ]

lemma eval_binomAltHarmonicPoly_zero (n : ℕ) :
    (binomAltHarmonicPoly n).eval 0 =
      ∑ i ∈ range n, (n.choose (i + 1) : ℚ) * (-1 : ℚ) ^ i / (i + 1) := by
  unfold binomAltHarmonicPoly
  rw [eval_finsetSum]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp [pow_succ]

lemma altHarmonicPoly_eq_binom_add_const (n : ℕ) (hn : Odd n) :
    altHarmonicPoly n =
      binomAltHarmonicPoly n +
        C (∑ i ∈ range n, (n.choose (i + 1) : ℚ) * (-1 : ℚ) ^ (i + 1) / (i + 1)) := by
  have hder : derivative (altHarmonicPoly n - binomAltHarmonicPoly n) = 0 := by
    rw [derivative_sub, derivative_altHarmonicPoly_eq_binom n hn, sub_self]
  have hC := eq_C_of_derivative_eq_zero hder
  have heval :
      (altHarmonicPoly n - binomAltHarmonicPoly n).eval 0 =
        ∑ i ∈ range n, (n.choose (i + 1) : ℚ) * (-1 : ℚ) ^ (i + 1) / (i + 1) := by
    rw [eval_sub, eval_altHarmonicPoly_zero, eval_binomAltHarmonicPoly_zero, zero_sub,
      ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun (i : ℕ) _ => ?_
    ring
  have hconst :
      altHarmonicPoly n - binomAltHarmonicPoly n =
        C (∑ i ∈ range n, (n.choose (i + 1) : ℚ) * (-1 : ℚ) ^ (i + 1) / (i + 1)) := by
    rw [hC, coeff_zero_eq_eval_zero, heval]
  exact eq_add_of_sub_eq' hconst

lemma eval_altHarmonicPoly_neg_two (n : ℕ) :
    (altHarmonicPoly n).eval (-2) = -∑ i ∈ range n, (2 : ℚ) ^ (i + 1) / (i + 1) := by
  unfold altHarmonicPoly
  rw [eval_finsetSum, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  have hpow : (-2 : ℚ) ^ (i + 1) = (-1 : ℚ) ^ (i + 1) * 2 ^ (i + 1) := by
    rw [neg_pow]
  rw [eval_C_mul, eval_pow, eval_X, hpow]
  have hsign : (-1 : ℚ) ^ (i + 1) * (-1) ^ i = -1 := by
    rw [← pow_add, show i + 1 + i = 2 * i + 1 by omega, pow_succ, pow_mul]
    ring
  field_simp
  linarith

lemma eval_binomAltHarmonicPoly_neg_two (n : ℕ) :
    (binomAltHarmonicPoly n).eval (-2) =
      ∑ i ∈ range n,
        (n.choose (i + 1) : ℚ) * (-1 : ℚ) ^ i / (i + 1) * (-1) ^ (i + 1) := by
  unfold binomAltHarmonicPoly
  rw [eval_finsetSum]
  refine Finset.sum_congr rfl fun i _ => ?_
  have hx : ((-2 : ℚ) + 1) = -1 := by ring
  simp [eval_pow, eval_add, eval_X, eval_one, hx]

/-- Komatsu–Sury Lemma 2 at `x = -2`, for odd `n`. -/
lemma sum_two_pow_div_eq_two_sum_odd_choose {n : ℕ} (hn : Odd n) :
    ∑ i ∈ range n, (2 : ℚ) ^ (i + 1) / (i + 1) =
      2 * ∑ i ∈ range n,
        if Odd (i + 1) then (n.choose (i + 1) : ℚ) / (i + 1) else 0 := by
  have h := congr_arg (eval (-2 : ℚ)) (altHarmonicPoly_eq_binom_add_const n hn)
  rw [eval_add, eval_C, eval_altHarmonicPoly_neg_two, eval_binomAltHarmonicPoly_neg_two] at h
  have hneg := congr_arg Neg.neg h
  simp only [neg_neg, neg_add] at hneg
  rw [hneg, mul_sum, ← Finset.sum_neg_distrib, ← Finset.sum_neg_distrib, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  by_cases hodd : Odd (i + 1)
  · have heven : Even i := by
      have : ¬ Odd i := by simpa [Nat.odd_add_one] using hodd
      exact Nat.not_odd_iff_even.mp this
    simp [if_pos hodd, heven.neg_one_pow, hodd.neg_one_pow]
    ring
  · have heven : Even (i + 1) := Nat.not_odd_iff_even.mp hodd
    have hiodd : Odd i := by
      simpa [Nat.odd_add_one] using hodd
    simp [if_neg hodd, hiodd.neg_one_pow, heven.neg_one_pow]
    ring

lemma ratExpression_eq_two_sum_odd_choose {n : ℕ} (hn : Odd n) (hn0 : 0 < n) :
    ratExpression n =
      (2 * ∑ i ∈ range n,
          (if Odd (i + 1) then (n.choose (i + 1) : ℚ) / (i + 1) else (0 : ℚ)))
        - (2 / n) := by
  rw [ratExpression_of_pos hn0, sum_two_pow_div_eq_two_sum_odd_choose hn]
  simp [sub_eq_add_neg, add_comm, neg_div]

lemma ratExpression_eq_two_sum_odd_choose_lt {n : ℕ} (hn : Odd n) (hn1 : 1 < n) :
    ratExpression n =
      2 * ∑ i ∈ range (n - 1),
        (if Odd (i + 1) then (n.choose (i + 1) : ℚ) / (i + 1) else (0 : ℚ)) := by
  have hn0 : 0 < n := Nat.zero_lt_of_lt hn1
  rw [ratExpression_eq_two_sum_odd_choose hn hn0]
  let f : ℕ → ℚ := fun i =>
    if Odd (i + 1) then (n.choose (i + 1) : ℚ) / (i + 1) else 0
  have hsplit : ∑ i ∈ range n, f i = ∑ i ∈ range (n - 1), f i + f (n - 1) := by
    have := Finset.sum_range_succ f (n - 1)
    rwa [Nat.sub_add_cancel (Nat.one_le_of_lt hn1)] at this
  have hlast : f (n - 1) = (1 : ℚ) / n := by
    have hn' : n - 1 + 1 = n := Nat.sub_add_cancel (Nat.one_le_of_lt hn1)
    have hodd : Odd (n - 1 + 1) := by simpa [hn'] using hn
    have hcast : ((n - 1 : ℕ) : ℚ) + 1 = n := by exact_mod_cast hn'
    simp only [f]
    rw [if_pos hodd, hn', Nat.choose_self, hcast]
    simp
  rw [hsplit, hlast]
  simp [f]
  ring

lemma choose_succ_div_eq (n k : ℕ) :
    ((n + 1).choose (k + 1) : ℚ) / (k + 1) =
      (n + 1) * (n.choose k : ℚ) / (k + 1) ^ 2 := by
  have hk : (k + 1 : ℚ) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero k
  have hN := Nat.add_one_mul_choose_eq n k
  have : ((n + 1).choose (k + 1) : ℚ) * (k + 1) =
      (n + 1) * (n.choose k : ℚ) := by
    exact_mod_cast hN.symm
  field_simp [hk]
  linarith

lemma ratExpression_eq_two_mul_n_sum_choose_sq {n : ℕ} (hn : Odd n) (hn1 : 1 < n) :
    ratExpression n =
      2 * n *
        ∑ i ∈ range (n - 1),
          if Odd (i + 1) then ((n - 1).choose i : ℚ) / (i + 1 : ℚ) ^ 2 else 0 := by
  rw [ratExpression_eq_two_sum_odd_choose_lt hn hn1]
  have hn' : n = n - 1 + 1 := (Nat.sub_add_cancel (Nat.one_le_of_lt hn1)).symm
  have hsum :
      ∑ i ∈ range (n - 1),
          (if Odd (i + 1) then (n.choose (i + 1) : ℚ) / (i + 1) else (0 : ℚ)) =
        n *
          ∑ i ∈ range (n - 1),
            if Odd (i + 1) then ((n - 1).choose i : ℚ) / (i + 1 : ℚ) ^ 2 else 0 := by
    rw [mul_sum]
    refine Finset.sum_congr rfl fun i hi => ?_
    by_cases hodd : Odd (i + 1)
    · have hn' : n - 1 + 1 = n := Nat.sub_add_cancel (Nat.one_le_of_lt hn1)
      have hcast : ((n - 1 : ℕ) : ℚ) + 1 = n := by exact_mod_cast hn'
      simp [if_pos hodd]
      have hdiv := choose_succ_div_eq (n - 1) i
      rw [hn'] at hdiv
      rw [hdiv, hcast]
      ring
    · simp [if_neg hodd]
  rw [hsum]
  ring

end OeisA108866
