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
import Mathlib.Data.Nat.Choose.Dvd
import Mathlib.Data.Nat.Factorial.NatCast
import Mathlib.Data.ZMod.Factorial
import Mathlib.Algebra.Field.ZMod

/-!
Partial development for OEIS A108866.

This file does not use `OeisA108866.conjecture`. It proves the even
converse, the Komatsu–Sury odd identity, the prime direction
`p^2 ∣ T(p).num` for primes `p > 3`, and reduction lemmas for the
odd-composite converse. For `1 < m < q` with `q` prime and
`q ∤ T(m).num`, it also proves `v_q(T(mq)) = -1`, hence the
converse at `n = mq`. The remaining odd-composite cases are not
proved here.
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

/- Prime direction: for an odd prime `p > 3`, `p^2` divides `T(p).num`. -/

def oddDenom (n : ℕ) : ℕ :=
  (Nat.factorial (n - 1))^2

def oddInnerNum (n : ℕ) : ℕ :=
  ∑ i ∈ range (n - 1),
    if Odd (i + 1) then (n - 1).choose i * (oddDenom n / (i + 1) ^ 2) else 0

lemma succ_sq_dvd_oddDenom {n i : ℕ} (_hn : 1 < n) (hi : i ∈ range (n - 1)) :
    (i + 1) ^ 2 ∣ oddDenom n := by
  have hle : i + 1 ≤ n - 1 := by
    have : i < n - 1 := mem_range.mp hi
    omega
  unfold oddDenom
  exact pow_dvd_pow_of_dvd (Nat.dvd_factorial (Nat.succ_pos i) hle) 2

lemma oddDenom_ne_zero {n : ℕ} : oddDenom n ≠ 0 := by
  unfold oddDenom
  exact pow_ne_zero _ (Nat.factorial_ne_zero _)

lemma two_mul_choose_two (n : ℕ) : 2 * n.choose 2 = n * (n - 1) := by
  rw [Nat.choose_two_right, Nat.mul_div_cancel' (Nat.even_mul_pred_self n).two_dvd]

lemma sq_eq_two_mul_choose_two_add (i : ℕ) : i ^ 2 = 2 * i.choose 2 + i := by
  rw [two_mul_choose_two]
  cases i with
  | zero => simp
  | succ k =>
    rw [Nat.add_sub_cancel]
    ring

lemma sum_range_choose_two (n : ℕ) : ∑ i ∈ range n, i.choose 2 = n.choose 3 := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [sum_range_succ, ih, add_comm, Nat.choose_succ_succ' n 2]

lemma sum_range_sq (n : ℕ) :
    ∑ i ∈ range n, i ^ 2 = 2 * n.choose 3 + n.choose 2 := by
  simp_rw [sq_eq_two_mul_choose_two_add]
  rw [sum_add_distrib, ← mul_sum, sum_range_choose_two, sum_range_id, ← Nat.choose_two_right]

lemma sum_range_sq_zmod {p : ℕ} (hp : p.Prime) (h5 : 5 ≤ p) :
    ∑ i ∈ range p, (i : ZMod p) ^ 2 = 0 := by
  have h2 : 2 < p := lt_of_lt_of_le (by decide : 2 < 5) h5
  have h3 : 3 < p := lt_of_lt_of_le (by decide : 3 < 5) h5
  simp_rw [← Nat.cast_pow]
  rw [← Nat.cast_sum, sum_range_sq, Nat.cast_add, Nat.cast_mul]
  have hC2 : (p.choose 2 : ZMod p) = 0 :=
    (ZMod.natCast_eq_zero_iff _ _).2 (hp.dvd_choose_self (by decide) h2)
  have hC3 : (p.choose 3 : ZMod p) = 0 :=
    (ZMod.natCast_eq_zero_iff _ _).2 (hp.dvd_choose_self (by decide) h3)
  simp [hC2, hC3]

lemma choose_pred_cast {p i : ℕ} (hp : p.Prime) (hi : i < p) :
    ((p - 1).choose i : ZMod p) = (-1) ^ i := by
  have : Fact p.Prime := ⟨hp⟩
  have hi' : i ≤ p := hi.le
  have hdesc := ZMod.cast_descFactorial hi'
  have hfac := Nat.descFactorial_eq_factorial_mul_choose (p - 1) i
  have hcast : ((p - 1).descFactorial i : ZMod p) =
      (i.factorial : ZMod p) * ((p - 1).choose i) := by
    rw [hfac, Nat.cast_mul]
  have hunit : IsUnit (i.factorial : ZMod p) :=
    (IsUnit.natCast_factorial_iff_of_charP (p := p) (A := ZMod p)).2 hi
  have hne : (i.factorial : ZMod p) ≠ 0 := IsUnit.ne_zero hunit
  have : (i.factorial : ZMod p) * ((p - 1).choose i) = (-1) ^ i * i.factorial := by
    rw [← hcast, hdesc]
  have hcomm : (i.factorial : ZMod p) * ((p - 1).choose i) =
      (i.factorial : ZMod p) * (-1) ^ i := by
    rw [this, mul_comm]
  exact mul_left_cancel₀ hne hcomm

lemma nat_div_sq_cast {p r D : ℕ} (hp : p.Prime) (hr : 0 < r) (hrp : r < p)
    (hdvd : r ^ 2 ∣ D) :
    ((D / r ^ 2 : ℕ) : ZMod p) = (D : ZMod p) * (r : ZMod p)⁻¹ ^ 2 := by
  have : Fact p.Prime := ⟨hp⟩
  have hr0 : (r : ZMod p) ≠ 0 := by
    intro h
    exact Nat.not_dvd_of_pos_of_lt hr hrp ((ZMod.natCast_eq_zero_iff _ _).1 h)
  have hunit : (r : ZMod p) ^ 2 * (r : ZMod p)⁻¹ ^ 2 = 1 := by
    rw [← mul_pow, mul_inv_cancel₀ hr0, one_pow]
  have hmul : ((D / r ^ 2 : ℕ) : ZMod p) * (r : ZMod p) ^ 2 = D := by
    rw [← Nat.cast_pow, ← Nat.cast_mul, Nat.div_mul_cancel hdvd]
  calc
    ((D / r ^ 2 : ℕ) : ZMod p) = ((D / r ^ 2 : ℕ) : ZMod p) * 1 := by rw [mul_one]
    _ = ((D / r ^ 2 : ℕ) : ZMod p) * ((r : ZMod p) ^ 2 * (r : ZMod p)⁻¹ ^ 2) := by
      rw [hunit]
    _ = ((D / r ^ 2 : ℕ) : ZMod p) * (r : ZMod p) ^ 2 * (r : ZMod p)⁻¹ ^ 2 := by
      rw [mul_assoc]
    _ = (D : ZMod p) * (r : ZMod p)⁻¹ ^ 2 := by rw [hmul]

lemma sum_inv_sq_eq_sum_sq_range {p : ℕ} (hp : p.Prime) :
    ∑ i ∈ range p, ((i : ZMod p)⁻¹) ^ 2 = ∑ i ∈ range p, (i : ZMod p) ^ 2 := by
  have : Fact p.Prime := ⟨hp⟩
  have : NeZero p := ⟨hp.ne_zero⟩
  refine sum_nbij (fun i => ((i : ZMod p)⁻¹).val) ?_ ?_ ?_ ?_
  · intro i _hi
    exact mem_range.mpr (ZMod.val_lt _)
  · intro i hi j hj h
    have hi' : i < p := mem_range.mp hi
    have hj' : j < p := mem_range.mp hj
    have hinv : (i : ZMod p)⁻¹ = (j : ZMod p)⁻¹ := ZMod.val_injective p h
    have hcast : (i : ZMod p) = (j : ZMod p) := by
      rw [← inv_inv (i : ZMod p), ← inv_inv (j : ZMod p), hinv]
    have hmod : i % p = j % p := (ZMod.natCast_eq_natCast_iff' _ _ _).1 hcast
    rw [Nat.mod_eq_of_lt hi', Nat.mod_eq_of_lt hj'] at hmod
    exact hmod
  · intro b hb
    refine ⟨((b : ZMod p)⁻¹).val, mem_range.mpr (ZMod.val_lt _), ?_⟩
    have hb' : b < p := mem_range.mp hb
    have : ((((b : ZMod p)⁻¹).val : ZMod p)⁻¹).val = b := by
      rw [ZMod.natCast_zmod_val, inv_inv, ZMod.val_natCast_of_lt hb']
    exact this
  · intro i _hi
    simp

lemma sum_inv_sq_range_eq_zero {p : ℕ} (hp : p.Prime) (h5 : 5 ≤ p) :
    ∑ i ∈ range p, ((i : ZMod p)⁻¹) ^ 2 = 0 := by
  rw [sum_inv_sq_eq_sum_sq_range hp, sum_range_sq_zmod hp h5]

lemma sum_odd_inv_sq_eq_even_erase {p : ℕ} (hp : p.Prime) (h5 : 5 ≤ p) :
    ∑ r ∈ (range p).filter Odd, ((r : ZMod p)⁻¹) ^ 2 =
      ∑ r ∈ ((range p).filter Even).erase 0, ((r : ZMod p)⁻¹) ^ 2 := by
  have hoddP : Odd p := hp.odd_of_ne_two (ne_of_gt (lt_of_lt_of_le (by decide : (2 : ℕ) < 5) h5))
  have hp0 : 0 < p := hp.pos
  have : Fact p.Prime := ⟨hp⟩
  refine sum_nbij (fun r => p - r) ?_ ?_ ?_ ?_
  · intro r hr
    have hr' := mem_filter.mp hr
    have hrlt : r < p := mem_range.mp hr'.1
    have hr0 : r ≠ 0 := by
      intro h
      subst h
      exact Nat.not_odd_iff_even.2 Even.zero hr'.2
    have hpos : 0 < r := Nat.pos_of_ne_zero hr0
    have hmem : p - r ∈ range p := mem_range.mpr (Nat.sub_lt hp0 hpos)
    have heven : Even (p - r) := by
      rw [Nat.even_sub hrlt.le]
      simp [Nat.not_even_iff_odd.2 hoddP, Nat.not_even_iff_odd.2 hr'.2]
    have hne : p - r ≠ 0 := Nat.sub_ne_zero_of_lt hrlt
    exact mem_erase.mpr ⟨hne, mem_filter.mpr ⟨hmem, heven⟩⟩
  · intro r hr s hs h
    have hrlt : r < p := mem_range.mp (mem_filter.mp hr).1
    have hslt : s < p := mem_range.mp (mem_filter.mp hs).1
    exact tsub_inj_right hrlt.le hslt.le h
  · intro b hb
    have hbE := mem_erase.mp hb
    have hb' := mem_filter.mp hbE.2
    have hblt : b < p := mem_range.mp hb'.1
    have hb0 : b ≠ 0 := hbE.1
    have hpos : 0 < b := Nat.pos_of_ne_zero hb0
    have hmem : p - b ∈ range p := mem_range.mpr (Nat.sub_lt hp0 hpos)
    have hodd : Odd (p - b) := by
      have hevenb : Even b := hb'.2
      have : ¬ Even (p - b) := by
        rw [Nat.even_sub hblt.le]
        intro hiff
        exact Nat.not_even_iff_odd.2 hoddP (hiff.mpr hevenb)
      exact Nat.not_even_iff_odd.1 this
    refine ⟨p - b, mem_filter.mpr ⟨hmem, hodd⟩, tsub_tsub_cancel_of_le hblt.le⟩
  · intro r hr
    have hr' := mem_filter.mp hr
    have hrlt : r < p := mem_range.mp hr'.1
    rw [Nat.cast_sub hrlt.le, ZMod.natCast_self, zero_sub, inv_neg, Even.neg_pow even_two]

lemma sum_odd_inv_sq_eq_zero {p : ℕ} (hp : p.Prime) (h5 : 5 ≤ p) :
    ∑ r ∈ (range p).filter Odd, ((r : ZMod p)⁻¹) ^ 2 = 0 := by
  have : Fact p.Prime := ⟨hp⟩
  have h2 : (2 : ZMod p) ≠ 0 := by
    intro h
    have : p ∣ 2 := (ZMod.natCast_eq_zero_iff 2 p).1 (by simpa using h)
    have : p ≤ 2 := Nat.le_of_dvd (by decide) this
    omega
  let f : ℕ → ZMod p := fun r => ((r : ZMod p)⁻¹) ^ 2
  have htotal : ∑ r ∈ range p, f r = 0 := sum_inv_sq_range_eq_zero hp h5
  have hsplit := sum_filter_add_sum_filter_not (range p) Odd f
  have hfeven : (range p).filter (fun r => ¬ Odd r) = (range p).filter Even := by
    ext x
    simp [Nat.not_odd_iff_even]
  have h0 : f 0 = 0 := by simp [f]
  have h0mem : 0 ∈ (range p).filter Even :=
    mem_filter.mpr ⟨mem_range.mpr hp.pos, Even.zero⟩
  have heven_split := add_sum_erase ((range p).filter Even) f h0mem
  have hpair := sum_odd_inv_sq_eq_even_erase hp h5
  have heven_eq_odd : ∑ r ∈ (range p).filter Even, f r = ∑ r ∈ (range p).filter Odd, f r := by
    rw [← heven_split, h0, zero_add, ← hpair]
  have htwo : (2 : ZMod p) * ∑ r ∈ (range p).filter Odd, f r = 0 := by
    rw [two_mul]
    nth_rw 1 [← heven_eq_odd]
    rw [← hfeven, add_comm, hsplit, htotal]
  apply mul_left_cancel₀ h2
  rw [htwo, mul_zero]

lemma sum_reindex_odd {α : Type*} [AddCommMonoid α] {p : ℕ} (f : ℕ → α) (hp : 1 < p) :
    ∑ i ∈ range (p - 1), (if Odd (i + 1) then f (i + 1) else 0) =
      ∑ r ∈ (range p).filter Odd, f r := by
  rw [← sum_filter]
  refine sum_nbij (fun i => i + 1) ?_ ?_ ?_ ?_
  · intro i hi
    have hi' := mem_filter.mp hi
    have hilt : i < p - 1 := mem_range.mp hi'.1
    exact mem_filter.mpr ⟨mem_range.mpr (by omega), hi'.2⟩
  · intro i _hi j _hj h
    exact Nat.succ_injective h
  · intro b hb
    have hb' := mem_filter.mp hb
    have hblt : b < p := mem_range.mp hb'.1
    have hodd := hb'.2
    have hb0 : b ≠ 0 := by
      intro h
      have : ¬ Odd (0 : ℕ) := Nat.not_odd_iff_even.2 Even.zero
      exact this (h ▸ hodd)
    have hpos : 0 < b := Nat.pos_of_ne_zero hb0
    refine ⟨b - 1, ?_, Nat.sub_add_cancel hpos⟩
    have hmem : b - 1 ∈ range (p - 1) := mem_range.mpr (by omega)
    have hodd' : Odd (b - 1 + 1) := by rwa [Nat.sub_add_cancel hpos]
    exact mem_filter.mpr ⟨hmem, hodd'⟩
  · intro i _hi
    rfl

lemma oddInnerSum_eq_div {n : ℕ} (hn : 1 < n) :
    ∑ i ∈ range (n - 1),
      (if Odd (i + 1) then ((n - 1).choose i : ℚ) / (i + 1 : ℚ) ^ 2 else 0) =
    (oddInnerNum n : ℚ) / oddDenom n := by
  have hD : (oddDenom n : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr oddDenom_ne_zero
  rw [eq_div_iff hD]
  unfold oddInnerNum
  rw [Nat.cast_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun i hi => ?_
  by_cases hodd : Odd (i + 1)
  · have hdvd := succ_sq_dvd_oddDenom hn hi
    have hr : (i + 1 : ℚ) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero i
    simp [if_pos hodd]
    have hcast : ((oddDenom n / (i + 1) ^ 2 : ℕ) : ℚ) =
        (oddDenom n : ℚ) / (i + 1 : ℚ) ^ 2 := by
      have hmul : ((oddDenom n / (i + 1) ^ 2 : ℕ) : ℚ) * ((i + 1 : ℕ) : ℚ) ^ 2 =
          oddDenom n := by
        rw [← Nat.cast_pow, ← Nat.cast_mul, Nat.div_mul_cancel hdvd]
      rw [eq_div_iff (pow_ne_zero _ hr)]
      convert hmul
      simp
    rw [hcast]
    field_simp [hr]
  · simp [if_neg hodd]

lemma not_dvd_oddDenom {p : ℕ} (hp : p.Prime) :
    ¬ p ∣ oddDenom p := by
  have hcop : p.Coprime (Nat.factorial (p - 1)) :=
    hp.coprime_factorial_of_lt (Nat.sub_one_lt hp.ne_zero)
  have : p.Coprime (oddDenom p) := (Nat.coprime_pow_right_iff (by decide : 0 < 2) _ _).2 hcop
  exact hp.coprime_iff_not_dvd.1 this

lemma oddInnerNum_cast {p : ℕ} (hp : p.Prime) (h5 : 5 ≤ p) :
    (oddInnerNum p : ZMod p) = 0 := by
  have : Fact p.Prime := ⟨hp⟩
  have hn1 : 1 < p := lt_of_lt_of_le (by decide : 1 < 5) h5
  unfold oddInnerNum
  rw [Nat.cast_sum]
  have hsum :
      ∑ i ∈ range (p - 1),
        ((if Odd (i + 1) then
            (p - 1).choose i * (oddDenom p / (i + 1) ^ 2) else 0 : ℕ) : ZMod p) =
      (oddDenom p : ZMod p) *
        ∑ i ∈ range (p - 1),
          (if Odd (i + 1) then ((i + 1 : ℕ) : ZMod p)⁻¹ ^ 2 else 0) := by
    rw [mul_sum]
    refine Finset.sum_congr rfl fun i hi => ?_
    by_cases hodd : Odd (i + 1)
    · have hi' : i < p - 1 := mem_range.mp hi
      have hrpos : 0 < i + 1 := Nat.succ_pos i
      have hrp : i + 1 < p := by omega
      have hdvd := succ_sq_dvd_oddDenom hn1 hi
      have hC : ((p - 1).choose i : ZMod p) = 1 := by
        have heven : Even i := by
          have : ¬ Odd i := by simpa [Nat.odd_add_one] using hodd
          exact Nat.not_odd_iff_even.mp this
        rw [choose_pred_cast hp (lt_trans hi' (Nat.sub_one_lt hp.ne_zero)), heven.neg_one_pow]
      simp [if_pos hodd, Nat.cast_mul, hC, nat_div_sq_cast hp hrpos hrp hdvd]
    · simp [if_neg hodd]
  rw [hsum]
  have hinner :
      ∑ i ∈ range (p - 1),
          (if Odd (i + 1) then ((i + 1 : ℕ) : ZMod p)⁻¹ ^ 2 else 0) =
        ∑ r ∈ (range p).filter Odd, ((r : ZMod p)⁻¹) ^ 2 :=
    sum_reindex_odd (fun r => ((r : ZMod p)⁻¹) ^ 2) hn1
  rw [hinner, sum_odd_inv_sq_eq_zero hp h5, mul_zero]

lemma dvd_oddInnerNum {p : ℕ} (hp : p.Prime) (h5 : 5 ≤ p) : p ∣ oddInnerNum p :=
  (ZMod.natCast_eq_zero_iff _ _).1 (oddInnerNum_cast hp h5)

lemma ratExpression_eq_two_mul_num_div_denom {n : ℕ} (hn : Odd n) (hn1 : 1 < n) :
    ratExpression n = 2 * n * (oddInnerNum n : ℚ) / oddDenom n := by
  rw [ratExpression_eq_two_mul_n_sum_choose_sq hn hn1, oddInnerSum_eq_div hn1]
  ring

lemma two_le_padicValRat_ratExpression_prime {p : ℕ} (hp : p.Prime) (h3 : p > 3) :
    2 ≤ padicValRat p (ratExpression p) := by
  have : Fact p.Prime := ⟨hp⟩
  have h5 : 5 ≤ p := by
    have : 3 < p := h3
    have hne4 : p ≠ 4 := by
      intro h
      subst h
      exact (by decide : ¬ Nat.Prime 4) hp
    omega
  have hn : Odd p := hp.odd_of_ne_two (by omega)
  have hn1 : 1 < p := by omega
  have hT := ratExpression_eq_two_mul_num_div_denom hn hn1
  have hTne : ratExpression p ≠ 0 := ne_of_gt (ratExpression_pos (by omega))
  have hNne : (oddInnerNum p : ℚ) ≠ 0 := by
    intro h0
    have : ratExpression p = 0 := by
      rw [hT, h0]
      simp
    exact hTne this
  have h2ne : (2 : ℚ) ≠ 0 := by norm_num
  have hpne : (p : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hp.ne_zero
  have hDne : (oddDenom p : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr oddDenom_ne_zero
  have h2val : padicValRat p (2 : ℚ) = 0 := by
    rw [show (2 : ℚ) = ((2 : ℕ) : ℚ) from rfl, padicValRat.of_nat]
    exact_mod_cast (padicValNat_primes (by omega : p ≠ 2))
  have hpval : padicValRat p (p : ℚ) = 1 := padicValRat.self hp.one_lt
  have hNval : 1 ≤ padicValRat p (oddInnerNum p : ℚ) := by
    have hpos : oddInnerNum p ≠ 0 := by
      exact_mod_cast hNne
    have : 1 ≤ padicValNat p (oddInnerNum p) :=
      one_le_padicValNat_of_dvd hpos (dvd_oddInnerNum hp h5)
    simpa [padicValRat.of_nat] using this
  have hDval : padicValRat p (oddDenom p : ℚ) = 0 := by
    rw [padicValRat.of_nat]
    exact_mod_cast padicValNat.eq_zero_of_not_dvd (not_dvd_oddDenom hp)
  have hprod : ratExpression p =
      ((2 : ℚ) * p * oddInnerNum p) / oddDenom p := by
    simpa [mul_assoc] using hT
  have hnumne : (2 : ℚ) * p * oddInnerNum p ≠ 0 :=
    mul_ne_zero (mul_ne_zero h2ne hpne) hNne
  rw [hprod, padicValRat.div hnumne hDne, padicValRat.mul (mul_ne_zero h2ne hpne) hNne,
    padicValRat.mul h2ne hpne, h2val, hpval, hDval]
  linarith

lemma not_dvd_den_of_nonneg_padicVal {p : ℕ} [Fact p.Prime] {q : ℚ}
    (_hq : q ≠ 0) (hval : 0 ≤ padicValRat p q) : ¬ p ∣ q.den := by
  intro hd
  have hred : Nat.gcd q.num.natAbs q.den = 1 := q.reduced
  have hnumA : ¬ p ∣ q.num.natAbs := by
    intro hn
    have : p ∣ 1 := by
      have hg := Nat.dvd_gcd hn hd
      simpa [hred] using hg
    exact ‹Fact p.Prime›.out.not_dvd_one this
  have hnum0 : padicValInt p q.num = 0 :=
    padicValInt.eq_zero_of_not_dvd (fun h ↦ hnumA (Int.natCast_dvd.mp h))
  have hden1 : 1 ≤ padicValNat p q.den :=
    one_le_padicValNat_of_dvd q.den_nz hd
  have : padicValRat p q ≤ -1 := by
    rw [padicValRat_def, hnum0, Nat.cast_zero, zero_sub]
    have : (1 : ℤ) ≤ padicValNat p q.den := by exact_mod_cast hden1
    linarith
  linarith

lemma not_dvd_den_ratExpression_prime {p : ℕ} (hp : p.Prime) (h3 : p > 3) :
    ¬ p ∣ (ratExpression p).den := by
  have : Fact p.Prime := ⟨hp⟩
  exact not_dvd_den_of_nonneg_padicVal
    (ne_of_gt (ratExpression_pos (by omega)))
    (le_trans (by decide : (0 : ℤ) ≤ 2) (two_le_padicValRat_ratExpression_prime hp h3))

/-- For a prime `p > 3`, `p^2` divides the reduced numerator of `T(p)`. -/
theorem n_sq_dvd_num_of_prime {p : ℕ} (hp : p.Prime) (h3 : p > 3) :
    (ratExpression p).num ≡ 0 [ZMOD (p ^ 2 : ℤ)] := by
  have : Fact p.Prime := ⟨hp⟩
  have hq0 : ratExpression p ≠ 0 := ne_of_gt (ratExpression_pos (by omega))
  have hval : 2 ≤ padicValRat p (ratExpression p) :=
    two_le_padicValRat_ratExpression_prime hp h3
  have hden : ¬ p ∣ (ratExpression p).den := not_dvd_den_ratExpression_prime hp h3
  have hden0 : padicValNat p (ratExpression p).den = 0 :=
    padicValNat.eq_zero_of_not_dvd hden
  have hnum : 2 ≤ padicValInt p (ratExpression p).num := by
    rw [padicValRat_def] at hval
    simp [hden0] at hval
    exact_mod_cast hval
  have hn0 : (ratExpression p).num.natAbs ≠ 0 :=
    Int.natAbs_ne_zero.mpr (Rat.num_ne_zero.mpr hq0)
  have hpow : p ^ 2 ∣ (ratExpression p).num.natAbs := by
    rw [padicValNat_dvd_iff_le hn0]
    simpa [padicValInt] using hnum
  exact Int.modEq_zero_iff_dvd.2 (Int.natCast_dvd.mpr hpow)

lemma not_n_sq_dvd_num_of_prime_dvd_den {n p : ℕ} (hp : p.Prime) (hpn : p ∣ n)
    (hd : p ∣ (ratExpression n).den) :
    ¬ (ratExpression n).num ≡ 0 [ZMOD (n ^ 2 : ℤ)] := by
  intro hcong
  have hdiv : (n ^ 2 : ℤ) ∣ (ratExpression n).num := Int.modEq_zero_iff_dvd.mp hcong
  have hpz : (p : ℤ) ∣ (n : ℤ) := by exact_mod_cast hpn
  have hpow : (p : ℤ) ∣ (n : ℤ) ^ 2 := dvd_pow hpz (by decide)
  have hnumZ : (p : ℤ) ∣ (ratExpression n).num := hpow.trans (by simpa using hdiv)
  have hnum : p ∣ (ratExpression n).num.natAbs := Int.natCast_dvd.mp hnumZ
  have hg : p ∣ Nat.gcd (ratExpression n).num.natAbs (ratExpression n).den :=
    Nat.dvd_gcd hnum hd
  have hred : Nat.gcd (ratExpression n).num.natAbs (ratExpression n).den = 1 :=
    (ratExpression n).reduced
  have : p ∣ 1 := by simpa [hred] using hg
  exact hp.not_dvd_one this

lemma not_n_sq_dvd_num_of_padicVal_lt {n p : ℕ} (hp : p.Prime) (hpn : p ∣ n)
    (hn0 : 0 < n) (hT : ratExpression n ≠ 0)
    (hval : padicValRat p (ratExpression n) < 2 * padicValNat p n) :
    ¬ (ratExpression n).num ≡ 0 [ZMOD (n ^ 2 : ℤ)] := by
  have : Fact p.Prime := ⟨hp⟩
  intro hcong
  have hdiv : (n ^ 2 : ℤ) ∣ (ratExpression n).num := Int.modEq_zero_iff_dvd.mp hcong
  have hn2 : p ^ (2 * padicValNat p n) ∣ n ^ 2 := by
    rw [mul_comm, pow_mul]
    exact pow_dvd_pow_of_dvd pow_padicValNat_dvd 2
  have hnumA : p ^ (2 * padicValNat p n) ∣ (ratExpression n).num.natAbs := by
    have hn2Z : (p ^ (2 * padicValNat p n) : ℤ) ∣ (n ^ 2 : ℤ) := by exact_mod_cast hn2
    have : (p ^ (2 * padicValNat p n) : ℤ) ∣ (ratExpression n).num :=
      hn2Z.trans (by simpa using hdiv)
    exact Int.natCast_dvd.mp this
  have hn00 : (ratExpression n).num.natAbs ≠ 0 :=
    Int.natAbs_ne_zero.mpr (Rat.num_ne_zero.mpr hT)
  have hle : 2 * padicValNat p n ≤ padicValNat p (ratExpression n).num.natAbs :=
    (padicValNat_dvd_iff_le hn00).1 hnumA
  have hp_num : p ∣ (ratExpression n).num.natAbs := by
    have : 1 ≤ padicValNat p n :=
      one_le_padicValNat_of_dvd (Nat.pos_iff_ne_zero.mp hn0) hpn
    have : 1 ≤ padicValNat p (ratExpression n).num.natAbs := by omega
    exact dvd_of_one_le_padicValNat this
  have hden0 : ¬ p ∣ (ratExpression n).den := by
    intro hd
    have hg : p ∣ Nat.gcd (ratExpression n).num.natAbs (ratExpression n).den :=
      Nat.dvd_gcd hp_num hd
    have hred : Nat.gcd (ratExpression n).num.natAbs (ratExpression n).den = 1 :=
      (ratExpression n).reduced
    exact hp.not_dvd_one (by simpa [hred] using hg)
  have hval' : padicValRat p (ratExpression n) =
      padicValInt p (ratExpression n).num := by
    rw [padicValRat_def, padicValNat.eq_zero_of_not_dvd hden0, Nat.cast_zero, sub_zero]
  have : (2 * padicValNat p n : ℤ) ≤ padicValRat p (ratExpression n) := by
    rw [hval']
    exact_mod_cast hle
  exact not_lt_of_ge this hval

lemma sq_dvd_oddDenom_of_prime_lt {n p : ℕ} (hp : p.Prime) (hlt : p < n) :
    p ^ 2 ∣ oddDenom n := by
  have : p ≤ n - 1 := Nat.le_sub_one_of_lt hlt
  unfold oddDenom
  exact pow_dvd_pow_of_dvd (Nat.dvd_factorial hp.pos this) 2

lemma exists_prime_dvd_lt_of_not_prime {n : ℕ} (hn : 1 < n) (hnp : ¬ n.Prime) :
    ∃ p, p.Prime ∧ p ∣ n ∧ p < n := by
  have hn1 : n ≠ 1 := ne_of_gt hn
  obtain ⟨p, hp, hpn⟩ := Nat.exists_prime_and_dvd hn1
  have hlt : p < n := lt_of_le_of_ne (Nat.le_of_dvd (Nat.zero_lt_of_lt hn) hpn) fun h =>
    hnp (h ▸ hp)
  exact ⟨p, hp, hpn, hlt⟩

lemma oddInnerNum_ne_zero {n : ℕ} (hn : Odd n) (hn1 : 1 < n) :
    oddInnerNum n ≠ 0 := by
  have hT := ratExpression_eq_two_mul_num_div_denom hn hn1
  have hTne : ratExpression n ≠ 0 := ne_of_gt (ratExpression_pos hn1)
  intro h0
  have : ratExpression n = 0 := by
    rw [hT, h0]
    simp
  exact hTne this

lemma padicValRat_ratExpression_odd {n p : ℕ} (hn : Odd n) (hn1 : 1 < n) (hp : p.Prime) :
    padicValRat p (ratExpression n) =
      padicValRat p (2 : ℚ) + padicValRat p (n : ℚ) +
        padicValRat p (oddInnerNum n : ℚ) - padicValRat p (oddDenom n : ℚ) := by
  have : Fact p.Prime := ⟨hp⟩
  have hTeq := ratExpression_eq_two_mul_num_div_denom hn hn1
  have hNne : (oddInnerNum n : ℚ) ≠ 0 := by
    exact_mod_cast (oddInnerNum_ne_zero hn hn1)
  have h2ne : (2 : ℚ) ≠ 0 := by norm_num
  have hnne : (n : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_zero_of_lt hn1)
  have hDne : (oddDenom n : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr oddDenom_ne_zero
  have hprod : ratExpression n = ((2 : ℚ) * n * oddInnerNum n) / oddDenom n := by
    simpa [mul_assoc] using hTeq
  have hnumne : (2 : ℚ) * n * oddInnerNum n ≠ 0 :=
    mul_ne_zero (mul_ne_zero h2ne hnne) hNne
  rw [hprod, padicValRat.div hnumne hDne, padicValRat.mul (mul_ne_zero h2ne hnne) hNne,
    padicValRat.mul h2ne hnne]

lemma padicValRat_ratExpression_of_odd_prime {n p : ℕ} (hn : Odd n) (hn1 : 1 < n)
    (hp : p.Prime) (hp2 : p ≠ 2) :
    padicValRat p (ratExpression n) =
      (padicValNat p n : ℤ) + padicValNat p (oddInnerNum n) -
        padicValNat p (oddDenom n) := by
  have : Fact p.Prime := ⟨hp⟩
  have h2 : padicValRat p (2 : ℚ) = 0 := by
    rw [show (2 : ℚ) = ((2 : ℕ) : ℚ) from rfl, padicValRat.of_nat]
    exact_mod_cast (padicValNat_primes hp2)
  have hnval : padicValRat p (n : ℚ) = padicValNat p n := padicValRat.of_nat
  have hNval : padicValRat p (oddInnerNum n : ℚ) = padicValNat p (oddInnerNum n) :=
    padicValRat.of_nat
  have hDval : padicValRat p (oddDenom n : ℚ) = padicValNat p (oddDenom n) :=
    padicValRat.of_nat
  rw [padicValRat_ratExpression_odd hn hn1 hp, h2, hnval, hNval, hDval]
  abel

lemma not_n_sq_dvd_num_of_odd_inner_lt {n p : ℕ} (hn : n > 3) (hodd : Odd n)
    (hp : p.Prime) (hp2 : p ≠ 2) (hpn : p ∣ n)
    (hval : padicValNat p (oddInnerNum n) <
      padicValNat p n + padicValNat p (oddDenom n)) :
    ¬ (ratExpression n).num ≡ 0 [ZMOD (n ^ 2 : ℤ)] := by
  have hn1 : 1 < n := by omega
  have hn0 : 0 < n := Nat.zero_lt_of_lt hn
  have hT : ratExpression n ≠ 0 := ne_of_gt (ratExpression_pos hn1)
  have hpad : padicValRat p (ratExpression n) =
      (padicValNat p n : ℤ) + padicValNat p (oddInnerNum n) -
        padicValNat p (oddDenom n) :=
    padicValRat_ratExpression_of_odd_prime hodd hn1 hp hp2
  have hlt : padicValRat p (ratExpression n) < 2 * padicValNat p n := by
    rw [hpad]
    have : (padicValNat p (oddInnerNum n) : ℤ) <
        padicValNat p n + padicValNat p (oddDenom n) := by exact_mod_cast hval
    linarith
  exact not_n_sq_dvd_num_of_padicVal_lt hp hpn hn0 hT hlt

lemma two_mul_prime_le_pred_of_odd_composite {n p : ℕ} (hn : 1 < n) (hnp : ¬ n.Prime)
    (hodd : Odd n) (hp : p.Prime) (hpn : p ∣ n) : 2 * p ≤ n - 1 := by
  have hn0 : 0 < n := Nat.zero_lt_of_lt hn
  have hmul : n / p * p = n := Nat.div_mul_cancel hpn
  have hquot_ne_one : n / p ≠ 1 := by
    intro h1
    have : n = p := by
      rw [h1, one_mul] at hmul
      exact hmul.symm
    exact hnp (this ▸ hp)
  have hquot_pos : 1 ≤ n / p := by
    have : p ≤ n := Nat.le_of_dvd hn0 hpn
    exact (Nat.one_le_div_iff hp.pos).mpr this
  have hquot_ne_two : n / p ≠ 2 := by
    intro h2
    have : n = 2 * p := by
      rw [h2] at hmul
      exact hmul.symm
    have : Even n := by
      rw [this]
      exact Even.mul_right even_two p
    exact Nat.not_odd_iff_even.mpr this hodd
  have hquot : 3 ≤ n / p := by omega
  have : 3 * p ≤ n := by
    rw [← hmul]
    exact Nat.mul_le_mul_right p hquot
  omega

lemma two_le_padicValNat_factorial_pred {n p : ℕ} [Fact p.Prime]
    (hn1 : 1 < n) (h : 2 * p ≤ n - 1) :
    2 ≤ padicValNat p (Nat.factorial (n - 1)) := by
  have hp1 : 1 < p := Nat.Prime.one_lt ‹Fact p.Prime›.out
  have hm0 : n - 1 ≠ 0 := by omega
  have hnb : Nat.log p (n - 1) < n :=
    (Nat.log_lt_self p hm0).trans (by omega)
  rw [padicValNat_factorial (p := p) (n := n - 1) (b := n) hnb]
  have h1mem : 1 ∈ Finset.Ico 1 n := Finset.mem_Ico.mpr ⟨le_rfl, hn1⟩
  have hterm : 2 ≤ (n - 1) / p ^ 1 := by
    rw [pow_one]
    exact (Nat.le_div_iff_mul_le (Nat.zero_lt_of_lt hp1)).2 (by simpa [mul_comm] using h)
  have := Finset.single_le_sum
    (fun i _ => Nat.zero_le ((n - 1) / p ^ i)) h1mem
  omega

lemma four_le_padicValNat_oddDenom {n p : ℕ} [Fact p.Prime]
    (hn1 : 1 < n) (h : 2 * p ≤ n - 1) :
    4 ≤ padicValNat p (oddDenom n) := by
  unfold oddDenom
  rw [padicValNat.pow]
  have : 2 ≤ padicValNat p (Nat.factorial (n - 1)) :=
    two_le_padicValNat_factorial_pred hn1 h
  omega

/-- If `v_p(N) ≤ v_p(D)` then `v_p(T) ≤ v_p(n) < 2 v_p(n)` for odd `p | n`. -/
lemma not_n_sq_dvd_num_of_inner_le_denom {n p : ℕ} (hn : n > 3) (hodd : Odd n)
    (hp : p.Prime) (hp2 : p ≠ 2) (hpn : p ∣ n)
    (hle : padicValNat p (oddInnerNum n) ≤ padicValNat p (oddDenom n)) :
    ¬ (ratExpression n).num ≡ 0 [ZMOD (n ^ 2 : ℤ)] := by
  have : Fact p.Prime := ⟨hp⟩
  have hn0 : 0 < n := by omega
  have _he : 1 ≤ padicValNat p n :=
    one_le_padicValNat_of_dvd (Nat.pos_iff_ne_zero.mp hn0) hpn
  refine not_n_sq_dvd_num_of_odd_inner_lt hn hodd hp hp2 hpn ?_
  omega

lemma conjecture_of_odd_composite_converse
    (hconv : ∀ {n : ℕ}, n > 3 → Odd n → ¬ n.Prime →
      ¬ (ratExpression n).num ≡ 0 [ZMOD (n ^ 2 : ℤ)]) :
    ∀ {n : ℕ}, n > 3 →
      ((ratExpression n).num ≡ 0 [ZMOD (n ^ 2 : ℤ)] ↔ n.Prime) := by
  intro n hn
  constructor
  · intro hcong
    by_contra hnp
    rcases Nat.even_or_odd n with he | ho
    · exact not_n_sq_dvd_num_of_even hn he hcong
    · exact hconv hn ho hnp hcong
  · intro hp
    exact n_sq_dvd_num_of_prime hp hn

/-- The `-2/n` terms cancel: `q T(pq) - T(p) = q S_{pq} - S_p`. -/
lemma q_mul_ratExpression_sub_eq_sum {p q : ℕ} (hp0 : 0 < p) (hq0 : 0 < q) :
    (q : ℚ) * ratExpression (p * q) - ratExpression p =
      (q : ℚ) * ∑ i ∈ range (p * q), (2 : ℚ) ^ (i + 1) / (i + 1) -
        ∑ i ∈ range p, (2 : ℚ) ^ (i + 1) / (i + 1) := by
  have hn : 0 < p * q := Nat.mul_pos hp0 hq0
  have hpne : (p : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.pos_iff_ne_zero.mp hp0)
  have hqne : (q : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.pos_iff_ne_zero.mp hq0)
  have hdiv : (q : ℚ) * ((-2 : ℚ) / (p * q)) = (-2 : ℚ) / p := by
    field_simp [hpne, hqne]
  rw [ratExpression_of_pos hn, ratExpression_of_pos hp0, mul_add, Nat.cast_mul, hdiv]
  ring

lemma two_eq_one_add_one_zmod {q : ℕ} : (2 : ZMod q) = 1 + 1 := by
  norm_num

lemma two_pow_card_eq_two {q : ℕ} [Fact q.Prime] : (2 : ZMod q) ^ q = 2 := by
  rw [two_eq_one_add_one_zmod, add_pow_char]
  simp

lemma two_pow_mul_eq_two_pow_zmod {q j : ℕ} [Fact q.Prime] :
    (2 : ZMod q) ^ (j * q) = (2 : ZMod q) ^ j := by
  rw [mul_comm, pow_mul, two_pow_card_eq_two]

lemma two_pow_j_le_of_mul {q j : ℕ} (hq : 0 < q) : 2 ^ j ≤ 2 ^ (j * q) :=
  Nat.pow_le_pow_right (by decide) (Nat.le_mul_of_pos_right j hq)

lemma q_dvd_two_pow_mul_sub {q j : ℕ} (hq : q.Prime) :
    q ∣ 2 ^ (j * q) - 2 ^ j := by
  have : Fact q.Prime := ⟨hq⟩
  have hle := two_pow_j_le_of_mul (j := j) hq.pos
  have hz : ((2 ^ (j * q) : ℕ) : ZMod q) = ((2 ^ j : ℕ) : ZMod q) := by
    rw [Nat.cast_pow, Nat.cast_pow]
    exact two_pow_mul_eq_two_pow_zmod
  exact (Nat.modEq_iff_dvd' hle).1 ((ZMod.natCast_eq_natCast_iff _ _ q).1 hz.symm)

lemma two_pow_mul_ne {q j : ℕ} (hq : 1 < q) (hj : 0 < j) : 2 ^ (j * q) ≠ 2 ^ j := by
  refine ne_of_gt (Nat.pow_lt_pow_right (by decide : 1 < 2) ?_)
  have : j * 1 < j * q := Nat.mul_lt_mul_of_pos_left hq hj
  simpa using this

lemma nat_cast_two_pow_mul_sub {q j : ℕ} (hq : 0 < q) :
    ((2 ^ (j * q) - 2 ^ j : ℕ) : ℚ) = (2 : ℚ) ^ (j * q) - (2 : ℚ) ^ j := by
  have hle := two_pow_j_le_of_mul (j := j) hq
  rw [Nat.cast_sub hle, Nat.cast_pow, Nat.cast_pow]
  simp

lemma one_le_padicValRat_two_pow_mul_sub {q j : ℕ} (hq : q.Prime) (hj : 0 < j) :
    1 ≤ padicValRat q ((2 : ℚ) ^ (j * q) - (2 : ℚ) ^ j) := by
  have : Fact q.Prime := ⟨hq⟩
  have hne := two_pow_mul_ne hq.one_lt hj
  have hdiff : 2 ^ (j * q) - 2 ^ j ≠ 0 :=
    Nat.sub_ne_zero_of_lt (lt_of_le_of_ne (two_pow_j_le_of_mul hq.pos) hne.symm)
  have hval : 1 ≤ padicValNat q (2 ^ (j * q) - 2 ^ j) :=
    one_le_padicValNat_of_dvd hdiff (q_dvd_two_pow_mul_sub hq)
  rw [← nat_cast_two_pow_mul_sub hq.pos, padicValRat.of_nat]
  exact_mod_cast hval

lemma padicValRat_nat_eq_zero_of_lt {q n : ℕ} [Fact q.Prime]
    (hn : 0 < n) (hlt : n < q) : padicValRat q (n : ℚ) = 0 := by
  rw [padicValRat.of_nat]
  exact_mod_cast padicValNat.eq_zero_of_not_dvd (Nat.not_dvd_of_pos_of_lt hn hlt)

lemma one_le_padicValRat_two_pow_mul_sub_div {q j : ℕ}
    (hq : q.Prime) (hj : 0 < j) (hjq : j < q) :
    1 ≤ padicValRat q (((2 : ℚ) ^ (j * q) - (2 : ℚ) ^ j) / j) := by
  have : Fact q.Prime := ⟨hq⟩
  have hj0 : (j : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.pos_iff_ne_zero.mp hj)
  have hnum : (2 : ℚ) ^ (j * q) - (2 : ℚ) ^ j ≠ 0 := by
    rw [← nat_cast_two_pow_mul_sub hq.pos]
    exact Nat.cast_ne_zero.mpr
      (Nat.sub_ne_zero_of_lt (lt_of_le_of_ne (two_pow_j_le_of_mul hq.pos)
        (two_pow_mul_ne hq.one_lt hj).symm))
  rw [padicValRat.div hnum hj0, padicValRat_nat_eq_zero_of_lt hj hjq, sub_zero]
  exact one_le_padicValRat_two_pow_mul_sub hq hj

lemma padicValRat_two_pow_eq_zero {q k : ℕ} [Fact q.Prime] (hq2 : q ≠ 2) :
    padicValRat q ((2 : ℚ) ^ k) = 0 := by
  rw [padicValRat.pow]
  have h2 : padicValRat q (2 : ℚ) = 0 := by
    rw [show (2 : ℚ) = ((2 : ℕ) : ℚ) from rfl, padicValRat.of_nat]
    exact_mod_cast (padicValNat_primes hq2)
  simp [h2]

lemma padicValRat_q_mul_two_pow_div {q k : ℕ} (hq : q.Prime) (hq2 : q ≠ 2)
    (hk : 0 < k) (hnd : ¬ q ∣ k) :
    padicValRat q ((q : ℚ) * (2 : ℚ) ^ k / k) = 1 := by
  have : Fact q.Prime := ⟨hq⟩
  have hk0 : (k : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.pos_iff_ne_zero.mp hk)
  have h2ne : (2 : ℚ) ^ k ≠ 0 := pow_ne_zero _ (by norm_num)
  have hqne : (q : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hq.ne_zero
  have hnum : (q : ℚ) * (2 : ℚ) ^ k ≠ 0 := mul_ne_zero hqne h2ne
  have hkval : padicValRat q (k : ℚ) = 0 := by
    rw [padicValRat.of_nat]
    exact_mod_cast padicValNat.eq_zero_of_not_dvd hnd
  rw [padicValRat.div hnum hk0, padicValRat.mul hqne h2ne, padicValRat.self hq.one_lt,
    padicValRat_two_pow_eq_zero hq2, hkval]
  simp

lemma one_le_padicValRat_sum {α : Type*} [DecidableEq α] {q : ℕ} [Fact q.Prime]
    {s : Finset α} (f : α → ℚ) (hf : ∀ i ∈ s, 1 ≤ padicValRat q (f i))
    (hsum : ∑ i ∈ s, f i ≠ 0) :
    1 ≤ padicValRat q (∑ i ∈ s, f i) := by
  induction s using Finset.induction_on with
  | empty =>
    simp at hsum
  | insert a s ha ih =>
    rw [sum_insert ha] at hsum ⊢
    by_cases hrest : ∑ i ∈ s, f i = 0
    · simpa [hrest] using hf a (mem_insert_self _ _)
    · have h1 := hf a (mem_insert_self _ _)
      have h2 := ih (fun i hi => hf i (mem_insert_of_mem hi)) hrest
      exact le_trans (le_min h1 h2) (padicValRat.min_le_padicValRat_add (p := q) hsum)

lemma den_int_div_nat (a : ℤ) (b : ℕ) : ((a : ℚ) / b).den ∣ b := by
  have h : ((a : ℚ) / (b : ℕ)) = (a : ℚ) / (b : ℤ) := by simp
  rw [h, Rat.intCast_div_eq_divInt]
  exact Int.natCast_dvd.mp (Rat.den_dvd a b)

lemma den_two_pow_div_dvd {k : ℕ} (_hk : 0 < k) : ((2 : ℚ) ^ k / k).den ∣ k := by
  have h : (2 : ℚ) ^ k / k = ((2 ^ k : ℤ) : ℚ) / k := by
    simp
  rw [h]
  exact den_int_div_nat _ k

lemma not_dvd_den_add {q : ℕ} (hq : q.Prime) {x y : ℚ}
    (hx : ¬ q ∣ x.den) (hy : ¬ q ∣ y.den) : ¬ q ∣ (x + y).den := by
  intro hd
  have hmul : q ∣ x.den * y.den :=
    (hd.trans (Rat.add_den_dvd_lcm x y)).trans (Nat.lcm_dvd_mul _ _)
  exact (hq.dvd_mul.mp hmul).elim hx hy

lemma not_dvd_den_sum {α : Type*} [DecidableEq α] {q : ℕ} (hq : q.Prime)
    {s : Finset α} (f : α → ℚ) (h : ∀ i ∈ s, ¬ q ∣ (f i).den) :
    ¬ q ∣ (∑ i ∈ s, f i).den := by
  induction s using Finset.induction_on with
  | empty =>
    simp [hq.not_dvd_one]
  | insert a s ha ih =>
    rw [sum_insert ha]
    exact not_dvd_den_add hq (h a (mem_insert_self _ _))
      (ih fun i hi => h i (mem_insert_of_mem hi))

lemma not_dvd_den_two_pow_div_of_lt {q k : ℕ} (_hq : q.Prime) (hk : 0 < k) (hlt : k < q) :
    ¬ q ∣ ((2 : ℚ) ^ k / k).den := by
  intro hd
  exact Nat.not_dvd_of_pos_of_lt hk hlt (hd.trans (den_two_pow_div_dvd hk))

lemma not_dvd_den_ratExpression_of_lt {n q : ℕ} (hq : q.Prime) (hn : 0 < n) (hlt : n < q) :
    ¬ q ∣ (ratExpression n).den := by
  rw [ratExpression_of_pos hn]
  refine not_dvd_den_add hq ?hneg ?hsum
  · have hden : ((-2 : ℚ) / n).den = ((2 : ℚ) / n).den := by
      have hneg : (-2 : ℚ) / n = -((2 : ℚ) / n) := by simp [div_eq_mul_inv]
      rw [hneg, Rat.den_neg_eq_den]
    have hdvd : ((2 : ℚ) / n).den ∣ n := by
      have : (2 : ℚ) / n = ((2 : ℤ) : ℚ) / n := by simp
      rw [this]
      exact den_int_div_nat 2 n
    intro hd
    exact Nat.not_dvd_of_pos_of_lt hn hlt ((hden ▸ hd).trans hdvd)
  · have heq : ∑ i ∈ range n, (2 : ℚ) ^ (i + 1) / (i + 1) =
        ∑ i ∈ range n, (2 : ℚ) ^ (i + 1) / (i + 1 : ℕ) :=
      sum_congr rfl fun i _ => by simp [Nat.cast_succ]
    rw [heq]
    refine not_dvd_den_sum hq (fun i => (2 : ℚ) ^ (i + 1) / (i + 1 : ℕ)) ?_
    intro i hi
    exact not_dvd_den_two_pow_div_of_lt hq (Nat.succ_pos i)
      (lt_of_le_of_lt (Nat.succ_le_of_lt (mem_range.mp hi)) hlt)

lemma padicValRat_eq_zero_of_not_dvd_num_den {q : ℕ} [Fact q.Prime] {x : ℚ}
    (hnum : ¬ q ∣ x.num.natAbs) (hden : ¬ q ∣ x.den) :
    padicValRat q x = 0 := by
  have hnumZ : ¬ (q : ℤ) ∣ x.num := fun h => hnum (Int.natCast_dvd.mp h)
  rw [padicValRat_def, padicValInt.eq_zero_of_not_dvd hnumZ,
    padicValNat.eq_zero_of_not_dvd hden]
  simp

lemma q_mul_two_pow_div_eq {q j : ℕ} (hq : 0 < q) (hj : 0 < j) :
    (q : ℚ) * ((2 : ℚ) ^ (j * q) / (j * q)) = (2 : ℚ) ^ (j * q) / j := by
  have hq0 : (q : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.pos_iff_ne_zero.mp hq)
  have hj0 : (j : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.pos_iff_ne_zero.mp hj)
  field_simp [hq0, hj0, Nat.cast_mul]

lemma sum_filter_dvd_succ {p q : ℕ} (hq0 : 0 < q) (f : ℕ → ℚ) :
    ∑ i ∈ (range (p * q)).filter (fun i => q ∣ i + 1), f (i + 1) =
      ∑ j ∈ range p, f ((j + 1) * q) := by
  refine Eq.symm (sum_nbij' (fun j => (j + 1) * q - 1) (fun i => (i + 1) / q - 1)
    ?hi ?hj ?left ?right ?heq)
  · intro j hj
    have hj1 : 0 < (j + 1) * q := Nat.mul_pos (Nat.succ_pos j) hq0
    have hle : (j + 1) * q ≤ p * q :=
      Nat.mul_le_mul_right q (Nat.succ_le_of_lt (mem_range.mp hj))
    have hsucc : (j + 1) * q - 1 + 1 = (j + 1) * q := Nat.sub_add_cancel hj1
    have hmem : (j + 1) * q - 1 < p * q :=
      Nat.lt_of_succ_le (by
        rw [Nat.succ_eq_add_one, Nat.sub_add_cancel hj1]
        exact hle)
    refine mem_filter.mpr ⟨mem_range.mpr hmem, ?_⟩
    rw [hsucc, mul_comm]
    exact Nat.dvd_mul_right q (j + 1)
  · intro i hi
    have hi' := mem_filter.mp hi
    have hilt : i < p * q := mem_range.mp hi'.1
    have hdvd : q ∣ i + 1 := hi'.2
    have hdiv : (i + 1) / q * q = i + 1 := Nat.div_mul_cancel hdvd
    have hpos : 0 < (i + 1) / q :=
      Nat.div_pos (Nat.le_of_dvd (Nat.succ_pos i) hdvd) hq0
    have hmul : (i + 1) / q * q ≤ p * q := by
      rw [hdiv]
      exact Nat.succ_le_of_lt hilt
    have hle : (i + 1) / q ≤ p := Nat.le_of_mul_le_mul_right hmul hq0
    exact mem_range.mpr (Nat.lt_of_succ_le (by
      rw [Nat.succ_eq_add_one, Nat.sub_add_cancel hpos]
      exact hle))
  · intro j _hj
    have hj1 : 0 < (j + 1) * q := Nat.mul_pos (Nat.succ_pos j) hq0
    have hsucc : (j + 1) * q - 1 + 1 = (j + 1) * q := Nat.sub_add_cancel hj1
    rw [hsucc, Nat.mul_div_cancel _ hq0, Nat.add_sub_cancel]
  · intro i hi
    have hi' := mem_filter.mp hi
    have hdvd : q ∣ i + 1 := hi'.2
    have hpos : 0 < (i + 1) / q :=
      Nat.div_pos (Nat.le_of_dvd (Nat.succ_pos i) hdvd) hq0
    rw [Nat.sub_add_cancel hpos, Nat.div_mul_cancel hdvd, Nat.add_sub_cancel]
  · intro j _hj
    have hj1 : 0 < (j + 1) * q := Nat.mul_pos (Nat.succ_pos j) hq0
    rw [Nat.sub_add_cancel hj1]

lemma q_mul_sum_dvd_eq {p q : ℕ} (hq0 : 0 < q) :
    (q : ℚ) * ∑ i ∈ (range (p * q)).filter (fun i => q ∣ i + 1),
        (2 : ℚ) ^ (i + 1) / (i + 1) =
      ∑ j ∈ range p, (2 : ℚ) ^ ((j + 1) * q) / (j + 1) := by
  have hsum : ∑ i ∈ (range (p * q)).filter (fun i => q ∣ i + 1),
      (2 : ℚ) ^ (i + 1) / (i + 1) =
    ∑ i ∈ (range (p * q)).filter (fun i => q ∣ i + 1),
      (2 : ℚ) ^ (i + 1) / (i + 1 : ℕ) :=
    sum_congr rfl fun i _ => by simp [Nat.cast_succ]
  rw [hsum, sum_filter_dvd_succ (f := fun k => (2 : ℚ) ^ k / k) hq0, mul_sum]
  refine sum_congr rfl fun j _ => ?_
  simpa [Nat.cast_succ] using q_mul_two_pow_div_eq hq0 (Nat.succ_pos j)

lemma q_mul_ratExpression_sub_eq_fermat_add {p q : ℕ} (hp0 : 0 < p) (hq0 : 0 < q) :
    (q : ℚ) * ratExpression (p * q) - ratExpression p =
      ∑ j ∈ range p,
          ((2 : ℚ) ^ ((j + 1) * q) - (2 : ℚ) ^ (j + 1)) / (j + 1) +
      ∑ i ∈ (range (p * q)).filter (fun i => ¬ q ∣ i + 1),
          (q : ℚ) * ((2 : ℚ) ^ (i + 1) / (i + 1)) := by
  rw [q_mul_ratExpression_sub_eq_sum hp0 hq0,
    ← sum_filter_add_sum_filter_not (range (p * q)) (fun i => q ∣ i + 1)
      (fun i => (2 : ℚ) ^ (i + 1) / (i + 1)),
    mul_add, q_mul_sum_dvd_eq hq0, mul_sum, add_sub_right_comm, ← sum_sub_distrib]
  refine congrArg₂ (· + ·) ?_ rfl
  refine sum_congr rfl fun j _ => (sub_div _ _ _).symm

lemma fermat_div_pos {q j : ℕ} (hq : 1 < q) (hj : 0 < j) :
    0 < ((2 : ℚ) ^ (j * q) - (2 : ℚ) ^ j) / j := by
  have hlt : 2 ^ j < 2 ^ (j * q) := by
    refine Nat.pow_lt_pow_right (by decide : 1 < 2) ?_
    have : j * 1 < j * q := Nat.mul_lt_mul_of_pos_left hq hj
    simpa using this
  have hnum : 0 < (2 : ℚ) ^ (j * q) - (2 : ℚ) ^ j := by
    rw [← nat_cast_two_pow_mul_sub (Nat.zero_lt_of_lt hq)]
    exact Nat.cast_pos.mpr (Nat.sub_pos_of_lt hlt)
  exact div_pos hnum (Nat.cast_pos.mpr hj)

lemma fermat_sum_pos {p q : ℕ} (hq : 1 < q) (hp0 : 0 < p) :
    0 < ∑ j ∈ range p,
        ((2 : ℚ) ^ ((j + 1) * q) - (2 : ℚ) ^ (j + 1)) / (j + 1) := by
  refine sum_pos (fun j _hj => ?_) (nonempty_range_iff.mpr (Nat.pos_iff_ne_zero.mp hp0))
  simpa [Nat.cast_succ] using fermat_div_pos hq (Nat.succ_pos j)

lemma rest_filter_nonempty {p q : ℕ} (hp0 : 0 < p) (hq : q.Prime) :
    ((range (p * q)).filter (fun i => ¬ q ∣ i + 1)).Nonempty := by
  refine ⟨0, mem_filter.mpr ⟨mem_range.mpr (Nat.mul_pos hp0 hq.pos), ?_⟩⟩
  simpa using hq.not_dvd_one

lemma rest_sum_pos {p q : ℕ} (hp0 : 0 < p) (hq : q.Prime) :
    0 < ∑ i ∈ (range (p * q)).filter (fun i => ¬ q ∣ i + 1),
        (q : ℚ) * ((2 : ℚ) ^ (i + 1) / (i + 1)) :=
  sum_pos (fun i _ => mul_pos (Nat.cast_pos.mpr hq.pos) (term_pos i))
    (rest_filter_nonempty hp0 hq)

lemma one_le_padicValRat_fermat_sum {p q : ℕ} [Fact q.Prime]
    (hq : q.Prime) (hp0 : 0 < p) (hpq : p < q) :
    1 ≤ padicValRat q (∑ j ∈ range p,
        ((2 : ℚ) ^ ((j + 1) * q) - (2 : ℚ) ^ (j + 1)) / (j + 1)) := by
  refine one_le_padicValRat_sum _ ?_ (ne_of_gt (fermat_sum_pos hq.one_lt hp0))
  intro j hj
  simpa [Nat.cast_succ] using one_le_padicValRat_two_pow_mul_sub_div hq (Nat.succ_pos j)
    (lt_of_le_of_lt (Nat.succ_le_of_lt (mem_range.mp hj)) hpq)

lemma one_le_padicValRat_rest_sum {p q : ℕ} [Fact q.Prime]
    (hq : q.Prime) (hq2 : q ≠ 2) (hp0 : 0 < p) :
    1 ≤ padicValRat q (∑ i ∈ (range (p * q)).filter (fun i => ¬ q ∣ i + 1),
        (q : ℚ) * ((2 : ℚ) ^ (i + 1) / (i + 1))) := by
  refine one_le_padicValRat_sum _ ?_ (ne_of_gt (rest_sum_pos hp0 hq))
  intro i hi
  have hnd : ¬ q ∣ i + 1 := (mem_filter.mp hi).2
  have hterm : (q : ℚ) * ((2 : ℚ) ^ (i + 1) / (i + 1)) =
      (q : ℚ) * (2 : ℚ) ^ (i + 1) / (i + 1) := (mul_div_assoc _ _ _).symm
  rw [hterm]
  simpa [Nat.cast_succ] using
    (padicValRat_q_mul_two_pow_div hq hq2 (Nat.succ_pos i) hnd).ge

lemma padicValNat_mul_prime_lt {m q : ℕ} (hm : 0 < m) (hq : q.Prime) (hlt : m < q) :
    padicValNat q (m * q) = 1 := by
  have : Fact q.Prime := ⟨hq⟩
  rw [padicValNat.mul (Nat.pos_iff_ne_zero.mp hm) hq.ne_zero,
    padicValNat.eq_zero_of_not_dvd (Nat.not_dvd_of_pos_of_lt hm hlt),
    padicValNat_self, zero_add]

/-- If `1 < m < q` with `q` prime and `q ∤ T(m).num`, then `v_q(T(mq)) = -1`. -/
lemma padicValRat_ratExpression_mul_eq_neg_one {m q : ℕ}
    (hm : 1 < m) (hq : q.Prime) (hmq : m < q)
    (hnum : ¬ q ∣ (ratExpression m).num.natAbs) :
    padicValRat q (ratExpression (m * q)) = -1 := by
  have : Fact q.Prime := ⟨hq⟩
  have hm2 : 2 ≤ m := Nat.succ_le_of_lt hm
  have hq2 : q ≠ 2 := fun h => (h ▸ hmq).not_ge hm2
  have hm0 : 0 < m := Nat.zero_lt_of_lt hm
  have hq0 : 0 < q := hq.pos
  have hn1 : 1 < m * q := by
    have : 2 * 2 ≤ m * q := Nat.mul_le_mul hm2 hq.two_le
    omega
  have hTp : ratExpression m ≠ 0 := ne_of_gt (ratExpression_pos hm)
  have hTn : ratExpression (m * q) ≠ 0 := ne_of_gt (ratExpression_pos hn1)
  have hqne : (q : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hq.ne_zero
  have hden : ¬ q ∣ (ratExpression m).den :=
    not_dvd_den_ratExpression_of_lt hq hm0 hmq
  have hBval : padicValRat q (ratExpression m) = 0 :=
    padicValRat_eq_zero_of_not_dvd_num_den hnum hden
  have hdiff := q_mul_ratExpression_sub_eq_fermat_add hm0 hq0
  set F := ∑ j ∈ range m,
      ((2 : ℚ) ^ ((j + 1) * q) - (2 : ℚ) ^ (j + 1)) / (j + 1)
  set O := ∑ i ∈ (range (m * q)).filter (fun i => ¬ q ∣ i + 1),
      (q : ℚ) * ((2 : ℚ) ^ (i + 1) / (i + 1))
  have hFpos : 0 < F := fermat_sum_pos hq.one_lt hm0
  have hOpos : 0 < O := rest_sum_pos hm0 hq
  have hD0 : F + O ≠ 0 := ne_of_gt (add_pos hFpos hOpos)
  have hFval : 1 ≤ padicValRat q F := one_le_padicValRat_fermat_sum hq hm0 hmq
  have hOval : 1 ≤ padicValRat q O := one_le_padicValRat_rest_sum hq hq2 hm0
  have hDval : 1 ≤ padicValRat q (F + O) :=
    le_trans (le_min hFval hOval) (padicValRat.min_le_padicValRat_add hD0)
  have hA : (q : ℚ) * ratExpression (m * q) = F + O + ratExpression m :=
    (sub_eq_iff_eq_add).mp hdiff
  have hA0 : (q : ℚ) * ratExpression (m * q) ≠ 0 := mul_ne_zero hqne hTn
  have hAval : padicValRat q ((q : ℚ) * ratExpression (m * q)) = 0 := by
    have hlt : padicValRat q (ratExpression m) < padicValRat q (F + O) := by
      rw [hBval]
      exact lt_of_lt_of_le (by decide : (0 : ℤ) < 1) hDval
    have hsum0 : ratExpression m + (F + O) ≠ 0 := by
      rw [add_comm, ← hA]
      exact hA0
    rw [hA, add_comm, padicValRat.add_eq_of_lt hsum0 hTp hD0 hlt, hBval]
  have hmul : padicValRat q ((q : ℚ) * ratExpression (m * q)) =
      1 + padicValRat q (ratExpression (m * q)) := by
    rw [padicValRat.mul hqne hTn, show padicValRat q (q : ℚ) = 1 from padicValRat.self hq.one_lt]
  linarith [hAval, hmul]

/-- Converse at `n = m q` when `q` is prime, `1 < m < q`, and `q ∤ T(m).num`. -/
lemma not_n_sq_dvd_num_of_mul_odd_primes {m q : ℕ}
    (hm : 1 < m) (hq : q.Prime) (hmq : m < q)
    (hnum : ¬ q ∣ (ratExpression m).num.natAbs) :
    ¬ (ratExpression (m * q)).num ≡ 0 [ZMOD ((m * q) ^ 2 : ℤ)] := by
  have : Fact q.Prime := ⟨hq⟩
  have hn0 : 0 < m * q := Nat.mul_pos (Nat.zero_lt_of_lt hm) hq.pos
  have hn1 : 1 < m * q := by
    have : 2 * 2 ≤ m * q := Nat.mul_le_mul (Nat.succ_le_of_lt hm) hq.two_le
    omega
  have hT : ratExpression (m * q) ≠ 0 := ne_of_gt (ratExpression_pos hn1)
  have hval : padicValRat q (ratExpression (m * q)) = -1 :=
    padicValRat_ratExpression_mul_eq_neg_one hm hq hmq hnum
  have hlt : padicValRat q (ratExpression (m * q)) < 2 * padicValNat q (m * q) := by
    rw [hval, padicValNat_mul_prime_lt (Nat.zero_lt_of_lt hm) hq hmq]
    simp
  exact not_n_sq_dvd_num_of_padicVal_lt hq (dvd_mul_left q m) hn0 hT hlt

#print axioms OeisA108866.not_n_sq_dvd_num_of_even
#print axioms OeisA108866.n_sq_dvd_num_of_prime
#print axioms OeisA108866.padicValRat_ratExpression_of_odd_prime
#print axioms OeisA108866.not_n_sq_dvd_num_of_odd_inner_lt
#print axioms OeisA108866.not_n_sq_dvd_num_of_inner_le_denom
#print axioms OeisA108866.q_dvd_two_pow_mul_sub
#print axioms OeisA108866.one_le_padicValRat_two_pow_mul_sub
#print axioms OeisA108866.not_dvd_den_ratExpression_of_lt
#print axioms OeisA108866.padicValRat_ratExpression_mul_eq_neg_one
#print axioms OeisA108866.not_n_sq_dvd_num_of_mul_odd_primes

end OeisA108866
