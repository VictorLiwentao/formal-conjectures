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
import Mathlib.Data.Nat.Factorial.BigOperators
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.ZMod.Factorial
import Mathlib.Algebra.Field.ZMod
import Mathlib.NumberTheory.Multiplicity
import Mathlib.FieldTheory.Finite.Basic

/-!
Partial development for OEIS A108866.

This file does not use `OeisA108866.conjecture`. It proves the even
converse, the Komatsu–Sury odd identity, the prime direction
`p^2 ∣ T(p).num` for primes `p > 3`, and reduction lemmas for the
odd-composite converse. For `1 < m < q` with `q` prime and
`q ∤ T(m).num`, it proves `v_q(T(mq)) = -1`. Lifting-the-exponent
gives the recurrence: if `v_q(T(m)) < 1` then
`v_q(T(mq)) = v_q(T(m)) - 1`. If an odd prime `p` satisfies
`p ≤ m < 2p` and `p ∤ m`, then `v_p(T(m)) = -1`, so the converse
holds at `n = mp`. If `p^e ≤ m < p^{e+1}`, `p ∤ m`, and the truncated
sum `L(m / p^e)` is nonzero in `𝔽_p`, then `v_p(T(m)) = -e`.
Kummer's theorem gives `v_p(C(p^e-1,k))=0`. For powers of 3 the
unique odd index of maximal 3-valuation is `3^{e-1}`, so
`v_3(T(3^e))=2-e<2e`. For `n=3 p^e` with prime `p≥5` the unique odd
index of maximal `p`-valuation is `p^e`, so `v_p(T(3 p^e))=-e<2e`.
The remaining odd-composite cases are not proved here.
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

lemma not_dvd_two_pow {q k : ℕ} (hq : q.Prime) (hq2 : q ≠ 2) : ¬ q ∣ 2 ^ k := by
  intro h
  have : q = 1 ∨ q = 2 := (Nat.dvd_prime Nat.prime_two).mp (hq.dvd_of_dvd_pow h)
  exact this.elim (fun h1 => hq.ne_one h1) hq2

lemma padicValNat_two_pow_mul_sub {q j : ℕ} (hq : q.Prime) (hq2 : q ≠ 2) (hj : 0 < j) :
    padicValNat q (2 ^ (j * q) - 2 ^ j) =
      padicValNat q (2 ^ q - 2) + padicValNat q j := by
  have : Fact q.Prime := ⟨hq⟩
  have hqodd : Odd q := hq.odd_of_ne_two hq2
  have hyx : 2 < 2 ^ q := Nat.pow_lt_pow_right (by decide : 1 < 2) hq.one_lt
  have hxy : q ∣ 2 ^ q - 2 := by
    simpa using q_dvd_two_pow_mul_sub (j := 1) hq
  have hx : ¬ q ∣ 2 ^ q := not_dvd_two_pow hq hq2
  have hpow : 2 ^ (j * q) - 2 ^ j = (2 ^ q) ^ j - 2 ^ j := by
    rw [← pow_mul, mul_comm]
  rw [hpow]
  exact padicValNat.pow_sub_pow hqodd hyx hxy hx (Nat.pos_iff_ne_zero.mp hj)

lemma one_le_padicValNat_two_pow_sub_two {q : ℕ} (hq : q.Prime) :
    1 ≤ padicValNat q (2 ^ q - 2) := by
  have : Fact q.Prime := ⟨hq⟩
  have hlt : 2 < 2 ^ q := Nat.pow_lt_pow_right (by decide : 1 < 2) hq.one_lt
  have hne : 2 ^ q - 2 ≠ 0 := Nat.sub_ne_zero_of_lt hlt
  exact one_le_padicValNat_of_dvd hne (by simpa using q_dvd_two_pow_mul_sub (j := 1) hq)

lemma one_le_padicValRat_two_pow_mul_sub_div {q j : ℕ}
    (hq : q.Prime) (hq2 : q ≠ 2) (hj : 0 < j) :
    1 ≤ padicValRat q (((2 : ℚ) ^ (j * q) - (2 : ℚ) ^ j) / j) := by
  have : Fact q.Prime := ⟨hq⟩
  have hj0 : (j : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.pos_iff_ne_zero.mp hj)
  have hnum : (2 : ℚ) ^ (j * q) - (2 : ℚ) ^ j ≠ 0 := by
    rw [← nat_cast_two_pow_mul_sub hq.pos]
    exact Nat.cast_ne_zero.mpr
      (Nat.sub_ne_zero_of_lt (lt_of_le_of_ne (two_pow_j_le_of_mul hq.pos)
        (two_pow_mul_ne hq.one_lt hj).symm))
  have hval : (padicValNat q (2 ^ (j * q) - 2 ^ j) : ℤ) - padicValNat q j =
      padicValNat q (2 ^ q - 2) := by
    rw [padicValNat_two_pow_mul_sub hq hq2 hj, Nat.cast_add, add_sub_cancel_right]
  rw [padicValRat.div hnum hj0, ← nat_cast_two_pow_mul_sub hq.pos, padicValRat.of_nat,
    padicValRat.of_nat, hval]
  exact_mod_cast one_le_padicValNat_two_pow_sub_two hq

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
    (hq : q.Prime) (hq2 : q ≠ 2) (hp0 : 0 < p) :
    1 ≤ padicValRat q (∑ j ∈ range p,
        ((2 : ℚ) ^ ((j + 1) * q) - (2 : ℚ) ^ (j + 1)) / (j + 1)) := by
  refine one_le_padicValRat_sum _ ?_ (ne_of_gt (fermat_sum_pos hq.one_lt hp0))
  intro j hj
  simpa [Nat.cast_succ] using one_le_padicValRat_two_pow_mul_sub_div hq hq2 (Nat.succ_pos j)

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
  have hFval : 1 ≤ padicValRat q F := one_le_padicValRat_fermat_sum hq hq2 hm0
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

lemma one_le_padicValRat_q_mul_sub_of_ne {m q : ℕ}
    (hm0 : 0 < m) (hq : q.Prime) (hq2 : q ≠ 2)
    (hD : (q : ℚ) * ratExpression (m * q) - ratExpression m ≠ 0) :
    1 ≤ padicValRat q ((q : ℚ) * ratExpression (m * q) - ratExpression m) := by
  have : Fact q.Prime := ⟨hq⟩
  have hdiff := q_mul_ratExpression_sub_eq_fermat_add hm0 hq.pos
  set F := ∑ j ∈ range m,
      ((2 : ℚ) ^ ((j + 1) * q) - (2 : ℚ) ^ (j + 1)) / (j + 1)
  set O := ∑ i ∈ (range (m * q)).filter (fun i => ¬ q ∣ i + 1),
      (q : ℚ) * ((2 : ℚ) ^ (i + 1) / (i + 1))
  have hFval : 1 ≤ padicValRat q F := one_le_padicValRat_fermat_sum hq hq2 hm0
  have hOval : 1 ≤ padicValRat q O := one_le_padicValRat_rest_sum hq hq2 hm0
  have hFO : F + O ≠ 0 := by
    rwa [hdiff] at hD
  rw [hdiff]
  exact le_trans (le_min hFval hOval) (padicValRat.min_le_padicValRat_add hFO)

/-- If `v_q(T(m)) < 1`, then `v_q(T(mq)) = v_q(T(m)) - 1`. -/
lemma padicValRat_ratExpression_mul_of_val_lt_one {m q : ℕ}
    (hm : 1 < m) (hq : q.Prime) (hq2 : q ≠ 2)
    (hB : padicValRat q (ratExpression m) < 1) :
    padicValRat q (ratExpression (m * q)) = padicValRat q (ratExpression m) - 1 := by
  have : Fact q.Prime := ⟨hq⟩
  have hm0 : 0 < m := Nat.zero_lt_of_lt hm
  have hn1 : 1 < m * q := by
    have : 2 * 2 ≤ m * q := Nat.mul_le_mul (Nat.succ_le_of_lt hm) hq.two_le
    omega
  have hTp : ratExpression m ≠ 0 := ne_of_gt (ratExpression_pos hm)
  have hTn : ratExpression (m * q) ≠ 0 := ne_of_gt (ratExpression_pos hn1)
  have hqne : (q : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hq.ne_zero
  have hA0 : (q : ℚ) * ratExpression (m * q) ≠ 0 := mul_ne_zero hqne hTn
  have hmul : padicValRat q ((q : ℚ) * ratExpression (m * q)) =
      1 + padicValRat q (ratExpression (m * q)) := by
    rw [padicValRat.mul hqne hTn, show padicValRat q (q : ℚ) = 1 from padicValRat.self hq.one_lt]
  by_cases hD0 : (q : ℚ) * ratExpression (m * q) - ratExpression m = 0
  · have hAeq : (q : ℚ) * ratExpression (m * q) = ratExpression m := sub_eq_zero.mp hD0
    linarith [hAeq ▸ hmul]
  · have hDval := one_le_padicValRat_q_mul_sub_of_ne hm0 hq hq2 hD0
    have hA : (q : ℚ) * ratExpression (m * q) =
        ((q : ℚ) * ratExpression (m * q) - ratExpression m) + ratExpression m := by
      ring
    have hlt : padicValRat q (ratExpression m) <
        padicValRat q ((q : ℚ) * ratExpression (m * q) - ratExpression m) :=
      lt_of_lt_of_le hB hDval
    have hsum0 : ((q : ℚ) * ratExpression (m * q) - ratExpression m) + ratExpression m ≠ 0 := by
      rwa [← hA]
    have hAval : padicValRat q ((q : ℚ) * ratExpression (m * q)) =
        padicValRat q (ratExpression m) := by
      rw [hA, add_comm]
      exact padicValRat.add_eq_of_lt (p := q)
        (by rwa [add_comm] at hsum0) hTp hD0 hlt
    linarith [hAval, hmul]

lemma not_n_sq_dvd_num_of_val_pred {m q : ℕ}
    (hm : 1 < m) (hq : q.Prime) (hq2 : q ≠ 2)
    (hn : 3 < m * q)
    (hB : padicValRat q (ratExpression m) < 1) :
    ¬ (ratExpression (m * q)).num ≡ 0 [ZMOD ((m * q) ^ 2 : ℤ)] := by
  have : Fact q.Prime := ⟨hq⟩
  have hn0 : 0 < m * q := Nat.mul_pos (Nat.zero_lt_of_lt hm) hq.pos
  have hn1 : 1 < m * q := lt_trans (by decide : 1 < 3) hn
  have hT : ratExpression (m * q) ≠ 0 := ne_of_gt (ratExpression_pos hn1)
  have hval : padicValRat q (ratExpression (m * q)) =
      padicValRat q (ratExpression m) - 1 :=
    padicValRat_ratExpression_mul_of_val_lt_one hm hq hq2 hB
  have hlt : padicValRat q (ratExpression (m * q)) < 2 * padicValNat q (m * q) := by
    have : padicValRat q (ratExpression (m * q)) < 0 := by
      rw [hval]
      linarith
    have hnn : 0 ≤ (2 * padicValNat q (m * q) : ℤ) := by
      exact mul_nonneg (by decide) (Nat.cast_nonneg _)
    linarith
  exact not_n_sq_dvd_num_of_padicVal_lt hq (dvd_mul_left q m) hn0 hT hlt

lemma padicValRat_two_pow_div_eq_neg_padicValNat {q k : ℕ}
    (hq : q.Prime) (hq2 : q ≠ 2) (hk : 0 < k) :
    padicValRat q ((2 : ℚ) ^ k / k) = - padicValNat q k := by
  have : Fact q.Prime := ⟨hq⟩
  have hk0 : (k : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.pos_iff_ne_zero.mp hk)
  have h2 : (2 : ℚ) ^ k ≠ 0 := pow_ne_zero _ (by norm_num)
  rw [padicValRat.div h2 hk0, padicValRat_two_pow_eq_zero hq2, padicValRat.of_nat, zero_sub]

lemma eq_prime_of_dvd_lt_two_mul {p k : ℕ} (hp : p.Prime) (hk0 : 0 < k)
    (hkm : k < 2 * p) (hdvd : p ∣ k) : k = p := by
  obtain ⟨t, ht⟩ := hdvd
  have ht0 : 0 < t := by
    exact Nat.pos_of_mul_pos_left (ht ▸ hk0)
  have hlt : t < 2 := by
    have : p * t < p * 2 := by
      rw [← ht, mul_comm]
      simpa [mul_comm] using hkm
    exact (Nat.mul_lt_mul_left hp.pos).mp this
  have ht1 : t = 1 := by omega
  rw [ht, ht1, mul_one]

lemma mem_range_pred_of_le {p m : ℕ} (hp0 : 0 < p) (hpm : p ≤ m) :
    p - 1 ∈ range m :=
  mem_range.mpr (Nat.sub_one_lt_of_le hp0 hpm)

lemma ratExpression_split_prime_term {m p : ℕ} (hp0 : 0 < p) (hpm : p ≤ m) :
    ratExpression m =
      (-2 : ℚ) / m + (2 : ℚ) ^ p / p +
        ∑ i ∈ (range m).erase (p - 1), (2 : ℚ) ^ (i + 1) / (i + 1) := by
  have hm0 : 0 < m := Nat.lt_of_lt_of_le hp0 hpm
  have hmem := mem_range_pred_of_le hp0 hpm
  have hp1 : p - 1 + 1 = p := Nat.sub_add_cancel hp0
  have hden : ((p - 1 : ℕ) : ℚ) + 1 = p := by
    rw [Nat.cast_sub hp0, Nat.cast_one]
    ring
  rw [ratExpression_of_pos hm0, ← sum_erase_add (range m) _ hmem, hp1, hden]
  ring

lemma zero_le_padicValRat_sum {α : Type*} [DecidableEq α] {q : ℕ} [Fact q.Prime]
    {s : Finset α} (f : α → ℚ) (hf : ∀ i ∈ s, 0 ≤ padicValRat q (f i)) :
    0 ≤ padicValRat q (∑ i ∈ s, f i) := by
  by_cases hsum : ∑ i ∈ s, f i = 0
  · simp [hsum]
  · induction s using Finset.induction_on with
    | empty =>
      simp at hsum
    | insert a s ha ih =>
      rw [sum_insert ha] at hsum ⊢
      by_cases hrest : ∑ i ∈ s, f i = 0
      · simpa [hrest] using hf a (mem_insert_self _ _)
      · have h1 := hf a (mem_insert_self _ _)
        have h2 := ih (fun i hi => hf i (mem_insert_of_mem hi)) hrest
        exact le_trans (le_min h1 h2) (padicValRat.min_le_padicValRat_add (p := q) hsum)

/-- If `p ≤ m < 2p` and `p ∤ m`, then `k = p` is the unique multiple of `p` in `1..m`,
so `v_p(T(m)) = -1`. -/
lemma padicValRat_ratExpression_eq_neg_one_of_unique {m p : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) (hpm : p ≤ m) (hm : m < 2 * p) (hnd : ¬ p ∣ m)
    (hm1 : 1 < m) :
    padicValRat p (ratExpression m) = -1 := by
  have : Fact p.Prime := ⟨hp⟩
  have hp0 : 0 < p := hp.pos
  have hm0 : 0 < m := Nat.zero_lt_of_lt hm1
  have hT : ratExpression m ≠ 0 := ne_of_gt (ratExpression_pos hm1)
  have hsplit := ratExpression_split_prime_term hp0 hpm
  set R := (-2 : ℚ) / m +
      ∑ i ∈ (range m).erase (p - 1), (2 : ℚ) ^ (i + 1) / (i + 1)
  have hTR : ratExpression m = (2 : ℚ) ^ p / p + R := by
    simpa [R, add_assoc, add_left_comm] using hsplit
  have hterm : padicValRat p ((2 : ℚ) ^ p / p) = -1 := by
    rw [padicValRat_two_pow_div_eq_neg_padicValNat hp hp2 hp0, padicValNat_self]
    simp
  have hterm0 : (2 : ℚ) ^ p / p ≠ 0 := by
    refine div_ne_zero (pow_ne_zero _ (by norm_num)) ?_
    exact Nat.cast_ne_zero.mpr hp.ne_zero
  have hneg : padicValRat p ((-2 : ℚ) / m) = 0 := by
    have hmne : (m : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.pos_iff_ne_zero.mp hm0)
    have h2ne : (-2 : ℚ) ≠ 0 := by norm_num
    have h2val : padicValRat p (2 : ℚ) = 0 := by
      rw [show (2 : ℚ) = ((2 : ℕ) : ℚ) from rfl, padicValRat.of_nat]
      exact_mod_cast (padicValNat_primes hp2)
    have hmval : padicValRat p (m : ℚ) = 0 := by
      rw [padicValRat.of_nat]
      exact_mod_cast padicValNat.eq_zero_of_not_dvd hnd
    rw [padicValRat.div h2ne hmne, padicValRat.neg, h2val, hmval]
    simp
  have hrest : 0 ≤ padicValRat p
      (∑ i ∈ (range m).erase (p - 1), (2 : ℚ) ^ (i + 1) / (i + 1)) := by
    refine zero_le_padicValRat_sum _ ?_
    intro i hi
    have hi' : i ∈ range m := mem_of_mem_erase hi
    have hne : i + 1 ≠ p := by
      intro h
      have : i = p - 1 := by
        rw [← h, Nat.add_sub_cancel]
      exact (mem_erase.mp hi).1 this
    have hndk : ¬ p ∣ i + 1 := by
      intro hd
      have hk0 : 0 < i + 1 := Nat.succ_pos i
      have hlt : i + 1 < 2 * p :=
        lt_of_le_of_lt (Nat.succ_le_of_lt (mem_range.mp hi')) hm
      exact hne (eq_prime_of_dvd_lt_two_mul hp hk0 hlt hd)
    have : padicValRat p ((2 : ℚ) ^ (i + 1) / (i + 1 : ℕ)) = 0 := by
      rw [padicValRat_two_pow_div_eq_neg_padicValNat hp hp2 (Nat.succ_pos i)]
      simp [padicValNat.eq_zero_of_not_dvd hndk]
    simpa [Nat.cast_succ] using this.ge
  have hR : 0 ≤ padicValRat p R := by
    by_cases hsum : (-2 : ℚ) / m +
        ∑ i ∈ (range m).erase (p - 1), (2 : ℚ) ^ (i + 1) / (i + 1) = 0
    · simp [R, hsum]
    · exact le_trans (le_min hneg.ge hrest)
        (padicValRat.min_le_padicValRat_add (p := p) (by simpa [R] using hsum))
  by_cases hR0 : R = 0
  · simp [hTR, hR0, hterm]
  · have hlt : padicValRat p ((2 : ℚ) ^ p / p) < padicValRat p R := by
      rw [hterm]
      linarith
    have hsum0 : (2 : ℚ) ^ p / p + R ≠ 0 := by
      rwa [← hTR]
    rw [hTR, padicValRat.add_eq_of_lt hsum0 hterm0 hR0 hlt, hterm]

/-- Converse at `n = m p` when `p` is an odd prime, `p ≤ m < 2p`, and `p ∤ m`. -/
lemma not_n_sq_dvd_num_of_unique_prime_mul {m p : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) (hpm : p ≤ m) (hm : m < 2 * p)
    (hnd : ¬ p ∣ m) (hm1 : 1 < m) (hn : 3 < m * p) :
    ¬ (ratExpression (m * p)).num ≡ 0 [ZMOD ((m * p) ^ 2 : ℤ)] := by
  have hB : padicValRat p (ratExpression m) < 1 := by
    have := padicValRat_ratExpression_eq_neg_one_of_unique hp hp2 hpm hm hnd hm1
    linarith
  exact not_n_sq_dvd_num_of_val_pred hm1 hp hp2 hn hB

/-- If `v_q(T(m)) ≠ v_q(q T(mq) - T(m))`, then
`v_q(T(mq)) = min(v_q(T(m)), v_q(q T(mq) - T(m))) - 1`. -/
lemma padicValRat_ratExpression_mul_eq_min_sub_one {m q : ℕ}
    (hm : 1 < m) (hq : q.Prime)
    (hD : (q : ℚ) * ratExpression (m * q) - ratExpression m ≠ 0)
    (hne : padicValRat q (ratExpression m) ≠
        padicValRat q ((q : ℚ) * ratExpression (m * q) - ratExpression m)) :
    padicValRat q (ratExpression (m * q)) =
      min (padicValRat q (ratExpression m))
          (padicValRat q ((q : ℚ) * ratExpression (m * q) - ratExpression m)) - 1 := by
  have : Fact q.Prime := ⟨hq⟩
  have hn1 : 1 < m * q := by
    have : 2 * 2 ≤ m * q := Nat.mul_le_mul (Nat.succ_le_of_lt hm) hq.two_le
    omega
  have hTp : ratExpression m ≠ 0 := ne_of_gt (ratExpression_pos hm)
  have hTn : ratExpression (m * q) ≠ 0 := ne_of_gt (ratExpression_pos hn1)
  have hqne : (q : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hq.ne_zero
  set A := (q : ℚ) * ratExpression (m * q)
  set B := ratExpression m
  set D := (q : ℚ) * ratExpression (m * q) - ratExpression m
  have hA : A = D + B := by
    simp [A, B, D]
  have hAval : padicValRat q A = min (padicValRat q D) (padicValRat q B) := by
    rw [hA]
    exact padicValRat.add_eq_min (p := q) (hA ▸ mul_ne_zero hqne hTn) hD hTp hne.symm
  have hmul : padicValRat q A = 1 + padicValRat q (ratExpression (m * q)) := by
    simp [A]
    rw [padicValRat.mul hqne hTn, show padicValRat q (q : ℚ) = 1 from padicValRat.self hq.one_lt]
  rw [min_comm] at hAval
  linarith [hAval, hmul]

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
#print axioms OeisA108866.padicValRat_ratExpression_mul_of_val_lt_one
#print axioms OeisA108866.not_n_sq_dvd_num_of_val_pred
#print axioms OeisA108866.padicValRat_ratExpression_eq_neg_one_of_unique
#print axioms OeisA108866.not_n_sq_dvd_num_of_unique_prime_mul
#print axioms OeisA108866.padicValRat_ratExpression_mul_eq_min_sub_one

/-- Integer `m! T(m)` after clearing denominators. -/
def factClear (m : ℕ) : ℤ :=
  -2 * ((m - 1).factorial : ℤ) +
    ∑ i ∈ range m, (2 : ℤ) ^ (i + 1) * (m.factorial / (i + 1) : ℕ)

lemma nat_cast_div_factorial {m k : ℕ} (hk : 0 < k) (hkm : k ≤ m) :
    ((m.factorial / k : ℕ) : ℚ) = (m.factorial : ℚ) / k := by
  have hdvd : k ∣ m.factorial := Nat.dvd_factorial hk hkm
  have hk0 : (k : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.pos_iff_ne_zero.mp hk)
  have := congrArg (fun n : ℕ => (n : ℚ)) (Nat.div_mul_cancel hdvd)
  rw [Nat.cast_mul] at this
  exact (eq_div_iff hk0).2 (by simpa [mul_comm] using this)

lemma factClear_eq {m : ℕ} (hm : 0 < m) :
    (factClear m : ℚ) = m.factorial * ratExpression m := by
  have hmne : (m : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.pos_iff_ne_zero.mp hm)
  have hsucc : (m.factorial : ℚ) = m * (m - 1).factorial := by
    rw [← Nat.mul_factorial_pred (Nat.pos_iff_ne_zero.mp hm), Nat.cast_mul]
  simp only [factClear, Int.cast_add, Int.cast_mul, Int.cast_neg, Int.cast_natCast,
    Int.cast_ofNat, Int.cast_sum, Int.cast_pow]
  rw [ratExpression_of_pos hm, mul_add]
  have hneg : (m.factorial : ℚ) * ((-2 : ℚ) / m) = -2 * (m - 1).factorial := by
    rw [hsucc]
    field_simp [hmne]
  rw [hneg, mul_sum]
  refine congrArg (fun t => -2 * (↑(m - 1).factorial : ℚ) + t) ?_
  refine sum_congr rfl fun i hi => ?_
  have hk : 0 < i + 1 := Nat.succ_pos i
  have hkm : i + 1 ≤ m := Nat.succ_le_of_lt (mem_range.mp hi)
  have hdiv := nat_cast_div_factorial hk hkm
  simp [Nat.cast_succ, hdiv, div_eq_mul_inv, mul_left_comm]

lemma padicValNat_factorial_eq_div {m p : ℕ} [Fact p.Prime]
    (hmp : m < p ^ 2) : padicValNat p m.factorial = m / p := by
  have hp := ‹Fact p.Prime›.out
  rw [← padicValNat_mul_div_factorial m, padicValNat_factorial_mul]
  have hlt : m / p < p := Nat.div_lt_of_lt_mul (by simpa [pow_two, mul_comm] using hmp)
  have hnd : ¬ p ∣ (m / p).factorial := by
    intro h
    exact hlt.not_ge ((hp.dvd_factorial).1 h)
  rw [padicValNat.eq_zero_of_not_dvd hnd, zero_add]

/-- Truncated base-2 harmonic sum `\sum_{j=1}^r 2^j/j` in `ZMod p`. -/
def twoHarmonicTrunc (r p : ℕ) : ZMod p :=
  ∑ j ∈ range r, (2 : ZMod p) ^ (j + 1) * (j + 1 : ZMod p)⁻¹

lemma twoHarmonicTrunc_two_ne_zero {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) :
    twoHarmonicTrunc 2 p ≠ 0 := by
  have hp : Nat.Prime p := ‹Fact p.Prime›.out
  have h2 : (2 : ZMod p) ≠ 0 := by
    intro h
    have : p ∣ 2 := (ZMod.natCast_eq_zero_iff _ _).1 (by simpa using h)
    have : p = 1 ∨ p = 2 := (Nat.dvd_prime Nat.prime_two).mp this
    exact this.elim (fun h1 => hp.ne_one h1) hp2
  have hinv : (2 : ZMod p) * (2 : ZMod p)⁻¹ = 1 := mul_inv_cancel₀ h2
  have hs : twoHarmonicTrunc 2 p =
      (2 : ZMod p) * (1 : ZMod p)⁻¹ + (2 : ZMod p) ^ 2 * (2 : ZMod p)⁻¹ := by
    simp [twoHarmonicTrunc, sum_range_succ, pow_one]
    exact Or.inl (by ring)
  rw [hs, inv_one, mul_one, pow_two, mul_assoc, hinv, mul_one]
  have h4z : (2 : ZMod p) + 2 = 4 := by ring
  rw [h4z]
  intro h0
  have hd : p ∣ 4 := (ZMod.natCast_eq_zero_iff _ _).1 h0
  have hpow : p ∣ 2 ^ 2 := by simpa using hd
  have : p ∣ 2 := hp.dvd_of_dvd_pow hpow
  have : p = 1 ∨ p = 2 := (Nat.dvd_prime Nat.prime_two).mp this
  exact this.elim (fun h1 => hp.ne_one h1) hp2

#print axioms OeisA108866.factClear_eq
#print axioms OeisA108866.padicValNat_factorial_eq_div
#print axioms OeisA108866.twoHarmonicTrunc_two_ne_zero

lemma twoHarmonicTrunc_one_ne_zero {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) :
    twoHarmonicTrunc 1 p ≠ 0 := by
  have hp : Nat.Prime p := ‹Fact p.Prime›.out
  have h2 : (2 : ZMod p) ≠ 0 := by
    intro h
    have : p ∣ 2 := (ZMod.natCast_eq_zero_iff _ _).1 (by simpa using h)
    have : p = 1 ∨ p = 2 := (Nat.dvd_prime Nat.prime_two).mp this
    exact this.elim (fun h1 => hp.ne_one h1) hp2
  simp [twoHarmonicTrunc]
  exact h2

#print axioms OeisA108866.twoHarmonicTrunc_one_ne_zero

lemma padicValRat_ratExpression_factClear {m p : ℕ} [Fact p.Prime]
    (hm1 : 1 < m) :
    padicValRat p (ratExpression m) =
      padicValInt p (factClear m) - padicValNat p m.factorial := by
  have hT : ratExpression m ≠ 0 := ne_of_gt (ratExpression_pos hm1)
  have hm0 : 0 < m := Nat.zero_lt_of_lt hm1
  have hfac : (m.factorial : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero m)
  have heq := factClear_eq hm0
  have hmul : padicValRat p (factClear m : ℚ) =
      padicValRat p (m.factorial : ℚ) + padicValRat p (ratExpression m) := by
    rw [heq, padicValRat.mul hfac hT]
  rw [padicValRat.of_int, padicValRat.of_nat] at hmul
  linarith

#print axioms OeisA108866.padicValRat_ratExpression_factClear

lemma sum_filter_dvd_succ_div {m q : ℕ} (hq0 : 0 < q) (f : ℕ → ℚ) :
    ∑ i ∈ (range m).filter (fun i => q ∣ i + 1), f (i + 1) =
      ∑ j ∈ range (m / q), f ((j + 1) * q) := by
  refine Eq.symm (sum_nbij' (fun j => (j + 1) * q - 1) (fun i => (i + 1) / q - 1)
    ?hi ?hj ?left ?right ?heq)
  · intro j hj
    have hj1 : 0 < (j + 1) * q := Nat.mul_pos (Nat.succ_pos j) hq0
    have hle : (j + 1) * q ≤ m := by
      have : j + 1 ≤ m / q := Nat.succ_le_of_lt (mem_range.mp hj)
      exact le_trans (Nat.mul_le_mul_right q this) (by
        rw [mul_comm]
        exact Nat.mul_div_le m q)
    have hsucc : (j + 1) * q - 1 + 1 = (j + 1) * q := Nat.sub_add_cancel hj1
    have hmem : (j + 1) * q - 1 < m :=
      Nat.lt_of_succ_le (by
        rw [Nat.succ_eq_add_one, Nat.sub_add_cancel hj1]
        exact hle)
    refine mem_filter.mpr ⟨mem_range.mpr hmem, ?_⟩
    rw [hsucc, mul_comm]
    exact Nat.dvd_mul_right q (j + 1)
  · intro i hi
    have hi' := mem_filter.mp hi
    have hdvd : q ∣ i + 1 := hi'.2
    have hpos : 0 < (i + 1) / q :=
      Nat.div_pos (Nat.le_of_dvd (Nat.succ_pos i) hdvd) hq0
    have hle : (i + 1) / q ≤ m / q :=
      Nat.div_le_div_right (Nat.succ_le_of_lt (mem_range.mp hi'.1))
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

lemma sum_pow_muls_eq_div {m p e : ℕ} (hp0 : 0 < p) :
    ∑ i ∈ (range m).filter (fun i => p ^ e ∣ i + 1),
        (2 : ℚ) ^ (i + 1) / (i + 1) =
      (∑ j ∈ range (m / p ^ e), (2 : ℚ) ^ ((j + 1) * p ^ e) / (j + 1)) /
        (p : ℚ) ^ e := by
  have hq0 : 0 < p ^ e := Nat.pow_pos hp0
  have hne : (p : ℚ) ^ e ≠ 0 :=
    pow_ne_zero _ (Nat.cast_ne_zero.mpr (Nat.pos_iff_ne_zero.mp hp0))
  have hsum : ∑ i ∈ (range m).filter (fun i => p ^ e ∣ i + 1),
      (2 : ℚ) ^ (i + 1) / (i + 1) =
    ∑ i ∈ (range m).filter (fun i => p ^ e ∣ i + 1),
      (2 : ℚ) ^ (i + 1) / (i + 1 : ℕ) :=
    sum_congr rfl fun i _ => by simp [Nat.cast_succ]
  rw [hsum, eq_div_iff hne, sum_filter_dvd_succ_div hq0 (fun k => (2 : ℚ) ^ k / k),
    mul_comm, mul_sum]
  refine sum_congr rfl fun j _ => ?_
  have hj0 : ((j + 1 : ℕ) : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.succ_ne_zero j)
  field_simp [hj0, hne]
  simp [Nat.cast_succ, Nat.cast_pow, Nat.cast_mul, mul_comm]

/-- Integer `r! ∑_{j=1}^r 2^{j e} / j`. -/
def twoHarmonicClear (r e : ℕ) : ℤ :=
  ∑ j ∈ range r, (2 : ℤ) ^ ((j + 1) * e) * (r.factorial / (j + 1) : ℕ)

lemma twoHarmonicClear_eq (r e : ℕ) :
    (twoHarmonicClear r e : ℚ) =
      (r.factorial : ℚ) * ∑ j ∈ range r, (2 : ℚ) ^ ((j + 1) * e) / (j + 1) := by
  simp only [twoHarmonicClear, Int.cast_sum, Int.cast_mul, Int.cast_pow, Int.cast_ofNat,
    Int.cast_natCast]
  rw [mul_sum]
  refine sum_congr rfl fun j hj => ?_
  have hk : 0 < j + 1 := Nat.succ_pos j
  have hkm : j + 1 ≤ r := Nat.succ_le_of_lt (mem_range.mp hj)
  have hdiv := nat_cast_div_factorial hk hkm
  simp [Nat.cast_succ, hdiv, div_eq_mul_inv, mul_left_comm]

lemma nat_cast_div_zmod {r k p : ℕ} [Fact p.Prime]
    (hk : 0 < k) (hkr : k ≤ r) (hr : r < p) :
    ((r.factorial / k : ℕ) : ZMod p) =
      (r.factorial : ZMod p) * (k : ZMod p)⁻¹ := by
  have hdvd : k ∣ r.factorial := Nat.dvd_factorial hk hkr
  have hk0 : (k : ZMod p) ≠ 0 := by
    intro h
    have hp := ‹Fact p.Prime›.out
    have : p ∣ k := (ZMod.natCast_eq_zero_iff _ _).1 h
    exact (Nat.le_of_dvd hk this).not_gt (lt_of_le_of_lt hkr hr)
  have hmul : ((r.factorial / k : ℕ) : ZMod p) * k = r.factorial := by
    rw [← Nat.cast_mul, Nat.div_mul_cancel hdvd]
  exact (eq_mul_inv_iff_mul_eq₀ hk0).mpr hmul

lemma natCast_factorial_ne_zero {r p : ℕ} [Fact p.Prime] (hr : r < p) :
    (r.factorial : ZMod p) ≠ 0 := by
  intro h
  have hp := ‹Fact p.Prime›.out
  have : p ∣ r.factorial := (ZMod.natCast_eq_zero_iff _ _).1 h
  exact hr.not_ge (hp.dvd_factorial.1 this)

lemma twoHarmonicClear_mod {r p e : ℕ} [Fact p.Prime] (hr : r < p) :
    (twoHarmonicClear r (p ^ e) : ZMod p) =
      (r.factorial : ZMod p) * twoHarmonicTrunc r p := by
  unfold twoHarmonicClear twoHarmonicTrunc
  rw [Int.cast_sum, mul_sum]
  refine sum_congr rfl fun j hj => ?_
  have hk : 0 < j + 1 := Nat.succ_pos j
  have hkm : j + 1 ≤ r := Nat.succ_le_of_lt (mem_range.mp hj)
  have hdiv := nat_cast_div_zmod hk hkm hr
  have hpow : ((2 : ℤ) : ZMod p) ^ ((j + 1) * p ^ e) = (2 : ZMod p) ^ (j + 1) := by
    have h2 : ((2 : ℤ) : ZMod p) = (2 : ZMod p) := by simp
    rw [h2, mul_comm (j + 1), pow_mul, ZMod.pow_card_pow]
  rw [Int.cast_mul, Int.cast_pow, Int.cast_natCast, hdiv, hpow]
  simp [Nat.cast_succ]
  ring

lemma padicValRat_twoHarmonic_pow_eq_zero {r p e : ℕ} [Fact p.Prime]
    (hr : r < p) (hL : twoHarmonicTrunc r p ≠ 0) :
    padicValRat p (∑ j ∈ range r, (2 : ℚ) ^ ((j + 1) * p ^ e) / (j + 1)) = 0 := by
  have hp := ‹Fact p.Prime›.out
  set H := ∑ j ∈ range r, (2 : ℚ) ^ ((j + 1) * p ^ e) / (j + 1)
  have hC := twoHarmonicClear_eq r (p ^ e)
  have hfac : (r.factorial : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero r)
  have hCmod : (twoHarmonicClear r (p ^ e) : ZMod p) ≠ 0 := by
    rw [twoHarmonicClear_mod hr]
    exact mul_ne_zero (natCast_factorial_ne_zero hr) hL
  have hCne : twoHarmonicClear r (p ^ e) ≠ 0 := by
    intro h
    exact hCmod (by simp [h])
  have hH : H ≠ 0 := by
    intro h0
    have : (twoHarmonicClear r (p ^ e) : ℚ) = 0 := by
      simp [H] at h0
      rw [hC, h0, mul_zero]
    exact hCne (Int.cast_eq_zero.mp this)
  have hfacval : padicValRat p (r.factorial : ℚ) = 0 := by
    rw [padicValRat.of_nat]
    exact_mod_cast padicValNat.eq_zero_of_not_dvd (fun h =>
      hr.not_ge (hp.dvd_factorial.1 h))
  have hCval : padicValRat p (twoHarmonicClear r (p ^ e) : ℚ) = 0 := by
    rw [padicValRat.of_int]
    have hnd : ¬ (p : ℤ) ∣ twoHarmonicClear r (p ^ e) := by
      intro hd
      exact hCmod ((ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mpr hd)
    exact_mod_cast padicValInt.eq_zero_of_not_dvd hnd
  have hmul : padicValRat p (twoHarmonicClear r (p ^ e) : ℚ) =
      padicValRat p (r.factorial : ℚ) + padicValRat p H := by
    rw [hC, padicValRat.mul hfac hH]
  linarith [hCval, hfacval, hmul]

lemma le_padicValRat_sum {α : Type*} [DecidableEq α] {q : ℕ} [Fact q.Prime]
    {s : Finset α} (f : α → ℚ) {n : ℤ} (hn : n ≤ 0)
    (hf : ∀ i ∈ s, n ≤ padicValRat q (f i)) :
    n ≤ padicValRat q (∑ i ∈ s, f i) := by
  by_cases hsum : ∑ i ∈ s, f i = 0
  · simpa [hsum] using hn
  · induction s using Finset.induction_on with
    | empty =>
      simp at hsum
    | insert a s ha ih =>
      rw [sum_insert ha] at hsum ⊢
      by_cases hrest : ∑ i ∈ s, f i = 0
      · simpa [hrest] using hf a (mem_insert_self _ _)
      · have h1 := hf a (mem_insert_self _ _)
        have h2 := ih (fun i hi => hf i (mem_insert_of_mem hi)) hrest
        exact le_trans (le_min h1 h2) (padicValRat.min_le_padicValRat_add (p := q) hsum)

lemma ratExpression_eq_pow_muls_add {m p e : ℕ} (hm : 0 < m) :
    ratExpression m =
      (-2 : ℚ) / m +
        ∑ i ∈ (range m).filter (fun i => p ^ e ∣ i + 1),
          (2 : ℚ) ^ (i + 1) / (i + 1) +
        ∑ i ∈ (range m).filter (fun i => ¬ p ^ e ∣ i + 1),
          (2 : ℚ) ^ (i + 1) / (i + 1) := by
  rw [ratExpression_of_pos hm, add_assoc,
    ← sum_filter_add_sum_filter_not (range m) (fun i => p ^ e ∣ i + 1)]

/-- If `p^e ≤ m < p^{e+1}`, `p ∤ m`, and `L(m/p^e) ≠ 0` in `𝔽_p`, then `v_p(T(m)) = -e`. -/
lemma padicValRat_ratExpression_eq_neg_pow_of_trunc {m p e : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) (he : 0 < e) (hpe : p ^ e ≤ m)
    (hm : m < p ^ (e + 1)) (hnd : ¬ p ∣ m) :
    twoHarmonicTrunc (m / p ^ e) p ≠ 0 →
      padicValRat p (ratExpression m) = -e := by
  intro hL
  have : Fact p.Prime := ⟨hp⟩
  have hp0 : 0 < p := hp.pos
  have hm1 : 1 < m :=
    lt_of_lt_of_le hp.one_lt (le_trans (Nat.le_self_pow (Nat.pos_iff_ne_zero.mp he) p) hpe)
  have hm0 : 0 < m := Nat.zero_lt_of_lt hm1
  have hT : ratExpression m ≠ 0 := ne_of_gt (ratExpression_pos hm1)
  have hr : m / p ^ e < p :=
    Nat.div_lt_of_lt_mul (by simpa [pow_succ, mul_comm] using hm)
  have hsplit := ratExpression_eq_pow_muls_add (p := p) (e := e) hm0
  set S := ∑ i ∈ (range m).filter (fun i => p ^ e ∣ i + 1),
      (2 : ℚ) ^ (i + 1) / (i + 1)
  set R := (-2 : ℚ) / m +
      ∑ i ∈ (range m).filter (fun i => ¬ p ^ e ∣ i + 1),
        (2 : ℚ) ^ (i + 1) / (i + 1)
  have hTR : ratExpression m = S + R := by
    simpa [S, R, add_assoc, add_left_comm] using hsplit
  have hSeq : S =
      (∑ j ∈ range (m / p ^ e), (2 : ℚ) ^ ((j + 1) * p ^ e) / (j + 1)) /
        (p : ℚ) ^ e :=
    sum_pow_muls_eq_div hp0
  have hHval : padicValRat p
      (∑ j ∈ range (m / p ^ e), (2 : ℚ) ^ ((j + 1) * p ^ e) / (j + 1)) = 0 :=
    padicValRat_twoHarmonic_pow_eq_zero hr hL
  have hHne : ∑ j ∈ range (m / p ^ e), (2 : ℚ) ^ ((j + 1) * p ^ e) / (j + 1) ≠ 0 := by
    intro h
    have hC := twoHarmonicClear_eq (m / p ^ e) (p ^ e)
    have hCmod : (twoHarmonicClear (m / p ^ e) (p ^ e) : ZMod p) ≠ 0 := by
      rw [twoHarmonicClear_mod hr]
      exact mul_ne_zero (natCast_factorial_ne_zero hr) hL
    have : (twoHarmonicClear (m / p ^ e) (p ^ e) : ℚ) = 0 := by
      rw [hC, h, mul_zero]
    exact hCmod (by
      have : twoHarmonicClear (m / p ^ e) (p ^ e) = 0 := Int.cast_eq_zero.mp this
      simp [this])
  have hpeval : padicValRat p ((p : ℚ) ^ e) = e := by
    rw [← Nat.cast_pow, padicValRat.of_nat]
    exact_mod_cast padicValNat.prime_pow e
  have hSval : padicValRat p S = -e := by
    have hpe0 : (p : ℚ) ^ e ≠ 0 :=
      pow_ne_zero _ (Nat.cast_ne_zero.mpr hp.ne_zero)
    rw [hSeq, padicValRat.div hHne hpe0, hHval, hpeval, zero_sub]
  have hS0 : S ≠ 0 := by
    intro h
    have : padicValRat p S = 0 := by simp [h]
    rw [hSval] at this
    exact (neg_ne_zero.mpr (Nat.cast_ne_zero.mpr (Nat.pos_iff_ne_zero.mp he))) this
  have hneg : padicValRat p ((-2 : ℚ) / m) = 0 := by
    have hmne : (m : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.pos_iff_ne_zero.mp hm0)
    have h2ne : (-2 : ℚ) ≠ 0 := by norm_num
    have h2val : padicValRat p (2 : ℚ) = 0 := by
      rw [show (2 : ℚ) = ((2 : ℕ) : ℚ) from rfl, padicValRat.of_nat]
      exact_mod_cast (padicValNat_primes hp2)
    have hmval : padicValRat p (m : ℚ) = 0 := by
      rw [padicValRat.of_nat]
      exact_mod_cast padicValNat.eq_zero_of_not_dvd hnd
    rw [padicValRat.div h2ne hmne, padicValRat.neg, h2val, hmval]
    simp
  have he1 : 1 ≤ e := Nat.succ_le_of_lt he
  have hrest : (1 - (e : ℤ)) ≤ padicValRat p
      (∑ i ∈ (range m).filter (fun i => ¬ p ^ e ∣ i + 1),
        (2 : ℚ) ^ (i + 1) / (i + 1)) := by
    refine le_padicValRat_sum _ (sub_nonpos.mpr (Nat.one_le_cast.mpr he1)) ?_
    intro i hi
    have hi' := mem_filter.mp hi
    have hndk : ¬ p ^ e ∣ i + 1 := hi'.2
    have hk0 : 0 < i + 1 := Nat.succ_pos i
    have hvlt : padicValNat p (i + 1) < e := by
      rw [← not_le]
      intro hle
      exact hndk ((padicValNat_dvd_iff_le (Nat.succ_ne_zero i)).2 hle)
    have hval : padicValRat p ((2 : ℚ) ^ (i + 1) / (i + 1)) =
        - (padicValNat p (i + 1) : ℤ) := by
      simpa [Nat.cast_succ] using
        padicValRat_two_pow_div_eq_neg_padicValNat hp hp2 hk0
    have hv : (padicValNat p (i + 1) : ℤ) < e := Nat.cast_lt.mpr hvlt
    linarith [hval, hv]
  have hR : (1 - (e : ℤ)) ≤ padicValRat p R := by
    by_cases hsum : (-2 : ℚ) / m +
        ∑ i ∈ (range m).filter (fun i => ¬ p ^ e ∣ i + 1),
          (2 : ℚ) ^ (i + 1) / (i + 1) = 0
    · have : (1 - (e : ℤ)) ≤ 0 := sub_nonpos.mpr (Nat.one_le_cast.mpr he1)
      simpa [R, hsum] using this
    · have hneg' : (1 - (e : ℤ)) ≤ padicValRat p ((-2 : ℚ) / m) :=
        le_trans (sub_nonpos.mpr (Nat.one_le_cast.mpr he1)) hneg.ge
      exact le_trans (le_min hneg' hrest)
        (padicValRat.min_le_padicValRat_add (p := p) (by simpa [R] using hsum))
  by_cases hR0 : R = 0
  · simpa [hTR, hR0] using hSval
  · have hlt : padicValRat p S < padicValRat p R := by
      rw [hSval]
      linarith
    have hsum0 : S + R ≠ 0 := by
      rwa [← hTR]
    rw [hTR, padicValRat.add_eq_of_lt hsum0 hS0 hR0 hlt, hSval]

lemma not_n_sq_dvd_num_of_trunc {m p e : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) (he : 0 < e) (hpe : p ^ e ≤ m)
    (hm : m < p ^ (e + 1)) (hnd : ¬ p ∣ m) (hn : 3 < m * p)
    (hL : twoHarmonicTrunc (m / p ^ e) p ≠ 0) :
    ¬ (ratExpression (m * p)).num ≡ 0 [ZMOD ((m * p) ^ 2 : ℤ)] := by
  have hm1 : 1 < m :=
    lt_of_lt_of_le hp.one_lt (le_trans (Nat.le_self_pow (Nat.pos_iff_ne_zero.mp he) p) hpe)
  have hB : padicValRat p (ratExpression m) < 1 := by
    have := padicValRat_ratExpression_eq_neg_pow_of_trunc hp hp2 he hpe hm hnd hL
    linarith
  exact not_n_sq_dvd_num_of_val_pred hm1 hp hp2 hn hB

lemma padicValRat_ratExpression_eq_neg_log_of_trunc {m p : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) (hpm : p ≤ m) (hnd : ¬ p ∣ m)
    (hL : twoHarmonicTrunc (m / p ^ Nat.log p m) p ≠ 0) :
    padicValRat p (ratExpression m) = - Nat.log p m :=
  padicValRat_ratExpression_eq_neg_pow_of_trunc hp hp2
    (Nat.log_pos hp.one_lt hpm)
    (Nat.pow_log_le_self p (Nat.pos_iff_ne_zero.mp (Nat.lt_of_lt_of_le hp.pos hpm)))
    (Nat.lt_pow_succ_log_self hp.one_lt m) hnd hL

lemma not_n_sq_dvd_num_of_log {m p : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) (hpm : p ≤ m) (hnd : ¬ p ∣ m)
    (hn : 3 < m * p)
    (hL : twoHarmonicTrunc (m / p ^ Nat.log p m) p ≠ 0) :
    ¬ (ratExpression (m * p)).num ≡ 0 [ZMOD ((m * p) ^ 2 : ℤ)] := by
  have hm1 : 1 < m := lt_of_lt_of_le hp.one_lt hpm
  have hB : padicValRat p (ratExpression m) < 1 := by
    have := padicValRat_ratExpression_eq_neg_log_of_trunc hp hp2 hpm hnd hL
    have : 0 < Nat.log p m := Nat.log_pos hp.one_lt hpm
    linarith
  exact not_n_sq_dvd_num_of_val_pred hm1 hp hp2 hn hB

lemma padicValRat_ratExpression_eq_neg_one_of_two_mul {m p : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) (h2 : 2 * p ≤ m) (h3 : m < 3 * p)
    (hnd : ¬ p ∣ m) :
    padicValRat p (ratExpression m) = -1 := by
  have : Fact p.Prime := ⟨hp⟩
  have he : 0 < (1 : ℕ) := Nat.succ_pos 0
  have hpe : p ^ 1 ≤ m := by
    rw [pow_one]
    exact le_trans (Nat.le_mul_of_pos_left p two_pos) h2
  have hmp : m < p ^ (1 + 1) := by
    have hp3 : 3 ≤ p := by
      have : 2 ≤ p := hp.two_le
      omega
    have : 3 * p ≤ p * p := Nat.mul_le_mul_right p hp3
    have : m < p * p := lt_of_lt_of_le h3 this
    simpa [pow_succ, pow_one] using this
  have hr : m / p ^ 1 = 2 := by
    rw [pow_one]
    exact Nat.div_eq_of_lt_le h2 h3
  have hL : twoHarmonicTrunc (m / p ^ 1) p ≠ 0 := by
    rw [hr]
    exact twoHarmonicTrunc_two_ne_zero hp2
  simpa using
    padicValRat_ratExpression_eq_neg_pow_of_trunc hp hp2 he (by simpa using hpe) hmp hnd hL

lemma not_n_sq_dvd_num_of_two_mul {m p : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) (h2 : 2 * p ≤ m) (h3 : m < 3 * p)
    (hnd : ¬ p ∣ m) (hn : 3 < m * p) :
    ¬ (ratExpression (m * p)).num ≡ 0 [ZMOD ((m * p) ^ 2 : ℤ)] := by
  have hm1 : 1 < m :=
    lt_of_lt_of_le hp.one_lt (le_trans (Nat.le_mul_of_pos_left p two_pos) h2)
  have hB : padicValRat p (ratExpression m) < 1 := by
    have := padicValRat_ratExpression_eq_neg_one_of_two_mul hp hp2 h2 h3 hnd
    linarith
  exact not_n_sq_dvd_num_of_val_pred hm1 hp hp2 hn hB

lemma not_n_sq_dvd_num_of_prime_factor {m p : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) (hm1 : 1 < m) (hn : 3 < m * p)
    (h : (m < p ∧ ¬ p ∣ (ratExpression m).num.natAbs) ∨
      (p ≤ m ∧ ¬ p ∣ m ∧
        twoHarmonicTrunc (m / p ^ Nat.log p m) p ≠ 0)) :
    ¬ (ratExpression (m * p)).num ≡ 0 [ZMOD ((m * p) ^ 2 : ℤ)] := by
  rcases h with ⟨hmq, hnum⟩ | ⟨hpm, hnd, hL⟩
  · exact not_n_sq_dvd_num_of_mul_odd_primes hm1 hp hmq hnum
  · exact not_n_sq_dvd_num_of_log hp hp2 hpm hnd hn hL

#print axioms OeisA108866.padicValRat_ratExpression_eq_neg_pow_of_trunc
#print axioms OeisA108866.not_n_sq_dvd_num_of_trunc
#print axioms OeisA108866.padicValRat_ratExpression_eq_neg_log_of_trunc
#print axioms OeisA108866.not_n_sq_dvd_num_of_log
#print axioms OeisA108866.padicValRat_ratExpression_eq_neg_one_of_two_mul
#print axioms OeisA108866.not_n_sq_dvd_num_of_two_mul
#print axioms OeisA108866.not_n_sq_dvd_num_of_prime_factor

lemma p_mul_ratExpression_sq_sub_pos {p : ℕ} (hp : p.Prime) :
    0 < (p : ℚ) * ratExpression (p * p) - ratExpression p := by
  have hm0 : 0 < p := hp.pos
  have hdiff := q_mul_ratExpression_sub_eq_fermat_add hm0 hm0
  have hF : 0 < ∑ j ∈ range p,
      ((2 : ℚ) ^ ((j + 1) * p) - (2 : ℚ) ^ (j + 1)) / (j + 1) :=
    fermat_sum_pos hp.one_lt hm0
  have hO : 0 < ∑ i ∈ (range (p * p)).filter (fun i => ¬ p ∣ i + 1),
      (p : ℚ) * ((2 : ℚ) ^ (i + 1) / (i + 1)) :=
    rest_sum_pos hm0 hp
  linarith [hdiff, hF, hO]

/-- If `v_p(T(p)) ≠ v_p(p T(p^2)-T(p))`, then
`v_p(T(p^2)) = min(v_p(T(p)), v_p(p T(p^2)-T(p))) - 1`. -/
lemma padicValRat_ratExpression_sq_eq_min_sub_one {p : ℕ} (hp : p.Prime)
    (hne : padicValRat p (ratExpression p) ≠
        padicValRat p ((p : ℚ) * ratExpression (p * p) - ratExpression p)) :
    padicValRat p (ratExpression (p * p)) =
      min (padicValRat p (ratExpression p))
          (padicValRat p ((p : ℚ) * ratExpression (p * p) - ratExpression p)) - 1 :=
  padicValRat_ratExpression_mul_eq_min_sub_one hp.one_lt hp
    (ne_of_gt (p_mul_ratExpression_sq_sub_pos hp)) hne

lemma ratExpression_nine : ratExpression 9 = (4714 : ℚ) / 35 := by
  rw [ratExpression_of_pos (by decide : 0 < 9)]
  norm_num

lemma ratExpression_nine_num : (ratExpression 9).num = 4714 := by
  rw [ratExpression_nine]
  have hcop : Nat.Coprime (4714 : ℤ).natAbs (35 : ℤ).natAbs := by decide
  have hb0 : (0 : ℤ) < 35 := by decide
  simpa using (Rat.num_div_eq_of_coprime hb0 hcop)

lemma not_n_sq_dvd_num_nine :
    ¬ (ratExpression 9).num ≡ 0 [ZMOD ((9 : ℕ) ^ 2 : ℤ)] := by
  rw [ratExpression_nine_num]
  decide

lemma ratExpression_twenty_five : ratExpression 25 = (187907123732870 : ℚ) / 66927861 := by
  rw [ratExpression_of_pos (by decide : 0 < 25)]
  norm_num

lemma ratExpression_twenty_five_num : (ratExpression 25).num = 187907123732870 := by
  rw [ratExpression_twenty_five]
  have hcop : Nat.Coprime (187907123732870 : ℤ).natAbs (66927861 : ℤ).natAbs := by decide
  have hb0 : (0 : ℤ) < 66927861 := by decide
  simpa using (Rat.num_div_eq_of_coprime hb0 hcop)

lemma not_n_sq_dvd_num_twenty_five :
    ¬ (ratExpression 25).num ≡ 0 [ZMOD ((25 : ℕ) ^ 2 : ℤ)] := by
  rw [ratExpression_twenty_five_num]
  decide

lemma ratExpression_twenty_seven : ratExpression 27 = (5777962561135174 : ℚ) / 557732175 := by
  rw [ratExpression_of_pos (by decide : 0 < 27)]
  norm_num

lemma ratExpression_twenty_seven_num : (ratExpression 27).num = 5777962561135174 := by
  rw [ratExpression_twenty_seven]
  have hcop : Nat.Coprime (5777962561135174 : ℤ).natAbs (557732175 : ℤ).natAbs := by decide
  have hb0 : (0 : ℤ) < 557732175 := by decide
  simpa using (Rat.num_div_eq_of_coprime hb0 hcop)

lemma not_n_sq_dvd_num_twenty_seven :
    ¬ (ratExpression 27).num ≡ 0 [ZMOD ((27 : ℕ) ^ 2 : ℤ)] := by
  rw [ratExpression_twenty_seven_num]
  decide

lemma ratExpression_forty_nine :
    ratExpression 49 = (46402816520579634557697354319514 : ℚ) / 1976431444034436675 := by
  rw [ratExpression_of_pos (by decide : 0 < 49)]
  norm_num

lemma ratExpression_forty_nine_num :
    (ratExpression 49).num = 46402816520579634557697354319514 := by
  rw [ratExpression_forty_nine]
  have hcop : Nat.Coprime (46402816520579634557697354319514 : ℤ).natAbs
      (1976431444034436675 : ℤ).natAbs := by decide
  have hb0 : (0 : ℤ) < 1976431444034436675 := by decide
  simpa using (Rat.num_div_eq_of_coprime hb0 hcop)

lemma not_n_sq_dvd_num_forty_nine :
    ¬ (ratExpression 49).num ≡ 0 [ZMOD ((49 : ℕ) ^ 2 : ℤ)] := by
  rw [ratExpression_forty_nine_num]
  decide

/- Unique-min valuation for powers of 3. -/

lemma pow_pred_eq_mul_add {p e i : ℕ} (hp0 : 0 < p) (hi : i ≤ e) :
    p ^ e - 1 = p ^ i * (p ^ (e - i) - 1) + (p ^ i - 1) := by
  have hpow : p ^ i * p ^ (e - i) = p ^ e := by
    rw [← pow_add, Nat.add_sub_cancel' hi]
  have h1i : 1 ≤ p ^ i := Nat.one_le_pow i p hp0
  have h1ei : 1 ≤ p ^ (e - i) := Nat.one_le_pow (e - i) p hp0
  have hmul_le : p ^ i ≤ p ^ i * p ^ (e - i) :=
    Nat.le_mul_of_pos_right _ (Nat.zero_lt_of_lt h1ei)
  calc
    p ^ e - 1 = p ^ i * p ^ (e - i) - 1 := by rw [hpow]
    _ = p ^ i * p ^ (e - i) - p ^ i + (p ^ i - 1) :=
      (Nat.sub_add_sub_cancel hmul_le h1i).symm
    _ = p ^ i * (p ^ (e - i) - 1) + (p ^ i - 1) := by rw [← Nat.mul_sub_one]

lemma pow_pred_div_pow {p e i : ℕ} (hp0 : 0 < p) (hi : i ≤ e) :
    (p ^ e - 1) / p ^ i = p ^ (e - i) - 1 := by
  have hp0i : 0 < p ^ i := pow_pos hp0 i
  have hlt : p ^ i - 1 < p ^ i := Nat.sub_lt hp0i (by decide)
  rw [pow_pred_eq_mul_add hp0 hi, Nat.mul_add_div hp0i, Nat.div_eq_of_lt hlt,
    add_zero]

lemma add_sub_add_of_le {a b c d : ℕ} (h1 : c ≤ a) (h2 : d ≤ b) :
    a + b - (c + d) = a - c + (b - d) := by omega

lemma add_mod_pow_pred {p e i k : ℕ} (hp0 : 0 < p) (hi : i ≤ e)
    (hk : k ≤ p ^ e - 1) :
    k % p ^ i + (p ^ e - 1 - k) % p ^ i = p ^ i - 1 := by
  have hp0i : 0 < p ^ i := pow_pos hp0 i
  have hdecomp := pow_pred_eq_mul_add hp0 hi
  set qd := k / p ^ i
  set rm := k % p ^ i
  have hk' : k = p ^ i * qd + rm := by
    simpa [qd, rm] using (Nat.div_add_mod k (p ^ i)).symm
  have hqd : qd ≤ p ^ (e - i) - 1 := by
    have h := Nat.div_le_div_right (c := p ^ i) hk
    simpa [qd, pow_pred_div_pow hp0 hi] using h
  have hrm : rm ≤ p ^ i - 1 := by
    simpa [rm] using Nat.le_sub_one_of_lt (Nat.mod_lt k hp0i)
  have hnk : p ^ e - 1 - k =
      p ^ i * (p ^ (e - i) - 1 - qd) + (p ^ i - 1 - rm) := by
    have hX : p ^ i * qd ≤ p ^ i * (p ^ (e - i) - 1) :=
      Nat.mul_le_mul_left _ hqd
    calc
      p ^ e - 1 - k =
          p ^ i * (p ^ (e - i) - 1) + (p ^ i - 1) - (p ^ i * qd + rm) := by
        rw [hdecomp, hk']
      _ = p ^ i * (p ^ (e - i) - 1) - p ^ i * qd + (p ^ i - 1 - rm) :=
        add_sub_add_of_le hX hrm
      _ = p ^ i * (p ^ (e - i) - 1 - qd) + (p ^ i - 1 - rm) := by
        rw [← Nat.mul_sub]
  have hB : p ^ i - 1 - rm < p ^ i :=
    lt_of_le_of_lt (Nat.sub_le _ _) (Nat.sub_lt hp0i (by decide))
  rw [hnk, Nat.mul_add_mod_self_left, Nat.mod_eq_of_lt hB]
  exact Nat.add_sub_of_le hrm

lemma padicValNat_choose_pow_pred {p e k : ℕ} [Fact p.Prime] (he : 0 < e)
    (hk : k ≤ p ^ e - 1) :
    padicValNat p ((p ^ e - 1).choose k) = 0 := by
  have hp := ‹Fact p.Prime›.out
  have hpe : 2 ≤ p ^ e := hp.two_le.trans (Nat.le_self_pow (Nat.pos_iff_ne_zero.mp he) p)
  have hne : p ^ e - 1 ≠ 0 := Nat.sub_ne_zero_of_lt (lt_of_lt_of_le (by decide : 1 < 2) hpe)
  have hnb : Nat.log p (p ^ e - 1) < e :=
    (Nat.log_lt_iff_lt_pow hp.one_lt hne).2 (Nat.sub_lt (pow_pos hp.pos e) (by decide))
  rw [padicValNat_choose hk hnb]
  refine Finset.card_eq_zero.mpr ?_
  refine Finset.filter_eq_empty_iff.mpr ?_
  intro i hi hle
  have hi' := Finset.mem_Ico.mp hi
  have heq := add_mod_pow_pred hp.pos (Nat.le_of_lt hi'.2) hk
  have hlt : p ^ i - 1 < p ^ i := Nat.sub_lt (pow_pos hp.pos i) (by decide)
  exact Nat.not_le_of_gt hlt (heq ▸ hle)

lemma oddInnerSum_eq_sum_filter_odd {n : ℕ} (hn1 : 1 < n) :
    ∑ i ∈ range (n - 1),
      (if Odd (i + 1) then ((n - 1).choose i : ℚ) / (i + 1 : ℚ) ^ 2 else 0) =
    ∑ r ∈ (range n).filter Odd,
      ((n - 1).choose (r - 1) : ℚ) / (r : ℚ) ^ 2 := by
  convert sum_reindex_odd (fun r => ((n - 1).choose (r - 1) : ℚ) / (r : ℚ) ^ 2) hn1 using 1
  refine sum_congr rfl fun i _hi => ?_
  by_cases hodd : Odd (i + 1)
  · simp [if_pos hodd, Nat.cast_succ]
  · simp [if_neg hodd]

lemma padicValRat_choose_div_sq {n p r : ℕ} [Fact p.Prime]
    (hr0 : 0 < r) (hrle : r ≤ n) :
    padicValRat p (((n - 1).choose (r - 1) : ℚ) / (r : ℚ) ^ 2) =
      (padicValNat p ((n - 1).choose (r - 1)) : ℤ) - 2 * padicValNat p r := by
  have hrne : (r : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.pos_iff_ne_zero.mp hr0)
  have hCle : r - 1 ≤ n - 1 := Nat.sub_le_sub_right hrle 1
  have hCne : ((n - 1).choose (r - 1) : ℚ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (Nat.choose_pos hCle).ne'
  have hpow : (r : ℚ) ^ 2 ≠ 0 := pow_ne_zero _ hrne
  rw [padicValRat.div hCne hpow, padicValRat.of_nat, padicValRat.pow, padicValRat.of_nat]
  norm_cast

lemma eq_three_pow_pred_of_odd_dvd {e r : ℕ} (he : 0 < e)
    (hr : r < 3 ^ e) (hodd : Odd r) (hd : 3 ^ (e - 1) ∣ r) :
    r = 3 ^ (e - 1) := by
  have hpos : 0 < 3 ^ (e - 1) := pow_pos (by decide) _
  have hrpos : 0 < r := Odd.pos hodd
  have hpow : 3 ^ e = 3 ^ (e - 1) * 3 := by
    rw [← pow_succ, Nat.sub_add_cancel he]
  have hdiv : r / 3 ^ (e - 1) < 3 := Nat.div_lt_of_lt_mul (hpow ▸ hr)
  have hrw : r = r / 3 ^ (e - 1) * 3 ^ (e - 1) := (Nat.div_mul_cancel hd).symm
  have ha0 : 0 < r / 3 ^ (e - 1) :=
    Nat.div_pos (Nat.le_of_dvd hrpos hd) hpos
  have ha : r / 3 ^ (e - 1) = 1 ∨ r / 3 ^ (e - 1) = 2 := by omega
  rcases ha with ha | ha
  · rw [hrw, ha, one_mul]
  · have heven : Even r := by
      rw [hrw, ha]
      exact even_two.mul_right _
    exact (Nat.not_odd_iff_even.2 heven).elim hodd

lemma padicValNat_le_sub_two_of_ne_three_pow {e r : ℕ} [Fact (Nat.Prime 3)]
    (he : 2 ≤ e) (hr : r < 3 ^ e) (hodd : Odd r) (hne : r ≠ 3 ^ (e - 1)) :
    padicValNat 3 r ≤ e - 2 := by
  have he0 : 0 < e := lt_of_lt_of_le (by decide : 0 < 2) he
  have hrne : r ≠ 0 := Nat.ne_of_gt (Odd.pos hodd)
  have hnd : ¬ 3 ^ (e - 1) ∣ r := fun hd =>
    hne (eq_three_pow_pred_of_odd_dvd he0 hr hodd hd)
  have : ¬ e - 1 ≤ padicValNat 3 r := by
    intro hle
    exact hnd ((padicValNat_dvd_iff_le hrne).2 hle)
  omega

lemma le_padicValRat_sum_of_ne_zero {α : Type*} [DecidableEq α] {q : ℕ} [Fact q.Prime]
    {s : Finset α} (f : α → ℚ) {n : ℤ}
    (hf : ∀ i ∈ s, n ≤ padicValRat q (f i)) (hsum : ∑ i ∈ s, f i ≠ 0) :
    n ≤ padicValRat q (∑ i ∈ s, f i) := by
  revert hf hsum
  induction s using Finset.induction_on with
  | empty =>
    intro _hf hsum
    simp at hsum
  | insert a s ha ih =>
    intro hf hsum
    rw [sum_insert ha] at hsum ⊢
    by_cases hrest : ∑ i ∈ s, f i = 0
    · simpa [hrest] using hf a (mem_insert_self _ _)
    · have h2 := ih (fun i hi => hf i (mem_insert_of_mem hi)) hrest
      exact le_trans (le_min (hf a (mem_insert_self _ _)) h2)
        (padicValRat.min_le_padicValRat_add (p := q) hsum)

lemma oddChooseTerm_pos {n r : ℕ} (hr0 : 0 < r) (hrle : r ≤ n) :
    0 < ((n - 1).choose (r - 1) : ℚ) / (r : ℚ) ^ 2 := by
  have hCle : r - 1 ≤ n - 1 := Nat.sub_le_sub_right hrle 1
  have hC : (0 : ℚ) < (n - 1).choose (r - 1) := Nat.cast_pos.mpr (Nat.choose_pos hCle)
  have hr : (0 : ℚ) < r := Nat.cast_pos.mpr hr0
  exact div_pos hC (pow_pos hr 2)

lemma padicValRat_inner_three_pow {e : ℕ} (he : 2 ≤ e) :
    padicValRat 3
      (∑ i ∈ range (3 ^ e - 1),
        if Odd (i + 1) then ((3 ^ e - 1).choose i : ℚ) / (i + 1 : ℚ) ^ 2 else 0) =
      - (2 : ℤ) * ((e : ℤ) - 1) := by
  have : Fact (Nat.Prime 3) := ⟨by decide⟩
  have he0 : 0 < e := lt_of_lt_of_le (by decide : 0 < 2) he
  have hn1 : 1 < 3 ^ e := Nat.one_lt_pow (Nat.pos_iff_ne_zero.mp he0) (by decide)
  have hpowsucc : 3 ^ e = 3 ^ (e - 1) * 3 := by
    rw [← pow_succ, Nat.sub_add_cancel he0]
  set n := 3 ^ e
  set r0 := 3 ^ (e - 1)
  have hr0pos : 0 < r0 := pow_pos (by decide) _
  have hr0lt : r0 < n := by
    rw [show n = r0 * 3 from hpowsucc]
    exact lt_mul_of_one_lt_right hr0pos (by decide : 1 < 3)
  have hodd0 : Odd r0 := Odd.pow (n := e - 1) (by decide : Odd 3)
  have hr0mem : r0 ∈ (range n).filter Odd :=
    mem_filter.mpr ⟨mem_range.mpr hr0lt, hodd0⟩
  have hsum := oddInnerSum_eq_sum_filter_odd (n := n) hn1
  simp [n] at hsum ⊢
  rw [hsum]
  have hC0 : padicValNat 3 ((n - 1).choose (r0 - 1)) = 0 := by
    have hk : r0 - 1 ≤ 3 ^ e - 1 := Nat.sub_le_sub_right (Nat.le_of_lt hr0lt) 1
    exact padicValNat_choose_pow_pred (p := 3) (e := e) he0 (by simpa [n] using hk)
  have hr0le : r0 ≤ n := Nat.le_of_lt hr0lt
  have hterm0 :
      padicValRat 3 (((n - 1).choose (r0 - 1) : ℚ) / (r0 : ℚ) ^ 2) =
        - (2 : ℤ) * ((e : ℤ) - 1) := by
    have hval := padicValRat_choose_div_sq (p := 3) hr0pos hr0le
    have hvpow : padicValNat 3 r0 = e - 1 := padicValNat.prime_pow (e - 1)
    rw [hval, hC0, hvpow, Nat.cast_sub (by omega : 1 ≤ e)]
    ring
  have hsplit :
      ∑ r ∈ (range n).filter Odd,
          ((n - 1).choose (r - 1) : ℚ) / (r : ℚ) ^ 2 =
        ((n - 1).choose (r0 - 1) : ℚ) / (r0 : ℚ) ^ 2 +
          ∑ r ∈ ((range n).filter Odd).erase r0,
            ((n - 1).choose (r - 1) : ℚ) / (r : ℚ) ^ 2 := by
    rw [← sum_erase_add _ _ hr0mem]
    abel
  have h1mem : 1 ∈ ((range n).filter Odd).erase r0 := by
    have hne1 : (1 : ℕ) ≠ r0 := by
      intro h
      have hlt : 1 < 3 ^ (e - 1) :=
        Nat.one_lt_pow (Nat.pos_iff_ne_zero.mp (Nat.sub_pos_of_lt he)) (by decide)
      exact hlt.ne' (by simpa [r0] using h.symm)
    exact mem_erase.mpr ⟨hne1, mem_filter.mpr ⟨mem_range.mpr hn1, by decide⟩⟩
  have hrest0 :
      ∑ r ∈ ((range n).filter Odd).erase r0,
          ((n - 1).choose (r - 1) : ℚ) / (r : ℚ) ^ 2 ≠ 0 := by
    refine ne_of_gt (sum_pos (fun r hr => ?_) ⟨1, h1mem⟩)
    have hr' := mem_erase.mp hr
    have hr'' := mem_filter.mp hr'.2
    exact oddChooseTerm_pos (Odd.pos hr''.2) (mem_range.mp hr''.1).le
  have htermne :
      ((n - 1).choose (r0 - 1) : ℚ) / (r0 : ℚ) ^ 2 ≠ 0 :=
    ne_of_gt (oddChooseTerm_pos hr0pos hr0le)
  have hrestval :
      - (2 : ℤ) * ((e : ℤ) - 2) ≤
        padicValRat 3
          (∑ r ∈ ((range n).filter Odd).erase r0,
            ((n - 1).choose (r - 1) : ℚ) / (r : ℚ) ^ 2) := by
    refine le_padicValRat_sum_of_ne_zero _ ?_ hrest0
    intro r hr
    have hr' := mem_erase.mp hr
    have hr'' := mem_filter.mp hr'.2
    have hlt : r < n := mem_range.mp hr''.1
    have hpos : 0 < r := Odd.pos hr''.2
    have hvr : padicValNat 3 r ≤ e - 2 :=
      padicValNat_le_sub_two_of_ne_three_pow he (by simpa [n] using hlt) hr''.2
        (by simpa [r0] using hr'.1)
    have hval := padicValRat_choose_div_sq (n := n) (p := 3) hpos hlt.le
    have hvC : (0 : ℤ) ≤ padicValNat 3 ((n - 1).choose (r - 1)) := Nat.cast_nonneg _
    have hvrZ : (padicValNat 3 r : ℤ) ≤ (e : ℤ) - 2 := by
      have h : (padicValNat 3 r : ℤ) ≤ ((e - 2 : ℕ) : ℤ) := Int.ofNat_le.mpr hvr
      rwa [Nat.cast_sub (by omega : 2 ≤ e)] at h
    rw [hval]
    linarith
  have hlt : padicValRat 3 (((n - 1).choose (r0 - 1) : ℚ) / (r0 : ℚ) ^ 2) <
      padicValRat 3
        (∑ r ∈ ((range n).filter Odd).erase r0,
          ((n - 1).choose (r - 1) : ℚ) / (r : ℚ) ^ 2) := by
    rw [hterm0]
    have : - (2 : ℤ) * ((e : ℤ) - 1) < - (2 : ℤ) * ((e : ℤ) - 2) := by
      have : (2 : ℤ) ≤ e := by exact_mod_cast he
      linarith
    exact lt_of_lt_of_le this hrestval
  have hsum0 :
      ((n - 1).choose (r0 - 1) : ℚ) / (r0 : ℚ) ^ 2 +
          ∑ r ∈ ((range n).filter Odd).erase r0,
            ((n - 1).choose (r - 1) : ℚ) / (r : ℚ) ^ 2 ≠ 0 :=
    ne_of_gt (add_pos_of_pos_of_nonneg (oddChooseTerm_pos hr0pos hr0le)
      (sum_nonneg fun r hr => le_of_lt (by
        have hr' := mem_erase.mp hr
        have hr'' := mem_filter.mp hr'.2
        exact oddChooseTerm_pos (Odd.pos hr''.2) (mem_range.mp hr''.1).le)))
  rw [hsplit, padicValRat.add_eq_of_lt hsum0 htermne hrest0 hlt, hterm0]
  ring

lemma padicValRat_ratExpression_three_pow {e : ℕ} (he : 2 ≤ e) :
    padicValRat 3 (ratExpression (3 ^ e)) = 2 - e := by
  have : Fact (Nat.Prime 3) := ⟨by decide⟩
  have hn : Odd (3 ^ e) := Odd.pow (n := e) (by decide : Odd 3)
  have hn1 : 1 < 3 ^ e :=
    Nat.one_lt_pow (Nat.pos_iff_ne_zero.mp (lt_of_lt_of_le (by decide : 0 < 2) he))
      (by decide)
  have hT := ratExpression_eq_two_mul_n_sum_choose_sq hn hn1
  have hS := padicValRat_inner_three_pow he
  have hSne :
      (∑ i ∈ range (3 ^ e - 1),
          (if Odd (i + 1) then ((3 ^ e - 1).choose i : ℚ) / (i + 1 : ℚ) ^ 2 else 0)) ≠ 0 := by
    intro h0
    have : padicValRat 3 (0 : ℚ) = - (2 : ℤ) * ((e : ℤ) - 1) := by simpa [h0] using hS
    have hneg : - (2 : ℤ) * ((e : ℤ) - 1) < 0 := by
      have : (2 : ℤ) ≤ e := by exact_mod_cast he
      linarith
    have : padicValRat 3 (0 : ℚ) = 0 := by simp
    linarith
  have h2ne : (2 : ℚ) ≠ 0 := by norm_num
  have hnne : ((3 ^ e : ℕ) : ℚ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (pow_ne_zero e (by decide : (3 : ℕ) ≠ 0))
  have h2val : padicValRat 3 (2 : ℚ) = 0 := by
    rw [show (2 : ℚ) = ((2 : ℕ) : ℚ) from rfl, padicValRat.of_nat]
    exact_mod_cast (padicValNat_primes (by decide : (3 : ℕ) ≠ 2))
  have hnval : padicValRat 3 ((3 ^ e : ℕ) : ℚ) = e := by
    rw [padicValRat.of_nat]
    exact_mod_cast padicValNat.prime_pow (p := 3) e
  have hprod : ratExpression (3 ^ e) =
      (2 : ℚ) * (3 ^ e : ℕ) *
        ∑ i ∈ range (3 ^ e - 1),
          if Odd (i + 1) then ((3 ^ e - 1).choose i : ℚ) / (i + 1 : ℚ) ^ 2 else 0 := by
    simpa using hT
  have hnumne : (2 : ℚ) * (3 ^ e : ℕ) *
      (∑ i ∈ range (3 ^ e - 1),
        if Odd (i + 1) then ((3 ^ e - 1).choose i : ℚ) / (i + 1 : ℚ) ^ 2 else 0) ≠ 0 :=
    mul_ne_zero (mul_ne_zero h2ne hnne) hSne
  rw [hprod, padicValRat.mul (mul_ne_zero h2ne hnne) hSne, padicValRat.mul h2ne hnne,
    h2val, hnval, hS]
  ring

/-- For `e ≥ 2`, `(3^e)^2` does not divide the reduced numerator of `T(3^e)`. -/
theorem not_n_sq_dvd_num_of_three_pow {e : ℕ} (he : 2 ≤ e) :
    ¬ (ratExpression (3 ^ e)).num ≡ 0 [ZMOD ((3 ^ e) ^ 2 : ℤ)] := by
  have hp : Nat.Prime 3 := by decide
  have : Fact (Nat.Prime 3) := ⟨hp⟩
  have hn : 3 < 3 ^ e :=
    Nat.pow_lt_pow_right (by decide : 1 < 3) (lt_of_lt_of_le (by decide : 1 < 2) he)
  have hn0 : 0 < 3 ^ e := pow_pos (by decide) _
  have hT : ratExpression (3 ^ e) ≠ 0 :=
    ne_of_gt (ratExpression_pos (lt_trans (by decide : 1 < 3) hn))
  have hval : padicValRat 3 (ratExpression (3 ^ e)) = 2 - e :=
    padicValRat_ratExpression_three_pow he
  have hvn : padicValNat 3 (3 ^ e) = e := padicValNat.prime_pow e
  have hlt : padicValRat 3 (ratExpression (3 ^ e)) < 2 * padicValNat 3 (3 ^ e) := by
    rw [hval, hvn]
    have : (2 - (e : ℤ)) < 2 * (e : ℤ) := by
      have : (2 : ℤ) ≤ e := by exact_mod_cast he
      linarith
    exact this
  exact not_n_sq_dvd_num_of_padicVal_lt hp (dvd_pow_self 3 (by omega)) hn0 hT hlt

lemma pow_pred_mod_pow {p e i : ℕ} (hp0 : 0 < p) (hi : i ≤ e) :
    (p ^ e - 1) % p ^ i = p ^ i - 1 := by
  have hp0i : 0 < p ^ i := pow_pos hp0 i
  have hlt : p ^ i - 1 < p ^ i := Nat.sub_lt hp0i (by decide)
  rw [pow_pred_eq_mul_add hp0 hi, Nat.mul_add_mod_self_left, Nat.mod_eq_of_lt hlt]

lemma two_mul_pow_mod_pow {p e i : ℕ} (_hp0 : 0 < p) (hi : i ≤ e) :
    (2 * p ^ e) % p ^ i = 0 := by
  have hdvd : p ^ i ∣ p ^ e := pow_dvd_pow p hi
  exact Nat.mod_eq_zero_of_dvd (dvd_mul_of_dvd_right hdvd 2)

lemma padicValNat_choose_three_mul_pow {p e : ℕ} [Fact p.Prime]
    (h5 : 5 ≤ p) (he : 0 < e) :
    padicValNat p ((3 * p ^ e - 1).choose (p ^ e - 1)) = 0 := by
  have hp := ‹Fact p.Prime›.out
  have hp0 : 0 < p := hp.pos
  have hpe : 0 < p ^ e := pow_pos hp0 e
  have hpe1 : 1 < p ^ e := Nat.one_lt_pow (Nat.pos_iff_ne_zero.mp he) hp.one_lt
  have hnpos : 0 < 3 * p ^ e := Nat.mul_pos (by decide) hpe
  have h1n : 1 < 3 * p ^ e :=
    lt_trans (by decide : 1 < 3) (lt_mul_of_one_lt_right (by decide : 0 < 3) hpe1)
  have h3lt : 3 < p := lt_of_lt_of_le (by decide : 3 < 5) h5
  have hpowlt : 3 * p ^ e < p ^ (e + 1) := by
    calc
      3 * p ^ e < p * p ^ e := Nat.mul_lt_mul_of_pos_right h3lt hpe
      _ = p ^ (e + 1) := by rw [pow_succ, mul_comm]
  have hne : 3 * p ^ e - 1 ≠ 0 := Nat.sub_ne_zero_of_lt h1n
  have hnb : Nat.log p (3 * p ^ e - 1) < e + 1 :=
    (Nat.log_lt_iff_lt_pow hp.one_lt hne).2
      (lt_trans (Nat.sub_lt hnpos (by decide)) hpowlt)
  have hk : p ^ e - 1 ≤ 3 * p ^ e - 1 :=
    Nat.sub_le_sub_right (Nat.le_mul_of_pos_left _ (by decide)) 1
  rw [padicValNat_choose hk hnb]
  refine Finset.card_eq_zero.mpr ?_
  refine Finset.filter_eq_empty_iff.mpr ?_
  intro i hi hle
  have hi' := Finset.mem_Ico.mp hi
  have hile : i ≤ e := Nat.lt_succ_iff.mp hi'.2
  have hnk : 3 * p ^ e - 1 - (p ^ e - 1) = 2 * p ^ e := by
    have : 1 ≤ p ^ e := hpe1.le
    have : p ^ e ≤ 3 * p ^ e := Nat.le_mul_of_pos_left _ (by decide)
    omega
  have heq : (p ^ e - 1) % p ^ i + (3 * p ^ e - 1 - (p ^ e - 1)) % p ^ i = p ^ i - 1 := by
    rw [hnk, pow_pred_mod_pow hp0 hile, two_mul_pow_mod_pow hp0 hile, add_zero]
  have hlt : p ^ i - 1 < p ^ i := Nat.sub_lt (pow_pos hp0 i) (by decide)
  exact Nat.not_le_of_gt hlt (heq ▸ hle)

lemma eq_pow_of_odd_dvd_lt_three_mul {p e r : ℕ} (hp : p.Prime)
    (_he : 0 < e) (hr : r < 3 * p ^ e) (hodd : Odd r) (hd : p ^ e ∣ r) :
    r = p ^ e := by
  have hpos : 0 < p ^ e := pow_pos hp.pos e
  have hrpos : 0 < r := Odd.pos hodd
  have hdiv : r / p ^ e < 3 :=
    Nat.div_lt_of_lt_mul (by simpa [mul_comm] using hr)
  have hrw : r = r / p ^ e * p ^ e := (Nat.div_mul_cancel hd).symm
  have ha0 : 0 < r / p ^ e := Nat.div_pos (Nat.le_of_dvd hrpos hd) hpos
  have ha : r / p ^ e = 1 ∨ r / p ^ e = 2 := by omega
  rcases ha with ha | ha
  · rw [hrw, ha, one_mul]
  · have heven : Even r := by
      rw [hrw, ha]
      exact even_two.mul_right _
    exact (Nat.not_odd_iff_even.2 heven).elim hodd

lemma padicValRat_inner_of_unique {n p r0 : ℕ} [Fact p.Prime]
    (hn1 : 1 < n) (hr0mem : r0 ∈ (range n).filter Odd)
    (hC0 : padicValNat p ((n - 1).choose (r0 - 1)) = 0)
    (hv0 : 1 ≤ padicValNat p r0)
    (huniq : ∀ r ∈ (range n).filter Odd, r ≠ r0 →
      padicValNat p r < padicValNat p r0) :
    padicValRat p
      (∑ i ∈ range (n - 1),
        if Odd (i + 1) then ((n - 1).choose i : ℚ) / (i + 1 : ℚ) ^ 2 else 0) =
      - (2 : ℤ) * padicValNat p r0 := by
  have hr0' := mem_filter.mp hr0mem
  have hr0lt : r0 < n := mem_range.mp hr0'.1
  have hodd0 : Odd r0 := hr0'.2
  have hr0pos : 0 < r0 := Odd.pos hodd0
  have hr0le : r0 ≤ n := Nat.le_of_lt hr0lt
  rw [oddInnerSum_eq_sum_filter_odd hn1]
  have hterm0 :
      padicValRat p (((n - 1).choose (r0 - 1) : ℚ) / (r0 : ℚ) ^ 2) =
        - (2 : ℤ) * padicValNat p r0 := by
    have hval := padicValRat_choose_div_sq (p := p) hr0pos hr0le
    rw [hval, hC0]
    ring
  have hsplit :
      ∑ r ∈ (range n).filter Odd,
          ((n - 1).choose (r - 1) : ℚ) / (r : ℚ) ^ 2 =
        ((n - 1).choose (r0 - 1) : ℚ) / (r0 : ℚ) ^ 2 +
          ∑ r ∈ ((range n).filter Odd).erase r0,
            ((n - 1).choose (r - 1) : ℚ) / (r : ℚ) ^ 2 := by
    rw [← sum_erase_add _ _ hr0mem]
    abel
  have h1mem : 1 ∈ ((range n).filter Odd).erase r0 := by
    have hne1 : (1 : ℕ) ≠ r0 := by
      intro h
      have h1 : padicValNat p 1 = 0 :=
        padicValNat.eq_zero_of_not_dvd ‹Fact p.Prime›.out.not_dvd_one
      have : padicValNat p r0 = 0 := by rw [← h]; exact h1
      omega
    exact mem_erase.mpr ⟨hne1, mem_filter.mpr ⟨mem_range.mpr hn1, by decide⟩⟩
  have hrest0 :
      ∑ r ∈ ((range n).filter Odd).erase r0,
          ((n - 1).choose (r - 1) : ℚ) / (r : ℚ) ^ 2 ≠ 0 := by
    refine ne_of_gt (sum_pos (fun r hr => ?_) ⟨1, h1mem⟩)
    have hr' := mem_erase.mp hr
    have hr'' := mem_filter.mp hr'.2
    exact oddChooseTerm_pos (Odd.pos hr''.2) (mem_range.mp hr''.1).le
  have htermne :
      ((n - 1).choose (r0 - 1) : ℚ) / (r0 : ℚ) ^ 2 ≠ 0 :=
    ne_of_gt (oddChooseTerm_pos hr0pos hr0le)
  have hrestval :
      - (2 : ℤ) * (padicValNat p r0 - 1 : ℤ) ≤
        padicValRat p
          (∑ r ∈ ((range n).filter Odd).erase r0,
            ((n - 1).choose (r - 1) : ℚ) / (r : ℚ) ^ 2) := by
    refine le_padicValRat_sum_of_ne_zero _ ?_ hrest0
    intro r hr
    have hr' := mem_erase.mp hr
    have hr'' := mem_filter.mp hr'.2
    have hlt : r < n := mem_range.mp hr''.1
    have hpos : 0 < r := Odd.pos hr''.2
    have hvrlt : padicValNat p r < padicValNat p r0 := huniq r hr'.2 hr'.1
    have hvr : padicValNat p r ≤ padicValNat p r0 - 1 := Nat.le_sub_one_of_lt hvrlt
    have hval := padicValRat_choose_div_sq (n := n) (p := p) hpos hlt.le
    have hvC : (0 : ℤ) ≤ padicValNat p ((n - 1).choose (r - 1)) := Nat.cast_nonneg _
    have hvrZ : (padicValNat p r : ℤ) ≤ (padicValNat p r0 : ℤ) - 1 := by
      have h : (padicValNat p r : ℤ) ≤ ((padicValNat p r0 - 1 : ℕ) : ℤ) :=
        Int.ofNat_le.mpr hvr
      rwa [Nat.cast_sub hv0] at h
    rw [hval]
    linarith
  have hlt : padicValRat p (((n - 1).choose (r0 - 1) : ℚ) / (r0 : ℚ) ^ 2) <
      padicValRat p
        (∑ r ∈ ((range n).filter Odd).erase r0,
          ((n - 1).choose (r - 1) : ℚ) / (r : ℚ) ^ 2) := by
    rw [hterm0]
    have : - (2 : ℤ) * padicValNat p r0 < - (2 : ℤ) * (padicValNat p r0 - 1 : ℤ) := by
      have : (1 : ℤ) ≤ padicValNat p r0 := by exact_mod_cast hv0
      linarith
    exact lt_of_lt_of_le this hrestval
  have hsum0 :
      ((n - 1).choose (r0 - 1) : ℚ) / (r0 : ℚ) ^ 2 +
          ∑ r ∈ ((range n).filter Odd).erase r0,
            ((n - 1).choose (r - 1) : ℚ) / (r : ℚ) ^ 2 ≠ 0 :=
    ne_of_gt (add_pos_of_pos_of_nonneg (oddChooseTerm_pos hr0pos hr0le)
      (sum_nonneg fun r hr => le_of_lt (by
        have hr' := mem_erase.mp hr
        have hr'' := mem_filter.mp hr'.2
        exact oddChooseTerm_pos (Odd.pos hr''.2) (mem_range.mp hr''.1).le)))
  rw [hsplit, padicValRat.add_eq_of_lt hsum0 htermne hrest0 hlt, hterm0]

lemma padicValRat_ratExpression_three_mul_pow {p e : ℕ} (hp : p.Prime)
    (h5 : 5 ≤ p) (he : 0 < e) :
    padicValRat p (ratExpression (3 * p ^ e)) = -e := by
  have : Fact p.Prime := ⟨hp⟩
  have hp2 : p ≠ 2 := ne_of_gt (lt_of_lt_of_le (by decide : 2 < 5) h5)
  have hn1 : 1 < 3 * p ^ e := by
    have : 1 ≤ p ^ e := Nat.one_le_pow e p hp.pos
    have : 3 ≤ 3 * p ^ e := Nat.le_mul_of_pos_right _ (Nat.zero_lt_of_lt this)
    omega
  have hodd : Odd (3 * p ^ e) :=
    (by decide : Odd 3).mul (Odd.pow (n := e) (hp.odd_of_ne_two hp2))
  set n := 3 * p ^ e
  set r0 := p ^ e
  have hr0pos : 0 < r0 := pow_pos hp.pos e
  have hr0lt : r0 < n := by
    change r0 < 3 * r0
    exact lt_mul_of_one_lt_left hr0pos (by decide : 1 < 3)
  have hodd0 : Odd r0 := Odd.pow (n := e) (hp.odd_of_ne_two hp2)
  have hr0mem : r0 ∈ (range n).filter Odd :=
    mem_filter.mpr ⟨mem_range.mpr hr0lt, hodd0⟩
  have hC0 : padicValNat p ((n - 1).choose (r0 - 1)) = 0 := by
    simpa [n, r0] using padicValNat_choose_three_mul_pow (p := p) (e := e) h5 he
  have hvpow0 : padicValNat p r0 = e := by
    simp only [r0]
    exact padicValNat.prime_pow e
  have hv0 : 1 ≤ padicValNat p r0 := by
    rw [hvpow0]
    exact he
  have huniq : ∀ r ∈ (range n).filter Odd, r ≠ r0 →
      padicValNat p r < padicValNat p r0 := by
    intro r hr hne
    have hr' := mem_filter.mp hr
    have hne' : r ≠ p ^ e := by simpa [r0] using hne
    have hrne : r ≠ 0 := Nat.ne_of_gt (Odd.pos hr'.2)
    have hnd : ¬ p ^ e ∣ r := fun hd =>
      hne' (eq_pow_of_odd_dvd_lt_three_mul hp he (mem_range.mp hr'.1) hr'.2 hd)
    have hnot : ¬ e ≤ padicValNat p r := fun hle =>
      hnd ((padicValNat_dvd_iff_le hrne).2 hle)
    have hlt : padicValNat p r < e := Nat.not_le.mp hnot
    rw [hvpow0]
    exact hlt
  have hS := padicValRat_inner_of_unique hn1 hr0mem hC0 hv0 huniq
  have hT := ratExpression_eq_two_mul_n_sum_choose_sq hodd hn1
  have hSne :
      (∑ i ∈ range (n - 1),
          (if Odd (i + 1) then ((n - 1).choose i : ℚ) / (i + 1 : ℚ) ^ 2 else 0)) ≠ 0 := by
    intro h0
    have : padicValRat p (0 : ℚ) = - (2 : ℤ) * padicValNat p r0 := by simpa [h0] using hS
    have hneg : - (2 : ℤ) * padicValNat p r0 < 0 := by
      have : (1 : ℤ) ≤ padicValNat p r0 := by exact_mod_cast hv0
      linarith
    have : padicValRat p (0 : ℚ) = 0 := by simp
    linarith
  have h2ne : (2 : ℚ) ≠ 0 := by norm_num
  have hnne : (n : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_zero_of_lt hn1)
  have h2val : padicValRat p (2 : ℚ) = 0 := by
    rw [show (2 : ℚ) = ((2 : ℕ) : ℚ) from rfl, padicValRat.of_nat]
    exact_mod_cast (padicValNat_primes hp2)
  have hnval : padicValRat p (n : ℚ) = e := by
    rw [padicValRat.of_nat]
    have : padicValNat p (3 * p ^ e) = e := by
      have h3 : padicValNat p 3 = 0 :=
        padicValNat.eq_zero_of_not_dvd (by
          intro hd
          have : p ≤ 3 := Nat.le_of_dvd (by decide) hd
          have : 5 ≤ 3 := le_trans h5 this
          omega)
      have hpe : padicValNat p (p ^ e) = e := padicValNat.prime_pow e
      have h3ne : (3 : ℕ) ≠ 0 := by decide
      have hpe0 : p ^ e ≠ 0 := pow_ne_zero _ hp.ne_zero
      rw [padicValNat.mul h3ne hpe0, h3, hpe, zero_add]
    simpa [n] using this
  have hprod : ratExpression n =
      (2 : ℚ) * n *
        ∑ i ∈ range (n - 1),
          if Odd (i + 1) then ((n - 1).choose i : ℚ) / (i + 1 : ℚ) ^ 2 else 0 := by
    simpa using hT
  have hnumne : (2 : ℚ) * n *
      (∑ i ∈ range (n - 1),
        if Odd (i + 1) then ((n - 1).choose i : ℚ) / (i + 1 : ℚ) ^ 2 else 0) ≠ 0 :=
    mul_ne_zero (mul_ne_zero h2ne hnne) hSne
  rw [hprod, padicValRat.mul (mul_ne_zero h2ne hnne) hSne, padicValRat.mul h2ne hnne,
    h2val, hnval, hS, hvpow0]
  ring

/-- For an odd prime `p ≥ 5` and `e ≥ 1`, `(3 p^e)^2` does not divide `T(3 p^e).num`. -/
theorem not_n_sq_dvd_num_of_three_mul_pow {p e : ℕ} (hp : p.Prime)
    (h5 : 5 ≤ p) (he : 0 < e) :
    ¬ (ratExpression (3 * p ^ e)).num ≡ 0 [ZMOD ((3 * p ^ e) ^ 2 : ℤ)] := by
  have : Fact p.Prime := ⟨hp⟩
  have hn : 3 < 3 * p ^ e := by
    have : 1 < p ^ e := Nat.one_lt_pow (Nat.pos_iff_ne_zero.mp he) hp.one_lt
    have : 3 * 1 < 3 * p ^ e := Nat.mul_lt_mul_of_pos_left this (by decide)
    simpa using this
  have hn0 : 0 < 3 * p ^ e := Nat.mul_pos (by decide) (pow_pos hp.pos e)
  have hT : ratExpression (3 * p ^ e) ≠ 0 :=
    ne_of_gt (ratExpression_pos (lt_trans (by decide : 1 < 3) hn))
  have hval : padicValRat p (ratExpression (3 * p ^ e)) = -e :=
    padicValRat_ratExpression_three_mul_pow hp h5 he
  have hvn : padicValNat p (3 * p ^ e) = e := by
    have h3 : padicValNat p 3 = 0 :=
      padicValNat.eq_zero_of_not_dvd (by
        intro hd
        have : p ≤ 3 := Nat.le_of_dvd (by decide) hd
        omega)
    have hpe : padicValNat p (p ^ e) = e := padicValNat.prime_pow e
    rw [padicValNat.mul (by decide : (3 : ℕ) ≠ 0) (pow_ne_zero _ hp.ne_zero), h3, hpe,
      zero_add]
  have hlt : padicValRat p (ratExpression (3 * p ^ e)) <
      2 * padicValNat p (3 * p ^ e) := by
    rw [hval, hvn]
    have : (-(e : ℤ)) < 2 * (e : ℤ) := by
      have : (0 : ℤ) < e := by exact_mod_cast he
      linarith
    exact this
  exact not_n_sq_dvd_num_of_padicVal_lt hp (dvd_mul_of_dvd_right (dvd_pow_self p (by omega)) 3)
    hn0 hT hlt

/- Leading binomial coefficients for `T(p^e)`, `p ≥ 5`, `e ≥ 2`. -/

lemma choose_cast_eq_prod {n k : ℕ} (_hk : k ≤ n) :
    (n.choose k : ℚ) =
      (∏ i ∈ range k, ((n - i : ℕ) : ℚ)) / (∏ i ∈ range k, (i + 1 : ℚ)) := by
  have hfac : (k.factorial : ℚ) = ∏ i ∈ range k, (i + 1 : ℚ) := by
    rw [Nat.factorial_eq_prod_range_add_one, Nat.cast_prod]
    refine prod_congr rfl fun i _ => by simp
  have hdesc : (n.descFactorial k : ℚ) = ∏ i ∈ range k, ((n - i : ℕ) : ℚ) := by
    rw [Nat.descFactorial_eq_prod_range, Nat.cast_prod]
  have hmul : (n.descFactorial k : ℚ) = (k.factorial : ℚ) * n.choose k := by
    rw [Nat.descFactorial_eq_factorial_mul_choose n k, Nat.cast_mul]
  have hden : (∏ i ∈ range k, (i + 1 : ℚ)) ≠ 0 :=
    prod_ne_zero_iff.2 fun i _ => by exact_mod_cast Nat.succ_ne_zero i
  rw [eq_div_iff hden, mul_comm, ← hfac, ← hdesc, hmul]

lemma choose_pow_pred_eq_prod {p e k : ℕ} (hp0 : 0 < p) (_he : 0 < e)
    (hk : k ≤ p ^ e - 1) :
    ((p ^ e - 1).choose k : ℚ) =
      ∏ i ∈ range k, (((p ^ e - (i + 1) : ℕ) : ℚ) / (i + 1 : ℚ)) := by
  have hpe1 : 1 ≤ p ^ e := Nat.one_le_pow e p hp0
  have hk' : k ≤ p ^ e - 1 := hk
  have hprod :
      ∏ i ∈ range k, ((p ^ e - 1 - i : ℕ) : ℚ) =
        ∏ i ∈ range k, ((p ^ e - (i + 1) : ℕ) : ℚ) := by
    refine prod_congr rfl fun i hi => ?_
    have : i < k := mem_range.mp hi
    have : i + 1 ≤ p ^ e := by omega
    congr 1
    omega
  have hdiv := choose_cast_eq_prod (n := p ^ e - 1) (k := k) hk
  rw [hprod] at hdiv
  rw [hdiv, prod_div_distrib]

lemma choose_pred_eq_prod {p a : ℕ} (ha : a ≤ p) :
    ((p - 1).choose (a - 1) : ℚ) =
      ∏ b ∈ Icc 1 (a - 1), ((p - b : ℕ) : ℚ) / b := by
  by_cases ha0 : a = 0
  · subst ha0
    simp
  have ha1 : 1 ≤ a := Nat.pos_of_ne_zero ha0
  have hk : a - 1 ≤ p - 1 := Nat.sub_le_sub_right ha 1
  have hprod :
      ∏ i ∈ range (a - 1), ((p - 1 - i : ℕ) : ℚ) =
        ∏ i ∈ range (a - 1), ((p - (i + 1) : ℕ) : ℚ) := by
    refine prod_congr rfl fun i hi => ?_
    have : i < a - 1 := mem_range.mp hi
    have : i + 1 ≤ p := by omega
    congr 1
    omega
  have hdiv := choose_cast_eq_prod (n := p - 1) (k := a - 1) hk
  rw [hprod] at hdiv
  have himg :
      ∏ i ∈ range (a - 1), (((p - (i + 1) : ℕ) : ℚ) / (i + 1 : ℚ)) =
        ∏ b ∈ Icc 1 (a - 1), ((p - b : ℕ) : ℚ) / b := by
    refine prod_nbij (fun i => i + 1) ?_ ?_ ?_ ?_
    · intro i hi
      have : i < a - 1 := mem_range.mp hi
      exact mem_Icc.mpr ⟨Nat.succ_pos i, Nat.succ_le_of_lt this⟩
    · intro i _ hi' _ h
      exact Nat.succ_injective h
    · intro b hb
      have hb' := mem_Icc.mp hb
      refine ⟨b - 1, mem_range.mpr ?_, ?_⟩
      · exact Nat.sub_lt_right_of_lt_add hb'.1 (by omega)
      · exact Nat.sub_add_cancel hb'.1
    · intro i _hi
      simp [Nat.cast_succ]
  rw [hdiv, ← prod_div_distrib]
  exact himg

lemma padicValRat_prod_eq_zero {p : ℕ} [Fact p.Prime] {s : Finset ℕ} (g : ℕ → ℚ)
    (hg0 : ∀ i ∈ s, g i ≠ 0) (hg : ∀ i ∈ s, padicValRat p (g i) = 0) :
    padicValRat p (∏ i ∈ s, g i) = 0 := by
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [prod_insert ha]
    have ha0 : g a ≠ 0 := hg0 a (mem_insert_self _ _)
    have hs0 : ∏ i ∈ s, g i ≠ 0 :=
      prod_ne_zero_iff.2 fun i hi => hg0 i (mem_insert_of_mem hi)
    rw [padicValRat.mul ha0 hs0, hg a (mem_insert_self _ _),
      ih (fun i hi => hg0 i (mem_insert_of_mem hi))
        (fun i hi => hg i (mem_insert_of_mem hi)), add_zero]

lemma padicValRat_one_add_eq_zero {p : ℕ} [Fact p.Prime] {x : ℚ}
    (hx : 0 < padicValRat p x) (hx0 : x ≠ 0) (h1x : (1 : ℚ) + x ≠ 0) :
    padicValRat p (1 + x) = 0 := by
  have h1 : padicValRat p (1 : ℚ) = 0 := by simp
  have hlt : padicValRat p (1 : ℚ) < padicValRat p x := by simpa [h1] using hx
  rw [padicValRat.add_eq_of_lt h1x (by simp : (1 : ℚ) ≠ 0) hx0 hlt, h1]

lemma padicValRat_prod_one_add_sub_one {p : ℕ} [Fact p.Prime]
    {s : Finset ℕ} (f : ℕ → ℚ) {n : ℤ} (hn : 0 < n)
    (hf : ∀ i ∈ s, n ≤ padicValRat p (f i))
    (hf0 : ∀ i ∈ s, f i ≠ 0)
    (h1f : ∀ i ∈ s, (1 : ℚ) + f i ≠ 0)
    (hne : ∏ i ∈ s, (1 + f i) ≠ 1) :
    n ≤ padicValRat p (∏ i ∈ s, (1 + f i) - 1) := by
  have hsum :
      ∏ i ∈ s, (1 + f i) - 1 =
        ∑ i ∈ s, f i * ∏ j ∈ s.filter (fun j => j < i), (1 + f j) := by
    rw [prod_one_add_ordered]
    ring
  have hsum0 :
      ∑ i ∈ s, f i * ∏ j ∈ s.filter (fun j => j < i), (1 + f j) ≠ 0 := by
    intro h0
    exact hne (by rw [prod_one_add_ordered, h0, add_zero])
  rw [hsum]
  refine le_padicValRat_sum_of_ne_zero _ ?_ hsum0
  intro i hi
  have hfne : f i ≠ 0 := hf0 i hi
  have h1val : ∀ j ∈ s.filter (fun j => j < i), padicValRat p (1 + f j) = 0 := by
    intro j hj
    have hj' := mem_filter.mp hj
    have hx : 0 < padicValRat p (f j) := lt_of_lt_of_le hn (hf j hj'.1)
    exact padicValRat_one_add_eq_zero hx (hf0 j hj'.1) (h1f j hj'.1)
  have h1ne : ∀ j ∈ s.filter (fun j => j < i), (1 : ℚ) + f j ≠ 0 :=
    fun j hj => h1f j (mem_filter.mp hj).1
  have hprod0 : ∏ j ∈ s.filter (fun j => j < i), (1 + f j) ≠ 0 :=
    prod_ne_zero_iff.2 h1ne
  have hprodval := padicValRat_prod_eq_zero (fun j => 1 + f j) h1ne h1val
  have hterm :
      padicValRat p (f i * ∏ j ∈ s.filter (fun j => j < i), (1 + f j)) =
        padicValRat p (f i) := by
    rw [padicValRat.mul hfne hprod0, hprodval, add_zero]
  rw [hterm]
  exact hf i hi

lemma filter_dvd_pow_pred_eq_image {p e a : ℕ} (hp0 : 0 < p) (_he : 0 < e)
    (ha : 1 ≤ a) :
    ((Icc 1 (a * p ^ (e - 1) - 1)).filter (fun j => p ^ (e - 1) ∣ j)) =
      (Icc 1 (a - 1)).image (fun b => b * p ^ (e - 1)) := by
  have hpos : 0 < p ^ (e - 1) := pow_pos hp0 _
  ext j
  constructor
  · intro hj
    have hj' := mem_filter.mp hj
    have hjI := mem_Icc.mp hj'.1
    have hdvd := hj'.2
    refine mem_image.mpr ⟨j / p ^ (e - 1), mem_Icc.mpr ⟨?_, ?_⟩, Nat.div_mul_cancel hdvd⟩
    · exact Nat.div_pos (Nat.le_of_dvd (Nat.zero_lt_of_lt hjI.1) hdvd) hpos
    · have hjlt : j < a * p ^ (e - 1) :=
        (Nat.le_sub_one_iff_lt (Nat.mul_pos (Nat.zero_lt_of_lt ha) hpos)).1 hjI.2
      have : j / p ^ (e - 1) < a := (Nat.div_lt_iff_lt_mul hpos).2 hjlt
      exact Nat.le_sub_one_of_lt this
  · intro hj
    obtain ⟨b, hb, rfl⟩ := mem_image.mp hj
    have hb' := mem_Icc.mp hb
    refine mem_filter.mpr ⟨mem_Icc.mpr ⟨?_, ?_⟩, dvd_mul_left _ _⟩
    · have : 1 ≤ b * p ^ (e - 1) :=
        le_trans (Nat.succ_le_of_lt hpos) (Nat.le_mul_of_pos_left _ hb'.1)
      exact this
    · have hle : b * p ^ (e - 1) ≤ (a - 1) * p ^ (e - 1) :=
        Nat.mul_le_mul_right _ hb'.2
      have hsub : (a - 1) * p ^ (e - 1) = a * p ^ (e - 1) - p ^ (e - 1) := by
        cases a with
        | zero => omega
        | succ a => simp [Nat.succ_mul]
      have hpe_le : p ^ (e - 1) ≤ a * p ^ (e - 1) :=
        Nat.le_mul_of_pos_left _ (Nat.zero_lt_of_lt ha)
      have : a * p ^ (e - 1) - p ^ (e - 1) ≤ a * p ^ (e - 1) - 1 :=
        Nat.sub_le_sub_left (Nat.succ_le_of_lt hpos) _
      omega

lemma pow_sub_mul_pow_pred {p e b : ℕ} (he : 0 < e) (hb : b ≤ p) :
    p ^ e - b * p ^ (e - 1) = (p - b) * p ^ (e - 1) := by
  have hpe : p ^ e = p * p ^ (e - 1) := by
    rw [← pow_succ', Nat.sub_add_cancel he]
  have hle : b * p ^ (e - 1) ≤ p ^ e := by
    rw [hpe]
    exact Nat.mul_le_mul_right _ hb
  calc
    p ^ e - b * p ^ (e - 1) = p * p ^ (e - 1) - b * p ^ (e - 1) := by rw [hpe]
    _ = p ^ (e - 1) * p - p ^ (e - 1) * b := by rw [mul_comm p, mul_comm b]
    _ = p ^ (e - 1) * (p - b) := by rw [← Nat.mul_sub]
    _ = (p - b) * p ^ (e - 1) := by rw [mul_comm]

lemma rat_pow_sub_mul_div {p e b : ℕ} (hp0 : 0 < p) (he : 0 < e)
    (hb0 : 0 < b) (hb : b ≤ p) :
    (((p ^ e - b * p ^ (e - 1) : ℕ) : ℚ) / (b * p ^ (e - 1) : ℕ)) =
      ((p - b : ℕ) : ℚ) / b := by
  have hpos : 0 < p ^ (e - 1) := pow_pos hp0 _
  have hne' : (b : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.pos_iff_ne_zero.mp hb0)
  have hpe0 : ((p ^ (e - 1) : ℕ) : ℚ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (Nat.pos_iff_ne_zero.mp hpos)
  rw [pow_sub_mul_pow_pred he hb, Nat.cast_mul, Nat.cast_mul]
  field_simp [hne', hpe0]

lemma choose_pow_pred_eq_prod_Icc {p e k : ℕ} (hp0 : 0 < p) (he : 0 < e)
    (hk : k ≤ p ^ e - 1) :
    ((p ^ e - 1).choose k : ℚ) =
      ∏ j ∈ Icc 1 k, (((p ^ e - j : ℕ) : ℚ) / j) := by
  rw [choose_pow_pred_eq_prod hp0 he hk]
  refine prod_nbij (fun i => i + 1) ?_ ?_ ?_ ?_
  · intro i hi
    have : i < k := mem_range.mp hi
    exact mem_Icc.mpr ⟨Nat.succ_pos i, Nat.succ_le_of_lt this⟩
  · intro i _ hi' _ h
    exact Nat.succ_injective h
  · intro b hb
    have hb' := mem_Icc.mp hb
    refine ⟨b - 1, mem_range.mpr ?_, Nat.sub_add_cancel hb'.1⟩
    exact Nat.sub_lt_right_of_lt_add hb'.1 (by omega)
  · intro i _hi
    simp [Nat.cast_succ]

lemma prod_mul_pow_pred_eq_choose_pred {p e a : ℕ} (hp0 : 0 < p) (he : 0 < e)
    (ha : 1 ≤ a) (hap : a ≤ p) :
    ∏ j ∈ (Icc 1 (a * p ^ (e - 1) - 1)).filter (fun j => p ^ (e - 1) ∣ j),
        (((p ^ e - j : ℕ) : ℚ) / j) =
      ((p - 1).choose (a - 1) : ℚ) := by
  have hpos : 0 < p ^ (e - 1) := pow_pos hp0 _
  rw [filter_dvd_pow_pred_eq_image hp0 he ha]
  rw [prod_image]
  · trans ∏ b ∈ Icc 1 (a - 1), ((p - b : ℕ) : ℚ) / b
    · refine prod_congr rfl fun b hb => ?_
      have hb' := mem_Icc.mp hb
      have hb_le : b ≤ p :=
        le_trans hb'.2 (le_trans (Nat.sub_le a 1) hap)
      exact rat_pow_sub_mul_div hp0 he (Nat.zero_lt_of_lt hb'.1) hb_le
    · exact (choose_pred_eq_prod hap).symm
  · intro b hb b' hb' h
    exact Nat.eq_of_mul_eq_mul_right hpos h

lemma choose_pow_pred_eq_mul_rest {p e a : ℕ} (hp0 : 0 < p) (he : 0 < e)
    (ha : 1 ≤ a) (hap : a ≤ p) :
    ((p ^ e - 1).choose (a * p ^ (e - 1) - 1) : ℚ) =
      ((p - 1).choose (a - 1) : ℚ) *
        ∏ j ∈ (Icc 1 (a * p ^ (e - 1) - 1)).filter (fun j => ¬ p ^ (e - 1) ∣ j),
          (((p ^ e - j : ℕ) : ℚ) / j) := by
  have hle : a * p ^ (e - 1) ≤ p ^ e := by
    have hpe : p ^ e = p * p ^ (e - 1) := by
      rw [← pow_succ', Nat.sub_add_cancel he]
    rw [hpe]
    exact Nat.mul_le_mul_right _ hap
  have hk : a * p ^ (e - 1) - 1 ≤ p ^ e - 1 := Nat.sub_le_sub_right hle 1
  rw [choose_pow_pred_eq_prod_Icc hp0 he hk]
  rw [← prod_filter_mul_prod_filter_not (Icc 1 (a * p ^ (e - 1) - 1))
      (fun j => p ^ (e - 1) ∣ j)]
  rw [prod_mul_pow_pred_eq_choose_pred hp0 he ha hap]

#print axioms OeisA108866.p_mul_ratExpression_sq_sub_pos
#print axioms OeisA108866.padicValRat_ratExpression_sq_eq_min_sub_one
#print axioms OeisA108866.ratExpression_nine
#print axioms OeisA108866.not_n_sq_dvd_num_nine
#print axioms OeisA108866.ratExpression_twenty_five
#print axioms OeisA108866.not_n_sq_dvd_num_twenty_five
#print axioms OeisA108866.ratExpression_twenty_seven
#print axioms OeisA108866.not_n_sq_dvd_num_twenty_seven
#print axioms OeisA108866.ratExpression_forty_nine
#print axioms OeisA108866.not_n_sq_dvd_num_forty_nine
#print axioms OeisA108866.not_n_sq_dvd_num_of_three_pow
#print axioms OeisA108866.not_n_sq_dvd_num_of_three_mul_pow

end OeisA108866

