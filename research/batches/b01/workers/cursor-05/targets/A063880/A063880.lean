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
AI assistance: Cursor Grok 4.6 Extra High, as a research assistant.
-/
import FormalConjectures.OEIS.«63880»

/-!
# Independent development for A063880

This file does not use the `sorry` theorems in `FormalConjectures.OEIS.63880`.
It imports only the definitions `A`, `usigma`, `unitaryDivisors`, and `IsPrimitiveTerm`.

The frozen targets are:

* `∀ {n : ℕ}, A n → n % 216 = 108`
* `∀ {n : ℕ}, IsPrimitiveTerm n → n = 108`

A claimed completion requires `#print axioms` with only `propext`,
`Classical.choice`, and/or `Quot.sound`.
-/

open scoped ArithmeticFunction.sigma Pointwise
open Nat Finset ArithmeticFunction

namespace Cursor05.A063880

open OeisA63880

section Unitary

lemma mem_unitaryDivisors {n d : ℕ} :
    d ∈ unitaryDivisors n ↔ d ∣ n ∧ n ≠ 0 ∧ d.Coprime (n / d) := by
  constructor
  · intro h
    simp only [unitaryDivisors, mem_filter, mem_divisors] at h
    exact ⟨h.1.1, h.1.2, h.2⟩
  · intro h
    simp only [unitaryDivisors, mem_filter, mem_divisors]
    exact ⟨⟨h.1, h.2.1⟩, h.2.2⟩

lemma usigma_zero : usigma 0 = 0 := by
  simp [usigma, unitaryDivisors, divisors_zero]

lemma unitaryDivisors_one : unitaryDivisors 1 = {1} := by
  ext d
  constructor
  · intro h
    have := (mem_unitaryDivisors.mp h).1
    simpa [Nat.dvd_one] using this
  · intro h
    simp only [mem_singleton] at h
    subst d
    exact mem_unitaryDivisors.mpr ⟨dvd_rfl, one_ne_zero, Nat.coprime_one_right _⟩

lemma usigma_one : usigma 1 = 1 := by
  simp [usigma, unitaryDivisors_one]

lemma gcd_pow_min (p a b : ℕ) :
    (p ^ a).gcd (p ^ b) = p ^ min a b := by
  rcases le_total a b with h | h
  · rw [gcd_eq_left (pow_dvd_pow p h), min_eq_left h]
  · rw [gcd_eq_right (pow_dvd_pow p h), min_eq_right h]

lemma pow_div_pow_of_le {p j k : ℕ} (hp : 0 < p) (hj : j ≤ k) :
    p ^ k / p ^ j = p ^ (k - j) := by
  rw [← pow_sub_mul_pow p hj, Nat.mul_div_left _ (pow_pos hp j)]

lemma unitaryDivisors_prime_pow {p k : ℕ} (hp : p.Prime) (_hk : 0 < k) :
    unitaryDivisors (p ^ k) = {1, p ^ k} := by
  ext d
  constructor
  · intro hd
    obtain ⟨hdvd, -, hcop⟩ := mem_unitaryDivisors.mp hd
    obtain ⟨j, hj, rfl⟩ := (dvd_prime_pow hp).mp hdvd
    have hcop' : (p ^ j).Coprime (p ^ (k - j)) := by
      rwa [pow_div_pow_of_le hp.pos hj] at hcop
    have hmin : j = 0 ∨ k - j = 0 := by
      have hg : (p ^ j).gcd (p ^ (k - j)) = 1 := hcop'
      rw [gcd_pow_min] at hg
      have hmin0 : min j (k - j) = 0 := by
        contrapose! hg
        exact (one_lt_pow hg hp.one_lt).ne.symm
      exact min_eq_zero_iff.mp hmin0
    rcases hmin with hj0 | hkj
    · simp [hj0]
    · have : j = k := by omega
      simp [this]
  · intro hd
    simp only [mem_insert, mem_singleton] at hd
    rcases hd with rfl | rfl
    · exact mem_unitaryDivisors.mpr ⟨one_dvd _, pow_ne_zero _ hp.ne_zero,
        Nat.coprime_one_left _⟩
    · refine mem_unitaryDivisors.mpr ⟨dvd_rfl, pow_ne_zero _ hp.ne_zero, ?_⟩
      rw [Nat.div_self (pow_pos hp.pos k)]
      exact Nat.coprime_one_right _

lemma usigma_prime_pow {p k : ℕ} (hp : p.Prime) (hk : 0 < k) :
    usigma (p ^ k) = 1 + p ^ k := by
  have hne : (1 : ℕ) ≠ p ^ k := (one_lt_pow hk.ne' hp.one_lt).ne
  rw [usigma, unitaryDivisors_prime_pow hp hk, sum_pair hne, add_comm]

lemma usigma_prime {p : ℕ} (hp : p.Prime) : usigma p = 1 + p := by
  simpa using usigma_prime_pow hp (Nat.succ_pos 0)

lemma div_mul_div_eq {a b m n : ℕ} (ha : a ∣ m) (hb : b ∣ n) :
    m / a * (n / b) = m * n / (a * b) := by
  obtain ⟨k, rfl⟩ := ha
  obtain ⟨l, rfl⟩ := hb
  by_cases h0 : a * b = 0
  · rcases Nat.mul_eq_zero.mp h0 with ha0 | hb0
    · simp [ha0]
    · simp [hb0]
  have ha_pos : 0 < a := pos_of_ne_zero (left_ne_zero_of_mul h0)
  have hb_pos : 0 < b := pos_of_ne_zero (right_ne_zero_of_mul h0)
  rw [Nat.mul_div_right k ha_pos, Nat.mul_div_right l hb_pos,
    mul_mul_mul_comm a k b l, Nat.mul_div_right (k * l) (mul_pos ha_pos hb_pos)]

lemma unitaryDivisors_subset_divisors (n : ℕ) :
    unitaryDivisors n ⊆ n.divisors := filter_subset _ _

lemma product_unitaryDivisors_subset {m n : ℕ} :
    unitaryDivisors m ×ˢ unitaryDivisors n ⊆ m.divisors ×ˢ n.divisors := by
  intro x hx
  exact mem_product.mpr
    ⟨unitaryDivisors_subset_divisors _ (mem_product.mp hx).1,
      unitaryDivisors_subset_divisors _ (mem_product.mp hx).2⟩

/-- Coprime multiplicativity of `usigma`. -/
lemma usigma_mul {m n : ℕ} (hmn : Coprime m n) : usigma (m * n) = usigma m * usigma n := by
  rcases eq_or_ne m 0 with rfl | hm0
  · simp [usigma_zero]
  rcases eq_or_ne n 0 with rfl | hn0
  · simp [usigma_zero]
  classical
  let f : ℕ × ℕ → ℕ := fun p => p.1 * p.2
  have hinj : Set.InjOn f ↑(unitaryDivisors m ×ˢ unitaryDivisors n) := by
    intro x hx y hy hxy
    exact hmn.mul_injOn_divisors
      (product_unitaryDivisors_subset hx) (product_unitaryDivisors_subset hy) hxy
  have hmap :
      (unitaryDivisors m ×ˢ unitaryDivisors n).image f = unitaryDivisors (m * n) := by
    ext d
    constructor
    · intro hd
      obtain ⟨⟨a, b⟩, hp, rfl⟩ := mem_image.mp hd
      obtain ⟨ha, hb⟩ := mem_product.mp hp
      obtain ⟨hadv, -, hacop⟩ := mem_unitaryDivisors.mp ha
      obtain ⟨hbdv, -, hbcop⟩ := mem_unitaryDivisors.mp hb
      refine mem_unitaryDivisors.mpr ⟨mul_dvd_mul hadv hbdv, mul_ne_zero hm0 hn0, ?_⟩
      rw [← div_mul_div_eq hadv hbdv]
      have ha_n : Coprime a n := hmn.coprime_dvd_left hadv
      have hb_m : Coprime b m := hmn.symm.coprime_dvd_left hbdv
      have ha_nb : Coprime a (n / b) := ha_n.coprime_dvd_right (div_dvd_of_dvd hbdv)
      have hb_ma : Coprime b (m / a) := hb_m.coprime_dvd_right (div_dvd_of_dvd hadv)
      rw [coprime_mul_iff_left, coprime_mul_iff_right, coprime_mul_iff_right]
      exact ⟨⟨hacop, ha_nb⟩, ⟨hb_ma, hbcop⟩⟩
    · intro hd
      obtain ⟨hdvd, hmn0, hcop⟩ := mem_unitaryDivisors.mp hd
      have hdivs : d ∈ (m * n).divisors := mem_divisors.mpr ⟨hdvd, hmn0⟩
      have hmul : d ∈ m.divisors * n.divisors := by
        rwa [← Nat.divisors_mul]
      obtain ⟨a, ha, b, hb, rfl⟩ := mem_mul.mp hmul
      have hadv : a ∣ m := dvd_of_mem_divisors ha
      have hbdv : b ∣ n := dvd_of_mem_divisors hb
      have hcop' : Coprime (a * b) (m / a * (n / b)) := by
        simpa [div_mul_div_eq hadv hbdv] using hcop
      have hsplit := coprime_mul_iff_left.mp hcop'
      have h1 := coprime_mul_iff_right.mp hsplit.1
      have h2 := coprime_mul_iff_right.mp hsplit.2
      have haU : a ∈ unitaryDivisors m := mem_unitaryDivisors.mpr ⟨hadv, hm0, h1.1⟩
      have hbU : b ∈ unitaryDivisors n := mem_unitaryDivisors.mpr ⟨hbdv, hn0, h2.2⟩
      exact mem_image.mpr ⟨⟨a, b⟩, mem_product.mpr ⟨haU, hbU⟩, rfl⟩
  rw [usigma, usigma, usigma, ← hmap, sum_image hinj, sum_product]
  simpa [f] using (sum_mul_sum (s := unitaryDivisors m) (t := unitaryDivisors n)
    (f := fun x => x) (g := fun y => y)).symm

lemma usigma_eq_prod {n : ℕ} (hn : n ≠ 0) :
    usigma n = n.factorization.prod fun p k => 1 + p ^ k := by
  rw [multiplicative_factorization (fun n => usigma n)
    (fun _ _ h => usigma_mul h) usigma_one hn, Finsupp.prod]
  refine prod_congr rfl fun p hp => ?_
  have hmem : p ∈ n.primeFactors := by
    rwa [← support_factorization]
  have hp' : p.Prime := prime_of_mem_primeFactors hmem
  have hk : 0 < n.factorization p := Nat.pos_of_ne_zero (Finsupp.mem_support_iff.mp hp)
  exact usigma_prime_pow hp' hk

lemma sigma_prime_pow_div {p k : ℕ} (hp : p.Prime) :
    σ 1 (p ^ k) = (p ^ (k + 1) - 1) / (p - 1) := by
  rw [sigma_one_apply_prime_pow hp, Nat.geomSum_eq hp.two_le]

lemma sub_one_dvd_pow_sub_one {p k : ℕ} :
    p - 1 ∣ p ^ k - 1 := by
  simpa using Nat.sub_dvd_pow_sub_pow p 1 k

lemma coprime_div_of_dvd_squarefree {n d : ℕ} (hn : Squarefree n) (hd : d ∣ n) :
    Coprime d (n / d) := by
  rcases eq_or_ne n 0 with rfl | _
  · exact (not_squarefree_zero hn).elim
  have hdecomp : n = d * (n / d) := (Nat.mul_div_cancel' hd).symm
  exact coprime_of_squarefree_mul (hdecomp ▸ hn)

lemma unitaryDivisors_eq_divisors_of_squarefree {n : ℕ} (hn : Squarefree n) :
    unitaryDivisors n = n.divisors := by
  ext d
  simp only [mem_unitaryDivisors, mem_divisors]
  constructor
  · exact fun h => ⟨h.1, h.2.1⟩
  · intro h
    exact ⟨h.1, h.2, coprime_div_of_dvd_squarefree hn h.1⟩

lemma usigma_eq_sigma_of_squarefree {n : ℕ} (hn : Squarefree n) :
    usigma n = σ 1 n := by
  simp [usigma, sigma_one_apply, unitaryDivisors_eq_divisors_of_squarefree hn]

lemma sigma_mul_of_coprime {m n : ℕ} (hmn : Coprime m n) :
    σ 1 (m * n) = σ 1 m * σ 1 n :=
  isMultiplicative_sigma.map_mul_of_coprime hmn

/-- Membership in `A` is preserved by coprime squarefree factors.
This is the independent form of the textbook helper
`a_of_primitive_mul_squarefree`, without using primitivity. -/
lemma A.mul_squarefree {m s : ℕ} (hm : A m) (hs : Squarefree s) (hc : Coprime m s) :
    A (m * s) := by
  have hs0 : s ≠ 0 := fun h => not_squarefree_zero (h ▸ hs)
  refine ⟨Nat.mul_pos hm.1 (Nat.pos_of_ne_zero hs0), ?_⟩
  rw [sigma_mul_of_coprime hc, usigma_mul hc, hm.2, usigma_eq_sigma_of_squarefree hs]
  ring

lemma usigma_four : usigma 4 = 5 := by
  simpa using usigma_prime_pow Nat.prime_two (by decide : 0 < 2)

lemma usigma_twentySeven : usigma 27 = 28 := by
  simpa using usigma_prime_pow Nat.prime_three (by decide : 0 < 3)

lemma coprime_four_twentySeven : Coprime 4 27 := by decide

lemma usigma_108 : usigma 108 = 140 := by
  rw [show (108 : ℕ) = 4 * 27 by decide, usigma_mul coprime_four_twentySeven,
    usigma_four, usigma_twentySeven]

lemma sigma_four : σ 1 4 = 7 := by decide

lemma coprime_four_of_odd {m : ℕ} (h : Odd m) : Coprime 4 m :=
  (coprime_pow_left_iff (n := 2) (by decide : 0 < 2) 2 m).mpr h.coprime_two_left

/-- If `4m` is in `A` and `m` is odd, the leftover equation is `7 σ(m) = 10 usigma(m)`. -/
lemma seven_sigma_eq_ten_usigma_of_A_four_mul {m : ℕ} (hm : Odd m) (hA : A (4 * m)) :
    7 * σ 1 m = 10 * usigma m := by
  have hc : Coprime 4 m := coprime_four_of_odd hm
  have heq := hA.2
  rw [sigma_mul_of_coprime hc, usigma_mul hc, usigma_four, sigma_four] at heq
  linarith

lemma usigma_le_sigma (n : ℕ) : usigma n ≤ σ 1 n := by
  simpa [usigma, sigma_one_apply] using
    sum_le_sum_of_subset_of_nonneg (unitaryDivisors_subset_divisors n)
      (fun _ _ _ => Nat.zero_le _)

lemma seven_mul_sigma_three_pow_gt {k : ℕ} (hk : 4 ≤ k) :
    10 * usigma (3 ^ k) < 7 * σ 1 (3 ^ k) := by
  have hk0 : 0 < k := by omega
  have hu : usigma (3 ^ k) = 1 + 3 ^ k := usigma_prime_pow Nat.prime_three hk0
  have hσ : σ 1 (3 ^ k) = (3 ^ (k + 1) - 1) / 2 := sigma_prime_pow_div Nat.prime_three
  have hdiv : 2 ∣ 3 ^ (k + 1) - 1 := sub_one_dvd_pow_sub_one (p := 3)
  have h81 : 81 ≤ 3 ^ k := by
    have : 3 ^ 4 = 81 := by decide
    exact this ▸ Nat.pow_le_pow_right (by decide : 1 ≤ 3) hk
  have hsucc : 3 ^ (k + 1) = 3 * 3 ^ k := by rw [pow_succ']
  have hpos : 1 ≤ 3 * 3 ^ k := by
    exact Nat.succ_le_of_lt (Nat.mul_pos (by decide) (Nat.pow_pos (n := k) (by decide : 0 < 3)))
  have hmain : 20 * (1 + 3 ^ k) < 7 * (3 ^ (k + 1) - 1) := by
    rw [hsucc]
    have : 27 < 3 ^ k := by omega
    have : 20 + 20 * 3 ^ k + 7 < 21 * 3 ^ k := by nlinarith
    have : 20 + 20 * 3 ^ k < 21 * 3 ^ k - 7 := by omega
    convert this using 1
    · ring
    · omega
  rw [hu, hσ]
  have hN : 7 * ((3 ^ (k + 1) - 1) / 2) = 7 * (3 ^ (k + 1) - 1) / 2 :=
    (Nat.mul_div_assoc 7 hdiv).symm
  rw [hN]
  have h2N : 2 ∣ 7 * (3 ^ (k + 1) - 1) := hdiv.mul_left 7
  have hcancel : 2 * (7 * (3 ^ (k + 1) - 1) / 2) = 7 * (3 ^ (k + 1) - 1) :=
    Nat.mul_div_cancel' h2N
  refine Nat.lt_of_mul_lt_mul_left (a := 2) ?_
  rw [hcancel]
  convert hmain using 1
  ring

lemma padicValNat_three_lt_four_of_seven_sigma {m : ℕ} (hm : m ≠ 0)
    (h : 7 * σ 1 m = 10 * usigma m) : padicValNat 3 m < 4 := by
  by_contra! hk
  have hdecomp : ordProj[3] m * ordCompl[3] m = m :=
    Nat.ordProj_mul_ordCompl_eq_self m 3
  have hc : Coprime (ordProj[3] m) (ordCompl[3] m) :=
    (Nat.coprime_ordCompl Nat.prime_three hm).pow_left (m.factorization 3)
  have h' : 7 * σ 1 (ordProj[3] m) * σ 1 (ordCompl[3] m) =
      10 * usigma (ordProj[3] m) * usigma (ordCompl[3] m) := by
    have := h
    rw [← hdecomp, sigma_mul_of_coprime hc, usigma_mul hc] at this
    convert this using 1 <;> ring
  have hle : 7 * σ 1 (ordProj[3] m) * σ 1 (ordCompl[3] m) ≤
      10 * usigma (ordProj[3] m) * σ 1 (ordCompl[3] m) := by
    rw [h']
    gcongr
    exact usigma_le_sigma _
  have ht : 0 < σ 1 (ordCompl[3] m) := by
    have : ordCompl[3] m ≠ 0 := by
      intro h0
      apply hm
      rw [← hdecomp, h0, mul_zero]
    exact sigma_pos_iff.mpr (Nat.pos_of_ne_zero this)
  have hle' : 7 * σ 1 (ordProj[3] m) ≤ 10 * usigma (ordProj[3] m) :=
    Nat.le_of_mul_le_mul_right hle ht
  have hproj : ordProj[3] m = 3 ^ padicValNat 3 m := by
    simp [Nat.factorization_def m Nat.prime_three]
  have hlt : 10 * usigma (3 ^ padicValNat 3 m) < 7 * σ 1 (3 ^ padicValNat 3 m) :=
    seven_mul_sigma_three_pow_gt hk
  rw [hproj] at hle'
  omega

lemma padicValNat_three_lt_four_of_A_four_mul {m : ℕ} (hm : Odd m) (hA : A (4 * m)) :
    padicValNat 3 m < 4 :=
  padicValNat_three_lt_four_of_seven_sigma (Nat.pos_iff_ne_zero.mp hm.pos)
    (seven_sigma_eq_ten_usigma_of_A_four_mul hm hA)

lemma sigma_twentySeven : σ 1 27 = 40 := by decide

lemma seven_sigma_twentySeven : 7 * σ 1 27 = 10 * usigma 27 := by
  rw [sigma_twentySeven, usigma_twentySeven]

lemma sigma_eq_usigma_ordCompl_of_val_three {m : ℕ} (hm : m ≠ 0)
    (h : 7 * σ 1 m = 10 * usigma m) (h3 : padicValNat 3 m = 3) :
    σ 1 (ordCompl[3] m) = usigma (ordCompl[3] m) := by
  have hv : m.factorization 3 = 3 := by
    rw [Nat.factorization_def m Nat.prime_three, h3]
  have hpow : 3 ^ m.factorization 3 = 27 := by
    rw [hv]
    decide
  have hc : Coprime 27 (m / 27) := by
    have : Coprime (3 ^ m.factorization 3) (m / 3 ^ m.factorization 3) :=
      (Nat.coprime_ordCompl Nat.prime_three hm).pow_left (m.factorization 3)
    simpa [hpow] using this
  have hdecomp : 27 * (m / 27) = m := by
    have := Nat.ordProj_mul_ordCompl_eq_self m 3
    simpa [hpow] using this
  have hmul : 7 * σ 1 27 * σ 1 (m / 27) = 10 * usigma 27 * usigma (m / 27) := by
    have := h
    rw [← hdecomp, sigma_mul_of_coprime hc, usigma_mul hc] at this
    convert this using 1 <;> ring
  have hcoeff : 7 * σ 1 27 = 10 * usigma 27 := seven_sigma_twentySeven
  have hpos : 0 < 7 * σ 1 27 := by
    rw [hcoeff, usigma_twentySeven]
    decide
  have : (7 * σ 1 27) * σ 1 (m / 27) = (7 * σ 1 27) * usigma (m / 27) := by
    rw [hmul, hcoeff]
  have heq := Nat.eq_of_mul_eq_mul_left hpos this
  simpa [hpow] using heq

lemma dvd_div_of_sq_dvd {n p : ℕ} (h : p ^ 2 ∣ n) : p ∣ n / p := by
  have hp_dvd : p ∣ n := (dvd_pow_self p (by decide : 2 ≠ 0)).trans h
  exact (Nat.dvd_div_iff_mul_dvd hp_dvd).2 (by simpa [pow_two] using h)

lemma not_coprime_of_sq_dvd {n p : ℕ} (hp : p.Prime) (h : p ^ 2 ∣ n) :
    ¬ p.Coprime (n / p) := by
  have hp_div : p ∣ n / p := dvd_div_of_sq_dvd h
  intro hc
  have hg : p.gcd (n / p) = 1 := hc
  have hgp : p.gcd (n / p) = p := Nat.gcd_eq_left hp_div
  exact hp.ne_one (hgp.symm.trans hg)

lemma exists_prime_pow_two_dvd_of_not_squarefree {n : ℕ} (hn : ¬ Squarefree n) :
    ∃ p, p.Prime ∧ p ^ 2 ∣ n := by
  rw [squarefree_iff_prime_squarefree] at hn
  push Not at hn
  obtain ⟨p, hp, h⟩ := hn
  exact ⟨p, hp, by simpa [pow_two] using h⟩

/-- On positive integers, `σ` and `usigma` agree if and only if `n` is squarefree.
If `p^2 ∣ n`, then `p` is a non-unitary divisor, so the sums differ. -/
lemma sigma_eq_usigma_iff_squarefree {n : ℕ} (hn : 0 < n) :
    σ 1 n = usigma n ↔ Squarefree n := by
  constructor
  · intro heq
    by_contra hnsq
    obtain ⟨p, hp, hsq⟩ := exists_prime_pow_two_dvd_of_not_squarefree hnsq
    have hp_dvd : p ∣ n := (dvd_pow_self p (by decide : 2 ≠ 0)).trans hsq
    have hmem : p ∈ n.divisors := mem_divisors.mpr ⟨hp_dvd, hn.ne'⟩
    have hnmem : p ∉ unitaryDivisors n := by
      intro hU
      exact not_coprime_of_sq_dvd hp hsq (mem_unitaryDivisors.mp hU).2.2
    have hlt : usigma n < σ 1 n := by
      rw [usigma, sigma_one_apply]
      exact sum_lt_sum_of_subset (unitaryDivisors_subset_divisors n) hmem hnmem
        hp.pos fun _ _ _ => Nat.zero_le _
    omega
  · intro hs
    exact (usigma_eq_sigma_of_squarefree hs).symm

lemma squarefree_ordCompl_of_val_three {m : ℕ} (hm : m ≠ 0)
    (h : 7 * σ 1 m = 10 * usigma m) (h3 : padicValNat 3 m = 3) :
    Squarefree (ordCompl[3] m) := by
  have hpos : 0 < ordCompl[3] m := Nat.ordCompl_pos 3 hm
  exact (sigma_eq_usigma_iff_squarefree hpos).mp
    (sigma_eq_usigma_ordCompl_of_val_three hm h h3)

/-- Peeling a prime-power factor from `A σ = B usigma`. -/
lemma mul_sigma_ordProj_le {A B n p : ℕ} (hp : p.Prime) (hn : n ≠ 0)
    (h : A * σ 1 n = B * usigma n) :
    A * σ 1 (ordProj[p] n) ≤ B * usigma (ordProj[p] n) := by
  have hdecomp : ordProj[p] n * ordCompl[p] n = n :=
    Nat.ordProj_mul_ordCompl_eq_self n p
  have hc : Coprime (ordProj[p] n) (ordCompl[p] n) :=
    (Nat.coprime_ordCompl hp hn).pow_left (n.factorization p)
  have h' : A * σ 1 (ordProj[p] n) * σ 1 (ordCompl[p] n) =
      B * usigma (ordProj[p] n) * usigma (ordCompl[p] n) := by
    have := h
    rw [← hdecomp, sigma_mul_of_coprime hc, usigma_mul hc] at this
    convert this using 1 <;> ring
  have hle : A * σ 1 (ordProj[p] n) * σ 1 (ordCompl[p] n) ≤
      B * usigma (ordProj[p] n) * σ 1 (ordCompl[p] n) := by
    rw [h']
    gcongr
    exact usigma_le_sigma _
  have ht : 0 < σ 1 (ordCompl[p] n) :=
    sigma_pos_iff.mpr (Nat.ordCompl_pos p hn)
  exact Nat.le_of_mul_le_mul_right hle ht

/-- For leftover `100/91`, every `5^k` with `k ≥ 2` overshoots. -/
lemma hundred_usigma_lt_ninety_one_sigma_five_pow {k : ℕ} (hk : 2 ≤ k) :
    100 * usigma (5 ^ k) < 91 * σ 1 (5 ^ k) := by
  have hk0 : 0 < k := by omega
  have hu : usigma (5 ^ k) = 1 + 5 ^ k := usigma_prime_pow Nat.prime_five hk0
  have hσ : σ 1 (5 ^ k) = (5 ^ (k + 1) - 1) / 4 := sigma_prime_pow_div Nat.prime_five
  have hdiv : 4 ∣ 5 ^ (k + 1) - 1 := sub_one_dvd_pow_sub_one (p := 5)
  have h25 : 25 ≤ 5 ^ k := by
    have : 5 ^ 2 = 25 := by decide
    exact this ▸ Nat.pow_le_pow_right (by decide : 1 ≤ 5) hk
  have hsucc : 5 ^ (k + 1) = 5 * 5 ^ k := by rw [pow_succ']
  have hmain : 400 * (1 + 5 ^ k) < 91 * (5 ^ (k + 1) - 1) := by
    rw [hsucc]
    have : 491 < 55 * 5 ^ k := by nlinarith
    have : 400 + 400 * 5 ^ k + 91 < 455 * 5 ^ k := by nlinarith
    have : 400 + 400 * 5 ^ k < 455 * 5 ^ k - 91 := by omega
    convert this using 1
    · ring
    · omega
  rw [hu, hσ]
  have hN : 91 * ((5 ^ (k + 1) - 1) / 4) = 91 * (5 ^ (k + 1) - 1) / 4 :=
    (Nat.mul_div_assoc 91 hdiv).symm
  rw [hN]
  have h4N : 4 ∣ 91 * (5 ^ (k + 1) - 1) := hdiv.mul_left 91
  have hcancel : 4 * (91 * (5 ^ (k + 1) - 1) / 4) = 91 * (5 ^ (k + 1) - 1) :=
    Nat.mul_div_cancel' h4N
  refine Nat.lt_of_mul_lt_mul_left (a := 4) ?_
  rw [hcancel]
  convert hmain using 1
  ring

/-- For leftover `100/91`, every `7^k` with `k ≥ 2` overshoots. -/
lemma hundred_usigma_lt_ninety_one_sigma_seven_pow {k : ℕ} (hk : 2 ≤ k) :
    100 * usigma (7 ^ k) < 91 * σ 1 (7 ^ k) := by
  have hk0 : 0 < k := by omega
  have hp7 : Nat.Prime 7 := by decide
  have hu : usigma (7 ^ k) = 1 + 7 ^ k := usigma_prime_pow hp7 hk0
  have hσ : σ 1 (7 ^ k) = (7 ^ (k + 1) - 1) / 6 := sigma_prime_pow_div hp7
  have hdiv : 6 ∣ 7 ^ (k + 1) - 1 := sub_one_dvd_pow_sub_one (p := 7)
  have h49 : 49 ≤ 7 ^ k := by
    have : 7 ^ 2 = 49 := by decide
    exact this ▸ Nat.pow_le_pow_right (by decide : 1 ≤ 7) hk
  have hsucc : 7 ^ (k + 1) = 7 * 7 ^ k := by rw [pow_succ']
  have hmain : 600 * (1 + 7 ^ k) < 91 * (7 ^ (k + 1) - 1) := by
    rw [hsucc]
    have : 691 < 37 * 7 ^ k := by nlinarith
    have : 600 + 600 * 7 ^ k + 91 < 637 * 7 ^ k := by nlinarith
    have : 600 + 600 * 7 ^ k < 637 * 7 ^ k - 91 := by omega
    convert this using 1
    · ring
    · omega
  rw [hu, hσ]
  have hN : 91 * ((7 ^ (k + 1) - 1) / 6) = 91 * (7 ^ (k + 1) - 1) / 6 :=
    (Nat.mul_div_assoc 91 hdiv).symm
  rw [hN]
  have h6N : 6 ∣ 91 * (7 ^ (k + 1) - 1) := hdiv.mul_left 91
  have hcancel : 6 * (91 * (7 ^ (k + 1) - 1) / 6) = 91 * (7 ^ (k + 1) - 1) :=
    Nat.mul_div_cancel' h6N
  refine Nat.lt_of_mul_lt_mul_left (a := 6) ?_
  rw [hcancel]
  convert hmain using 1
  ring

/-- For leftover `100/91`, every `11^k` with `k ≥ 3` overshoots. -/
lemma hundred_usigma_lt_ninety_one_sigma_eleven_pow {k : ℕ} (hk : 3 ≤ k) :
    100 * usigma (11 ^ k) < 91 * σ 1 (11 ^ k) := by
  have hk0 : 0 < k := by omega
  have hp11 : Nat.Prime 11 := by decide
  have hu : usigma (11 ^ k) = 1 + 11 ^ k := usigma_prime_pow hp11 hk0
  have hσ : σ 1 (11 ^ k) = (11 ^ (k + 1) - 1) / 10 := sigma_prime_pow_div hp11
  have hdiv : 10 ∣ 11 ^ (k + 1) - 1 := sub_one_dvd_pow_sub_one (p := 11)
  have h1331 : 1331 ≤ 11 ^ k := by
    have : 11 ^ 3 = 1331 := by decide
    exact this ▸ Nat.pow_le_pow_right (by decide : 1 ≤ 11) hk
  have hsucc : 11 ^ (k + 1) = 11 * 11 ^ k := by rw [pow_succ']
  have hmain : 1000 * (1 + 11 ^ k) < 91 * (11 ^ (k + 1) - 1) := by
    rw [hsucc]
    have : 1091 < 11 ^ k := by nlinarith
    have : 1000 + 1000 * 11 ^ k + 91 < 1001 * 11 ^ k := by nlinarith
    have : 1000 + 1000 * 11 ^ k < 1001 * 11 ^ k - 91 := by omega
    convert this using 1
    · ring
    · omega
  rw [hu, hσ]
  have hN : 91 * ((11 ^ (k + 1) - 1) / 10) = 91 * (11 ^ (k + 1) - 1) / 10 :=
    (Nat.mul_div_assoc 91 hdiv).symm
  rw [hN]
  have h10N : 10 ∣ 91 * (11 ^ (k + 1) - 1) := hdiv.mul_left 91
  have hcancel : 10 * (91 * (11 ^ (k + 1) - 1) / 10) = 91 * (11 ^ (k + 1) - 1) :=
    Nat.mul_div_cancel' h10N
  refine Nat.lt_of_mul_lt_mul_left (a := 10) ?_
  rw [hcancel]
  convert hmain using 1
  ring

lemma padicValNat_five_lt_two_of_hundred_ninety_one {t : ℕ} (ht : t ≠ 0)
    (h : 91 * σ 1 t = 100 * usigma t) :
    padicValNat 5 t < 2 := by
  by_contra! hk
  have hproj : ordProj[5] t = 5 ^ padicValNat 5 t := by
    simp [Nat.factorization_def t Nat.prime_five]
  have hle := mul_sigma_ordProj_le Nat.prime_five ht h
  rw [hproj] at hle
  have hover := hundred_usigma_lt_ninety_one_sigma_five_pow hk
  omega

lemma padicValNat_seven_lt_two_of_hundred_ninety_one {t : ℕ} (ht : t ≠ 0)
    (h : 91 * σ 1 t = 100 * usigma t) :
    padicValNat 7 t < 2 := by
  by_contra! hk
  have hp7 : Nat.Prime 7 := by decide
  have hproj : ordProj[7] t = 7 ^ padicValNat 7 t := by
    simp [Nat.factorization_def t hp7]
  have hle := mul_sigma_ordProj_le hp7 ht h
  rw [hproj] at hle
  have hover := hundred_usigma_lt_ninety_one_sigma_seven_pow hk
  omega

lemma padicValNat_eleven_lt_three_of_hundred_ninety_one {t : ℕ} (ht : t ≠ 0)
    (h : 91 * σ 1 t = 100 * usigma t) :
    padicValNat 11 t < 3 := by
  by_contra! hk
  have hp11 : Nat.Prime 11 := by decide
  have hproj : ordProj[11] t = 11 ^ padicValNat 11 t := by
    simp [Nat.factorization_def t hp11]
  have hle := mul_sigma_ordProj_le hp11 ht h
  rw [hproj] at hle
  have hover := hundred_usigma_lt_ninety_one_sigma_eleven_pow hk
  omega

lemma ninety_one_sigma_eq_hundred_usigma_of_val_three_two {m : ℕ} (hm : m ≠ 0)
    (h : 7 * σ 1 m = 10 * usigma m) (h3 : padicValNat 3 m = 2) :
    91 * σ 1 (ordCompl[3] m) = 100 * usigma (ordCompl[3] m) := by
  have hv : m.factorization 3 = 2 := by
    rw [Nat.factorization_def m Nat.prime_three, h3]
  have hpow : 3 ^ m.factorization 3 = 9 := by
    rw [hv]
    decide
  have hc : Coprime 9 (m / 9) := by
    have : Coprime (3 ^ m.factorization 3) (m / 3 ^ m.factorization 3) :=
      (Nat.coprime_ordCompl Nat.prime_three hm).pow_left (m.factorization 3)
    simpa [hpow] using this
  have hdecomp : 9 * (m / 9) = m := by
    have := Nat.ordProj_mul_ordCompl_eq_self m 3
    simpa [hpow] using this
  have hσ9 : σ 1 9 = 13 := by decide
  have hu9 : usigma 9 = 10 := by
    simpa using usigma_prime_pow Nat.prime_three (by decide : 0 < 2)
  have hmul : 7 * σ 1 9 * σ 1 (m / 9) = 10 * usigma 9 * usigma (m / 9) := by
    have := h
    rw [← hdecomp, sigma_mul_of_coprime hc, usigma_mul hc] at this
    convert this using 1 <;> ring
  rw [hσ9, hu9] at hmul
  have : 91 * σ 1 (m / 9) = 100 * usigma (m / 9) := by
    rw [show (91 : ℕ) = 7 * 13 by decide, show (100 : ℕ) = 10 * 10 by decide]
    exact hmul
  simpa [hpow] using this

lemma usigma_eleven_pow_two : usigma (11 ^ 2) = 122 := by
  simpa using usigma_prime_pow (by decide : Nat.Prime 11) (by decide : 0 < 2)

lemma sigma_eleven_pow_two : σ 1 (11 ^ 2) = 133 := by
  rw [sigma_prime_pow_div (by decide : Nat.Prime 11)]
  norm_num

lemma twelve_thousand_sigma_eq_of_val_eleven_two {t : ℕ} (ht : t ≠ 0)
    (h : 91 * σ 1 t = 100 * usigma t) (h11 : padicValNat 11 t = 2) :
    12103 * σ 1 (ordCompl[11] t) = 12200 * usigma (ordCompl[11] t) := by
  have hp11 : Nat.Prime 11 := by decide
  have hv : t.factorization 11 = 2 := by
    rw [Nat.factorization_def t hp11, h11]
  have hpow : 11 ^ t.factorization 11 = 121 := by
    rw [hv]
    decide
  have hc : Coprime 121 (t / 121) := by
    have : Coprime (11 ^ t.factorization 11) (t / 11 ^ t.factorization 11) :=
      (Nat.coprime_ordCompl hp11 ht).pow_left (t.factorization 11)
    simpa [hpow] using this
  have hdecomp : 121 * (t / 121) = t := by
    have := Nat.ordProj_mul_ordCompl_eq_self t 11
    simpa [hpow] using this
  have hmul : 91 * σ 1 121 * σ 1 (t / 121) = 100 * usigma 121 * usigma (t / 121) := by
    have := h
    rw [← hdecomp, sigma_mul_of_coprime hc, usigma_mul hc] at this
    convert this using 1 <;> ring
  have h121 : (121 : ℕ) = 11 ^ 2 := by decide
  rw [h121, sigma_eleven_pow_two, usigma_eleven_pow_two] at hmul
  have : 12103 * σ 1 (t / 121) = 12200 * usigma (t / 121) := by
    rw [show (12103 : ℕ) = 91 * 133 by decide, show (12200 : ℕ) = 100 * 122 by decide]
    exact hmul
  simpa [hpow] using this

lemma not_squarefree_ordCompl_of_val_eleven_two {t : ℕ} (ht : t ≠ 0)
    (h : 91 * σ 1 t = 100 * usigma t) (h11 : padicValNat 11 t = 2) :
    ¬ Squarefree (ordCompl[11] t) := by
  intro hs
  have hpos : 0 < ordCompl[11] t := Nat.ordCompl_pos 11 ht
  have heq := twelve_thousand_sigma_eq_of_val_eleven_two ht h h11
  have hσu := (sigma_eq_usigma_iff_squarefree hpos).mpr hs
  rw [hσu] at heq
  have hpos' : 0 < usigma (ordCompl[11] t) := by
    have : ordCompl[11] t ≠ 0 := hpos.ne'
    have : usigma (ordCompl[11] t) = σ 1 (ordCompl[11] t) := hσu.symm
    have : 0 < σ 1 (ordCompl[11] t) := sigma_pos_iff.mpr hpos
    omega
  have : 12103 = 12200 := Nat.eq_of_mul_eq_mul_right hpos' heq
  contradiction

lemma twelve_two_usigma_lt_sigma_thirteen_pow {k : ℕ} (hk : 2 ≤ k) :
    12200 * usigma (13 ^ k) < 12103 * σ 1 (13 ^ k) := by
  have hk0 : 0 < k := by omega
  have hp13 : Nat.Prime 13 := by decide
  have hu : usigma (13 ^ k) = 1 + 13 ^ k := usigma_prime_pow hp13 hk0
  have hσ : σ 1 (13 ^ k) = (13 ^ (k + 1) - 1) / 12 := sigma_prime_pow_div hp13
  have hdiv : 12 ∣ 13 ^ (k + 1) - 1 := sub_one_dvd_pow_sub_one (p := 13)
  have h169 : 169 ≤ 13 ^ k := by
    have : 13 ^ 2 = 169 := by decide
    exact this ▸ Nat.pow_le_pow_right (by decide : 1 ≤ 13) hk
  have hsucc : 13 ^ (k + 1) = 13 * 13 ^ k := by rw [pow_succ']
  have hmain : 146400 * (1 + 13 ^ k) < 12103 * (13 ^ (k + 1) - 1) := by
    rw [hsucc]
    have : 158503 < 10939 * 13 ^ k := by nlinarith
    have : 146400 + 146400 * 13 ^ k + 12103 < 157339 * 13 ^ k := by nlinarith
    have : 146400 + 146400 * 13 ^ k < 157339 * 13 ^ k - 12103 := by omega
    convert this using 1
    · ring
    · omega
  rw [hu, hσ]
  have hN : 12103 * ((13 ^ (k + 1) - 1) / 12) = 12103 * (13 ^ (k + 1) - 1) / 12 :=
    (Nat.mul_div_assoc 12103 hdiv).symm
  rw [hN]
  have h12N : 12 ∣ 12103 * (13 ^ (k + 1) - 1) := hdiv.mul_left 12103
  have hcancel : 12 * (12103 * (13 ^ (k + 1) - 1) / 12) = 12103 * (13 ^ (k + 1) - 1) :=
    Nat.mul_div_cancel' h12N
  refine Nat.lt_of_mul_lt_mul_left (a := 12) ?_
  rw [hcancel]
  convert hmain using 1
  ring

lemma padicValNat_thirteen_lt_two_of_val_eleven_two {t : ℕ} (ht : t ≠ 0)
    (h : 91 * σ 1 t = 100 * usigma t) (h11 : padicValNat 11 t = 2) :
    padicValNat 13 (ordCompl[11] t) < 2 := by
  have hr := twelve_thousand_sigma_eq_of_val_eleven_two ht h h11
  have hr0 : ordCompl[11] t ≠ 0 := (Nat.ordCompl_pos 11 ht).ne'
  by_contra! hk
  have hp13 : Nat.Prime 13 := by decide
  have hproj : ordProj[13] (ordCompl[11] t) = 13 ^ padicValNat 13 (ordCompl[11] t) := by
    simp [Nat.factorization_def (ordCompl[11] t) hp13]
  have hle := mul_sigma_ordProj_le hp13 hr0 hr
  rw [hproj] at hle
  have hover := twelve_two_usigma_lt_sigma_thirteen_pow hk
  omega

lemma coprime_eight_of_odd {m : ℕ} (h : Odd m) : Coprime 8 m :=
  (coprime_pow_left_iff (n := 3) (by decide : 0 < 3) 2 m).mpr h.coprime_two_left

lemma usigma_eight : usigma 8 = 9 := by
  simpa using usigma_prime_pow Nat.prime_two (by decide : 0 < 3)

lemma sigma_eight : σ 1 8 = 15 := by decide

/-- If `8m` is in `A` and `m` is odd, the leftover equation is `5 σ(m) = 6 usigma(m)`. -/
lemma five_sigma_eq_six_usigma_of_A_eight_mul {m : ℕ} (hm : Odd m) (hA : A (8 * m)) :
    5 * σ 1 m = 6 * usigma m := by
  have hc : Coprime 8 m := coprime_eight_of_odd hm
  have heq := hA.2
  rw [sigma_mul_of_coprime hc, usigma_mul hc, usigma_eight, sigma_eight] at heq
  linarith

lemma six_usigma_lt_five_sigma_three_pow {k : ℕ} (hk : 2 ≤ k) :
    6 * usigma (3 ^ k) < 5 * σ 1 (3 ^ k) := by
  have hk0 : 0 < k := by omega
  have hu : usigma (3 ^ k) = 1 + 3 ^ k := usigma_prime_pow Nat.prime_three hk0
  have hσ : σ 1 (3 ^ k) = (3 ^ (k + 1) - 1) / 2 := sigma_prime_pow_div Nat.prime_three
  have hdiv : 2 ∣ 3 ^ (k + 1) - 1 := sub_one_dvd_pow_sub_one (p := 3)
  have h9 : 9 ≤ 3 ^ k := by
    have : 3 ^ 2 = 9 := by decide
    exact this ▸ Nat.pow_le_pow_right (by decide : 1 ≤ 3) hk
  have hsucc : 3 ^ (k + 1) = 3 * 3 ^ k := by rw [pow_succ']
  have hmain : 12 * (1 + 3 ^ k) < 5 * (3 ^ (k + 1) - 1) := by
    rw [hsucc]
    have : 17 < 3 * 3 ^ k := by nlinarith
    have : 12 + 12 * 3 ^ k + 5 < 15 * 3 ^ k := by nlinarith
    have : 12 + 12 * 3 ^ k < 15 * 3 ^ k - 5 := by omega
    convert this using 1
    · ring
    · omega
  rw [hu, hσ]
  have hN : 5 * ((3 ^ (k + 1) - 1) / 2) = 5 * (3 ^ (k + 1) - 1) / 2 :=
    (Nat.mul_div_assoc 5 hdiv).symm
  rw [hN]
  have h2N : 2 ∣ 5 * (3 ^ (k + 1) - 1) := hdiv.mul_left 5
  have hcancel : 2 * (5 * (3 ^ (k + 1) - 1) / 2) = 5 * (3 ^ (k + 1) - 1) :=
    Nat.mul_div_cancel' h2N
  refine Nat.lt_of_mul_lt_mul_left (a := 2) ?_
  rw [hcancel]
  convert hmain using 1
  ring

lemma padicValNat_three_lt_two_of_A_eight_mul {m : ℕ} (hm : Odd m) (hA : A (8 * m)) :
    padicValNat 3 m < 2 := by
  have h := five_sigma_eq_six_usigma_of_A_eight_mul hm hA
  by_contra! hk
  have hm0 : m ≠ 0 := Nat.pos_iff_ne_zero.mp hm.pos
  have hproj : ordProj[3] m = 3 ^ padicValNat 3 m := by
    simp [Nat.factorization_def m Nat.prime_three]
  have hle := mul_sigma_ordProj_le Nat.prime_three hm0 h
  rw [hproj] at hle
  have hover := six_usigma_lt_five_sigma_three_pow hk
  omega

/-- For leftover `6/5`, every `5^k` with `k ≥ 3` overshoots. -/
lemma six_usigma_lt_five_sigma_five_pow {k : ℕ} (hk : 3 ≤ k) :
    6 * usigma (5 ^ k) < 5 * σ 1 (5 ^ k) := by
  have hk0 : 0 < k := by omega
  have hu : usigma (5 ^ k) = 1 + 5 ^ k := usigma_prime_pow Nat.prime_five hk0
  have hσ : σ 1 (5 ^ k) = (5 ^ (k + 1) - 1) / 4 := sigma_prime_pow_div Nat.prime_five
  have hdiv : 4 ∣ 5 ^ (k + 1) - 1 := sub_one_dvd_pow_sub_one (p := 5)
  have h125 : 125 ≤ 5 ^ k := by
    have : 5 ^ 3 = 125 := by decide
    exact this ▸ Nat.pow_le_pow_right (by decide : 1 ≤ 5) hk
  have hsucc : 5 ^ (k + 1) = 5 * 5 ^ k := by rw [Nat.pow_succ']
  have hmain : 24 * (1 + 5 ^ k) < 5 * (5 ^ (k + 1) - 1) := by
    rw [hsucc]
    have : 29 < 5 ^ k := by nlinarith
    have : 24 + 24 * 5 ^ k + 5 < 25 * 5 ^ k := by nlinarith
    have : 24 + 24 * 5 ^ k < 25 * 5 ^ k - 5 := by omega
    convert this using 1
    · ring
    · omega
  rw [hu, hσ]
  have hN : 5 * ((5 ^ (k + 1) - 1) / 4) = 5 * (5 ^ (k + 1) - 1) / 4 :=
    (Nat.mul_div_assoc 5 hdiv).symm
  rw [hN]
  have h4N : 4 ∣ 5 * (5 ^ (k + 1) - 1) := hdiv.mul_left 5
  have hcancel : 4 * (5 * (5 ^ (k + 1) - 1) / 4) = 5 * (5 ^ (k + 1) - 1) :=
    Nat.mul_div_cancel' h4N
  refine Nat.lt_of_mul_lt_mul_left (a := 4) ?_
  rw [hcancel]
  convert hmain using 1
  ring

lemma padicValNat_five_lt_three_of_A_eight_mul {m : ℕ} (hm : Odd m) (hA : A (8 * m)) :
    padicValNat 5 m < 3 := by
  have h := five_sigma_eq_six_usigma_of_A_eight_mul hm hA
  by_contra! hk
  have hm0 : m ≠ 0 := Nat.pos_iff_ne_zero.mp hm.pos
  have hproj : ordProj[5] m = 5 ^ padicValNat 5 m := by
    simp [Nat.factorization_def m Nat.prime_five]
  have hle := mul_sigma_ordProj_le Nat.prime_five hm0 h
  rw [hproj] at hle
  have hover := six_usigma_lt_five_sigma_five_pow hk
  omega

lemma usigma_five_pow_two : usigma (5 ^ 2) = 26 := by
  simpa using usigma_prime_pow Nat.prime_five (by decide : 0 < 2)

lemma sigma_five_pow_two : σ 1 (5 ^ 2) = 31 := by
  rw [sigma_prime_pow_div Nat.prime_five]
  norm_num

lemma one_fifty_five_sigma_eq_of_val_five_two {m : ℕ} (hm : m ≠ 0)
    (h : 5 * σ 1 m = 6 * usigma m) (h5 : padicValNat 5 m = 2) :
    155 * σ 1 (ordCompl[5] m) = 156 * usigma (ordCompl[5] m) := by
  have hv : m.factorization 5 = 2 := by
    rw [Nat.factorization_def m Nat.prime_five, h5]
  have hpow : 5 ^ m.factorization 5 = 25 := by
    rw [hv]
    decide
  have hc : Coprime 25 (m / 25) := by
    have : Coprime (5 ^ m.factorization 5) (m / 5 ^ m.factorization 5) :=
      (Nat.coprime_ordCompl Nat.prime_five hm).pow_left (m.factorization 5)
    simpa [hpow] using this
  have hdecomp : 25 * (m / 25) = m := by
    have := Nat.ordProj_mul_ordCompl_eq_self m 5
    simpa [hpow] using this
  have hmul : 5 * σ 1 25 * σ 1 (m / 25) = 6 * usigma 25 * usigma (m / 25) := by
    have := h
    rw [← hdecomp, sigma_mul_of_coprime hc, usigma_mul hc] at this
    convert this using 1 <;> ring
  have h25 : (25 : ℕ) = 5 ^ 2 := by decide
  rw [h25, sigma_five_pow_two, usigma_five_pow_two] at hmul
  have : 155 * σ 1 (m / 25) = 156 * usigma (m / 25) := by
    rw [show (155 : ℕ) = 5 * 31 by decide, show (156 : ℕ) = 6 * 26 by decide]
    exact hmul
  simpa [hpow] using this

lemma not_squarefree_ordCompl_of_eight_mul_val_five_two {m : ℕ} (hm : Odd m)
    (hA : A (8 * m)) (h5 : padicValNat 5 m = 2) :
    ¬ Squarefree (ordCompl[5] m) := by
  have hm0 : m ≠ 0 := Nat.pos_iff_ne_zero.mp hm.pos
  have h := five_sigma_eq_six_usigma_of_A_eight_mul hm hA
  intro hs
  have hpos : 0 < ordCompl[5] m := Nat.ordCompl_pos 5 hm0
  have heq := one_fifty_five_sigma_eq_of_val_five_two hm0 h h5
  have hσu := (sigma_eq_usigma_iff_squarefree hpos).mpr hs
  rw [hσu] at heq
  have hpos' : 0 < usigma (ordCompl[5] m) := by
    rw [← hσu]
    exact sigma_pos_iff.mpr hpos
  have : 155 = 156 := Nat.eq_of_mul_eq_mul_right hpos' heq
  contradiction

lemma sigma_two_pow (a : ℕ) : σ 1 (2 ^ a) = 2 ^ (a + 1) - 1 := by
  rw [sigma_prime_pow_div Nat.prime_two, Nat.div_one]

lemma usigma_two_pow {a : ℕ} (ha : 0 < a) : usigma (2 ^ a) = 1 + 2 ^ a :=
  usigma_prime_pow Nat.prime_two ha

/-- Split `A n` across the 2-power and the odd part. -/
lemma sigma_eq_two_usigma_odd_part {n : ℕ} (hA : A n) :
    σ 1 (ordProj[2] n) * σ 1 (ordCompl[2] n) =
      2 * usigma (ordProj[2] n) * usigma (ordCompl[2] n) := by
  have hn : n ≠ 0 := hA.1.ne'
  have hdecomp : ordProj[2] n * ordCompl[2] n = n :=
    Nat.ordProj_mul_ordCompl_eq_self n 2
  have hc : Coprime (ordProj[2] n) (ordCompl[2] n) :=
    (Nat.coprime_ordCompl Nat.prime_two hn).pow_left (n.factorization 2)
  have := hA.2
  rw [← hdecomp, sigma_mul_of_coprime hc, usigma_mul hc] at this
  convert this using 1
  ring

lemma padicValNat_three_ordCompl_two {n : ℕ} :
    padicValNat 3 (ordCompl[2] n) = padicValNat 3 n := by
  rw [← Nat.factorization_def (ordCompl[2] n) Nat.prime_three,
    ← Nat.factorization_def n Nat.prime_three, Nat.factorization_ordCompl]
  simp [Finsupp.erase_ne (by decide : (3 : ℕ) ≠ 2)]

/-- `3 + 6A + 7T < 2AT` for `A ≥ 8` and `T ≥ 9`. -/
lemma add_six_mul_add_seven_mul_lt {A T : ℕ} (hA : 8 ≤ A) (hT : 9 ≤ T) :
    3 + 6 * A + 7 * T < 2 * A * T := by
  have hA' : (8 : ℤ) ≤ A := Int.ofNat_le.mpr hA
  have hT' : (9 : ℤ) ≤ T := Int.ofNat_le.mpr hT
  have h : (3 : ℤ) + 6 * (A : ℤ) + 7 * (T : ℤ) < 2 * (A : ℤ) * (T : ℤ) := by
    nlinarith
  exact_mod_cast h

/-- `4(1+A)(1+T) < (2A-1)(3T-1)` for `A ≥ 8` and `T ≥ 9`. -/
lemma four_mul_succ_two_three_lt {A T : ℕ} (hA : 8 ≤ A) (hT : 9 ≤ T) :
    4 * (1 + A) * (1 + T) < (2 * A - 1) * (3 * T - 1) := by
  have h2A : 1 ≤ 2 * A := by nlinarith
  have h3T : 1 ≤ 3 * T := by nlinarith
  have hA' : (8 : ℤ) ≤ A := Int.ofNat_le.mpr hA
  have hT' : (9 : ℤ) ≤ T := Int.ofNat_le.mpr hT
  have hL : ((4 * (1 + A) * (1 + T) : ℕ) : ℤ) =
      4 * (1 + (A : ℤ)) * (1 + (T : ℤ)) := by push_cast; rfl
  have hR : (((2 * A - 1) * (3 * T - 1) : ℕ) : ℤ) =
      (2 * (A : ℤ) - 1) * (3 * (T : ℤ) - 1) := by
    rw [Nat.cast_mul, Nat.cast_sub h2A, Nat.cast_sub h3T]
    push_cast; rfl
  have hint : (4 : ℤ) * (1 + (A : ℤ)) * (1 + (T : ℤ)) <
      (2 * (A : ℤ) - 1) * (3 * (T : ℤ) - 1) := by
    nlinarith
  exact Nat.cast_lt.mp (by rw [hL, hR]; exact hint)

/-- `ρ(2^a) ρ(3^k) > 2` whenever `a ≥ 3` and `k ≥ 2`. -/
lemma two_pow_ge_three_three_pow_overshoot {a k : ℕ} (ha : 3 ≤ a) (hk : 2 ≤ k) :
    2 * usigma (2 ^ a) * usigma (3 ^ k) < σ 1 (2 ^ a) * σ 1 (3 ^ k) := by
  have ha0 : 0 < a := by omega
  have hk0 : 0 < k := by omega
  have hA : 8 ≤ 2 ^ a := by
    have : 2 ^ 3 = 8 := by decide
    exact this ▸ Nat.pow_le_pow_right (by decide : 1 ≤ 2) ha
  have hT : 9 ≤ 3 ^ k := by
    have : 3 ^ 2 = 9 := by decide
    exact this ▸ Nat.pow_le_pow_right (by decide : 1 ≤ 3) hk
  have hu2 : usigma (2 ^ a) = 1 + 2 ^ a := usigma_two_pow ha0
  have hu3 : usigma (3 ^ k) = 1 + 3 ^ k := usigma_prime_pow Nat.prime_three hk0
  have hσ2 : σ 1 (2 ^ a) = 2 ^ (a + 1) - 1 := sigma_two_pow a
  have hσ3 : σ 1 (3 ^ k) = (3 ^ (k + 1) - 1) / 2 := sigma_prime_pow_div Nat.prime_three
  have hdiv : 2 ∣ 3 ^ (k + 1) - 1 := sub_one_dvd_pow_sub_one (p := 3)
  have hsucc2 : 2 ^ (a + 1) = 2 * 2 ^ a := by rw [Nat.pow_succ']
  have hsucc3 : 3 ^ (k + 1) = 3 * 3 ^ k := by rw [Nat.pow_succ']
  have hmain := four_mul_succ_two_three_lt (A := 2 ^ a) (T := 3 ^ k) hA hT
  rw [hu2, hu3, hσ2, hσ3, hsucc2, hsucc3]
  have hdiv' : 2 ∣ 3 * 3 ^ k - 1 := by simpa [hsucc3] using hdiv
  have hR : (2 * 2 ^ a - 1) * ((3 * 3 ^ k - 1) / 2) =
      (2 * 2 ^ a - 1) * (3 * 3 ^ k - 1) / 2 :=
    (Nat.mul_div_assoc _ hdiv').symm
  rw [hR]
  refine Nat.lt_of_mul_lt_mul_left (a := 2) ?_
  have hcancel :
      2 * ((2 * 2 ^ a - 1) * (3 * 3 ^ k - 1) / 2) =
        (2 * 2 ^ a - 1) * (3 * 3 ^ k - 1) :=
    Nat.mul_div_cancel' (hdiv'.mul_left _)
  rw [hcancel]
  convert hmain using 1
  ring

lemma padicValNat_three_lt_two_of_A_of_val_two_ge_three {n : ℕ} (hA : A n)
    (h2 : 3 ≤ padicValNat 2 n) : padicValNat 3 n < 2 := by
  have hn : n ≠ 0 := hA.1.ne'
  have hsplit := sigma_eq_two_usigma_odd_part hA
  have hproj2 : ordProj[2] n = 2 ^ padicValNat 2 n := by
    simp [Nat.factorization_def n Nat.prime_two]
  rw [hproj2] at hsplit
  have hm0 : ordCompl[2] n ≠ 0 := (Nat.ordCompl_pos 2 hn).ne'
  by_contra! hk
  have hle :=
    mul_sigma_ordProj_le (A := σ 1 (2 ^ padicValNat 2 n))
      (B := 2 * usigma (2 ^ padicValNat 2 n)) Nat.prime_three hm0 hsplit
  have hproj3 : ordProj[3] (ordCompl[2] n) =
      3 ^ padicValNat 3 (ordCompl[2] n) := by
    simp [Nat.factorization_def (ordCompl[2] n) Nat.prime_three]
  rw [hproj3] at hle
  have hk3 : 2 ≤ padicValNat 3 (ordCompl[2] n) := by
    rwa [padicValNat_three_ordCompl_two]
  have hover :=
    two_pow_ge_three_three_pow_overshoot (a := padicValNat 2 n)
      (k := padicValNat 3 (ordCompl[2] n)) h2 hk3
  omega

/-- Every prime `p ≥ 5` undershoots leftover `10/7`. -/
lemma seven_sigma_lt_ten_usigma_prime_pow_ge_five {p k : ℕ}
    (hp : p.Prime) (hp5 : 5 ≤ p) (hk : 0 < k) :
    7 * σ 1 (p ^ k) < 10 * usigma (p ^ k) := by
  have hu : usigma (p ^ k) = 1 + p ^ k := usigma_prime_pow hp hk
  have hσ : σ 1 (p ^ k) = (p ^ (k + 1) - 1) / (p - 1) := sigma_prime_pow_div hp
  have hdiv : p - 1 ∣ p ^ (k + 1) - 1 := sub_one_dvd_pow_sub_one
  have hsucc : p ^ (k + 1) = p * p ^ k := by rw [Nat.pow_succ']
  have hpos : 1 ≤ p * p ^ k :=
    Nat.succ_le_of_lt (Nat.mul_pos hp.pos (Nat.pow_pos hp.pos))
  have hp1 : 1 ≤ p := hp.one_le
  have hmain : 7 * (p * p ^ k - 1) < 10 * (p - 1) * (1 + p ^ k) := by
    have hp' : (5 : ℤ) ≤ p := Int.ofNat_le.mpr hp5
    have hpk : (1 : ℤ) ≤ p ^ k := by
      exact_mod_cast (Nat.one_le_pow k p hp.pos : 1 ≤ p ^ k)
    have hL : ((7 * (p * p ^ k - 1) : ℕ) : ℤ) =
        7 * ((p : ℤ) * p ^ k - 1) := by
      rw [Nat.cast_mul, Nat.cast_sub hpos]
      push_cast; rfl
    have hR : ((10 * (p - 1) * (1 + p ^ k) : ℕ) : ℤ) =
        10 * ((p : ℤ) - 1) * (1 + p ^ k) := by
      rw [Nat.cast_mul, Nat.cast_mul, Nat.cast_sub hp1]
      push_cast; rfl
    have hint : (7 : ℤ) * ((p : ℤ) * p ^ k - 1) <
        10 * ((p : ℤ) - 1) * (1 + p ^ k) := by
      nlinarith
    exact Nat.cast_lt.mp (by rw [hL, hR]; exact hint)
  rw [hu, hσ]
  have hN : 7 * ((p ^ (k + 1) - 1) / (p - 1)) = 7 * (p ^ (k + 1) - 1) / (p - 1) :=
    (Nat.mul_div_assoc 7 hdiv).symm
  rw [hN, hsucc]
  refine Nat.lt_of_mul_lt_mul_left (a := p - 1) ?_
  have hcancel :
      (p - 1) * (7 * (p * p ^ k - 1) / (p - 1)) = 7 * (p * p ^ k - 1) :=
    Nat.mul_div_cancel' (by simpa [hsucc] using hdiv.mul_left 7)
  rw [hcancel]
  convert hmain using 1
  ring

lemma not_seven_sigma_eq_ten_usigma_prime_pow_ge_five {p k : ℕ}
    (hp : p.Prime) (hp5 : 5 ≤ p) (hk : 0 < k) :
    ¬ 7 * σ 1 (p ^ k) = 10 * usigma (p ^ k) := by
  intro h
  have := seven_sigma_lt_ten_usigma_prime_pow_ge_five hp hp5 hk
  omega

/-- A squarefree leftover cannot satisfy `7 σ = 10 usigma`. -/
lemma not_squarefree_of_seven_sigma {m : ℕ} (hm : 0 < m)
    (h : 7 * σ 1 m = 10 * usigma m) : ¬ Squarefree m := by
  intro hs
  have hσu := (sigma_eq_usigma_iff_squarefree hm).mpr hs
  rw [hσu] at h
  have hpos : 0 < usigma m := by
    rw [← hσu]
    exact sigma_pos_iff.mpr hm
  have : 7 = 10 := Nat.eq_of_mul_eq_mul_right hpos h
  contradiction

/-- Caps of `{5, 11}` cannot reach leftover `10/7`. -/
lemma five_eleven_cap_lt_ten_seven : 5 * 11 * 7 < 10 * 4 * 10 := by decide

/-- Caps of `{7, 11}` cannot reach leftover `10/7`. -/
lemma seven_eleven_cap_lt_ten_seven : 7 * 11 * 7 < 10 * 6 * 10 := by decide

/-- `ρ(25) · 7/6 < 10/7`. -/
lemma twenty_five_seven_cap_lt_ten_seven : 31 * 7 * 7 < 10 * 26 * 6 := by decide

/-- `5/4 · ρ(49) < 10/7`. -/
lemma five_cap_forty_nine_lt_ten_seven : 5 * 57 * 7 < 10 * 4 * 50 := by decide

/-- `ρ(125) ρ(343) > 10/7`. -/
lemma five_pow_three_seven_pow_three_overshoot :
    10 * usigma (5 ^ 3) * usigma (7 ^ 3) < 7 * σ 1 (5 ^ 3) * σ 1 (7 ^ 3) := by
  have hu5 : usigma (5 ^ 3) = 1 + 5 ^ 3 :=
    usigma_prime_pow Nat.prime_five (by decide : 0 < 3)
  have hu7 : usigma (7 ^ 3) = 1 + 7 ^ 3 :=
    usigma_prime_pow (by decide : Nat.Prime 7) (by decide : 0 < 3)
  have hσ5 : σ 1 (5 ^ 3) = (5 ^ 4 - 1) / 4 := sigma_prime_pow_div Nat.prime_five
  have hσ7 : σ 1 (7 ^ 3) = (7 ^ 4 - 1) / 6 :=
    sigma_prime_pow_div (by decide : Nat.Prime 7)
  rw [hu5, hu7, hσ5, hσ7]
  norm_num

lemma sigma_prime_pow_two {p : ℕ} (hp : p.Prime) :
    σ 1 (p ^ 2) = 1 + p + p ^ 2 := by
  rw [sigma_one_apply_prime_pow hp, sum_range_succ, sum_range_succ, sum_range_succ]
  simp [pow_zero, pow_one, pow_two]

/-- `97(p^2+1) < 12103 p` for `13 ≤ p ≤ 113`. -/
lemma ninety_seven_mul_sq_succ_lt {p : ℕ} (hp : 13 ≤ p) (hp' : p ≤ 113) :
    97 * (p ^ 2 + 1) < 12103 * p := by
  have hsq : p ^ 2 ≤ 113 * p := by
    rw [pow_two, mul_comm 113]
    exact Nat.mul_le_mul_left p hp'
  have hle : 97 * (p ^ 2 + 1) ≤ 97 * (113 * p + 1) :=
    Nat.mul_le_mul_left 97 (Nat.add_le_add_right hsq 1)
  have hcoeff : 97 * 113 = 10961 := by decide
  have h1142 : 10961 + 1142 = 12103 := by decide
  have h97 : 97 < 1142 * p := by
    have : 1142 * 13 = 14846 := by decide
    nlinarith
  have hlin : 97 * (113 * p + 1) < 12103 * p := by
    have hex : 97 * (113 * p + 1) = 10961 * p + 97 := by
      rw [mul_add, ← mul_assoc, hcoeff]
    rw [hex]
    have : 10961 * p + 97 < 10961 * p + 1142 * p := Nat.add_lt_add_left h97 _
    have hsum : 10961 * p + 1142 * p = 12103 * p := by
      rw [← add_mul, h1142]
    omega
  omega

lemma twelve_two_usigma_lt_sigma_sq {p : ℕ} (hp : 13 ≤ p) (hp' : p ≤ 113) :
    12200 * (1 + p ^ 2) < 12103 * (1 + p + p ^ 2) := by
  have h := ninety_seven_mul_sq_succ_lt hp hp'
  nlinarith

lemma twelve_two_usigma_lt_sigma_pow_two {p : ℕ} (hp : p.Prime)
    (h13 : 13 ≤ p) (h113 : p ≤ 113) :
    12200 * usigma (p ^ 2) < 12103 * σ 1 (p ^ 2) := by
  have hu : usigma (p ^ 2) = 1 + p ^ 2 := usigma_prime_pow hp (by decide : 0 < 2)
  rw [hu, sigma_prime_pow_two hp]
  exact twelve_two_usigma_lt_sigma_sq h13 h113

/-- Closed form of leftover `12200/12103` overshoot for `13 ≤ p ≤ 113` and `k ≥ 2`. -/
lemma twelve_two_usigma_lt_sigma_prime_pow {p k : ℕ} (hp : p.Prime)
    (h13 : 13 ≤ p) (h113 : p ≤ 113) (hk : 2 ≤ k) :
    12200 * usigma (p ^ k) < 12103 * σ 1 (p ^ k) := by
  have hk0 : 0 < k := by omega
  have hu : usigma (p ^ k) = 1 + p ^ k := usigma_prime_pow hp hk0
  have hσ : σ 1 (p ^ k) = (p ^ (k + 1) - 1) / (p - 1) := sigma_prime_pow_div hp
  have hdiv : p - 1 ∣ p ^ (k + 1) - 1 := sub_one_dvd_pow_sub_one
  have hP : p ^ 2 ≤ p ^ k := Nat.pow_le_pow_right hp.one_le hk
  have hsucc : p ^ (k + 1) = p * p ^ k := by rw [Nat.pow_succ']
  have hpos : 1 ≤ p * p ^ k :=
    Nat.succ_le_of_lt (Nat.mul_pos hp.pos (Nat.pow_pos hp.pos))
  have hp1 : 1 ≤ p := hp.one_le
  have hmain : 12200 * (p - 1) * (1 + p ^ k) < 12103 * (p * p ^ k - 1) := by
    have hp13' : (13 : ℤ) ≤ p := Int.ofNat_le.mpr h13
    have hp113' : (p : ℤ) ≤ 113 := Int.ofNat_le.mpr h113
    have hP' : (p : ℤ) ^ 2 ≤ (p : ℤ) ^ k := by exact_mod_cast hP
    have hL : ((12200 * (p - 1) * (1 + p ^ k) : ℕ) : ℤ) =
        12200 * ((p : ℤ) - 1) * (1 + p ^ k) := by
      rw [Nat.cast_mul, Nat.cast_mul, Nat.cast_sub hp1]
      push_cast; rfl
    have hR : ((12103 * (p * p ^ k - 1) : ℕ) : ℤ) =
        12103 * ((p : ℤ) * p ^ k - 1) := by
      rw [Nat.cast_mul, Nat.cast_sub hpos]
      push_cast; rfl
    have hint : (12200 : ℤ) * ((p : ℤ) - 1) * (1 + p ^ k) <
        12103 * ((p : ℤ) * p ^ k - 1) := by
      nlinarith
    exact Nat.cast_lt.mp (by rw [hL, hR]; exact hint)
  rw [hu, hσ]
  have hN : 12103 * ((p ^ (k + 1) - 1) / (p - 1)) =
      12103 * (p ^ (k + 1) - 1) / (p - 1) :=
    (Nat.mul_div_assoc 12103 hdiv).symm
  rw [hN, hsucc]
  refine Nat.lt_of_mul_lt_mul_left (a := p - 1) ?_
  have hcancel :
      (p - 1) * (12103 * (p * p ^ k - 1) / (p - 1)) =
        12103 * (p * p ^ k - 1) :=
    Nat.mul_div_cancel' (by simpa [hsucc] using hdiv.mul_left 12103)
  rw [hcancel]
  convert hmain using 1
  ring

lemma padicValNat_lt_two_of_twelve_thousand_le_113 {u p : ℕ} (hu : u ≠ 0)
    (hp : p.Prime) (h13 : 13 ≤ p) (h113 : p ≤ 113)
    (h : 12103 * σ 1 u = 12200 * usigma u) :
    padicValNat p u < 2 := by
  by_contra! hk
  have hproj : ordProj[p] u = p ^ padicValNat p u := by
    simp [Nat.factorization_def u hp]
  have hle := mul_sigma_ordProj_le hp hu h
  rw [hproj] at hle
  have hover := twelve_two_usigma_lt_sigma_prime_pow hp h13 h113 hk
  omega

/-- `127/126 < 12200/12103`, hence every prime `p ≥ 127` has cap below leftover. -/
lemma cap_lt_twelve_thousand {p : ℕ} (hp : 127 ≤ p) :
    12103 * p < 12200 * (p - 1) := by
  have hp1 : 1 ≤ p := by omega
  have hsub : 12200 * (p - 1) = 12200 * p - 12200 :=
    Nat.mul_sub_left_distrib 12200 p 1
  have h97 : 12200 < 97 * p := by
    have : 97 * 127 = 12319 := by decide
    nlinarith
  have hadd : 12103 * p + 12200 < 12200 * p := by
    have : 12103 * p + 97 * p = 12200 * p := by
      rw [← add_mul, show (12103 + 97 : ℕ) = 12200 by decide]
    have : 12103 * p + 12200 < 12103 * p + 97 * p := Nat.add_lt_add_left h97 _
    omega
  have hle : 12200 ≤ 12200 * p := Nat.le_mul_of_pos_right 12200 (by omega)
  rw [hsub]
  exact Nat.lt_sub_of_add_lt hadd

/-- `ρ(p^k) < p/(p-1)` for `k > 0`. -/
lemma sigma_lt_cap_usigma {p k : ℕ} (hp : p.Prime) (hk : 0 < k) :
    (p - 1) * σ 1 (p ^ k) < p * usigma (p ^ k) := by
  have hu : usigma (p ^ k) = 1 + p ^ k := usigma_prime_pow hp hk
  have hσ : σ 1 (p ^ k) = (p ^ (k + 1) - 1) / (p - 1) := sigma_prime_pow_div hp
  have hdiv : p - 1 ∣ p ^ (k + 1) - 1 := sub_one_dvd_pow_sub_one
  have hp1 : 1 ≤ p := hp.one_le
  have hsucc : p ^ (k + 1) = p * p ^ k := by rw [Nat.pow_succ']
  have hpos : 1 ≤ p * p ^ k :=
    Nat.succ_le_of_lt (Nat.mul_pos hp.pos (Nat.pow_pos hp.pos))
  rw [hu, hσ, Nat.mul_div_cancel' hdiv, hsucc]
  have : p * p ^ k - 1 < p * (1 + p ^ k) := by
    have hL : ((p * p ^ k - 1 : ℕ) : ℤ) = (p : ℤ) * p ^ k - 1 := by
      rw [Nat.cast_sub hpos]; push_cast; rfl
    have hR : ((p * (1 + p ^ k) : ℕ) : ℤ) = (p : ℤ) * (1 + p ^ k) := by
      push_cast; rfl
    have : (p : ℤ) * p ^ k - 1 < p * (1 + p ^ k) := by nlinarith
    exact Nat.cast_lt.mp (by rw [hL, hR]; exact this)
  exact this

/-- If the `p`-free part is squarefree, leftover `10/7` is concentrated on `p^k`. -/
lemma seven_sigma_eq_ten_of_squarefree_ordCompl {m p : ℕ} (hm : m ≠ 0)
    (hp : p.Prime) (h : 7 * σ 1 m = 10 * usigma m)
    (hs : Squarefree (ordCompl[p] m)) :
    7 * σ 1 (ordProj[p] m) = 10 * usigma (ordProj[p] m) := by
  have hdecomp : ordProj[p] m * ordCompl[p] m = m :=
    Nat.ordProj_mul_ordCompl_eq_self m p
  have hc : Coprime (ordProj[p] m) (ordCompl[p] m) :=
    (Nat.coprime_ordCompl hp hm).pow_left (m.factorization p)
  have hmul : 7 * σ 1 (ordProj[p] m) * σ 1 (ordCompl[p] m) =
      10 * usigma (ordProj[p] m) * usigma (ordCompl[p] m) := by
    have := h
    rw [← hdecomp, sigma_mul_of_coprime hc, usigma_mul hc] at this
    simpa [mul_assoc, mul_left_comm, mul_comm] using this
  have hσu := (sigma_eq_usigma_iff_squarefree (Nat.ordCompl_pos p hm)).mpr hs
  rw [hσu] at hmul
  have hpos : 0 < usigma (ordCompl[p] m) := by
    rw [← hσu]
    exact sigma_pos_iff.mpr (Nat.ordCompl_pos p hm)
  exact Nat.eq_of_mul_eq_mul_right hpos hmul

/-- Leftover `10/7` cannot be a single prime power `p^k` with `p ≥ 5`. -/
lemma not_seven_sigma_of_unique_sq_prime_ge_five {m p : ℕ} (hm : m ≠ 0)
    (hp : p.Prime) (hp5 : 5 ≤ p) (h : 7 * σ 1 m = 10 * usigma m)
    (hk : 0 < padicValNat p m) (hs : Squarefree (ordCompl[p] m)) : False := by
  have heq := seven_sigma_eq_ten_of_squarefree_ordCompl hm hp h hs
  have hproj : ordProj[p] m = p ^ padicValNat p m := by
    simp [Nat.factorization_def m hp]
  rw [hproj] at heq
  exact not_seven_sigma_eq_ten_usigma_prime_pow_ge_five hp hp5 hk heq

lemma six_sigma_lt_seven_usigma {k : ℕ} (hk : 0 < k) :
    6 * σ 1 (7 ^ k) < 7 * usigma (7 ^ k) :=
  sigma_lt_cap_usigma (by decide : Nat.Prime 7) hk

lemma four_sigma_lt_five_usigma {k : ℕ} (hk : 0 < k) :
    4 * σ 1 (5 ^ k) < 5 * usigma (5 ^ k) :=
  sigma_lt_cap_usigma Nat.prime_five hk

/-- Numerator comparison for `ρ(p^{a+1}) > ρ(p^a)`.
The difference of the two sides is `p^a (p^2 - 1)`. -/
lemma geom_ratio_strict_mono {p a : ℕ} (hp : 2 ≤ p) (_ha : 0 < a) :
    (p ^ (a + 1) - 1) * (p ^ (a + 1) + 1) <
      (p ^ (a + 2) - 1) * (p ^ a + 1) := by
  have hx : 1 ≤ p ^ (a + 1) := Nat.one_le_pow (a + 1) p (by omega)
  have hy : 1 ≤ p ^ (a + 2) := Nat.one_le_pow (a + 2) p (by omega)
  have hL : (((p ^ (a + 1) - 1) * (p ^ (a + 1) + 1) : ℕ) : ℤ) =
      ((p : ℤ) ^ (a + 1) - 1) * ((p : ℤ) ^ (a + 1) + 1) := by
    rw [Nat.cast_mul, Nat.cast_sub hx, Nat.cast_add, Nat.cast_one]
    push_cast; rfl
  have hR : (((p ^ (a + 2) - 1) * (p ^ a + 1) : ℕ) : ℤ) =
      ((p : ℤ) ^ (a + 2) - 1) * ((p : ℤ) ^ a + 1) := by
    rw [Nat.cast_mul, Nat.cast_sub hy, Nat.cast_add, Nat.cast_one]
    push_cast; rfl
  have hdiff :
      ((p : ℤ) ^ (a + 2) - 1) * ((p : ℤ) ^ a + 1) -
        ((p : ℤ) ^ (a + 1) - 1) * ((p : ℤ) ^ (a + 1) + 1) =
      (p : ℤ) ^ a * ((p : ℤ) ^ 2 - 1) := by
    have h1 : (p : ℤ) ^ (a + 1) = p * p ^ a := _root_.pow_succ' (p : ℤ) a
    have h2 : (p : ℤ) ^ (a + 2) = p * p * p ^ a := by
      have : a + 2 = a + 1 + 1 := by omega
      rw [this, _root_.pow_succ' (p : ℤ) (a + 1), h1]
      ring
    rw [h1, h2]
    ring
  have hpos : (0 : ℤ) < (p : ℤ) ^ a * ((p : ℤ) ^ 2 - 1) := by
    have hp' : (2 : ℤ) ≤ p := Int.ofNat_le.mpr hp
    have hpa : (0 : ℤ) < p ^ a := by
      have : 0 < p ^ a := Nat.pow_pos (by omega : 0 < p)
      exact_mod_cast this
    have hsq : (p : ℤ) ^ 2 = p * p := sq (p : ℤ)
    have h4 : (4 : ℤ) ≤ p * p :=
      mul_le_mul hp' hp' (by linarith) (by linarith)
    have hdiffpos : (0 : ℤ) < p ^ 2 - 1 := by
      rw [hsq]
      linarith
    exact mul_pos hpa hdiffpos
  have hint : ((p : ℤ) ^ (a + 1) - 1) * ((p : ℤ) ^ (a + 1) + 1) <
      ((p : ℤ) ^ (a + 2) - 1) * ((p : ℤ) ^ a + 1) := by
    linarith
  exact Nat.cast_lt.mp (by rw [hL, hR]; exact hint)

lemma sigma_usigma_ratio_strict_mono {p a : ℕ} (hp : p.Prime) (ha : 0 < a) :
    σ 1 (p ^ a) * usigma (p ^ (a + 1)) <
      σ 1 (p ^ (a + 1)) * usigma (p ^ a) := by
  have hu1 : usigma (p ^ a) = 1 + p ^ a := usigma_prime_pow hp ha
  have hu2 : usigma (p ^ (a + 1)) = 1 + p ^ (a + 1) :=
    usigma_prime_pow hp (Nat.succ_pos a)
  have hσ1 : σ 1 (p ^ a) = (p ^ (a + 1) - 1) / (p - 1) := sigma_prime_pow_div hp
  have hσ2 : σ 1 (p ^ (a + 1)) = (p ^ (a + 2) - 1) / (p - 1) :=
    sigma_prime_pow_div hp
  have hdiv1 : p - 1 ∣ p ^ (a + 1) - 1 := sub_one_dvd_pow_sub_one
  have hdiv2 : p - 1 ∣ p ^ (a + 2) - 1 := sub_one_dvd_pow_sub_one
  have hgeom := geom_ratio_strict_mono hp.two_le ha
  rw [hu1, hu2, hσ1, hσ2]
  have hN1 : (1 + p ^ (a + 1)) * ((p ^ (a + 1) - 1) / (p - 1)) =
      (1 + p ^ (a + 1)) * (p ^ (a + 1) - 1) / (p - 1) :=
    (Nat.mul_div_assoc _ hdiv1).symm
  have hN2 : (1 + p ^ a) * ((p ^ (a + 2) - 1) / (p - 1)) =
      (1 + p ^ a) * (p ^ (a + 2) - 1) / (p - 1) :=
    (Nat.mul_div_assoc _ hdiv2).symm
  rw [mul_comm ((p ^ (a + 1) - 1) / (p - 1)),
    mul_comm ((p ^ (a + 2) - 1) / (p - 1)), hN1, hN2]
  refine Nat.lt_of_mul_lt_mul_left (a := p - 1) ?_
  have hc1 : (p - 1) * ((1 + p ^ (a + 1)) * (p ^ (a + 1) - 1) / (p - 1)) =
      (1 + p ^ (a + 1)) * (p ^ (a + 1) - 1) :=
    Nat.mul_div_cancel' (hdiv1.mul_left _)
  have hc2 : (p - 1) * ((1 + p ^ a) * (p ^ (a + 2) - 1) / (p - 1)) =
      (1 + p ^ a) * (p ^ (a + 2) - 1) :=
    Nat.mul_div_cancel' (hdiv2.mul_left _)
  rw [hc1, hc2]
  simpa [mul_comm, add_comm] using hgeom

lemma sigma_usigma_ratio_le_of_le {p a b : ℕ} (hp : p.Prime) (ha : 0 < a)
    (hab : a ≤ b) :
    σ 1 (p ^ a) * usigma (p ^ b) ≤ σ 1 (p ^ b) * usigma (p ^ a) := by
  obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_le hab
  subst b
  clear hab
  induction k with
  | zero => simp
  | succ k ih =>
    have hkpos : 0 < a + k := by omega
    have hstrict := (sigma_usigma_ratio_strict_mono hp hkpos).le
    have hu : 0 < usigma (p ^ (a + k)) := by
      rw [usigma_prime_pow hp hkpos]
      exact Nat.add_pos_left (by decide : 0 < 1) _
    have h1 : σ 1 (p ^ a) * usigma (p ^ (a + k)) * usigma (p ^ (a + k + 1)) ≤
        σ 1 (p ^ (a + k)) * usigma (p ^ a) * usigma (p ^ (a + k + 1)) :=
      Nat.mul_le_mul_right _ ih
    have h2 : σ 1 (p ^ (a + k)) * usigma (p ^ (a + k + 1)) * usigma (p ^ a) ≤
        σ 1 (p ^ (a + k + 1)) * usigma (p ^ (a + k)) * usigma (p ^ a) :=
      Nat.mul_le_mul_right _ hstrict
    have : σ 1 (p ^ a) * usigma (p ^ (a + k + 1)) * usigma (p ^ (a + k)) ≤
        σ 1 (p ^ (a + k + 1)) * usigma (p ^ a) * usigma (p ^ (a + k)) := by
      have h1' : σ 1 (p ^ a) * usigma (p ^ (a + k + 1)) * usigma (p ^ (a + k)) ≤
          σ 1 (p ^ (a + k)) * usigma (p ^ a) * usigma (p ^ (a + k + 1)) := by
        simpa [mul_assoc, mul_left_comm, mul_comm] using h1
      have h2' : σ 1 (p ^ (a + k)) * usigma (p ^ a) * usigma (p ^ (a + k + 1)) ≤
          σ 1 (p ^ (a + k + 1)) * usigma (p ^ a) * usigma (p ^ (a + k)) := by
        simpa [mul_assoc, mul_left_comm, mul_comm] using h2
      exact le_trans h1' h2'
    exact Nat.le_of_mul_le_mul_right this hu

/-- `ρ(25) ρ(7^b) < 10/7`. -/
lemma twenty_five_seven_pow_lt_ten_seven {b : ℕ} (hb : 0 < b) :
    7 * σ 1 (5 ^ 2) * σ 1 (7 ^ b) < 10 * usigma (5 ^ 2) * usigma (7 ^ b) := by
  have hσ5 : σ 1 (5 ^ 2) = 31 := by
    rw [sigma_prime_pow_two Nat.prime_five]
    decide
  have hu5 : usigma (5 ^ 2) = 26 := usigma_five_pow_two
  rw [hσ5, hu5]
  have hcap : (6 : ℤ) * σ 1 (7 ^ b) < 7 * usigma (7 ^ b) := by
    exact_mod_cast six_sigma_lt_seven_usigma hb
  have hσpos : (0 : ℤ) < σ 1 (7 ^ b) := by
    exact_mod_cast (sigma_pos_iff.mpr (pow_pos (by decide : 0 < 7) b))
  have hupos : (0 : ℤ) < usigma (7 ^ b) := by
    have : 0 < usigma (7 ^ b) := by
      rw [usigma_prime_pow (by decide : Nat.Prime 7) hb]
      exact Nat.add_pos_left (by decide : 0 < 1) _
    exact_mod_cast this
  have hint : (7 : ℤ) * 31 * σ 1 (7 ^ b) < 10 * 26 * usigma (7 ^ b) := by
    nlinarith
  exact_mod_cast hint

/-- `ρ(5^a) ρ(49) < 10/7`. -/
lemma five_pow_forty_nine_lt_ten_seven {a : ℕ} (ha : 0 < a) :
    7 * σ 1 (5 ^ a) * σ 1 (7 ^ 2) < 10 * usigma (5 ^ a) * usigma (7 ^ 2) := by
  have hp7 : Nat.Prime 7 := by decide
  have hσ7 : σ 1 (7 ^ 2) = 57 := by
    rw [sigma_prime_pow_two hp7]
    decide
  have hu7 : usigma (7 ^ 2) = 50 := by
    simpa using usigma_prime_pow hp7 (by decide : 0 < 2)
  rw [hσ7, hu7]
  have hcap : (4 : ℤ) * σ 1 (5 ^ a) < 5 * usigma (5 ^ a) := by
    exact_mod_cast four_sigma_lt_five_usigma ha
  have hσpos : (0 : ℤ) < σ 1 (5 ^ a) := by
    exact_mod_cast (sigma_pos_iff.mpr (pow_pos (by decide : 0 < 5) a))
  have hupos : (0 : ℤ) < usigma (5 ^ a) := by
    have : 0 < usigma (5 ^ a) := by
      rw [usigma_prime_pow Nat.prime_five ha]
      exact Nat.add_pos_left (by decide : 0 < 1) _
    exact_mod_cast this
  have hint : (7 : ℤ) * σ 1 (5 ^ a) * 57 < 10 * usigma (5 ^ a) * 50 := by
    nlinarith
  exact_mod_cast hint

/-- `ρ(5^a) ρ(7^b) > 10/7` for `a ≥ 3` and `b ≥ 3`. -/
lemma five_seven_pow_ge_three_overshoot {a b : ℕ} (ha : 3 ≤ a) (hb : 3 ≤ b) :
    10 * usigma (5 ^ a) * usigma (7 ^ b) < 7 * σ 1 (5 ^ a) * σ 1 (7 ^ b) := by
  have ha0 : 0 < a := by omega
  have hb0 : 0 < b := by omega
  have hp7 : Nat.Prime 7 := by decide
  have h5 := sigma_usigma_ratio_le_of_le Nat.prime_five (by decide : 0 < 3) ha
  have h7 := sigma_usigma_ratio_le_of_le hp7 (by decide : 0 < 3) hb
  have hover := five_pow_three_seven_pow_three_overshoot
  have hu53 : 0 < usigma (5 ^ 3) := by
    rw [usigma_prime_pow Nat.prime_five (by decide : 0 < 3)]
    exact Nat.add_pos_left (by decide : 0 < 1) _
  have hu73 : 0 < usigma (7 ^ 3) := by
    rw [usigma_prime_pow hp7 (by decide : 0 < 3)]
    exact Nat.add_pos_left (by decide : 0 < 1) _
  have hu5 : 0 < usigma (5 ^ a) := by
    rw [usigma_prime_pow Nat.prime_five ha0]
    exact Nat.add_pos_left (by decide : 0 < 1) _
  have hu7 : 0 < usigma (7 ^ b) := by
    rw [usigma_prime_pow hp7 hb0]
    exact Nat.add_pos_left (by decide : 0 < 1) _
  have hσ53 : 0 < σ 1 (5 ^ 3) := sigma_pos_iff.mpr (by decide)
  have hσ73 : 0 < σ 1 (7 ^ 3) := sigma_pos_iff.mpr (by decide)
  -- σ(5^3) u(5^a) ≤ σ(5^a) u(5^3), similarly for 7.
  have hmul : σ 1 (5 ^ 3) * σ 1 (7 ^ 3) * usigma (5 ^ a) * usigma (7 ^ b) ≤
      σ 1 (5 ^ a) * σ 1 (7 ^ b) * usigma (5 ^ 3) * usigma (7 ^ 3) := by
    have h5' : σ 1 (5 ^ 3) * usigma (5 ^ a) * (σ 1 (7 ^ 3) * usigma (7 ^ b)) ≤
        σ 1 (5 ^ a) * usigma (5 ^ 3) * (σ 1 (7 ^ 3) * usigma (7 ^ b)) :=
      Nat.mul_le_mul_right _ h5
    have h7' : σ 1 (5 ^ a) * usigma (5 ^ 3) * (σ 1 (7 ^ 3) * usigma (7 ^ b)) ≤
        σ 1 (5 ^ a) * usigma (5 ^ 3) * (σ 1 (7 ^ b) * usigma (7 ^ 3)) :=
      Nat.mul_le_mul_left _ h7
    have := le_trans h5' (by simpa [mul_assoc, mul_left_comm, mul_comm] using h7')
    simpa [mul_assoc, mul_left_comm, mul_comm] using this
  have h7mul : 7 * σ 1 (5 ^ 3) * σ 1 (7 ^ 3) * usigma (5 ^ a) * usigma (7 ^ b) ≤
      7 * σ 1 (5 ^ a) * σ 1 (7 ^ b) * usigma (5 ^ 3) * usigma (7 ^ 3) := by
    simpa [mul_assoc, mul_left_comm, mul_comm] using Nat.mul_le_mul_left 7 hmul
  have h10 : 10 * usigma (5 ^ 3) * usigma (7 ^ 3) * usigma (5 ^ a) * usigma (7 ^ b) <
      7 * σ 1 (5 ^ 3) * σ 1 (7 ^ 3) * usigma (5 ^ a) * usigma (7 ^ b) := by
    have := Nat.mul_lt_mul_of_pos_right hover (mul_pos hu5 hu7)
    simpa [mul_assoc, mul_left_comm, mul_comm] using this
  have hchain : 10 * usigma (5 ^ a) * usigma (7 ^ b) * usigma (5 ^ 3) * usigma (7 ^ 3) <
      7 * σ 1 (5 ^ a) * σ 1 (7 ^ b) * usigma (5 ^ 3) * usigma (7 ^ 3) :=
    lt_of_lt_of_le (by simpa [mul_assoc, mul_left_comm, mul_comm] using h10) h7mul
  have hpos : 0 < usigma (5 ^ 3) * usigma (7 ^ 3) := mul_pos hu53 hu73
  exact Nat.lt_of_mul_lt_mul_right (a := usigma (5 ^ 3) * usigma (7 ^ 3))
    (by simpa [mul_assoc, mul_left_comm, mul_comm] using hchain)

lemma not_seven_sigma_eq_ten_usigma_five_seven {a b : ℕ} (ha : 2 ≤ a) (hb : 2 ≤ b) :
    ¬ 7 * σ 1 (5 ^ a) * σ 1 (7 ^ b) = 10 * usigma (5 ^ a) * usigma (7 ^ b) := by
  intro heq
  rcases eq_or_lt_of_le ha with ha2 | ha3
  · rw [← ha2] at heq
    exact (twenty_five_seven_pow_lt_ten_seven (by omega)).ne heq
  · rcases eq_or_lt_of_le hb with hb2 | hb3
    · rw [← hb2] at heq
      exact (five_pow_forty_nine_lt_ten_seven (by omega)).ne heq
    · have hover := five_seven_pow_ge_three_overshoot (Nat.succ_le_of_lt ha3)
        (Nat.succ_le_of_lt hb3)
      rw [← heq] at hover
      exact lt_irrefl _ hover

/-- If two Euler-product caps multiply below leftover `10/7`, the product
of the two prime-power ratios is strictly below leftover `10/7`. -/
lemma seven_ten_of_two_caps {A B X Y C D P Q : ℕ}
    (hA : A * X < B * Y) (hC : C * P < D * Q)
    (hcap : 7 * B * D ≤ 10 * A * C)
    (hB : 0 < B) (hY : 0 < Y) :
    7 * X * P < 10 * Y * Q := by
  have hprod : (A * X) * (C * P) < (B * Y) * (D * Q) :=
    Nat.mul_lt_mul_of_le_of_lt (Nat.le_of_lt hA) hC (Nat.mul_pos hB hY)
  have h7 : 7 * ((A * X) * (C * P)) < 7 * ((B * Y) * (D * Q)) :=
    Nat.mul_lt_mul_of_pos_left hprod (by decide)
  have h10 : 7 * B * D * (Y * Q) ≤ 10 * A * C * (Y * Q) :=
    Nat.mul_le_mul_right (Y * Q) hcap
  have hchain : 7 * A * C * X * P < 10 * A * C * Y * Q := by
    have hL : 7 * A * C * X * P = 7 * ((A * X) * (C * P)) := by ring
    have hmid : 7 * ((B * Y) * (D * Q)) = 7 * B * D * (Y * Q) := by ring
    have hR : 7 * B * D * (Y * Q) ≤ 10 * A * C * Y * Q := by
      simpa [mul_assoc, mul_left_comm, mul_comm] using h10
    calc
      7 * A * C * X * P = 7 * ((A * X) * (C * P)) := hL
      _ < 7 * ((B * Y) * (D * Q)) := h7
      _ = 7 * B * D * (Y * Q) := hmid
      _ ≤ 10 * A * C * Y * Q := hR
  have hcancel : A * C * (7 * X * P) < A * C * (10 * Y * Q) := by
    have h1 : A * C * (7 * X * P) = 7 * A * C * X * P := by ring
    have h2 : A * C * (10 * Y * Q) = 10 * A * C * Y * Q := by ring
    rw [h1, h2]
    exact hchain
  exact Nat.lt_of_mul_lt_mul_left hcancel

lemma seven_p_q_cap {p q : ℕ} (hp : 7 ≤ p) (hq : 11 ≤ q) (hp1 : 1 ≤ p)
    (hq1 : 1 ≤ q) : 7 * p * q ≤ 10 * (p - 1) * (q - 1) := by
  have hp' : (7 : ℤ) ≤ p := Int.ofNat_le.mpr hp
  have hq' : (11 : ℤ) ≤ q := Int.ofNat_le.mpr hq
  have hL : ((7 * p * q : ℕ) : ℤ) = 7 * (p : ℤ) * q := by push_cast; rfl
  have hR : ((10 * (p - 1) * (q - 1) : ℕ) : ℤ) =
      10 * ((p : ℤ) - 1) * ((q : ℤ) - 1) := by
    rw [Nat.cast_mul, Nat.cast_mul, Nat.cast_sub hp1, Nat.cast_sub hq1]
    push_cast; rfl
  have : (7 : ℤ) * p * q ≤ 10 * (p - 1) * (q - 1) := by nlinarith
  exact Nat.cast_le.mp (by rw [hL, hR]; exact this)

lemma seven_five_q_cap {q : ℕ} (hq : 11 ≤ q) (hq1 : 1 ≤ q) :
    7 * 5 * q ≤ 10 * 4 * (q - 1) := by
  have hq' : (11 : ℤ) ≤ q := Int.ofNat_le.mpr hq
  have hL : ((7 * 5 * q : ℕ) : ℤ) = 7 * 5 * (q : ℤ) := by push_cast; rfl
  have hR : ((10 * 4 * (q - 1) : ℕ) : ℤ) = 10 * 4 * ((q : ℤ) - 1) := by
    rw [Nat.cast_mul, Nat.cast_mul, Nat.cast_sub hq1]
    push_cast; rfl
  have : (7 : ℤ) * 5 * q ≤ 10 * 4 * (q - 1) := by nlinarith
  exact Nat.cast_le.mp (by rw [hL, hR]; exact this)

/-- If `p ≥ 7` and `q ≥ 11`, the caps cannot reach leftover `10/7`. -/
lemma seven_sigma_lt_ten_usigma_two_large {p q a b : ℕ}
    (hp : p.Prime) (hq : q.Prime) (hp7 : 7 ≤ p) (hq11 : 11 ≤ q)
    (ha : 0 < a) (hb : 0 < b) :
    7 * σ 1 (p ^ a) * σ 1 (q ^ b) < 10 * usigma (p ^ a) * usigma (q ^ b) := by
  have hcp := sigma_lt_cap_usigma hp ha
  have hcq := sigma_lt_cap_usigma hq hb
  have hup : 0 < usigma (p ^ a) := by
    rw [usigma_prime_pow hp ha]
    exact Nat.add_pos_left (by decide : 0 < 1) _
  have hcap := seven_p_q_cap hp7 hq11 hp.one_le hq.one_le
  have := seven_ten_of_two_caps (A := p - 1) (B := p) (X := σ 1 (p ^ a))
    (Y := usigma (p ^ a)) (C := q - 1) (D := q) (P := σ 1 (q ^ b))
    (Q := usigma (q ^ b)) hcp hcq hcap hp.pos hup
  simpa [mul_assoc] using this

/-- If `p = 5` and `q ≥ 11`, the caps cannot reach leftover `10/7`. -/
lemma seven_sigma_lt_ten_usigma_five_and_large {q a b : ℕ}
    (hq : q.Prime) (hq11 : 11 ≤ q) (ha : 0 < a) (hb : 0 < b) :
    7 * σ 1 (5 ^ a) * σ 1 (q ^ b) < 10 * usigma (5 ^ a) * usigma (q ^ b) := by
  have hcp := four_sigma_lt_five_usigma ha
  have hcq := sigma_lt_cap_usigma hq hb
  have hup : 0 < usigma (5 ^ a) := by
    rw [usigma_prime_pow Nat.prime_five ha]
    exact Nat.add_pos_left (by decide : 0 < 1) _
  have hcap := seven_five_q_cap hq11 hq.one_le
  have := seven_ten_of_two_caps (A := 4) (B := 5) (X := σ 1 (5 ^ a))
    (Y := usigma (5 ^ a)) (C := q - 1) (D := q) (P := σ 1 (q ^ b))
    (Q := usigma (q ^ b)) hcp hcq hcap (by decide : 0 < 5) hup
  simpa [mul_assoc] using this

lemma padicValNat_ordCompl_of_ne {n p q : ℕ} (hq : q.Prime) (hpq : p ≠ q) :
    padicValNat q (ordCompl[p] n) = padicValNat q n := by
  rw [← Nat.factorization_def (ordCompl[p] n) hq,
    ← Nat.factorization_def n hq, Nat.factorization_ordCompl]
  exact Finsupp.erase_ne hpq.symm

/-- If the rest after two distinct prime powers is squarefree, leftover `10/7`
is concentrated on those two prime powers. -/
lemma seven_sigma_eq_ten_of_two_squareful {m p q : ℕ} (hm : m ≠ 0)
    (hp : p.Prime) (hq : q.Prime) (_hpq : p ≠ q)
    (h : 7 * σ 1 m = 10 * usigma m)
    (hs : Squarefree (ordCompl[q] (ordCompl[p] m))) :
    7 * σ 1 (ordProj[p] m) * σ 1 (ordProj[q] (ordCompl[p] m)) =
      10 * usigma (ordProj[p] m) * usigma (ordProj[q] (ordCompl[p] m)) := by
  set r := ordCompl[q] (ordCompl[p] m)
  have hm' : ordCompl[p] m ≠ 0 := (Nat.ordCompl_pos p hm).ne'
  have hdecomp_p : ordProj[p] m * ordCompl[p] m = m :=
    Nat.ordProj_mul_ordCompl_eq_self m p
  have hdecomp_q : ordProj[q] (ordCompl[p] m) * r = ordCompl[p] m :=
    Nat.ordProj_mul_ordCompl_eq_self (ordCompl[p] m) q
  have hc_p : Coprime (ordProj[p] m) (ordCompl[p] m) :=
    (Nat.coprime_ordCompl hp hm).pow_left (m.factorization p)
  have hc_q : Coprime (ordProj[q] (ordCompl[p] m)) r :=
    (Nat.coprime_ordCompl hq hm').pow_left ((ordCompl[p] m).factorization q)
  have hmul : 7 * σ 1 (ordProj[p] m) * σ 1 (ordProj[q] (ordCompl[p] m)) * σ 1 r =
      10 * usigma (ordProj[p] m) * usigma (ordProj[q] (ordCompl[p] m)) * usigma r := by
    have := h
    rw [← hdecomp_p, sigma_mul_of_coprime hc_p, usigma_mul hc_p] at this
    rw [← hdecomp_q, sigma_mul_of_coprime hc_q, usigma_mul hc_q] at this
    simpa [mul_assoc, mul_left_comm, mul_comm] using this
  have hσu := (sigma_eq_usigma_iff_squarefree (Nat.ordCompl_pos q hm')).mpr hs
  rw [hσu] at hmul
  have hpos : 0 < usigma r := by
    rw [← hσu]
    exact sigma_pos_iff.mpr (Nat.ordCompl_pos q hm')
  exact Nat.eq_of_mul_eq_mul_right hpos hmul

/-- Leftover `10/7` cannot be two squareful primes `p < q`, both at least `5`,
times a squarefree coprime factor. -/
lemma not_seven_sigma_of_two_sq_primes {m p q : ℕ} (hm : m ≠ 0)
    (hp : p.Prime) (hq : q.Prime) (hpq : p < q) (hp5 : 5 ≤ p)
    (h : 7 * σ 1 m = 10 * usigma m)
    (hkp : 2 ≤ padicValNat p m) (hkq : 2 ≤ padicValNat q m)
    (hs : Squarefree (ordCompl[q] (ordCompl[p] m))) : False := by
  have hpq_ne : p ≠ q := Nat.ne_of_lt hpq
  have heq := seven_sigma_eq_ten_of_two_squareful hm hp hq hpq_ne h hs
  have hproj_p : ordProj[p] m = p ^ padicValNat p m := by
    simp [Nat.factorization_def m hp]
  have hproj_q : ordProj[q] (ordCompl[p] m) =
      q ^ padicValNat q (ordCompl[p] m) := by
    simp [Nat.factorization_def (ordCompl[p] m) hq]
  rw [hproj_q, padicValNat_ordCompl_of_ne hq hpq_ne, hproj_p] at heq
  have ha : 0 < padicValNat p m := by omega
  have hb : 0 < padicValNat q m := by omega
  have hp_cases : p = 5 ∨ 7 ≤ p := by
    have : p = 5 ∨ 6 ≤ p := by omega
    rcases this with rfl | h6
    · exact Or.inl rfl
    · have : p ≠ 6 := fun h6eq => (by decide : ¬ Nat.Prime 6) (h6eq ▸ hp)
      exact Or.inr (by omega)
  rcases hp_cases with rfl | hp7
  · have hq7 : 7 ≤ q := by
      have : 6 ≤ q := by omega
      have : q ≠ 6 := fun h6eq => (by decide : ¬ Nat.Prime 6) (h6eq ▸ hq)
      omega
    have hq_cases : q = 7 ∨ 11 ≤ q := by
      have hmem : q = 7 ∨ q = 8 ∨ q = 9 ∨ q = 10 ∨ 11 ≤ q := by omega
      rcases hmem with rfl | rfl | rfl | rfl | h11
      · exact Or.inl rfl
      · cases (by decide : ¬ Nat.Prime 8) hq
      · cases (by decide : ¬ Nat.Prime 9) hq
      · cases (by decide : ¬ Nat.Prime 10) hq
      · exact Or.inr h11
    rcases hq_cases with rfl | hq11
    · exact not_seven_sigma_eq_ten_usigma_five_seven hkp hkq heq
    · exact (seven_sigma_lt_ten_usigma_five_and_large hq hq11 ha hb).ne heq
  · have hq11 : 11 ≤ q := by
      have : 8 ≤ q := by omega
      have hmem : q = 8 ∨ q = 9 ∨ q = 10 ∨ 11 ≤ q := by omega
      rcases hmem with rfl | rfl | rfl | h11
      · cases (by decide : ¬ Nat.Prime 8) hq
      · cases (by decide : ¬ Nat.Prime 9) hq
      · cases (by decide : ¬ Nat.Prime 10) hq
      · exact h11
    exact (seven_sigma_lt_ten_usigma_two_large hp hq hp7 hq11 ha hb).ne heq

/-- `p/(p-1)` is antitone for `p ≥ 2`. -/
lemma cap_ratio_anti {p p0 : ℕ} (_hp0 : 2 ≤ p0) (hle : p0 ≤ p) :
    p * (p0 - 1) ≤ p0 * (p - 1) := by
  have hL : p * (p0 - 1) = p * p0 - p := by
    simpa using Nat.mul_sub_left_distrib p p0 1
  have hR : p0 * (p - 1) = p0 * p - p0 := by
    simpa using Nat.mul_sub_left_distrib p0 p 1
  rw [hL, hR, mul_comm p0 p]
  exact Nat.sub_le_sub_left hle _

lemma seven_eleven_thirteen_cap : 7 * 7 * 11 * 13 ≤ 10 * 6 * 10 * 12 := by decide

lemma seven_p_q_r_cap {p q r : ℕ} (hp : 7 ≤ p) (hq : 11 ≤ q) (hr : 13 ≤ r) :
    7 * p * q * r ≤ 10 * (p - 1) * (q - 1) * (r - 1) := by
  have hp6 : p * 6 ≤ 7 * (p - 1) := cap_ratio_anti (by decide : 2 ≤ 7) hp
  have hq10 : q * 10 ≤ 11 * (q - 1) := cap_ratio_anti (by decide : 2 ≤ 11) hq
  have hr12 : r * 12 ≤ 13 * (r - 1) := cap_ratio_anti (by decide : 2 ≤ 13) hr
  have hprod : p * q * r * 6 * 10 * 12 ≤ 7 * 11 * 13 * (p - 1) * (q - 1) * (r - 1) := by
    have h1 : p * 6 * (q * 10) * (r * 12) ≤ 7 * (p - 1) * (11 * (q - 1)) * (13 * (r - 1)) :=
      Nat.mul_le_mul (Nat.mul_le_mul hp6 hq10) hr12
    simpa [mul_assoc, mul_left_comm, mul_comm] using h1
  have h7 : 7 * p * q * r * 6 * 10 * 12 ≤
      7 * 7 * 11 * 13 * (p - 1) * (q - 1) * (r - 1) := by
    simpa [mul_assoc, mul_left_comm, mul_comm] using Nat.mul_le_mul_left 7 hprod
  have h10 : 7 * 7 * 11 * 13 * (p - 1) * (q - 1) * (r - 1) ≤
      10 * 6 * 10 * 12 * (p - 1) * (q - 1) * (r - 1) := by
    simpa [mul_assoc, mul_left_comm, mul_comm] using
      Nat.mul_le_mul_right ((p - 1) * (q - 1) * (r - 1)) seven_eleven_thirteen_cap
  have hchain : 7 * p * q * r * 6 * 10 * 12 ≤
      10 * 6 * 10 * 12 * (p - 1) * (q - 1) * (r - 1) :=
    le_trans h7 (by simpa [mul_assoc, mul_left_comm, mul_comm] using h10)
  have hcancel : 6 * 10 * 12 * (7 * p * q * r) ≤
      6 * 10 * 12 * (10 * (p - 1) * (q - 1) * (r - 1)) := by
    have h1 : 6 * 10 * 12 * (7 * p * q * r) = 7 * p * q * r * 6 * 10 * 12 := by ring
    have h2 : 6 * 10 * 12 * (10 * (p - 1) * (q - 1) * (r - 1)) =
        10 * 6 * 10 * 12 * (p - 1) * (q - 1) * (r - 1) := by ring
    rw [h1, h2]
    exact hchain
  exact Nat.le_of_mul_le_mul_left hcancel (by decide : 0 < 6 * 10 * 12)

lemma seven_ten_of_three_caps {A B X Y C D P Q E F R S : ℕ}
    (hA : A * X < B * Y) (hC : C * P < D * Q) (hE : E * R < F * S)
    (hcap : 7 * B * D * F ≤ 10 * A * C * E)
    (hB : 0 < B) (hY : 0 < Y) (hD : 0 < D) (hQ : 0 < Q) :
    7 * X * P * R < 10 * Y * Q * S := by
  have hprod12 : (A * X) * (C * P) < (B * Y) * (D * Q) :=
    Nat.mul_lt_mul_of_le_of_lt (Nat.le_of_lt hA) hC (Nat.mul_pos hB hY)
  have hprod : ((A * X) * (C * P)) * (E * R) < ((B * Y) * (D * Q)) * (F * S) :=
    Nat.mul_lt_mul_of_le_of_lt (Nat.le_of_lt hprod12) hE
      (Nat.mul_pos (Nat.mul_pos hB hY) (Nat.mul_pos hD hQ))
  have h7 : 7 * (((A * X) * (C * P)) * (E * R)) <
      7 * (((B * Y) * (D * Q)) * (F * S)) :=
    Nat.mul_lt_mul_of_pos_left hprod (by decide)
  have h10 : 7 * B * D * F * (Y * Q * S) ≤ 10 * A * C * E * (Y * Q * S) :=
    Nat.mul_le_mul_right (Y * Q * S) hcap
  have hchain : 7 * A * C * E * X * P * R < 10 * A * C * E * Y * Q * S := by
    have hL : 7 * A * C * E * X * P * R =
        7 * (((A * X) * (C * P)) * (E * R)) := by ring
    have hmid : 7 * (((B * Y) * (D * Q)) * (F * S)) =
        7 * B * D * F * (Y * Q * S) := by ring
    have hR : 7 * B * D * F * (Y * Q * S) ≤ 10 * A * C * E * Y * Q * S := by
      simpa [mul_assoc, mul_left_comm, mul_comm] using h10
    calc
      7 * A * C * E * X * P * R = 7 * (((A * X) * (C * P)) * (E * R)) := hL
      _ < 7 * (((B * Y) * (D * Q)) * (F * S)) := h7
      _ = 7 * B * D * F * (Y * Q * S) := hmid
      _ ≤ 10 * A * C * E * Y * Q * S := hR
  have hcancel : A * C * E * (7 * X * P * R) < A * C * E * (10 * Y * Q * S) := by
    have h1 : A * C * E * (7 * X * P * R) = 7 * A * C * E * X * P * R := by ring
    have h2 : A * C * E * (10 * Y * Q * S) = 10 * A * C * E * Y * Q * S := by ring
    rw [h1, h2]
    exact hchain
  exact Nat.lt_of_mul_lt_mul_left hcancel

/-- Three squareful primes all at least `7` cannot fill leftover `10/7`.
The Euler-product cap is at most `7/6 · 11/10 · 13/12 = 1001/720 < 10/7`. -/
lemma seven_sigma_lt_ten_usigma_three_large {p q r a b c : ℕ}
    (hp : p.Prime) (hq : q.Prime) (hr : r.Prime)
    (hp7 : 7 ≤ p) (hq11 : 11 ≤ q) (hr13 : 13 ≤ r)
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    7 * σ 1 (p ^ a) * σ 1 (q ^ b) * σ 1 (r ^ c) <
      10 * usigma (p ^ a) * usigma (q ^ b) * usigma (r ^ c) := by
  have hcp := sigma_lt_cap_usigma hp ha
  have hcq := sigma_lt_cap_usigma hq hb
  have hcr := sigma_lt_cap_usigma hr hc
  have hup : 0 < usigma (p ^ a) := by
    rw [usigma_prime_pow hp ha]
    exact Nat.add_pos_left (by decide : 0 < 1) _
  have huq : 0 < usigma (q ^ b) := by
    rw [usigma_prime_pow hq hb]
    exact Nat.add_pos_left (by decide : 0 < 1) _
  have hcap := seven_p_q_r_cap hp7 hq11 hr13
  have := seven_ten_of_three_caps (A := p - 1) (B := p) (X := σ 1 (p ^ a))
    (Y := usigma (p ^ a)) (C := q - 1) (D := q) (P := σ 1 (q ^ b))
    (Q := usigma (q ^ b)) (E := r - 1) (F := r) (R := σ 1 (r ^ c))
    (S := usigma (r ^ c)) hcp hcq hcr hcap hp.pos hup hq.pos huq
  simpa [mul_assoc] using this

lemma seven_ten_of_four_caps {A B X Y C D P Q E F R S G H T U : ℕ}
    (hA : A * X < B * Y) (hC : C * P < D * Q) (hE : E * R < F * S)
    (hG : G * T < H * U)
    (hcap : 7 * B * D * F * H ≤ 10 * A * C * E * G)
    (hB : 0 < B) (hY : 0 < Y) (hD : 0 < D) (hQ : 0 < Q)
    (hF : 0 < F) (hS : 0 < S) :
    7 * X * P * R * T < 10 * Y * Q * S * U := by
  have hprod12 : (A * X) * (C * P) < (B * Y) * (D * Q) :=
    Nat.mul_lt_mul_of_le_of_lt (Nat.le_of_lt hA) hC (Nat.mul_pos hB hY)
  have hprod123 : ((A * X) * (C * P)) * (E * R) <
      ((B * Y) * (D * Q)) * (F * S) :=
    Nat.mul_lt_mul_of_le_of_lt (Nat.le_of_lt hprod12) hE
      (Nat.mul_pos (Nat.mul_pos hB hY) (Nat.mul_pos hD hQ))
  have hprod : (((A * X) * (C * P)) * (E * R)) * (G * T) <
      (((B * Y) * (D * Q)) * (F * S)) * (H * U) :=
    Nat.mul_lt_mul_of_le_of_lt (Nat.le_of_lt hprod123) hG
      (Nat.mul_pos (Nat.mul_pos (Nat.mul_pos hB hY) (Nat.mul_pos hD hQ))
        (Nat.mul_pos hF hS))
  have h7 : 7 * ((((A * X) * (C * P)) * (E * R)) * (G * T)) <
      7 * ((((B * Y) * (D * Q)) * (F * S)) * (H * U)) :=
    Nat.mul_lt_mul_of_pos_left hprod (by decide)
  have h10 : 7 * B * D * F * H * (Y * Q * S * U) ≤
      10 * A * C * E * G * (Y * Q * S * U) :=
    Nat.mul_le_mul_right (Y * Q * S * U) hcap
  have hchain : 7 * A * C * E * G * X * P * R * T <
      10 * A * C * E * G * Y * Q * S * U := by
    have hL : 7 * A * C * E * G * X * P * R * T =
        7 * ((((A * X) * (C * P)) * (E * R)) * (G * T)) := by ring
    have hmid : 7 * ((((B * Y) * (D * Q)) * (F * S)) * (H * U)) =
        7 * B * D * F * H * (Y * Q * S * U) := by ring
    have hR : 7 * B * D * F * H * (Y * Q * S * U) ≤
        10 * A * C * E * G * Y * Q * S * U := by
      simpa [mul_assoc, mul_left_comm, mul_comm] using h10
    calc
      7 * A * C * E * G * X * P * R * T =
          7 * ((((A * X) * (C * P)) * (E * R)) * (G * T)) := hL
      _ < 7 * ((((B * Y) * (D * Q)) * (F * S)) * (H * U)) := h7
      _ = 7 * B * D * F * H * (Y * Q * S * U) := hmid
      _ ≤ 10 * A * C * E * G * Y * Q * S * U := hR
  have hcancel : A * C * E * G * (7 * X * P * R * T) <
      A * C * E * G * (10 * Y * Q * S * U) := by
    have h1 : A * C * E * G * (7 * X * P * R * T) =
        7 * A * C * E * G * X * P * R * T := by ring
    have h2 : A * C * E * G * (10 * Y * Q * S * U) =
        10 * A * C * E * G * Y * Q * S * U := by ring
    rw [h1, h2]
    exact hchain
  exact Nat.lt_of_mul_lt_mul_left hcancel

lemma seven_eleven_thirteen_forty_one_cap :
    7 * 7 * 11 * 13 * 41 ≤ 10 * 6 * 10 * 12 * 40 := by
  decide

lemma seven_p_q_r_s_cap {p q r s : ℕ}
    (hp : 7 ≤ p) (hq : 11 ≤ q) (hr : 13 ≤ r) (hs : 41 ≤ s) :
    7 * p * q * r * s ≤ 10 * (p - 1) * (q - 1) * (r - 1) * (s - 1) := by
  have hp6 : p * 6 ≤ 7 * (p - 1) := cap_ratio_anti (by decide : 2 ≤ 7) hp
  have hq10 : q * 10 ≤ 11 * (q - 1) := cap_ratio_anti (by decide : 2 ≤ 11) hq
  have hr12 : r * 12 ≤ 13 * (r - 1) := cap_ratio_anti (by decide : 2 ≤ 13) hr
  have hs40 : s * 40 ≤ 41 * (s - 1) := cap_ratio_anti (by decide : 2 ≤ 41) hs
  have hprod : p * q * r * s * 6 * 10 * 12 * 40 ≤
      7 * 11 * 13 * 41 * (p - 1) * (q - 1) * (r - 1) * (s - 1) := by
    have h1 : p * 6 * (q * 10) * (r * 12) * (s * 40) ≤
        7 * (p - 1) * (11 * (q - 1)) * (13 * (r - 1)) * (41 * (s - 1)) :=
      Nat.mul_le_mul (Nat.mul_le_mul (Nat.mul_le_mul hp6 hq10) hr12) hs40
    simpa [mul_assoc, mul_left_comm, mul_comm] using h1
  have h7 : 7 * p * q * r * s * 6 * 10 * 12 * 40 ≤
      7 * 7 * 11 * 13 * 41 * (p - 1) * (q - 1) * (r - 1) * (s - 1) := by
    simpa [mul_assoc, mul_left_comm, mul_comm] using Nat.mul_le_mul_left 7 hprod
  have h10 : 7 * 7 * 11 * 13 * 41 * (p - 1) * (q - 1) * (r - 1) * (s - 1) ≤
      10 * 6 * 10 * 12 * 40 * (p - 1) * (q - 1) * (r - 1) * (s - 1) := by
    simpa [mul_assoc, mul_left_comm, mul_comm] using
      Nat.mul_le_mul_right ((p - 1) * (q - 1) * (r - 1) * (s - 1))
        seven_eleven_thirteen_forty_one_cap
  have hchain : 7 * p * q * r * s * 6 * 10 * 12 * 40 ≤
      10 * 6 * 10 * 12 * 40 * (p - 1) * (q - 1) * (r - 1) * (s - 1) :=
    le_trans h7 (by simpa [mul_assoc, mul_left_comm, mul_comm] using h10)
  have hcancel : 6 * 10 * 12 * 40 * (7 * p * q * r * s) ≤
      6 * 10 * 12 * 40 * (10 * (p - 1) * (q - 1) * (r - 1) * (s - 1)) := by
    have h1 : 6 * 10 * 12 * 40 * (7 * p * q * r * s) =
        7 * p * q * r * s * 6 * 10 * 12 * 40 := by ring
    have h2 : 6 * 10 * 12 * 40 * (10 * (p - 1) * (q - 1) * (r - 1) * (s - 1)) =
        10 * 6 * 10 * 12 * 40 * (p - 1) * (q - 1) * (r - 1) * (s - 1) := by ring
    rw [h1, h2]
    exact hchain
  exact Nat.le_of_mul_le_mul_left hcancel (by decide : 0 < 6 * 10 * 12 * 40)

/-- Four squareful primes `7 ≤ p < q < r < s` with `s ≥ 41` cannot fill
leftover `10/7`. -/
lemma seven_sigma_lt_ten_usigma_four_large {p q r s a b c d : ℕ}
    (hp : p.Prime) (hq : q.Prime) (hr : r.Prime) (hs : s.Prime)
    (hp7 : 7 ≤ p) (hq11 : 11 ≤ q) (hr13 : 13 ≤ r) (hs41 : 41 ≤ s)
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d) :
    7 * σ 1 (p ^ a) * σ 1 (q ^ b) * σ 1 (r ^ c) * σ 1 (s ^ d) <
      10 * usigma (p ^ a) * usigma (q ^ b) * usigma (r ^ c) * usigma (s ^ d) := by
  have hcp := sigma_lt_cap_usigma hp ha
  have hcq := sigma_lt_cap_usigma hq hb
  have hcr := sigma_lt_cap_usigma hr hc
  have hcs := sigma_lt_cap_usigma hs hd
  have hup : 0 < usigma (p ^ a) := by
    rw [usigma_prime_pow hp ha]
    exact Nat.add_pos_left (by decide : 0 < 1) _
  have huq : 0 < usigma (q ^ b) := by
    rw [usigma_prime_pow hq hb]
    exact Nat.add_pos_left (by decide : 0 < 1) _
  have hur : 0 < usigma (r ^ c) := by
    rw [usigma_prime_pow hr hc]
    exact Nat.add_pos_left (by decide : 0 < 1) _
  have hcap := seven_p_q_r_s_cap hp7 hq11 hr13 hs41
  have := seven_ten_of_four_caps (A := p - 1) (B := p) (X := σ 1 (p ^ a))
    (Y := usigma (p ^ a)) (C := q - 1) (D := q) (P := σ 1 (q ^ b))
    (Q := usigma (q ^ b)) (E := r - 1) (F := r) (R := σ 1 (r ^ c))
    (S := usigma (r ^ c)) (G := s - 1) (H := s) (T := σ 1 (s ^ d))
    (U := usigma (s ^ d)) hcp hcq hcr hcs hcap hp.pos hup hq.pos huq hr.pos hur
  simpa [mul_assoc] using this

lemma seven_mul_twenty_five_forty_nine_cap {p : ℕ} (hp : 23 ≤ p) :
    7 * 31 * 57 * p ≤ 10 * 26 * 50 * (p - 1) := by
  have hp1 : 1 ≤ p := by omega
  have hL : ((7 * 31 * 57 * p : ℕ) : ℤ) = 12369 * (p : ℤ) := by
    push_cast; rfl
  have hR : ((10 * 26 * 50 * (p - 1) : ℕ) : ℤ) = 13000 * ((p : ℤ) - 1) := by
    rw [Nat.cast_mul, Nat.cast_mul, Nat.cast_mul, Nat.cast_sub hp1]
    push_cast; rfl
  have hint : (12369 : ℤ) * p ≤ 13000 * (p - 1) := by
    have hp' : (23 : ℤ) ≤ p := Int.ofNat_le.mpr hp
    nlinarith
  exact Nat.cast_le.mp (by rw [hL, hR]; exact hint)

/-- `ρ(25) ρ(49) ρ(p^k) < 10/7` for every `p ≥ 23`. -/
lemma seven_sigma_lt_ten_usigma_five_seven_sq_large {p k : ℕ}
    (hp : p.Prime) (hp23 : 23 ≤ p) (hk : 0 < k) :
    7 * σ 1 (5 ^ 2) * σ 1 (7 ^ 2) * σ 1 (p ^ k) <
      10 * usigma (5 ^ 2) * usigma (7 ^ 2) * usigma (p ^ k) := by
  have hσ5 : σ 1 (5 ^ 2) = 31 := by
    rw [sigma_prime_pow_two Nat.prime_five]
    decide
  have hu5 : usigma (5 ^ 2) = 26 := usigma_five_pow_two
  have hp7 : Nat.Prime 7 := by decide
  have hσ7 : σ 1 (7 ^ 2) = 57 := by
    rw [sigma_prime_pow_two hp7]
    decide
  have hu7 : usigma (7 ^ 2) = 50 := by
    simpa using usigma_prime_pow hp7 (by decide : 0 < 2)
  rw [hσ5, hu5, hσ7, hu7]
  have hcp := sigma_lt_cap_usigma hp hk
  have hnum := seven_mul_twenty_five_forty_nine_cap hp23
  have hprod : (p - 1) * σ 1 (p ^ k) * (7 * 31 * 57) <
      p * usigma (p ^ k) * (7 * 31 * 57) :=
    Nat.mul_lt_mul_of_pos_right hcp (by decide)
  have h10 : p * usigma (p ^ k) * (7 * 31 * 57) ≤
      (p - 1) * usigma (p ^ k) * (10 * 26 * 50) := by
    have := Nat.mul_le_mul_right (usigma (p ^ k)) hnum
    have hL : 7 * 31 * 57 * p * usigma (p ^ k) =
        p * usigma (p ^ k) * (7 * 31 * 57) := by ring
    have hR : 10 * 26 * 50 * (p - 1) * usigma (p ^ k) =
        (p - 1) * usigma (p ^ k) * (10 * 26 * 50) := by ring
    have hthis : 7 * 31 * 57 * p * usigma (p ^ k) ≤
        10 * 26 * 50 * (p - 1) * usigma (p ^ k) := by
      simpa [mul_assoc, mul_left_comm, mul_comm] using this
    rw [hL, hR] at hthis
    exact hthis
  have hlt : (p - 1) * σ 1 (p ^ k) * (7 * 31 * 57) <
      (p - 1) * usigma (p ^ k) * (10 * 26 * 50) :=
    lt_of_lt_of_le hprod h10
  have hcancel : (p - 1) * (7 * 31 * 57 * σ 1 (p ^ k)) <
      (p - 1) * (10 * 26 * 50 * usigma (p ^ k)) := by
    have h1 : (p - 1) * (7 * 31 * 57 * σ 1 (p ^ k)) =
        (p - 1) * σ 1 (p ^ k) * (7 * 31 * 57) := by ring
    have h2 : (p - 1) * (10 * 26 * 50 * usigma (p ^ k)) =
        (p - 1) * usigma (p ^ k) * (10 * 26 * 50) := by ring
    rw [h1, h2]
    exact hlt
  exact Nat.lt_of_mul_lt_mul_left hcancel

lemma seven_five_eleven_cap {p : ℕ} (hp : 29 ≤ p) :
    7 * 5 * 11 * p ≤ 10 * 4 * 10 * (p - 1) := by
  have hp1 : 1 ≤ p := by omega
  have hp' : (29 : ℤ) ≤ p := Int.ofNat_le.mpr hp
  have hL : ((7 * 5 * 11 * p : ℕ) : ℤ) = 385 * (p : ℤ) := by push_cast; rfl
  have hR : ((10 * 4 * 10 * (p - 1) : ℕ) : ℤ) = 400 * ((p : ℤ) - 1) := by
    rw [Nat.cast_mul, Nat.cast_mul, Nat.cast_mul, Nat.cast_sub hp1]
    push_cast; rfl
  have : (385 : ℤ) * p ≤ 400 * (p - 1) := by nlinarith
  exact Nat.cast_le.mp (by rw [hL, hR]; exact this)

/-- `{5, 11, p}` with `p ≥ 29` cannot fill leftover `10/7`. -/
lemma seven_sigma_lt_ten_usigma_five_eleven_large {p a b c : ℕ}
    (hp : p.Prime) (hp29 : 29 ≤ p) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    7 * σ 1 (5 ^ a) * σ 1 (11 ^ b) * σ 1 (p ^ c) <
      10 * usigma (5 ^ a) * usigma (11 ^ b) * usigma (p ^ c) := by
  have h5 := four_sigma_lt_five_usigma ha
  have h11 := sigma_lt_cap_usigma (by decide : Nat.Prime 11) hb
  have hpcap := sigma_lt_cap_usigma hp hc
  have hup : 0 < usigma (5 ^ a) := by
    rw [usigma_prime_pow Nat.prime_five ha]
    exact Nat.add_pos_left (by decide : 0 < 1) _
  have hu11 : 0 < usigma (11 ^ b) := by
    rw [usigma_prime_pow (by decide : Nat.Prime 11) hb]
    exact Nat.add_pos_left (by decide : 0 < 1) _
  have hcap := seven_five_eleven_cap hp29
  have := seven_ten_of_three_caps (A := 4) (B := 5) (X := σ 1 (5 ^ a))
    (Y := usigma (5 ^ a)) (C := 10) (D := 11) (P := σ 1 (11 ^ b))
    (Q := usigma (11 ^ b)) (E := p - 1) (F := p) (R := σ 1 (p ^ c))
    (S := usigma (p ^ c)) h5 h11 hpcap hcap (by decide : 0 < 5) hup
    (by decide : 0 < 11) hu11
  simpa [mul_assoc] using this

lemma seven_five_thirteen_cap {p : ℕ} (hp : 23 ≤ p) :
    7 * 5 * 13 * p ≤ 10 * 4 * 12 * (p - 1) := by
  have hp1 : 1 ≤ p := by omega
  have hp' : (23 : ℤ) ≤ p := Int.ofNat_le.mpr hp
  have hL : ((7 * 5 * 13 * p : ℕ) : ℤ) = 455 * (p : ℤ) := by push_cast; rfl
  have hR : ((10 * 4 * 12 * (p - 1) : ℕ) : ℤ) = 480 * ((p : ℤ) - 1) := by
    rw [Nat.cast_mul, Nat.cast_mul, Nat.cast_mul, Nat.cast_sub hp1]
    push_cast; rfl
  have : (455 : ℤ) * p ≤ 480 * (p - 1) := by nlinarith
  exact Nat.cast_le.mp (by rw [hL, hR]; exact this)

/-- `{5, 13, p}` with `p ≥ 23` cannot fill leftover `10/7`. -/
lemma seven_sigma_lt_ten_usigma_five_thirteen_large {p a b c : ℕ}
    (hp : p.Prime) (hp23 : 23 ≤ p) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    7 * σ 1 (5 ^ a) * σ 1 (13 ^ b) * σ 1 (p ^ c) <
      10 * usigma (5 ^ a) * usigma (13 ^ b) * usigma (p ^ c) := by
  have h5 := four_sigma_lt_five_usigma ha
  have h13 := sigma_lt_cap_usigma (by decide : Nat.Prime 13) hb
  have hpcap := sigma_lt_cap_usigma hp hc
  have hup : 0 < usigma (5 ^ a) := by
    rw [usigma_prime_pow Nat.prime_five ha]
    exact Nat.add_pos_left (by decide : 0 < 1) _
  have hu13 : 0 < usigma (13 ^ b) := by
    rw [usigma_prime_pow (by decide : Nat.Prime 13) hb]
    exact Nat.add_pos_left (by decide : 0 < 1) _
  have hcap := seven_five_thirteen_cap hp23
  have := seven_ten_of_three_caps (A := 4) (B := 5) (X := σ 1 (5 ^ a))
    (Y := usigma (5 ^ a)) (C := 12) (D := 13) (P := σ 1 (13 ^ b))
    (Q := usigma (13 ^ b)) (E := p - 1) (F := p) (R := σ 1 (p ^ c))
    (S := usigma (p ^ c)) h5 h13 hpcap hcap (by decide : 0 < 5) hup
    (by decide : 0 < 13) hu13
  simpa [mul_assoc] using this

lemma seven_five_seventeen_cap {p : ℕ} (hp : 19 ≤ p) :
    7 * 5 * 17 * p ≤ 10 * 4 * 16 * (p - 1) := by
  have hp1 : 1 ≤ p := by omega
  have hp' : (19 : ℤ) ≤ p := Int.ofNat_le.mpr hp
  have hL : ((7 * 5 * 17 * p : ℕ) : ℤ) = 595 * (p : ℤ) := by push_cast; rfl
  have hR : ((10 * 4 * 16 * (p - 1) : ℕ) : ℤ) = 640 * ((p : ℤ) - 1) := by
    rw [Nat.cast_mul, Nat.cast_mul, Nat.cast_mul, Nat.cast_sub hp1]
    push_cast; rfl
  have : (595 : ℤ) * p ≤ 640 * (p - 1) := by nlinarith
  exact Nat.cast_le.mp (by rw [hL, hR]; exact this)

/-- `{5, 17, p}` with `p ≥ 19` cannot fill leftover `10/7`. -/
lemma seven_sigma_lt_ten_usigma_five_seventeen_large {p a b c : ℕ}
    (hp : p.Prime) (hp19 : 19 ≤ p) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    7 * σ 1 (5 ^ a) * σ 1 (17 ^ b) * σ 1 (p ^ c) <
      10 * usigma (5 ^ a) * usigma (17 ^ b) * usigma (p ^ c) := by
  have h5 := four_sigma_lt_five_usigma ha
  have h17 := sigma_lt_cap_usigma (by decide : Nat.Prime 17) hb
  have hpcap := sigma_lt_cap_usigma hp hc
  have hup : 0 < usigma (5 ^ a) := by
    rw [usigma_prime_pow Nat.prime_five ha]
    exact Nat.add_pos_left (by decide : 0 < 1) _
  have hu17 : 0 < usigma (17 ^ b) := by
    rw [usigma_prime_pow (by decide : Nat.Prime 17) hb]
    exact Nat.add_pos_left (by decide : 0 < 1) _
  have hcap := seven_five_seventeen_cap hp19
  have := seven_ten_of_three_caps (A := 4) (B := 5) (X := σ 1 (5 ^ a))
    (Y := usigma (5 ^ a)) (C := 16) (D := 17) (P := σ 1 (17 ^ b))
    (Q := usigma (17 ^ b)) (E := p - 1) (F := p) (R := σ 1 (p ^ c))
    (S := usigma (p ^ c)) h5 h17 hpcap hcap (by decide : 0 < 5) hup
    (by decide : 0 < 17) hu17
  simpa [mul_assoc] using this

/-- Euler caps of `{5, q, r}` undershoot leftover `10/7` once `19 ≤ q < r`. -/
lemma seven_five_q_r_cap {q r : ℕ} (hq : 19 ≤ q) (hqr : q < r) :
    7 * 5 * q * r ≤ 10 * 4 * (q - 1) * (r - 1) := by
  have hq1 : 1 ≤ q := by omega
  have hr1 : 1 ≤ r := by omega
  have hq' : (19 : ℤ) ≤ q := Int.ofNat_le.mpr hq
  have hr' : (q : ℤ) + 1 ≤ r := Int.ofNat_le.mpr (Nat.succ_le_of_lt hqr)
  have hL : ((7 * 5 * q * r : ℕ) : ℤ) = 35 * (q : ℤ) * r := by push_cast; rfl
  have hR : ((10 * 4 * (q - 1) * (r - 1) : ℕ) : ℤ) =
      40 * ((q : ℤ) - 1) * ((r : ℤ) - 1) := by
    rw [Nat.cast_mul, Nat.cast_mul, Nat.cast_mul, Nat.cast_sub hq1, Nat.cast_sub hr1]
    push_cast; rfl
  have : (35 : ℤ) * q * r ≤ 40 * (q - 1) * (r - 1) := by nlinarith
  exact Nat.cast_le.mp (by rw [hL, hR]; exact this)

/-- `{5, q, r}` with `19 ≤ q < r` cannot fill leftover `10/7`. -/
lemma seven_sigma_lt_ten_usigma_five_two_large {q r a b c : ℕ}
    (hq : q.Prime) (hr : r.Prime) (hq19 : 19 ≤ q) (hqr : q < r)
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    7 * σ 1 (5 ^ a) * σ 1 (q ^ b) * σ 1 (r ^ c) <
      10 * usigma (5 ^ a) * usigma (q ^ b) * usigma (r ^ c) := by
  have h5 := four_sigma_lt_five_usigma ha
  have hqcap := sigma_lt_cap_usigma hq hb
  have hrcap := sigma_lt_cap_usigma hr hc
  have hup : 0 < usigma (5 ^ a) := by
    rw [usigma_prime_pow Nat.prime_five ha]
    exact Nat.add_pos_left (by decide : 0 < 1) _
  have huq : 0 < usigma (q ^ b) := by
    rw [usigma_prime_pow hq hb]
    exact Nat.add_pos_left (by decide : 0 < 1) _
  have hcap := seven_five_q_r_cap hq19 hqr
  have := seven_ten_of_three_caps (A := 4) (B := 5) (X := σ 1 (5 ^ a))
    (Y := usigma (5 ^ a)) (C := q - 1) (D := q) (P := σ 1 (q ^ b))
    (Q := usigma (q ^ b)) (E := r - 1) (F := r) (R := σ 1 (r ^ c))
    (S := usigma (r ^ c)) h5 hqcap hrcap hcap (by decide : 0 < 5) hup
    (by omega : 0 < q) huq
  simpa [mul_assoc] using this

lemma twenty_five_forty_nine_eleven_sq_overshoot :
    10 * usigma (5 ^ 2) * usigma (7 ^ 2) * usigma (11 ^ 2) <
      7 * σ 1 (5 ^ 2) * σ 1 (7 ^ 2) * σ 1 (11 ^ 2) := by
  have hp7 : Nat.Prime 7 := by decide
  rw [sigma_prime_pow_two Nat.prime_five, usigma_five_pow_two,
    sigma_prime_pow_two hp7, usigma_prime_pow hp7 (by decide : 0 < 2),
    sigma_eleven_pow_two, usigma_eleven_pow_two]
  decide

lemma twenty_five_forty_nine_thirteen_sq_overshoot :
    10 * usigma (5 ^ 2) * usigma (7 ^ 2) * usigma (13 ^ 2) <
      7 * σ 1 (5 ^ 2) * σ 1 (7 ^ 2) * σ 1 (13 ^ 2) := by
  have hp7 : Nat.Prime 7 := by decide
  have hp13 : Nat.Prime 13 := by decide
  rw [sigma_prime_pow_two Nat.prime_five, usigma_five_pow_two,
    sigma_prime_pow_two hp7, usigma_prime_pow hp7 (by decide : 0 < 2),
    sigma_prime_pow_two hp13, usigma_prime_pow hp13 (by decide : 0 < 2)]
  decide

lemma twenty_five_forty_nine_seventeen_sq_overshoot :
    10 * usigma (5 ^ 2) * usigma (7 ^ 2) * usigma (17 ^ 2) <
      7 * σ 1 (5 ^ 2) * σ 1 (7 ^ 2) * σ 1 (17 ^ 2) := by
  have hp7 : Nat.Prime 7 := by decide
  have hp17 : Nat.Prime 17 := by decide
  rw [sigma_prime_pow_two Nat.prime_five, usigma_five_pow_two,
    sigma_prime_pow_two hp7, usigma_prime_pow hp7 (by decide : 0 < 2),
    sigma_prime_pow_two hp17, usigma_prime_pow hp17 (by decide : 0 < 2)]
  decide

lemma twenty_five_forty_nine_nineteen_sq_overshoot :
    10 * usigma (5 ^ 2) * usigma (7 ^ 2) * usigma (19 ^ 2) <
      7 * σ 1 (5 ^ 2) * σ 1 (7 ^ 2) * σ 1 (19 ^ 2) := by
  have hp7 : Nat.Prime 7 := by decide
  have hp19 : Nat.Prime 19 := by decide
  rw [sigma_prime_pow_two Nat.prime_five, usigma_five_pow_two,
    sigma_prime_pow_two hp7, usigma_prime_pow hp7 (by decide : 0 < 2),
    sigma_prime_pow_two hp19, usigma_prime_pow hp19 (by decide : 0 < 2)]
  decide

/-- Two Euler-product caps times a constant ratio, strictly below leftover `10/7`. -/
lemma seven_ten_of_two_caps_times_const {A B X Y C D P Q S T : ℕ}
    (hA : A * X < B * Y) (hC : C * P < D * Q)
    (hcap : 7 * B * D * T ≤ 10 * A * C * S)
    (hB : 0 < B) (hY : 0 < Y) (hT : 0 < T) :
    7 * X * P * T < 10 * Y * Q * S := by
  have hprod : (A * X) * (C * P) < (B * Y) * (D * Q) :=
    Nat.mul_lt_mul_of_le_of_lt (Nat.le_of_lt hA) hC (Nat.mul_pos hB hY)
  have h7' : 7 * ((A * X) * (C * P)) < 7 * ((B * Y) * (D * Q)) :=
    Nat.mul_lt_mul_of_pos_left hprod (by decide)
  have h7 : 7 * ((A * X) * (C * P)) * T < 7 * ((B * Y) * (D * Q)) * T :=
    Nat.mul_lt_mul_of_pos_right h7' hT
  have h10 : 7 * B * D * T * (Y * Q) ≤ 10 * A * C * S * (Y * Q) :=
    Nat.mul_le_mul_right (Y * Q) hcap
  have hchain : 7 * A * C * X * P * T < 10 * A * C * Y * Q * S := by
    have hL : 7 * A * C * X * P * T = 7 * ((A * X) * (C * P)) * T := by ring
    have hmid : 7 * ((B * Y) * (D * Q)) * T = 7 * B * D * T * (Y * Q) := by ring
    have hR : 7 * B * D * T * (Y * Q) ≤ 10 * A * C * S * (Y * Q) := by
      simpa [mul_assoc, mul_left_comm, mul_comm] using h10
    have hR' : 10 * A * C * S * (Y * Q) = 10 * A * C * Y * Q * S := by ring
    calc
      7 * A * C * X * P * T = 7 * ((A * X) * (C * P)) * T := hL
      _ < 7 * ((B * Y) * (D * Q)) * T := h7
      _ = 7 * B * D * T * (Y * Q) := hmid
      _ ≤ 10 * A * C * S * (Y * Q) := hR
      _ = 10 * A * C * Y * Q * S := hR'
  have hcancel : A * C * (7 * X * P * T) < A * C * (10 * Y * Q * S) := by
    have h1 : A * C * (7 * X * P * T) = 7 * A * C * X * P * T := by ring
    have h2 : A * C * (10 * Y * Q * S) = 10 * A * C * Y * Q * S := by ring
    rw [h1, h2]
    exact hchain
  exact Nat.lt_of_mul_lt_mul_left hcancel

/-- Raising any of three exponents cannot repair an overshoot of leftover `10/7`. -/
lemma ten_seven_overshoot_mono_three {p q r a a' b b' c c' : ℕ}
    (hp : p.Prime) (hq : q.Prime) (hr : r.Prime)
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (haa : a ≤ a') (hbb : b ≤ b') (hcc : c ≤ c')
    (hover : 10 * usigma (p ^ a) * usigma (q ^ b) * usigma (r ^ c) <
      7 * σ 1 (p ^ a) * σ 1 (q ^ b) * σ 1 (r ^ c)) :
    10 * usigma (p ^ a') * usigma (q ^ b') * usigma (r ^ c') <
      7 * σ 1 (p ^ a') * σ 1 (q ^ b') * σ 1 (r ^ c') := by
  have ha0 : 0 < a' := by omega
  have hb0 : 0 < b' := by omega
  have hc0 : 0 < c' := by omega
  have hp_le := sigma_usigma_ratio_le_of_le hp ha haa
  have hq_le := sigma_usigma_ratio_le_of_le hq hb hbb
  have hr_le := sigma_usigma_ratio_le_of_le hr hc hcc
  have hup : 0 < usigma (p ^ a) := by
    rw [usigma_prime_pow hp ha]
    exact Nat.add_pos_left (by decide : 0 < 1) _
  have huq : 0 < usigma (q ^ b) := by
    rw [usigma_prime_pow hq hb]
    exact Nat.add_pos_left (by decide : 0 < 1) _
  have hur : 0 < usigma (r ^ c) := by
    rw [usigma_prime_pow hr hc]
    exact Nat.add_pos_left (by decide : 0 < 1) _
  have hup' : 0 < usigma (p ^ a') := by
    rw [usigma_prime_pow hp ha0]
    exact Nat.add_pos_left (by decide : 0 < 1) _
  have huq' : 0 < usigma (q ^ b') := by
    rw [usigma_prime_pow hq hb0]
    exact Nat.add_pos_left (by decide : 0 < 1) _
  have hur' : 0 < usigma (r ^ c') := by
    rw [usigma_prime_pow hr hc0]
    exact Nat.add_pos_left (by decide : 0 < 1) _
  have hmul : σ 1 (p ^ a) * σ 1 (q ^ b) * σ 1 (r ^ c) *
        usigma (p ^ a') * usigma (q ^ b') * usigma (r ^ c') ≤
      σ 1 (p ^ a') * σ 1 (q ^ b') * σ 1 (r ^ c') *
        usigma (p ^ a) * usigma (q ^ b) * usigma (r ^ c) := by
    have h1 : σ 1 (p ^ a) * usigma (p ^ a') *
          (σ 1 (q ^ b) * usigma (q ^ b') * (σ 1 (r ^ c) * usigma (r ^ c'))) ≤
        σ 1 (p ^ a') * usigma (p ^ a) *
          (σ 1 (q ^ b) * usigma (q ^ b') * (σ 1 (r ^ c) * usigma (r ^ c'))) :=
      Nat.mul_le_mul_right _ hp_le
    have h2 : σ 1 (p ^ a') * usigma (p ^ a) *
          (σ 1 (q ^ b) * usigma (q ^ b') * (σ 1 (r ^ c) * usigma (r ^ c'))) ≤
        σ 1 (p ^ a') * usigma (p ^ a) *
          (σ 1 (q ^ b') * usigma (q ^ b) * (σ 1 (r ^ c) * usigma (r ^ c'))) :=
      Nat.mul_le_mul_left _ (Nat.mul_le_mul_right _ hq_le)
    have h3 : σ 1 (p ^ a') * usigma (p ^ a) *
          (σ 1 (q ^ b') * usigma (q ^ b) * (σ 1 (r ^ c) * usigma (r ^ c'))) ≤
        σ 1 (p ^ a') * usigma (p ^ a) *
          (σ 1 (q ^ b') * usigma (q ^ b) * (σ 1 (r ^ c') * usigma (r ^ c))) :=
      Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ hr_le)
    have h12 := le_trans h1 (by simpa [mul_assoc, mul_left_comm, mul_comm] using h2)
    have h123 := le_trans h12 (by simpa [mul_assoc, mul_left_comm, mul_comm] using h3)
    simpa [mul_assoc, mul_left_comm, mul_comm] using h123
  have h7mul : 7 * σ 1 (p ^ a) * σ 1 (q ^ b) * σ 1 (r ^ c) *
        usigma (p ^ a') * usigma (q ^ b') * usigma (r ^ c') ≤
      7 * σ 1 (p ^ a') * σ 1 (q ^ b') * σ 1 (r ^ c') *
        usigma (p ^ a) * usigma (q ^ b) * usigma (r ^ c) := by
    simpa [mul_assoc, mul_left_comm, mul_comm] using Nat.mul_le_mul_left 7 hmul
  have h10 : 10 * usigma (p ^ a) * usigma (q ^ b) * usigma (r ^ c) *
        usigma (p ^ a') * usigma (q ^ b') * usigma (r ^ c') <
      7 * σ 1 (p ^ a) * σ 1 (q ^ b) * σ 1 (r ^ c) *
        usigma (p ^ a') * usigma (q ^ b') * usigma (r ^ c') := by
    have := Nat.mul_lt_mul_of_pos_right hover (mul_pos hup' (mul_pos huq' hur'))
    simpa [mul_assoc, mul_left_comm, mul_comm] using this
  have hchain : 10 * usigma (p ^ a') * usigma (q ^ b') * usigma (r ^ c') *
        usigma (p ^ a) * usigma (q ^ b) * usigma (r ^ c) <
      7 * σ 1 (p ^ a') * σ 1 (q ^ b') * σ 1 (r ^ c') *
        usigma (p ^ a) * usigma (q ^ b) * usigma (r ^ c) :=
    lt_of_lt_of_le (by simpa [mul_assoc, mul_left_comm, mul_comm] using h10) h7mul
  exact Nat.lt_of_mul_lt_mul_right
    (a := usigma (p ^ a) * usigma (q ^ b) * usigma (r ^ c))
    (by simpa [mul_assoc, mul_left_comm, mul_comm] using hchain)

lemma one_mem_unitaryDivisors {n : ℕ} (hn : n ≠ 0) :
    1 ∈ unitaryDivisors n :=
  mem_unitaryDivisors.mpr ⟨one_dvd n, hn, Nat.coprime_one_left (n / 1)⟩

lemma usigma_pos {n : ℕ} (hn : n ≠ 0) : 0 < usigma n := by
  have h1 : 1 ∈ unitaryDivisors n := one_mem_unitaryDivisors hn
  have hsum : (1 : ℕ) ≤ ∑ d ∈ unitaryDivisors n, d :=
    Finset.single_le_sum (f := fun d => d) (fun _ _ => Nat.zero_le _) h1
  have : 1 ≤ usigma n := by simpa [usigma] using hsum
  omega

/-- An extra coprime factor cannot repair an overshoot of leftover `10/7`. -/
lemma ten_seven_overshoot_mul {s t n : ℕ} (hn : n ≠ 0)
    (hover : 10 * s < 7 * t) :
    10 * s * usigma n < 7 * t * σ 1 n := by
  have hu : 0 < usigma n := usigma_pos hn
  have h1 : 10 * s * usigma n < 7 * t * usigma n :=
    Nat.mul_lt_mul_of_pos_right hover hu
  have h2 : 7 * t * usigma n ≤ 7 * t * σ 1 n :=
    Nat.mul_le_mul_left _ (usigma_le_sigma n)
  exact lt_of_lt_of_le h1 h2

/-- `{5^a, 7^b}` with `a,b ≥ 3` already overshoots leftover `10/7`, so any extra
positive factor still overshoots. -/
lemma five_seven_pow_ge_three_mul_overshoot {a b n : ℕ}
    (ha : 3 ≤ a) (hb : 3 ≤ b) (hn : n ≠ 0) :
    10 * usigma (5 ^ a) * usigma (7 ^ b) * usigma n <
      7 * σ 1 (5 ^ a) * σ 1 (7 ^ b) * σ 1 n := by
  have hover := five_seven_pow_ge_three_overshoot ha hb
  have h := ten_seven_overshoot_mul (s := usigma (5 ^ a) * usigma (7 ^ b))
      (t := σ 1 (5 ^ a) * σ 1 (7 ^ b)) hn (by simpa [mul_assoc] using hover)
  simpa [mul_assoc] using h

lemma not_seven_sigma_eq_ten_usigma_five_seven_ge_three_mul {a b n : ℕ}
    (ha : 3 ≤ a) (hb : 3 ≤ b) (hn : n ≠ 0) :
    ¬ 7 * σ 1 (5 ^ a) * σ 1 (7 ^ b) * σ 1 n =
        10 * usigma (5 ^ a) * usigma (7 ^ b) * usigma n :=
  (five_seven_pow_ge_three_mul_overshoot ha hb hn).ne'

lemma usigma_five_pow_three : usigma (5 ^ 3) = 126 := by
  rw [usigma_prime_pow Nat.prime_five (by decide : 0 < 3)]
  decide

lemma sigma_five_pow_three : σ 1 (5 ^ 3) = 156 := by
  rw [sigma_prime_pow_div Nat.prime_five]
  norm_num

lemma usigma_seven_pow_three : usigma (7 ^ 3) = 344 := by
  rw [usigma_prime_pow (by decide : Nat.Prime 7) (by decide : 0 < 3)]
  decide

lemma sigma_seven_pow_three : σ 1 (7 ^ 3) = 400 := by
  rw [sigma_prime_pow_div (by decide : Nat.Prime 7)]
  norm_num

/-- `ρ(25) cap(11) cap(q) < 10/7` for every `q ≥ 13`. -/
lemma seven_mul_twenty_five_eleven_cap {q : ℕ} (hq : 13 ≤ q) :
    7 * 11 * q * 31 ≤ 10 * 10 * (q - 1) * 26 := by
  have hq1 : 1 ≤ q := by omega
  have hq' : (13 : ℤ) ≤ q := Int.ofNat_le.mpr hq
  have hL : ((7 * 11 * q * 31 : ℕ) : ℤ) = (77 : ℤ) * q * 31 := by
    rw [Nat.cast_mul, Nat.cast_mul, Nat.cast_mul]; rfl
  have hR : ((10 * 10 * (q - 1) * 26 : ℕ) : ℤ) =
      (100 : ℤ) * ((q : ℤ) - 1) * 26 := by
    rw [Nat.cast_mul, Nat.cast_mul, Nat.cast_mul, Nat.cast_sub hq1]
    rfl
  have : (77 : ℤ) * q * 31 ≤ 100 * (q - 1) * 26 := by nlinarith
  exact Nat.cast_le.mp (by rw [hL, hR]; exact this)

/-- `{5^2, 11^b, q^c}` undershoots leftover `10/7` for every `q ≥ 13`. -/
lemma seven_sigma_lt_ten_usigma_five_sq_eleven_large {q b c : ℕ}
    (hq : q.Prime) (hq13 : 13 ≤ q) (hb : 0 < b) (hc : 0 < c) :
    7 * σ 1 (5 ^ 2) * σ 1 (11 ^ b) * σ 1 (q ^ c) <
      10 * usigma (5 ^ 2) * usigma (11 ^ b) * usigma (q ^ c) := by
  have hσ5 : σ 1 (5 ^ 2) = 31 := by
    rw [sigma_prime_pow_two Nat.prime_five]
    decide
  have hu5 : usigma (5 ^ 2) = 26 := usigma_five_pow_two
  rw [hσ5, hu5]
  have h11 := sigma_lt_cap_usigma (by decide : Nat.Prime 11) hb
  have hqcap := sigma_lt_cap_usigma hq hc
  have hu11 : 0 < usigma (11 ^ b) := by
    rw [usigma_prime_pow (by decide : Nat.Prime 11) hb]
    exact Nat.add_pos_left (by decide : 0 < 1) _
  have hcap := seven_mul_twenty_five_eleven_cap hq13
  have hlt := seven_ten_of_two_caps_times_const (A := 10) (B := 11)
    (X := σ 1 (11 ^ b)) (Y := usigma (11 ^ b)) (C := q - 1) (D := q)
    (P := σ 1 (q ^ c)) (Q := usigma (q ^ c)) (S := 26) (T := 31)
    h11 hqcap hcap (by decide : 0 < 11) hu11 (by decide : 0 < 31)
  have hL : 7 * 31 * σ 1 (11 ^ b) * σ 1 (q ^ c) =
      7 * σ 1 (11 ^ b) * σ 1 (q ^ c) * 31 := by ring
  have hR : 10 * 26 * usigma (11 ^ b) * usigma (q ^ c) =
      10 * usigma (11 ^ b) * usigma (q ^ c) * 26 := by ring
  rw [hL, hR]
  exact hlt

lemma five_pow_three_eleven_thirteen_sq_overshoot :
    10 * usigma (5 ^ 3) * usigma (11 ^ 2) * usigma (13 ^ 2) <
      7 * σ 1 (5 ^ 3) * σ 1 (11 ^ 2) * σ 1 (13 ^ 2) := by
  have hp13 : Nat.Prime 13 := by decide
  rw [usigma_five_pow_three, sigma_five_pow_three, sigma_eleven_pow_two,
    usigma_eleven_pow_two, sigma_prime_pow_two hp13,
    usigma_prime_pow hp13 (by decide : 0 < 2)]
  norm_num

lemma five_pow_three_eleven_seventeen_sq_overshoot :
    10 * usigma (5 ^ 3) * usigma (11 ^ 2) * usigma (17 ^ 2) <
      7 * σ 1 (5 ^ 3) * σ 1 (11 ^ 2) * σ 1 (17 ^ 2) := by
  have hp17 : Nat.Prime 17 := by decide
  rw [usigma_five_pow_three, sigma_five_pow_three, sigma_eleven_pow_two,
    usigma_eleven_pow_two, sigma_prime_pow_two hp17,
    usigma_prime_pow hp17 (by decide : 0 < 2)]
  norm_num

/-- `{5, 11, 13}` cannot fill leftover `10/7`. -/
lemma not_seven_sigma_eq_ten_usigma_five_eleven_thirteen {a b c : ℕ}
    (ha : 2 ≤ a) (hb : 2 ≤ b) (hc : 2 ≤ c) :
    ¬ 7 * σ 1 (5 ^ a) * σ 1 (11 ^ b) * σ 1 (13 ^ c) =
        10 * usigma (5 ^ a) * usigma (11 ^ b) * usigma (13 ^ c) := by
  intro heq
  rcases eq_or_lt_of_le ha with ha2 | ha3
  · rw [← ha2] at heq
    exact (seven_sigma_lt_ten_usigma_five_sq_eleven_large
      (by decide : Nat.Prime 13) (by decide : 13 ≤ 13) (by omega) (by omega)).ne heq
  · have hover := ten_seven_overshoot_mono_three Nat.prime_five
        (by decide : Nat.Prime 11) (by decide : Nat.Prime 13)
        (by decide : 0 < 3) (by decide : 0 < 2) (by decide : 0 < 2)
        (Nat.succ_le_of_lt ha3) hb hc five_pow_three_eleven_thirteen_sq_overshoot
    rw [← heq] at hover
    exact lt_irrefl _ hover

/-- `{5, 11, 17}` cannot fill leftover `10/7`. -/
lemma not_seven_sigma_eq_ten_usigma_five_eleven_seventeen {a b c : ℕ}
    (ha : 2 ≤ a) (hb : 2 ≤ b) (hc : 2 ≤ c) :
    ¬ 7 * σ 1 (5 ^ a) * σ 1 (11 ^ b) * σ 1 (17 ^ c) =
        10 * usigma (5 ^ a) * usigma (11 ^ b) * usigma (17 ^ c) := by
  intro heq
  rcases eq_or_lt_of_le ha with ha2 | ha3
  · rw [← ha2] at heq
    exact (seven_sigma_lt_ten_usigma_five_sq_eleven_large
      (by decide : Nat.Prime 17) (by decide : 13 ≤ 17) (by omega) (by omega)).ne heq
  · have hover := ten_seven_overshoot_mono_three Nat.prime_five
        (by decide : Nat.Prime 11) (by decide : Nat.Prime 17)
        (by decide : 0 < 3) (by decide : 0 < 2) (by decide : 0 < 2)
        (Nat.succ_le_of_lt ha3) hb hc five_pow_three_eleven_seventeen_sq_overshoot
    rw [← heq] at hover
    exact lt_irrefl _ hover

lemma five_seven_eleven_pow_ge_two_overshoot {a b c : ℕ}
    (ha : 2 ≤ a) (hb : 2 ≤ b) (hc : 2 ≤ c) :
    10 * usigma (5 ^ a) * usigma (7 ^ b) * usigma (11 ^ c) <
      7 * σ 1 (5 ^ a) * σ 1 (7 ^ b) * σ 1 (11 ^ c) :=
  ten_seven_overshoot_mono_three Nat.prime_five (by decide : Nat.Prime 7)
    (by decide : Nat.Prime 11) (by decide : 0 < 2) (by decide : 0 < 2)
    (by decide : 0 < 2) ha hb hc twenty_five_forty_nine_eleven_sq_overshoot

lemma five_seven_thirteen_pow_ge_two_overshoot {a b c : ℕ}
    (ha : 2 ≤ a) (hb : 2 ≤ b) (hc : 2 ≤ c) :
    10 * usigma (5 ^ a) * usigma (7 ^ b) * usigma (13 ^ c) <
      7 * σ 1 (5 ^ a) * σ 1 (7 ^ b) * σ 1 (13 ^ c) :=
  ten_seven_overshoot_mono_three Nat.prime_five (by decide : Nat.Prime 7)
    (by decide : Nat.Prime 13) (by decide : 0 < 2) (by decide : 0 < 2)
    (by decide : 0 < 2) ha hb hc twenty_five_forty_nine_thirteen_sq_overshoot

lemma five_seven_seventeen_pow_ge_two_overshoot {a b c : ℕ}
    (ha : 2 ≤ a) (hb : 2 ≤ b) (hc : 2 ≤ c) :
    10 * usigma (5 ^ a) * usigma (7 ^ b) * usigma (17 ^ c) <
      7 * σ 1 (5 ^ a) * σ 1 (7 ^ b) * σ 1 (17 ^ c) :=
  ten_seven_overshoot_mono_three Nat.prime_five (by decide : Nat.Prime 7)
    (by decide : Nat.Prime 17) (by decide : 0 < 2) (by decide : 0 < 2)
    (by decide : 0 < 2) ha hb hc twenty_five_forty_nine_seventeen_sq_overshoot

lemma five_seven_nineteen_pow_ge_two_overshoot {a b c : ℕ}
    (ha : 2 ≤ a) (hb : 2 ≤ b) (hc : 2 ≤ c) :
    10 * usigma (5 ^ a) * usigma (7 ^ b) * usigma (19 ^ c) <
      7 * σ 1 (5 ^ a) * σ 1 (7 ^ b) * σ 1 (19 ^ c) :=
  ten_seven_overshoot_mono_three Nat.prime_five (by decide : Nat.Prime 7)
    (by decide : Nat.Prime 19) (by decide : 0 < 2) (by decide : 0 < 2)
    (by decide : 0 < 2) ha hb hc twenty_five_forty_nine_nineteen_sq_overshoot

lemma not_seven_sigma_eq_ten_usigma_five_seven_eleven {a b c : ℕ}
    (ha : 2 ≤ a) (hb : 2 ≤ b) (hc : 2 ≤ c) :
    ¬ 7 * σ 1 (5 ^ a) * σ 1 (7 ^ b) * σ 1 (11 ^ c) =
        10 * usigma (5 ^ a) * usigma (7 ^ b) * usigma (11 ^ c) :=
  (five_seven_eleven_pow_ge_two_overshoot ha hb hc).ne'

lemma not_seven_sigma_eq_ten_usigma_five_seven_thirteen {a b c : ℕ}
    (ha : 2 ≤ a) (hb : 2 ≤ b) (hc : 2 ≤ c) :
    ¬ 7 * σ 1 (5 ^ a) * σ 1 (7 ^ b) * σ 1 (13 ^ c) =
        10 * usigma (5 ^ a) * usigma (7 ^ b) * usigma (13 ^ c) :=
  (five_seven_thirteen_pow_ge_two_overshoot ha hb hc).ne'

lemma not_seven_sigma_eq_ten_usigma_five_seven_seventeen {a b c : ℕ}
    (ha : 2 ≤ a) (hb : 2 ≤ b) (hc : 2 ≤ c) :
    ¬ 7 * σ 1 (5 ^ a) * σ 1 (7 ^ b) * σ 1 (17 ^ c) =
        10 * usigma (5 ^ a) * usigma (7 ^ b) * usigma (17 ^ c) :=
  (five_seven_seventeen_pow_ge_two_overshoot ha hb hc).ne'

lemma not_seven_sigma_eq_ten_usigma_five_seven_nineteen {a b c : ℕ}
    (ha : 2 ≤ a) (hb : 2 ≤ b) (hc : 2 ≤ c) :
    ¬ 7 * σ 1 (5 ^ a) * σ 1 (7 ^ b) * σ 1 (19 ^ c) =
        10 * usigma (5 ^ a) * usigma (7 ^ b) * usigma (19 ^ c) :=
  (five_seven_nineteen_pow_ge_two_overshoot ha hb hc).ne'

/-- `ρ(125) ρ(49) ρ(p^2) > 10/7` for `23 ≤ p ≤ 79`. -/
lemma five_cube_forty_nine_sq_overshoot {p : ℕ} (hp : p.Prime)
    (h23 : 23 ≤ p) (h79 : p ≤ 79) :
    10 * usigma (5 ^ 3) * usigma (7 ^ 2) * usigma (p ^ 2) <
      7 * σ 1 (5 ^ 3) * σ 1 (7 ^ 2) * σ 1 (p ^ 2) := by
  have hp7 : Nat.Prime 7 := by decide
  have hu7 : usigma (7 ^ 2) = 50 := by
    simpa using usigma_prime_pow hp7 (by decide : 0 < 2)
  have hσ7 : σ 1 (7 ^ 2) = 57 := by
    rw [sigma_prime_pow_two hp7]
    decide
  rw [usigma_five_pow_three, sigma_five_pow_three, hu7, hσ7,
    usigma_prime_pow hp (by decide : 0 < 2), sigma_prime_pow_two hp]
  have hquad : 3 * p * p + 3 < 247 * p := by
    have hle : 3 * p * p ≤ 3 * 79 * p := by
      have : p * p ≤ 79 * p := Nat.mul_le_mul_right p h79
      nlinarith
    have h237 : 3 * 79 * p + 3 < 247 * p := by
      have : 3 < 10 * p := by nlinarith
      nlinarith
    omega
  have hL : ((10 * 126 * 50 * (1 + p ^ 2) : ℕ) : ℤ) =
      10 * 126 * 50 * (1 + (p : ℤ) ^ 2) := by push_cast; rfl
  have hR : ((7 * 156 * 57 * (1 + p + p ^ 2) : ℕ) : ℤ) =
      7 * 156 * 57 * (1 + (p : ℤ) + (p : ℤ) ^ 2) := by push_cast; rfl
  have hint : (10 : ℤ) * 126 * 50 * (1 + p ^ 2) <
      7 * 156 * 57 * (1 + p + p ^ 2) := by
    have h247 : (3 : ℤ) * p * p + 3 < 247 * p := by exact_mod_cast hquad
    have h756 : (756 : ℤ) * (1 + p ^ 2) < 252 * 247 * p := by
      have : (3 : ℤ) * (1 + p ^ 2) < 247 * p := by nlinarith
      have hmul := mul_lt_mul_of_pos_left this (by decide : (0 : ℤ) < 252)
      nlinarith
    nlinarith
  exact Nat.cast_lt.mp (by rw [hL, hR]; exact hint)

lemma five_cube_forty_nine_pow_ge_two_overshoot {p k : ℕ} (hp : p.Prime)
    (h23 : 23 ≤ p) (h79 : p ≤ 79) (hk : 2 ≤ k) :
    10 * usigma (5 ^ 3) * usigma (7 ^ 2) * usigma (p ^ k) <
      7 * σ 1 (5 ^ 3) * σ 1 (7 ^ 2) * σ 1 (p ^ k) :=
  ten_seven_overshoot_mono_three Nat.prime_five (by decide : Nat.Prime 7) hp
    (by decide : 0 < 3) (by decide : 0 < 2) (by decide : 0 < 2)
    (le_refl _) (le_refl _) hk (five_cube_forty_nine_sq_overshoot hp h23 h79)

/-- `ρ(125) ρ(49) cap(p) < 10/7` for every `p ≥ 89`. -/
lemma seven_mul_five_cube_forty_nine_cap {p : ℕ} (hp : 89 ≤ p) :
    7 * 156 * 57 * p ≤ 10 * 126 * 50 * (p - 1) := by
  have hp1 : 1 ≤ p := by omega
  have hp' : (89 : ℤ) ≤ p := Int.ofNat_le.mpr hp
  have hL : ((7 * 156 * 57 * p : ℕ) : ℤ) = 7 * 156 * 57 * (p : ℤ) := by
    push_cast; rfl
  have hR : ((10 * 126 * 50 * (p - 1) : ℕ) : ℤ) =
      10 * 126 * 50 * ((p : ℤ) - 1) := by
    rw [Nat.cast_mul, Nat.cast_mul, Nat.cast_mul, Nat.cast_sub hp1]
    push_cast; rfl
  have : (7 : ℤ) * 156 * 57 * p ≤ 10 * 126 * 50 * (p - 1) := by nlinarith
  exact Nat.cast_le.mp (by rw [hL, hR]; exact this)

lemma seven_sigma_lt_ten_usigma_five_cube_seven_sq_large {p k : ℕ}
    (hp : p.Prime) (hp89 : 89 ≤ p) (hk : 0 < k) :
    7 * σ 1 (5 ^ 3) * σ 1 (7 ^ 2) * σ 1 (p ^ k) <
      10 * usigma (5 ^ 3) * usigma (7 ^ 2) * usigma (p ^ k) := by
  have hp7 : Nat.Prime 7 := by decide
  have hσ7 : σ 1 (7 ^ 2) = 57 := by
    rw [sigma_prime_pow_two hp7]
    decide
  have hu7 : usigma (7 ^ 2) = 50 := by
    simpa using usigma_prime_pow hp7 (by decide : 0 < 2)
  rw [sigma_five_pow_three, usigma_five_pow_three, hσ7, hu7]
  have hcp := sigma_lt_cap_usigma hp hk
  have hnum := seven_mul_five_cube_forty_nine_cap hp89
  have hprod : (p - 1) * σ 1 (p ^ k) * (7 * 156 * 57) <
      p * usigma (p ^ k) * (7 * 156 * 57) :=
    Nat.mul_lt_mul_of_pos_right hcp (by decide)
  have h10 : p * usigma (p ^ k) * (7 * 156 * 57) ≤
      (p - 1) * usigma (p ^ k) * (10 * 126 * 50) := by
    have := Nat.mul_le_mul_right (usigma (p ^ k)) hnum
    have hL : 7 * 156 * 57 * p * usigma (p ^ k) =
        p * usigma (p ^ k) * (7 * 156 * 57) := by ring
    have hR : 10 * 126 * 50 * (p - 1) * usigma (p ^ k) =
        (p - 1) * usigma (p ^ k) * (10 * 126 * 50) := by ring
    have hthis : 7 * 156 * 57 * p * usigma (p ^ k) ≤
        10 * 126 * 50 * (p - 1) * usigma (p ^ k) := by
      simpa [mul_assoc, mul_left_comm, mul_comm] using this
    rw [hL, hR] at hthis
    exact hthis
  have hlt : (p - 1) * σ 1 (p ^ k) * (7 * 156 * 57) <
      (p - 1) * usigma (p ^ k) * (10 * 126 * 50) :=
    lt_of_lt_of_le hprod h10
  have hcancel : (p - 1) * (7 * 156 * 57 * σ 1 (p ^ k)) <
      (p - 1) * (10 * 126 * 50 * usigma (p ^ k)) := by
    have h1 : (p - 1) * (7 * 156 * 57 * σ 1 (p ^ k)) =
        (p - 1) * σ 1 (p ^ k) * (7 * 156 * 57) := by ring
    have h2 : (p - 1) * (10 * 126 * 50 * usigma (p ^ k)) =
        (p - 1) * usigma (p ^ k) * (10 * 126 * 50) := by ring
    rw [h1, h2]
    exact hlt
  exact Nat.lt_of_mul_lt_mul_left hcancel

lemma eighty_three_sq_five_cube_forty_nine_undershoot :
    7 * σ 1 (5 ^ 3) * σ 1 (7 ^ 2) * σ 1 (83 ^ 2) <
      10 * usigma (5 ^ 3) * usigma (7 ^ 2) * usigma (83 ^ 2) := by
  have hp7 : Nat.Prime 7 := by decide
  have hp83 : Nat.Prime 83 := by decide
  have hσ7 : σ 1 (7 ^ 2) = 57 := by
    rw [sigma_prime_pow_two hp7]
    decide
  have hu7 : usigma (7 ^ 2) = 50 := by
    simpa using usigma_prime_pow hp7 (by decide : 0 < 2)
  rw [sigma_five_pow_three, usigma_five_pow_three, hσ7, hu7,
    sigma_prime_pow_two hp83, usigma_prime_pow hp83 (by decide : 0 < 2)]
  norm_num

lemma eighty_three_cube_five_cube_forty_nine_overshoot :
    10 * usigma (5 ^ 3) * usigma (7 ^ 2) * usigma (83 ^ 3) <
      7 * σ 1 (5 ^ 3) * σ 1 (7 ^ 2) * σ 1 (83 ^ 3) := by
  have hp7 : Nat.Prime 7 := by decide
  have hp83 : Nat.Prime 83 := by decide
  have hσ7 : σ 1 (7 ^ 2) = 57 := by
    rw [sigma_prime_pow_two hp7]
    decide
  have hu7 : usigma (7 ^ 2) = 50 := by
    simpa using usigma_prime_pow hp7 (by decide : 0 < 2)
  have hu83 : usigma (83 ^ 3) = 1 + 83 ^ 3 :=
    usigma_prime_pow hp83 (by decide : 0 < 3)
  have hσ83 : σ 1 (83 ^ 3) = (83 ^ 4 - 1) / 82 := sigma_prime_pow_div hp83
  rw [usigma_five_pow_three, sigma_five_pow_three, hu7, hσ7, hu83, hσ83]
  norm_num

lemma not_seven_sigma_eq_ten_usigma_five_cube_seven_sq_eighty_three {k : ℕ}
    (hk : 2 ≤ k) :
    ¬ 7 * σ 1 (5 ^ 3) * σ 1 (7 ^ 2) * σ 1 (83 ^ k) =
        10 * usigma (5 ^ 3) * usigma (7 ^ 2) * usigma (83 ^ k) := by
  intro heq
  rcases eq_or_lt_of_le hk with hk2 | hk3
  · rw [← hk2] at heq
    exact eighty_three_sq_five_cube_forty_nine_undershoot.ne heq
  · have hover := ten_seven_overshoot_mono_three Nat.prime_five
        (by decide : Nat.Prime 7) (by decide : Nat.Prime 83)
        (by decide : 0 < 3) (by decide : 0 < 2) (by decide : 0 < 3)
        (le_refl _) (le_refl _) (Nat.succ_le_of_lt hk3)
        eighty_three_cube_five_cube_forty_nine_overshoot
    rw [← heq] at hover
    exact lt_irrefl _ hover

/-- `ρ(25) ρ(343) cap(p) < 10/7` for every `p ≥ 37`. -/
lemma seven_mul_twenty_five_seven_cube_cap {p : ℕ} (hp : 37 ≤ p) :
    7 * 31 * 400 * p ≤ 10 * 26 * 344 * (p - 1) := by
  have hp1 : 1 ≤ p := by omega
  have hp' : (37 : ℤ) ≤ p := Int.ofNat_le.mpr hp
  have hL : ((7 * 31 * 400 * p : ℕ) : ℤ) = 7 * 31 * 400 * (p : ℤ) := by
    push_cast; rfl
  have hR : ((10 * 26 * 344 * (p - 1) : ℕ) : ℤ) =
      10 * 26 * 344 * ((p : ℤ) - 1) := by
    rw [Nat.cast_mul, Nat.cast_mul, Nat.cast_mul, Nat.cast_sub hp1]
    push_cast; rfl
  have : (7 : ℤ) * 31 * 400 * p ≤ 10 * 26 * 344 * (p - 1) := by nlinarith
  exact Nat.cast_le.mp (by rw [hL, hR]; exact this)

lemma seven_sigma_lt_ten_usigma_five_sq_seven_cube_large {p k : ℕ}
    (hp : p.Prime) (hp37 : 37 ≤ p) (hk : 0 < k) :
    7 * σ 1 (5 ^ 2) * σ 1 (7 ^ 3) * σ 1 (p ^ k) <
      10 * usigma (5 ^ 2) * usigma (7 ^ 3) * usigma (p ^ k) := by
  have hσ5 : σ 1 (5 ^ 2) = 31 := by
    rw [sigma_prime_pow_two Nat.prime_five]
    decide
  have hu5 : usigma (5 ^ 2) = 26 := usigma_five_pow_two
  rw [hσ5, hu5, sigma_seven_pow_three, usigma_seven_pow_three]
  have hcp := sigma_lt_cap_usigma hp hk
  have hnum := seven_mul_twenty_five_seven_cube_cap hp37
  have hprod : (p - 1) * σ 1 (p ^ k) * (7 * 31 * 400) <
      p * usigma (p ^ k) * (7 * 31 * 400) :=
    Nat.mul_lt_mul_of_pos_right hcp (by decide)
  have h10 : p * usigma (p ^ k) * (7 * 31 * 400) ≤
      (p - 1) * usigma (p ^ k) * (10 * 26 * 344) := by
    have := Nat.mul_le_mul_right (usigma (p ^ k)) hnum
    have hL : 7 * 31 * 400 * p * usigma (p ^ k) =
        p * usigma (p ^ k) * (7 * 31 * 400) := by ring
    have hR : 10 * 26 * 344 * (p - 1) * usigma (p ^ k) =
        (p - 1) * usigma (p ^ k) * (10 * 26 * 344) := by ring
    have hthis : 7 * 31 * 400 * p * usigma (p ^ k) ≤
        10 * 26 * 344 * (p - 1) * usigma (p ^ k) := by
      simpa [mul_assoc, mul_left_comm, mul_comm] using this
    rw [hL, hR] at hthis
    exact hthis
  have hlt : (p - 1) * σ 1 (p ^ k) * (7 * 31 * 400) <
      (p - 1) * usigma (p ^ k) * (10 * 26 * 344) :=
    lt_of_lt_of_le hprod h10
  have hcancel : (p - 1) * (7 * 31 * 400 * σ 1 (p ^ k)) <
      (p - 1) * (10 * 26 * 344 * usigma (p ^ k)) := by
    have h1 : (p - 1) * (7 * 31 * 400 * σ 1 (p ^ k)) =
        (p - 1) * σ 1 (p ^ k) * (7 * 31 * 400) := by ring
    have h2 : (p - 1) * (10 * 26 * 344 * usigma (p ^ k)) =
        (p - 1) * usigma (p ^ k) * (10 * 26 * 344) := by ring
    rw [h1, h2]
    exact hlt
  exact Nat.lt_of_mul_lt_mul_left hcancel

/-- `ρ(25) ρ(343) ρ(p^2) > 10/7` for `23 ≤ p ≤ 31`. -/
lemma twenty_five_seven_cube_sq_overshoot {p : ℕ} (hp : p.Prime)
    (h23 : 23 ≤ p) (h31 : p ≤ 31) :
    10 * usigma (5 ^ 2) * usigma (7 ^ 3) * usigma (p ^ 2) <
      7 * σ 1 (5 ^ 2) * σ 1 (7 ^ 3) * σ 1 (p ^ 2) := by
  have hσ5 : σ 1 (5 ^ 2) = 31 := by
    rw [sigma_prime_pow_two Nat.prime_five]
    decide
  have hu5 : usigma (5 ^ 2) = 26 := usigma_five_pow_two
  rw [hσ5, hu5, usigma_seven_pow_three, sigma_seven_pow_three,
    usigma_prime_pow hp (by decide : 0 < 2), sigma_prime_pow_two hp]
  have hquad : 33 * p * p + 33 < 1085 * p := by
    have hle : 33 * p * p ≤ 33 * 31 * p := by
      have : p * p ≤ 31 * p := Nat.mul_le_mul_right p h31
      nlinarith
    have h1023 : 33 * 31 * p + 33 < 1085 * p := by
      have : 33 < 62 * p := by nlinarith
      nlinarith
    omega
  have hL : ((10 * 26 * 344 * (1 + p ^ 2) : ℕ) : ℤ) =
      10 * 26 * 344 * (1 + (p : ℤ) ^ 2) := by push_cast; rfl
  have hR : ((7 * 31 * 400 * (1 + p + p ^ 2) : ℕ) : ℤ) =
      7 * 31 * 400 * (1 + (p : ℤ) + (p : ℤ) ^ 2) := by push_cast; rfl
  have hint : (10 : ℤ) * 26 * 344 * (1 + p ^ 2) <
      7 * 31 * 400 * (1 + p + p ^ 2) := by
    have h1085 : (33 : ℤ) * p * p + 33 < 1085 * p := by exact_mod_cast hquad
    have hscale : (2640 : ℤ) * (1 + p ^ 2) < 80 * 1085 * p := by
      have : (33 : ℤ) * (1 + p ^ 2) < 1085 * p := by nlinarith
      have hmul := mul_lt_mul_of_pos_left this (by decide : (0 : ℤ) < 80)
      nlinarith
    nlinarith
  exact Nat.cast_lt.mp (by rw [hL, hR]; exact hint)

lemma twenty_five_seven_cube_pow_ge_two_overshoot {p k : ℕ} (hp : p.Prime)
    (h23 : 23 ≤ p) (h31 : p ≤ 31) (hk : 2 ≤ k) :
    10 * usigma (5 ^ 2) * usigma (7 ^ 3) * usigma (p ^ k) <
      7 * σ 1 (5 ^ 2) * σ 1 (7 ^ 3) * σ 1 (p ^ k) :=
  ten_seven_overshoot_mono_three Nat.prime_five (by decide : Nat.Prime 7) hp
    (by decide : 0 < 2) (by decide : 0 < 3) (by decide : 0 < 2)
    (le_refl _) (le_refl _) hk (twenty_five_seven_cube_sq_overshoot hp h23 h31)

lemma prime_ge_eighty_eq_eighty_three_or_ge_eighty_nine {p : ℕ}
    (hp : p.Prime) (h : 80 ≤ p) : p = 83 ∨ 89 ≤ p := by
  have hmem : p = 80 ∨ p = 81 ∨ p = 82 ∨ p = 83 ∨ p = 84 ∨ p = 85 ∨
      p = 86 ∨ p = 87 ∨ p = 88 ∨ 89 ≤ p := by omega
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | h89
  · exact (False.elim ((by decide : ¬ Nat.Prime 80) hp))
  · exact (False.elim ((by decide : ¬ Nat.Prime 81) hp))
  · exact (False.elim ((by decide : ¬ Nat.Prime 82) hp))
  · exact Or.inl rfl
  · exact (False.elim ((by decide : ¬ Nat.Prime 84) hp))
  · exact (False.elim ((by decide : ¬ Nat.Prime 85) hp))
  · exact (False.elim ((by decide : ¬ Nat.Prime 86) hp))
  · exact (False.elim ((by decide : ¬ Nat.Prime 87) hp))
  · exact (False.elim ((by decide : ¬ Nat.Prime 88) hp))
  · exact Or.inr h89

/-- `{5^3, 7^2, p^k}` cannot fill leftover `10/7` for `p ≥ 23` and `k ≥ 2`. -/
lemma not_seven_sigma_eq_ten_usigma_five_cube_seven_sq {p k : ℕ}
    (hp : p.Prime) (hp23 : 23 ≤ p) (hk : 2 ≤ k) :
    ¬ 7 * σ 1 (5 ^ 3) * σ 1 (7 ^ 2) * σ 1 (p ^ k) =
        10 * usigma (5 ^ 3) * usigma (7 ^ 2) * usigma (p ^ k) := by
  intro heq
  rcases le_or_gt p 79 with h79 | h80
  · exact (five_cube_forty_nine_pow_ge_two_overshoot hp hp23 h79 hk).ne' heq
  · have h80 : 80 ≤ p := by omega
    rcases prime_ge_eighty_eq_eighty_three_or_ge_eighty_nine hp h80 with rfl | h89
    · exact not_seven_sigma_eq_ten_usigma_five_cube_seven_sq_eighty_three hk heq
    · exact (seven_sigma_lt_ten_usigma_five_cube_seven_sq_large hp h89
        (by omega)).ne heq

lemma prime_ge_thirty_two_ge_thirty_seven {p : ℕ} (hp : p.Prime)
    (h : 32 ≤ p) : 37 ≤ p := by
  have hmem : p = 32 ∨ p = 33 ∨ p = 34 ∨ p = 35 ∨ p = 36 ∨ 37 ≤ p := by omega
  rcases hmem with rfl | rfl | rfl | rfl | rfl | h37
  · exact False.elim ((by decide : ¬ Nat.Prime 32) hp)
  · exact False.elim ((by decide : ¬ Nat.Prime 33) hp)
  · exact False.elim ((by decide : ¬ Nat.Prime 34) hp)
  · exact False.elim ((by decide : ¬ Nat.Prime 35) hp)
  · exact False.elim ((by decide : ¬ Nat.Prime 36) hp)
  · exact h37

/-- `{5^2, 7^3, p^k}` cannot fill leftover `10/7` for `p ≥ 23` and `k ≥ 2`. -/
lemma not_seven_sigma_eq_ten_usigma_five_sq_seven_cube {p k : ℕ}
    (hp : p.Prime) (hp23 : 23 ≤ p) (hk : 2 ≤ k) :
    ¬ 7 * σ 1 (5 ^ 2) * σ 1 (7 ^ 3) * σ 1 (p ^ k) =
        10 * usigma (5 ^ 2) * usigma (7 ^ 3) * usigma (p ^ k) := by
  intro heq
  rcases le_or_gt p 31 with h31 | h32
  · exact (twenty_five_seven_cube_pow_ge_two_overshoot hp hp23 h31 hk).ne' heq
  · have : 37 ≤ p := prime_ge_thirty_two_ge_thirty_seven hp (by omega)
    exact (seven_sigma_lt_ten_usigma_five_sq_seven_cube_large hp this
      (by omega)).ne heq

lemma sigma_seven_pow_four : σ 1 (7 ^ 4) = 2801 := by
  rw [sigma_prime_pow_div (by decide : Nat.Prime 7)]
  norm_num

lemma usigma_seven_pow_four : usigma (7 ^ 4) = 2402 := by
  rw [usigma_prime_pow (by decide : Nat.Prime 7) (by decide : 0 < 4)]
  decide

lemma sigma_seven_pow_five : σ 1 (7 ^ 5) = 19608 := by
  rw [sigma_prime_pow_div (by decide : Nat.Prime 7)]
  norm_num

lemma usigma_seven_pow_five : usigma (7 ^ 5) = 16808 := by
  rw [usigma_prime_pow (by decide : Nat.Prime 7) (by decide : 0 < 5)]
  decide

lemma sigma_seven_pow_six : σ 1 (7 ^ 6) = 137257 := by
  rw [sigma_prime_pow_div (by decide : Nat.Prime 7)]
  norm_num

lemma usigma_seven_pow_six : usigma (7 ^ 6) = 117650 := by
  rw [usigma_prime_pow (by decide : Nat.Prime 7) (by decide : 0 < 6)]
  decide

lemma sigma_seven_pow_seven : σ 1 (7 ^ 7) = 960800 := by
  rw [sigma_prime_pow_div (by decide : Nat.Prime 7)]
  norm_num

lemma usigma_seven_pow_seven : usigma (7 ^ 7) = 823544 := by
  rw [usigma_prime_pow (by decide : Nat.Prime 7) (by decide : 0 < 7)]
  decide

/-- `ρ(25) ρ(7^4) ρ(p^2) > 10/7` for `23 ≤ p ≤ 31`. -/
lemma twenty_five_seven_fourth_sq_overshoot {p : ℕ} (hp : p.Prime)
    (h23 : 23 ≤ p) (h31 : p ≤ 31) :
    10 * usigma (5 ^ 2) * usigma (7 ^ 4) * usigma (p ^ 2) <
      7 * σ 1 (5 ^ 2) * σ 1 (7 ^ 4) * σ 1 (p ^ 2) := by
  have hσ5 : σ 1 (5 ^ 2) = 31 := by
    rw [sigma_prime_pow_two Nat.prime_five]
    decide
  have hu5 : usigma (5 ^ 2) = 26 := usigma_five_pow_two
  rw [hσ5, hu5, usigma_seven_pow_four, sigma_seven_pow_four,
    usigma_prime_pow hp (by decide : 0 < 2), sigma_prime_pow_two hp]
  have hquad : 16703 * p * p + 16703 < 607817 * p := by
    have hle : 16703 * p * p ≤ 16703 * 31 * p := by
      have : p * p ≤ 31 * p := Nat.mul_le_mul_right p h31
      nlinarith
    have h1023 : 16703 * 31 * p + 16703 < 607817 * p := by
      have : 16703 < 90024 * p := by nlinarith
      nlinarith
    omega
  have hL : ((10 * 26 * 2402 * (1 + p ^ 2) : ℕ) : ℤ) =
      10 * 26 * 2402 * (1 + (p : ℤ) ^ 2) := by push_cast; rfl
  have hR : ((7 * 31 * 2801 * (1 + p + p ^ 2) : ℕ) : ℤ) =
      7 * 31 * 2801 * (1 + (p : ℤ) + (p : ℤ) ^ 2) := by push_cast; rfl
  have hint : (10 : ℤ) * 26 * 2402 * (1 + p ^ 2) <
      7 * 31 * 2801 * (1 + p + p ^ 2) := by
    have h247 : (16703 : ℤ) * p * p + 16703 < 607817 * p := by exact_mod_cast hquad
    nlinarith
  exact Nat.cast_lt.mp (by rw [hL, hR]; exact hint)

lemma twenty_five_seven_pow_ge_four_small_overshoot {p k b : ℕ} (hp : p.Prime)
    (h23 : 23 ≤ p) (h31 : p ≤ 31) (hb : 4 ≤ b) (hk : 2 ≤ k) :
    10 * usigma (5 ^ 2) * usigma (7 ^ b) * usigma (p ^ k) <
      7 * σ 1 (5 ^ 2) * σ 1 (7 ^ b) * σ 1 (p ^ k) :=
  ten_seven_overshoot_mono_three Nat.prime_five (by decide : Nat.Prime 7) hp
    (by decide : 0 < 2) (by decide : 0 < 4) (by decide : 0 < 2)
    (le_refl _) hb hk (twenty_five_seven_fourth_sq_overshoot hp h23 h31)

/-- `ρ(25) cap(7) cap(p) < 10/7` for every `p ≥ 41`. -/
lemma seven_mul_twenty_five_seven_cap {p : ℕ} (hp : 41 ≤ p) :
    7 * 7 * p * 31 ≤ 10 * 6 * (p - 1) * 26 := by
  have hp1 : 1 ≤ p := by omega
  have hp' : (41 : ℤ) ≤ p := Int.ofNat_le.mpr hp
  have hL : ((7 * 7 * p * 31 : ℕ) : ℤ) = (49 : ℤ) * p * 31 := by
    rw [Nat.cast_mul, Nat.cast_mul, Nat.cast_mul]; rfl
  have hR : ((10 * 6 * (p - 1) * 26 : ℕ) : ℤ) =
      (60 : ℤ) * ((p : ℤ) - 1) * 26 := by
    rw [Nat.cast_mul, Nat.cast_mul, Nat.cast_mul, Nat.cast_sub hp1]
    rfl
  have : (49 : ℤ) * p * 31 ≤ 60 * (p - 1) * 26 := by nlinarith
  exact Nat.cast_le.mp (by rw [hL, hR]; exact this)

lemma seven_sigma_lt_ten_usigma_five_sq_seven_large {p b k : ℕ}
    (hp : p.Prime) (hp41 : 41 ≤ p) (hb : 0 < b) (hk : 0 < k) :
    7 * σ 1 (5 ^ 2) * σ 1 (7 ^ b) * σ 1 (p ^ k) <
      10 * usigma (5 ^ 2) * usigma (7 ^ b) * usigma (p ^ k) := by
  have hσ5 : σ 1 (5 ^ 2) = 31 := by
    rw [sigma_prime_pow_two Nat.prime_five]
    decide
  have hu5 : usigma (5 ^ 2) = 26 := usigma_five_pow_two
  rw [hσ5, hu5]
  have h7 := six_sigma_lt_seven_usigma hb
  have hpcap := sigma_lt_cap_usigma hp hk
  have hu7 : 0 < usigma (7 ^ b) := by
    rw [usigma_prime_pow (by decide : Nat.Prime 7) hb]
    exact Nat.add_pos_left (by decide : 0 < 1) _
  have hcap := seven_mul_twenty_five_seven_cap hp41
  have hlt := seven_ten_of_two_caps_times_const (A := 6) (B := 7)
    (X := σ 1 (7 ^ b)) (Y := usigma (7 ^ b)) (C := p - 1) (D := p)
    (P := σ 1 (p ^ k)) (Q := usigma (p ^ k)) (S := 26) (T := 31)
    h7 hpcap hcap (by decide : 0 < 7) hu7 (by decide : 0 < 31)
  have hL : 7 * 31 * σ 1 (7 ^ b) * σ 1 (p ^ k) =
      7 * σ 1 (7 ^ b) * σ 1 (p ^ k) * 31 := by ring
  have hR : 10 * 26 * usigma (7 ^ b) * usigma (p ^ k) =
      10 * usigma (7 ^ b) * usigma (p ^ k) * 26 := by ring
  rw [hL, hR]
  exact hlt

lemma prime_eq_thirty_seven_or_ge_forty_one {p : ℕ} (hp : p.Prime)
    (h : 37 ≤ p) : p = 37 ∨ 41 ≤ p := by
  have hmem : p = 37 ∨ p = 38 ∨ p = 39 ∨ p = 40 ∨ 41 ≤ p := by omega
  rcases hmem with rfl | rfl | rfl | rfl | h41
  · exact Or.inl rfl
  · exact False.elim ((by decide : ¬ Nat.Prime 38) hp)
  · exact False.elim ((by decide : ¬ Nat.Prime 39) hp)
  · exact False.elim ((by decide : ¬ Nat.Prime 40) hp)
  · exact Or.inr h41

lemma seven_sigma_lt_ten_usigma_five_sq_seven_fourth_thirty_seven_sq :
    7 * σ 1 (5 ^ 2) * σ 1 (7 ^ 4) * σ 1 (37 ^ 2) <
      10 * usigma (5 ^ 2) * usigma (7 ^ 4) * usigma (37 ^ 2) := by
  have hp37 : Nat.Prime 37 := by decide
  have hσ5 : σ 1 (5 ^ 2) = 31 := by
    rw [sigma_prime_pow_two Nat.prime_five]
    decide
  have hu5 : usigma (5 ^ 2) = 26 := usigma_five_pow_two
  rw [hσ5, hu5, sigma_seven_pow_four, usigma_seven_pow_four,
    sigma_prime_pow_two hp37, usigma_prime_pow hp37 (by decide : 0 < 2)]
  norm_num

lemma seven_sigma_lt_ten_usigma_five_sq_seven_fifth_thirty_seven_sq :
    7 * σ 1 (5 ^ 2) * σ 1 (7 ^ 5) * σ 1 (37 ^ 2) <
      10 * usigma (5 ^ 2) * usigma (7 ^ 5) * usigma (37 ^ 2) := by
  have hp37 : Nat.Prime 37 := by decide
  have hσ5 : σ 1 (5 ^ 2) = 31 := by
    rw [sigma_prime_pow_two Nat.prime_five]
    decide
  have hu5 : usigma (5 ^ 2) = 26 := usigma_five_pow_two
  rw [hσ5, hu5, sigma_seven_pow_five, usigma_seven_pow_five,
    sigma_prime_pow_two hp37, usigma_prime_pow hp37 (by decide : 0 < 2)]
  norm_num

lemma twenty_five_seven_fourth_thirty_seven_cube_overshoot :
    10 * usigma (5 ^ 2) * usigma (7 ^ 4) * usigma (37 ^ 3) <
      7 * σ 1 (5 ^ 2) * σ 1 (7 ^ 4) * σ 1 (37 ^ 3) := by
  have hp37 : Nat.Prime 37 := by decide
  have hσ5 : σ 1 (5 ^ 2) = 31 := by
    rw [sigma_prime_pow_two Nat.prime_five]
    decide
  have hu5 : usigma (5 ^ 2) = 26 := usigma_five_pow_two
  have hu37 : usigma (37 ^ 3) = 1 + 37 ^ 3 :=
    usigma_prime_pow hp37 (by decide : 0 < 3)
  have hσ37 : σ 1 (37 ^ 3) = (37 ^ 4 - 1) / 36 := sigma_prime_pow_div hp37
  rw [hσ5, hu5, usigma_seven_pow_four, sigma_seven_pow_four, hu37, hσ37]
  norm_num

lemma twenty_five_seven_sixth_thirty_seven_sq_overshoot :
    10 * usigma (5 ^ 2) * usigma (7 ^ 6) * usigma (37 ^ 2) <
      7 * σ 1 (5 ^ 2) * σ 1 (7 ^ 6) * σ 1 (37 ^ 2) := by
  have hp37 : Nat.Prime 37 := by decide
  have hσ5 : σ 1 (5 ^ 2) = 31 := by
    rw [sigma_prime_pow_two Nat.prime_five]
    decide
  have hu5 : usigma (5 ^ 2) = 26 := usigma_five_pow_two
  rw [hσ5, hu5, usigma_seven_pow_six, sigma_seven_pow_six,
    usigma_prime_pow hp37 (by decide : 0 < 2), sigma_prime_pow_two hp37]
  norm_num

/-- `{5^2, 7^b, p^k}` with `b ≥ 4` cannot fill leftover `10/7` for `p ≥ 23`
and `k ≥ 2`. -/
lemma not_seven_sigma_eq_ten_usigma_five_sq_seven_pow_ge_four {p k b : ℕ}
    (hp : p.Prime) (hp23 : 23 ≤ p) (hb : 4 ≤ b) (hk : 2 ≤ k) :
    ¬ 7 * σ 1 (5 ^ 2) * σ 1 (7 ^ b) * σ 1 (p ^ k) =
        10 * usigma (5 ^ 2) * usigma (7 ^ b) * usigma (p ^ k) := by
  intro heq
  rcases le_or_gt p 31 with h31 | h32
  · exact (twenty_five_seven_pow_ge_four_small_overshoot hp hp23 h31 hb hk).ne'
      heq
  · have h37 : 37 ≤ p := prime_ge_thirty_two_ge_thirty_seven hp (by omega)
    rcases prime_eq_thirty_seven_or_ge_forty_one hp h37 with rfl | h41
    · rcases eq_or_lt_of_le hk with hk2 | hk3
      · rw [← hk2] at heq
        rcases eq_or_lt_of_le hb with hb4 | hb5
        · rw [← hb4] at heq
          exact seven_sigma_lt_ten_usigma_five_sq_seven_fourth_thirty_seven_sq.ne
            heq
        · have hb5' : 5 ≤ b := Nat.succ_le_of_lt hb5
          rcases eq_or_lt_of_le hb5' with hb5eq | hb6
          · rw [← hb5eq] at heq
            exact seven_sigma_lt_ten_usigma_five_sq_seven_fifth_thirty_seven_sq.ne
              heq
          · have hover := ten_seven_overshoot_mono_three Nat.prime_five
                (by decide : Nat.Prime 7) hp
                (by decide : 0 < 2) (by decide : 0 < 6) (by decide : 0 < 2)
                (le_refl _) (Nat.succ_le_of_lt hb6) (le_refl _)
                twenty_five_seven_sixth_thirty_seven_sq_overshoot
            rw [← heq] at hover
            exact lt_irrefl _ hover
      · have hover := ten_seven_overshoot_mono_three Nat.prime_five
            (by decide : Nat.Prime 7) hp
            (by decide : 0 < 2) (by decide : 0 < 4) (by decide : 0 < 3)
            (le_refl _) hb (Nat.succ_le_of_lt hk3)
            twenty_five_seven_fourth_thirty_seven_cube_overshoot
        rw [← heq] at hover
        exact lt_irrefl _ hover
    · exact (seven_sigma_lt_ten_usigma_five_sq_seven_large hp h41 (by omega)
        (by omega)).ne heq

lemma seven_mul_five_cube_eleven_sq_nineteen_cap :
    7 * 156 * 133 * 19 ≤ 10 * 126 * 122 * 18 := by decide

/-- `ρ(125) ρ(121) ρ(19^c) < 10/7`. -/
lemma seven_sigma_lt_ten_usigma_five_cube_eleven_sq_nineteen {c : ℕ}
    (hc : 0 < c) :
    7 * σ 1 (5 ^ 3) * σ 1 (11 ^ 2) * σ 1 (19 ^ c) <
      10 * usigma (5 ^ 3) * usigma (11 ^ 2) * usigma (19 ^ c) := by
  have hp19 : Nat.Prime 19 := by decide
  rw [sigma_five_pow_three, usigma_five_pow_three, sigma_eleven_pow_two,
    usigma_eleven_pow_two]
  have hcp := sigma_lt_cap_usigma hp19 hc
  have hnum := seven_mul_five_cube_eleven_sq_nineteen_cap
  have hprod : 18 * σ 1 (19 ^ c) * (7 * 156 * 133) <
      19 * usigma (19 ^ c) * (7 * 156 * 133) :=
    Nat.mul_lt_mul_of_pos_right hcp (by decide)
  have h10 : 19 * usigma (19 ^ c) * (7 * 156 * 133) ≤
      18 * usigma (19 ^ c) * (10 * 126 * 122) := by
    have := Nat.mul_le_mul_right (usigma (19 ^ c)) hnum
    have hL : 7 * 156 * 133 * 19 * usigma (19 ^ c) =
        19 * usigma (19 ^ c) * (7 * 156 * 133) := by ring
    have hR : 10 * 126 * 122 * 18 * usigma (19 ^ c) =
        18 * usigma (19 ^ c) * (10 * 126 * 122) := by ring
    have hthis : 7 * 156 * 133 * 19 * usigma (19 ^ c) ≤
        10 * 126 * 122 * 18 * usigma (19 ^ c) := by
      simpa [mul_assoc, mul_left_comm, mul_comm] using this
    rw [hL, hR] at hthis
    exact hthis
  have hlt : 18 * σ 1 (19 ^ c) * (7 * 156 * 133) <
      18 * usigma (19 ^ c) * (10 * 126 * 122) :=
    lt_of_lt_of_le hprod h10
  have hcancel : 18 * (7 * 156 * 133 * σ 1 (19 ^ c)) <
      18 * (10 * 126 * 122 * usigma (19 ^ c)) := by
    have h1 : 18 * (7 * 156 * 133 * σ 1 (19 ^ c)) =
        18 * σ 1 (19 ^ c) * (7 * 156 * 133) := by ring
    have h2 : 18 * (10 * 126 * 122 * usigma (19 ^ c)) =
        18 * usigma (19 ^ c) * (10 * 126 * 122) := by ring
    rw [h1, h2]
    exact hlt
  exact Nat.lt_of_mul_lt_mul_left hcancel

lemma five_cube_eleven_cube_nineteen_sq_overshoot :
    10 * usigma (5 ^ 3) * usigma (11 ^ 3) * usigma (19 ^ 2) <
      7 * σ 1 (5 ^ 3) * σ 1 (11 ^ 3) * σ 1 (19 ^ 2) := by
  have hp11 : Nat.Prime 11 := by decide
  have hp19 : Nat.Prime 19 := by decide
  have hu11 : usigma (11 ^ 3) = 1 + 11 ^ 3 :=
    usigma_prime_pow hp11 (by decide : 0 < 3)
  have hσ11 : σ 1 (11 ^ 3) = (11 ^ 4 - 1) / 10 := sigma_prime_pow_div hp11
  rw [usigma_five_pow_three, sigma_five_pow_three, hu11, hσ11,
    usigma_prime_pow hp19 (by decide : 0 < 2), sigma_prime_pow_two hp19]
  norm_num

lemma five_fourth_eleven_sq_nineteen_sq_overshoot :
    10 * usigma (5 ^ 4) * usigma (11 ^ 2) * usigma (19 ^ 2) <
      7 * σ 1 (5 ^ 4) * σ 1 (11 ^ 2) * σ 1 (19 ^ 2) := by
  have hp19 : Nat.Prime 19 := by decide
  have hu5 : usigma (5 ^ 4) = 1 + 5 ^ 4 :=
    usigma_prime_pow Nat.prime_five (by decide : 0 < 4)
  have hσ5 : σ 1 (5 ^ 4) = (5 ^ 5 - 1) / 4 := sigma_prime_pow_div Nat.prime_five
  rw [hu5, hσ5, sigma_eleven_pow_two, usigma_eleven_pow_two,
    usigma_prime_pow hp19 (by decide : 0 < 2), sigma_prime_pow_two hp19]
  norm_num

/-- `{5, 11, 19}` cannot fill leftover `10/7`. -/
lemma not_seven_sigma_eq_ten_usigma_five_eleven_nineteen {a b c : ℕ}
    (ha : 2 ≤ a) (hb : 2 ≤ b) (hc : 2 ≤ c) :
    ¬ 7 * σ 1 (5 ^ a) * σ 1 (11 ^ b) * σ 1 (19 ^ c) =
        10 * usigma (5 ^ a) * usigma (11 ^ b) * usigma (19 ^ c) := by
  intro heq
  rcases eq_or_lt_of_le ha with ha2 | ha3
  · rw [← ha2] at heq
    exact (seven_sigma_lt_ten_usigma_five_sq_eleven_large
      (by decide : Nat.Prime 19) (by decide : 13 ≤ 19) (by omega) (by omega)).ne heq
  · have ha3' : 3 ≤ a := Nat.succ_le_of_lt ha3
    rcases eq_or_lt_of_le ha3' with ha3eq | ha4
    · rw [← ha3eq] at heq
      rcases eq_or_lt_of_le hb with hb2 | hb3
      · rw [← hb2] at heq
        exact (seven_sigma_lt_ten_usigma_five_cube_eleven_sq_nineteen
          (by omega)).ne heq
      · have hover := ten_seven_overshoot_mono_three Nat.prime_five
            (by decide : Nat.Prime 11) (by decide : Nat.Prime 19)
            (by decide : 0 < 3) (by decide : 0 < 3) (by decide : 0 < 2)
            (le_refl _) (Nat.succ_le_of_lt hb3) hc
            five_cube_eleven_cube_nineteen_sq_overshoot
        rw [← heq] at hover
        exact lt_irrefl _ hover
    · have hover := ten_seven_overshoot_mono_three Nat.prime_five
          (by decide : Nat.Prime 11) (by decide : Nat.Prime 19)
          (by decide : 0 < 4) (by decide : 0 < 2) (by decide : 0 < 2)
          (Nat.succ_le_of_lt ha4) hb hc five_fourth_eleven_sq_nineteen_sq_overshoot
      rw [← heq] at hover
      exact lt_irrefl _ hover

lemma five_seven_eleven_mul_overshoot {a b c n : ℕ}
    (ha : 2 ≤ a) (hb : 2 ≤ b) (hc : 2 ≤ c) (hn : n ≠ 0) :
    10 * usigma (5 ^ a) * usigma (7 ^ b) * usigma (11 ^ c) * usigma n <
      7 * σ 1 (5 ^ a) * σ 1 (7 ^ b) * σ 1 (11 ^ c) * σ 1 n := by
  have hover := five_seven_eleven_pow_ge_two_overshoot ha hb hc
  have h := ten_seven_overshoot_mul (s := usigma (5 ^ a) * usigma (7 ^ b) *
      usigma (11 ^ c)) (t := σ 1 (5 ^ a) * σ 1 (7 ^ b) * σ 1 (11 ^ c)) hn
      (by simpa [mul_assoc] using hover)
  simpa [mul_assoc] using h

lemma seven_mul_five_cube_eleven_twenty_three_cap :
    7 * 11 * 23 * 156 ≤ 10 * 10 * 22 * 126 := by decide

/-- `ρ(125) cap(11) cap(23) < 10/7`. -/
lemma seven_sigma_lt_ten_usigma_five_cube_eleven_twenty_three {b c : ℕ}
    (hb : 0 < b) (hc : 0 < c) :
    7 * σ 1 (5 ^ 3) * σ 1 (11 ^ b) * σ 1 (23 ^ c) <
      10 * usigma (5 ^ 3) * usigma (11 ^ b) * usigma (23 ^ c) := by
  have hp23 : Nat.Prime 23 := by decide
  rw [sigma_five_pow_three, usigma_five_pow_three]
  have h11 := sigma_lt_cap_usigma (by decide : Nat.Prime 11) hb
  have h23 := sigma_lt_cap_usigma hp23 hc
  have hu11 : 0 < usigma (11 ^ b) := by
    rw [usigma_prime_pow (by decide : Nat.Prime 11) hb]
    exact Nat.add_pos_left (by decide : 0 < 1) _
  have hcap := seven_mul_five_cube_eleven_twenty_three_cap
  have hlt := seven_ten_of_two_caps_times_const (A := 10) (B := 11)
    (X := σ 1 (11 ^ b)) (Y := usigma (11 ^ b)) (C := 22) (D := 23)
    (P := σ 1 (23 ^ c)) (Q := usigma (23 ^ c)) (S := 126) (T := 156)
    h11 h23 hcap (by decide : 0 < 11) hu11 (by decide : 0 < 156)
  have hL : 7 * 156 * σ 1 (11 ^ b) * σ 1 (23 ^ c) =
      7 * σ 1 (11 ^ b) * σ 1 (23 ^ c) * 156 := by ring
  have hR : 10 * 126 * usigma (11 ^ b) * usigma (23 ^ c) =
      10 * usigma (11 ^ b) * usigma (23 ^ c) * 126 := by ring
  rw [hL, hR]
  exact hlt

lemma seven_mul_five_eleven_sq_twenty_three_cap :
    7 * 5 * 23 * 133 ≤ 10 * 4 * 22 * 122 := by decide

/-- `ρ(5^a) ρ(121) ρ(23^c) < 10/7`. -/
lemma seven_sigma_lt_ten_usigma_five_eleven_sq_twenty_three {a c : ℕ}
    (ha : 0 < a) (hc : 0 < c) :
    7 * σ 1 (5 ^ a) * σ 1 (11 ^ 2) * σ 1 (23 ^ c) <
      10 * usigma (5 ^ a) * usigma (11 ^ 2) * usigma (23 ^ c) := by
  have hp23 : Nat.Prime 23 := by decide
  rw [sigma_eleven_pow_two, usigma_eleven_pow_two]
  have h5 := four_sigma_lt_five_usigma ha
  have h23 := sigma_lt_cap_usigma hp23 hc
  have hu5 : 0 < usigma (5 ^ a) := by
    rw [usigma_prime_pow Nat.prime_five ha]
    exact Nat.add_pos_left (by decide : 0 < 1) _
  have hcap := seven_mul_five_eleven_sq_twenty_three_cap
  have hlt := seven_ten_of_two_caps_times_const (A := 4) (B := 5)
    (X := σ 1 (5 ^ a)) (Y := usigma (5 ^ a)) (C := 22) (D := 23)
    (P := σ 1 (23 ^ c)) (Q := usigma (23 ^ c)) (S := 122) (T := 133)
    h5 h23 hcap (by decide : 0 < 5) hu5 (by decide : 0 < 133)
  have hL : 7 * σ 1 (5 ^ a) * 133 * σ 1 (23 ^ c) =
      7 * σ 1 (5 ^ a) * σ 1 (23 ^ c) * 133 := by ring
  have hR : 10 * usigma (5 ^ a) * 122 * usigma (23 ^ c) =
      10 * usigma (5 ^ a) * usigma (23 ^ c) * 122 := by ring
  rw [hL, hR]
  exact hlt

lemma five_fourth_eleven_cube_twenty_three_sq_overshoot :
    10 * usigma (5 ^ 4) * usigma (11 ^ 3) * usigma (23 ^ 2) <
      7 * σ 1 (5 ^ 4) * σ 1 (11 ^ 3) * σ 1 (23 ^ 2) := by
  have hp11 : Nat.Prime 11 := by decide
  have hp23 : Nat.Prime 23 := by decide
  have hu5 : usigma (5 ^ 4) = 1 + 5 ^ 4 :=
    usigma_prime_pow Nat.prime_five (by decide : 0 < 4)
  have hσ5 : σ 1 (5 ^ 4) = (5 ^ 5 - 1) / 4 := sigma_prime_pow_div Nat.prime_five
  have hu11 : usigma (11 ^ 3) = 1 + 11 ^ 3 :=
    usigma_prime_pow hp11 (by decide : 0 < 3)
  have hσ11 : σ 1 (11 ^ 3) = (11 ^ 4 - 1) / 10 := sigma_prime_pow_div hp11
  rw [hu5, hσ5, hu11, hσ11, usigma_prime_pow hp23 (by decide : 0 < 2),
    sigma_prime_pow_two hp23]
  norm_num

/-- `{5, 11, 23}` cannot fill leftover `10/7`. -/
lemma not_seven_sigma_eq_ten_usigma_five_eleven_twenty_three {a b c : ℕ}
    (ha : 2 ≤ a) (hb : 2 ≤ b) (hc : 2 ≤ c) :
    ¬ 7 * σ 1 (5 ^ a) * σ 1 (11 ^ b) * σ 1 (23 ^ c) =
        10 * usigma (5 ^ a) * usigma (11 ^ b) * usigma (23 ^ c) := by
  intro heq
  rcases eq_or_lt_of_le ha with ha2 | ha3
  · rw [← ha2] at heq
    exact (seven_sigma_lt_ten_usigma_five_sq_eleven_large
      (by decide : Nat.Prime 23) (by decide : 13 ≤ 23) (by omega) (by omega)).ne heq
  · have ha3' : 3 ≤ a := Nat.succ_le_of_lt ha3
    rcases eq_or_lt_of_le ha3' with ha3eq | ha4
    · rw [← ha3eq] at heq
      exact (seven_sigma_lt_ten_usigma_five_cube_eleven_twenty_three
        (by omega) (by omega)).ne heq
    · rcases eq_or_lt_of_le hb with hb2 | hb3
      · rw [← hb2] at heq
        exact (seven_sigma_lt_ten_usigma_five_eleven_sq_twenty_three
          (by omega) (by omega)).ne heq
      · have hover := ten_seven_overshoot_mono_three Nat.prime_five
            (by decide : Nat.Prime 11) (by decide : Nat.Prime 23)
            (by decide : 0 < 4) (by decide : 0 < 3) (by decide : 0 < 2)
            (Nat.succ_le_of_lt ha4) (Nat.succ_le_of_lt hb3) hc
            five_fourth_eleven_cube_twenty_three_sq_overshoot
        rw [← heq] at hover
        exact lt_irrefl _ hover

lemma seven_mul_twenty_five_thirteen_seventeen_cap :
    7 * 13 * 17 * 31 ≤ 10 * 12 * 16 * 26 := by decide

/-- `{5^2, 13^b, 17^c}` undershoots leftover `10/7`. -/
lemma seven_sigma_lt_ten_usigma_five_sq_thirteen_seventeen {b c : ℕ}
    (hb : 0 < b) (hc : 0 < c) :
    7 * σ 1 (5 ^ 2) * σ 1 (13 ^ b) * σ 1 (17 ^ c) <
      10 * usigma (5 ^ 2) * usigma (13 ^ b) * usigma (17 ^ c) := by
  have hp13 : Nat.Prime 13 := by decide
  have hp17 : Nat.Prime 17 := by decide
  have hσ5 : σ 1 (5 ^ 2) = 31 := by
    rw [sigma_prime_pow_two Nat.prime_five]
    decide
  have hu5 : usigma (5 ^ 2) = 26 := usigma_five_pow_two
  rw [hσ5, hu5]
  have h13 := sigma_lt_cap_usigma hp13 hb
  have h17 := sigma_lt_cap_usigma hp17 hc
  have hu13 : 0 < usigma (13 ^ b) := by
    rw [usigma_prime_pow hp13 hb]
    exact Nat.add_pos_left (by decide : 0 < 1) _
  have hcap := seven_mul_twenty_five_thirteen_seventeen_cap
  have hlt := seven_ten_of_two_caps_times_const (A := 12) (B := 13)
    (X := σ 1 (13 ^ b)) (Y := usigma (13 ^ b)) (C := 16) (D := 17)
    (P := σ 1 (17 ^ c)) (Q := usigma (17 ^ c)) (S := 26) (T := 31)
    h13 h17 hcap (by decide : 0 < 13) hu13 (by decide : 0 < 31)
  have hL : 7 * 31 * σ 1 (13 ^ b) * σ 1 (17 ^ c) =
      7 * σ 1 (13 ^ b) * σ 1 (17 ^ c) * 31 := by ring
  have hR : 10 * 26 * usigma (13 ^ b) * usigma (17 ^ c) =
      10 * usigma (13 ^ b) * usigma (17 ^ c) * 26 := by ring
  rw [hL, hR]
  exact hlt

lemma seven_mul_five_cube_thirteen_seventeen_cap :
    7 * 13 * 17 * 156 ≤ 10 * 12 * 16 * 126 := by decide

/-- `{5^3, 13^b, 17^c}` undershoots leftover `10/7`. -/
lemma seven_sigma_lt_ten_usigma_five_cube_thirteen_seventeen {b c : ℕ}
    (hb : 0 < b) (hc : 0 < c) :
    7 * σ 1 (5 ^ 3) * σ 1 (13 ^ b) * σ 1 (17 ^ c) <
      10 * usigma (5 ^ 3) * usigma (13 ^ b) * usigma (17 ^ c) := by
  have hp13 : Nat.Prime 13 := by decide
  have hp17 : Nat.Prime 17 := by decide
  rw [sigma_five_pow_three, usigma_five_pow_three]
  have h13 := sigma_lt_cap_usigma hp13 hb
  have h17 := sigma_lt_cap_usigma hp17 hc
  have hu13 : 0 < usigma (13 ^ b) := by
    rw [usigma_prime_pow hp13 hb]
    exact Nat.add_pos_left (by decide : 0 < 1) _
  have hcap := seven_mul_five_cube_thirteen_seventeen_cap
  have hlt := seven_ten_of_two_caps_times_const (A := 12) (B := 13)
    (X := σ 1 (13 ^ b)) (Y := usigma (13 ^ b)) (C := 16) (D := 17)
    (P := σ 1 (17 ^ c)) (Q := usigma (17 ^ c)) (S := 126) (T := 156)
    h13 h17 hcap (by decide : 0 < 13) hu13 (by decide : 0 < 156)
  have hL : 7 * 156 * σ 1 (13 ^ b) * σ 1 (17 ^ c) =
      7 * σ 1 (13 ^ b) * σ 1 (17 ^ c) * 156 := by ring
  have hR : 10 * 126 * usigma (13 ^ b) * usigma (17 ^ c) =
      10 * usigma (13 ^ b) * usigma (17 ^ c) * 126 := by ring
  rw [hL, hR]
  exact hlt

lemma seven_mul_five_thirteen_sq_seventeen_sq_cap :
    7 * 5 * 183 * 307 ≤ 10 * 4 * 170 * 290 := by
  norm_num

/-- `ρ(5^a) ρ(169) ρ(289) < 10/7`. -/
lemma seven_sigma_lt_ten_usigma_five_thirteen_seventeen_sq {a : ℕ}
    (ha : 0 < a) :
    7 * σ 1 (5 ^ a) * σ 1 (13 ^ 2) * σ 1 (17 ^ 2) <
      10 * usigma (5 ^ a) * usigma (13 ^ 2) * usigma (17 ^ 2) := by
  have hp13 : Nat.Prime 13 := by decide
  have hp17 : Nat.Prime 17 := by decide
  have hσ13 : σ 1 (13 ^ 2) = 183 := by
    rw [sigma_prime_pow_two hp13]
    norm_num
  have hu13 : usigma (13 ^ 2) = 170 := by
    simpa using usigma_prime_pow hp13 (by decide : 0 < 2)
  have hσ17 : σ 1 (17 ^ 2) = 307 := by
    rw [sigma_prime_pow_two hp17]
    norm_num
  have hu17 : usigma (17 ^ 2) = 290 := by
    simpa using usigma_prime_pow hp17 (by decide : 0 < 2)
  rw [hσ13, hu13, hσ17, hu17]
  have h5 := four_sigma_lt_five_usigma ha
  have hpos : 0 < 7 * 183 * 307 := by norm_num
  have hprod : 4 * σ 1 (5 ^ a) * (7 * 183 * 307) <
      5 * usigma (5 ^ a) * (7 * 183 * 307) :=
    Nat.mul_lt_mul_of_pos_right h5 hpos
  have hnum := seven_mul_five_thirteen_sq_seventeen_sq_cap
  have h10 : 5 * usigma (5 ^ a) * (7 * 183 * 307) ≤
      4 * usigma (5 ^ a) * (10 * 170 * 290) := by
    have := Nat.mul_le_mul_right (usigma (5 ^ a)) hnum
    have hL : 7 * 5 * 183 * 307 * usigma (5 ^ a) =
        5 * usigma (5 ^ a) * (7 * 183 * 307) := by ring
    have hR : 10 * 4 * 170 * 290 * usigma (5 ^ a) =
        4 * usigma (5 ^ a) * (10 * 170 * 290) := by ring
    have hthis : 7 * 5 * 183 * 307 * usigma (5 ^ a) ≤
        10 * 4 * 170 * 290 * usigma (5 ^ a) := by
      simpa [mul_assoc, mul_left_comm, mul_comm] using this
    rw [hL, hR] at hthis
    exact hthis
  have hlt : 4 * σ 1 (5 ^ a) * (7 * 183 * 307) <
      4 * usigma (5 ^ a) * (10 * 170 * 290) :=
    lt_of_lt_of_le hprod h10
  have hcancel : 4 * (7 * σ 1 (5 ^ a) * 183 * 307) <
      4 * (10 * usigma (5 ^ a) * 170 * 290) := by
    have h1 : 4 * (7 * σ 1 (5 ^ a) * 183 * 307) =
        4 * σ 1 (5 ^ a) * (7 * 183 * 307) := by ring
    have h2 : 4 * (10 * usigma (5 ^ a) * 170 * 290) =
        4 * usigma (5 ^ a) * (10 * 170 * 290) := by ring
    rw [h1, h2]
    exact hlt
  exact Nat.lt_of_mul_lt_mul_left hcancel

lemma sigma_five_pow_four : σ 1 (5 ^ 4) = 781 := by
  rw [sigma_prime_pow_div Nat.prime_five]
  norm_num

lemma usigma_five_pow_four : usigma (5 ^ 4) = 626 := by
  rw [usigma_prime_pow Nat.prime_five (by decide : 0 < 4)]
  decide

lemma seven_mul_five_fourth_thirteen_sq_seventeen_cap :
    7 * 781 * 183 * 17 ≤ 10 * 626 * 170 * 16 := by
  norm_num

/-- `ρ(625) ρ(169) ρ(17^c) < 10/7`. -/
lemma seven_sigma_lt_ten_usigma_five_fourth_thirteen_sq_seventeen {c : ℕ}
    (hc : 0 < c) :
    7 * σ 1 (5 ^ 4) * σ 1 (13 ^ 2) * σ 1 (17 ^ c) <
      10 * usigma (5 ^ 4) * usigma (13 ^ 2) * usigma (17 ^ c) := by
  have hp13 : Nat.Prime 13 := by decide
  have hp17 : Nat.Prime 17 := by decide
  have hσ13 : σ 1 (13 ^ 2) = 183 := by
    rw [sigma_prime_pow_two hp13]
    decide
  have hu13 : usigma (13 ^ 2) = 170 := by
    simpa using usigma_prime_pow hp13 (by decide : 0 < 2)
  rw [sigma_five_pow_four, usigma_five_pow_four, hσ13, hu13]
  have h17 := sigma_lt_cap_usigma hp17 hc
  have hnum := seven_mul_five_fourth_thirteen_sq_seventeen_cap
  have hprod : 16 * σ 1 (17 ^ c) * (7 * 781 * 183) <
      17 * usigma (17 ^ c) * (7 * 781 * 183) :=
    Nat.mul_lt_mul_of_pos_right h17 (by norm_num : 0 < 7 * 781 * 183)
  have h10 : 17 * usigma (17 ^ c) * (7 * 781 * 183) ≤
      16 * usigma (17 ^ c) * (10 * 626 * 170) := by
    have := Nat.mul_le_mul_right (usigma (17 ^ c)) hnum
    have hL : 7 * 781 * 183 * 17 * usigma (17 ^ c) =
        17 * usigma (17 ^ c) * (7 * 781 * 183) := by ring
    have hR : 10 * 626 * 170 * 16 * usigma (17 ^ c) =
        16 * usigma (17 ^ c) * (10 * 626 * 170) := by ring
    have hthis : 7 * 781 * 183 * 17 * usigma (17 ^ c) ≤
        10 * 626 * 170 * 16 * usigma (17 ^ c) := by
      simpa [mul_assoc, mul_left_comm, mul_comm] using this
    rw [hL, hR] at hthis
    exact hthis
  have hlt : 16 * σ 1 (17 ^ c) * (7 * 781 * 183) <
      16 * usigma (17 ^ c) * (10 * 626 * 170) :=
    lt_of_lt_of_le hprod h10
  have hcancel : 16 * (7 * 781 * 183 * σ 1 (17 ^ c)) <
      16 * (10 * 626 * 170 * usigma (17 ^ c)) := by
    have h1 : 16 * (7 * 781 * 183 * σ 1 (17 ^ c)) =
        16 * σ 1 (17 ^ c) * (7 * 781 * 183) := by ring
    have h2 : 16 * (10 * 626 * 170 * usigma (17 ^ c)) =
        16 * usigma (17 ^ c) * (10 * 626 * 170) := by ring
    rw [h1, h2]
    exact hlt
  exact Nat.lt_of_mul_lt_mul_left hcancel

lemma five_fourth_thirteen_cube_seventeen_sq_overshoot :
    10 * usigma (5 ^ 4) * usigma (13 ^ 3) * usigma (17 ^ 2) <
      7 * σ 1 (5 ^ 4) * σ 1 (13 ^ 3) * σ 1 (17 ^ 2) := by
  have hp13 : Nat.Prime 13 := by decide
  have hp17 : Nat.Prime 17 := by decide
  have hu13 : usigma (13 ^ 3) = 1 + 13 ^ 3 :=
    usigma_prime_pow hp13 (by decide : 0 < 3)
  have hσ13 : σ 1 (13 ^ 3) = (13 ^ 4 - 1) / 12 := sigma_prime_pow_div hp13
  rw [usigma_five_pow_four, sigma_five_pow_four, hu13, hσ13,
    usigma_prime_pow hp17 (by decide : 0 < 2), sigma_prime_pow_two hp17]
  norm_num

lemma five_fifth_thirteen_sq_seventeen_cube_overshoot :
    10 * usigma (5 ^ 5) * usigma (13 ^ 2) * usigma (17 ^ 3) <
      7 * σ 1 (5 ^ 5) * σ 1 (13 ^ 2) * σ 1 (17 ^ 3) := by
  have hp13 : Nat.Prime 13 := by decide
  have hp17 : Nat.Prime 17 := by decide
  have hu5 : usigma (5 ^ 5) = 1 + 5 ^ 5 :=
    usigma_prime_pow Nat.prime_five (by decide : 0 < 5)
  have hσ5 : σ 1 (5 ^ 5) = (5 ^ 6 - 1) / 4 := sigma_prime_pow_div Nat.prime_five
  have hu13 : usigma (13 ^ 2) = 170 := by
    simpa using usigma_prime_pow hp13 (by decide : 0 < 2)
  have hσ13 : σ 1 (13 ^ 2) = 183 := by
    rw [sigma_prime_pow_two hp13]
    decide
  have hu17 : usigma (17 ^ 3) = 1 + 17 ^ 3 :=
    usigma_prime_pow hp17 (by decide : 0 < 3)
  have hσ17 : σ 1 (17 ^ 3) = (17 ^ 4 - 1) / 16 := sigma_prime_pow_div hp17
  rw [hu5, hσ5, hu13, hσ13, hu17, hσ17]
  norm_num

/-- `{5, 13, 17}` cannot fill leftover `10/7`. -/
lemma not_seven_sigma_eq_ten_usigma_five_thirteen_seventeen {a b c : ℕ}
    (ha : 2 ≤ a) (hb : 2 ≤ b) (hc : 2 ≤ c) :
    ¬ 7 * σ 1 (5 ^ a) * σ 1 (13 ^ b) * σ 1 (17 ^ c) =
        10 * usigma (5 ^ a) * usigma (13 ^ b) * usigma (17 ^ c) := by
  intro heq
  rcases eq_or_lt_of_le ha with ha2 | ha3
  · rw [← ha2] at heq
    exact (seven_sigma_lt_ten_usigma_five_sq_thirteen_seventeen
      (by omega) (by omega)).ne heq
  · have ha3' : 3 ≤ a := Nat.succ_le_of_lt ha3
    rcases eq_or_lt_of_le ha3' with ha3eq | ha4
    · rw [← ha3eq] at heq
      exact (seven_sigma_lt_ten_usigma_five_cube_thirteen_seventeen
        (by omega) (by omega)).ne heq
    · have ha4' : 4 ≤ a := Nat.succ_le_of_lt ha4
      rcases eq_or_lt_of_le hb with hb2 | hb3
      · rw [← hb2] at heq
        rcases eq_or_lt_of_le hc with hc2 | hc3
        · rw [← hc2] at heq
          exact (seven_sigma_lt_ten_usigma_five_thirteen_seventeen_sq
            (by omega)).ne heq
        · rcases eq_or_lt_of_le ha4' with ha4eq | ha5
          · rw [← ha4eq] at heq
            exact (seven_sigma_lt_ten_usigma_five_fourth_thirteen_sq_seventeen
              (by omega)).ne heq
          · have hover := ten_seven_overshoot_mono_three Nat.prime_five
                (by decide : Nat.Prime 13) (by decide : Nat.Prime 17)
                (by decide : 0 < 5) (by decide : 0 < 2) (by decide : 0 < 3)
                (Nat.succ_le_of_lt ha5) (le_refl _) (Nat.succ_le_of_lt hc3)
                five_fifth_thirteen_sq_seventeen_cube_overshoot
            rw [← heq] at hover
            exact lt_irrefl _ hover
      · have hover := ten_seven_overshoot_mono_three Nat.prime_five
            (by decide : Nat.Prime 13) (by decide : Nat.Prime 17)
            (by decide : 0 < 4) (by decide : 0 < 3) (by decide : 0 < 2)
            ha4' (Nat.succ_le_of_lt hb3) hc
            five_fourth_thirteen_cube_seventeen_sq_overshoot
        rw [← heq] at hover
        exact lt_irrefl _ hover

lemma seven_mul_twenty_five_thirteen_nineteen_cap :
    7 * 13 * 19 * 31 ≤ 10 * 12 * 18 * 26 := by
  norm_num

/-- `{5^2, 13^b, 19^c}` undershoots leftover `10/7`. -/
lemma seven_sigma_lt_ten_usigma_five_sq_thirteen_nineteen {b c : ℕ}
    (hb : 0 < b) (hc : 0 < c) :
    7 * σ 1 (5 ^ 2) * σ 1 (13 ^ b) * σ 1 (19 ^ c) <
      10 * usigma (5 ^ 2) * usigma (13 ^ b) * usigma (19 ^ c) := by
  have hp13 : Nat.Prime 13 := by decide
  have hp19 : Nat.Prime 19 := by decide
  have hσ5 : σ 1 (5 ^ 2) = 31 := by
    rw [sigma_prime_pow_two Nat.prime_five]
    decide
  have hu5 : usigma (5 ^ 2) = 26 := usigma_five_pow_two
  rw [hσ5, hu5]
  have h13 := sigma_lt_cap_usigma hp13 hb
  have h19 := sigma_lt_cap_usigma hp19 hc
  have hu13 : 0 < usigma (13 ^ b) := by
    rw [usigma_prime_pow hp13 hb]
    exact Nat.add_pos_left (by decide : 0 < 1) _
  have hcap := seven_mul_twenty_five_thirteen_nineteen_cap
  have hlt := seven_ten_of_two_caps_times_const (A := 12) (B := 13)
    (X := σ 1 (13 ^ b)) (Y := usigma (13 ^ b)) (C := 18) (D := 19)
    (P := σ 1 (19 ^ c)) (Q := usigma (19 ^ c)) (S := 26) (T := 31)
    h13 h19 hcap (by decide : 0 < 13) hu13 (by decide : 0 < 31)
  have hL : 7 * 31 * σ 1 (13 ^ b) * σ 1 (19 ^ c) =
      7 * σ 1 (13 ^ b) * σ 1 (19 ^ c) * 31 := by ring
  have hR : 10 * 26 * usigma (13 ^ b) * usigma (19 ^ c) =
      10 * usigma (13 ^ b) * usigma (19 ^ c) * 26 := by ring
  rw [hL, hR]
  exact hlt

lemma seven_mul_five_cube_thirteen_nineteen_cap :
    7 * 13 * 19 * 156 ≤ 10 * 12 * 18 * 126 := by
  norm_num

/-- `{5^3, 13^b, 19^c}` undershoots leftover `10/7`. -/
lemma seven_sigma_lt_ten_usigma_five_cube_thirteen_nineteen {b c : ℕ}
    (hb : 0 < b) (hc : 0 < c) :
    7 * σ 1 (5 ^ 3) * σ 1 (13 ^ b) * σ 1 (19 ^ c) <
      10 * usigma (5 ^ 3) * usigma (13 ^ b) * usigma (19 ^ c) := by
  have hp13 : Nat.Prime 13 := by decide
  have hp19 : Nat.Prime 19 := by decide
  rw [sigma_five_pow_three, usigma_five_pow_three]
  have h13 := sigma_lt_cap_usigma hp13 hb
  have h19 := sigma_lt_cap_usigma hp19 hc
  have hu13 : 0 < usigma (13 ^ b) := by
    rw [usigma_prime_pow hp13 hb]
    exact Nat.add_pos_left (by decide : 0 < 1) _
  have hcap := seven_mul_five_cube_thirteen_nineteen_cap
  have hlt := seven_ten_of_two_caps_times_const (A := 12) (B := 13)
    (X := σ 1 (13 ^ b)) (Y := usigma (13 ^ b)) (C := 18) (D := 19)
    (P := σ 1 (19 ^ c)) (Q := usigma (19 ^ c)) (S := 126) (T := 156)
    h13 h19 hcap (by decide : 0 < 13) hu13 (by decide : 0 < 156)
  have hL : 7 * 156 * σ 1 (13 ^ b) * σ 1 (19 ^ c) =
      7 * σ 1 (13 ^ b) * σ 1 (19 ^ c) * 156 := by ring
  have hR : 10 * 126 * usigma (13 ^ b) * usigma (19 ^ c) =
      10 * usigma (13 ^ b) * usigma (19 ^ c) * 126 := by ring
  rw [hL, hR]
  exact hlt

lemma seven_mul_five_thirteen_sq_nineteen_cap :
    7 * 5 * 19 * 183 ≤ 10 * 4 * 18 * 170 := by
  norm_num

/-- `ρ(5^a) ρ(169) ρ(19^c) < 10/7`. -/
lemma seven_sigma_lt_ten_usigma_five_thirteen_sq_nineteen {a c : ℕ}
    (ha : 0 < a) (hc : 0 < c) :
    7 * σ 1 (5 ^ a) * σ 1 (13 ^ 2) * σ 1 (19 ^ c) <
      10 * usigma (5 ^ a) * usigma (13 ^ 2) * usigma (19 ^ c) := by
  have hp13 : Nat.Prime 13 := by decide
  have hp19 : Nat.Prime 19 := by decide
  have hσ13 : σ 1 (13 ^ 2) = 183 := by
    rw [sigma_prime_pow_two hp13]
    decide
  have hu13 : usigma (13 ^ 2) = 170 := by
    simpa using usigma_prime_pow hp13 (by decide : 0 < 2)
  rw [hσ13, hu13]
  have h5 := four_sigma_lt_five_usigma ha
  have h19 := sigma_lt_cap_usigma hp19 hc
  have hu5 : 0 < usigma (5 ^ a) := by
    rw [usigma_prime_pow Nat.prime_five ha]
    exact Nat.add_pos_left (by decide : 0 < 1) _
  have hcap := seven_mul_five_thirteen_sq_nineteen_cap
  have hlt := seven_ten_of_two_caps_times_const (A := 4) (B := 5)
    (X := σ 1 (5 ^ a)) (Y := usigma (5 ^ a)) (C := 18) (D := 19)
    (P := σ 1 (19 ^ c)) (Q := usigma (19 ^ c)) (S := 170) (T := 183)
    h5 h19 hcap (by decide : 0 < 5) hu5 (by decide : 0 < 183)
  have hL : 7 * σ 1 (5 ^ a) * 183 * σ 1 (19 ^ c) =
      7 * σ 1 (5 ^ a) * σ 1 (19 ^ c) * 183 := by ring
  have hR : 10 * usigma (5 ^ a) * 170 * usigma (19 ^ c) =
      10 * usigma (5 ^ a) * usigma (19 ^ c) * 170 := by ring
  rw [hL, hR]
  exact hlt

lemma seven_mul_five_fourth_thirteen_nineteen_cap :
    7 * 13 * 19 * 781 ≤ 10 * 12 * 18 * 626 := by
  norm_num

/-- `{5^4, 13^b, 19^c}` undershoots leftover `10/7`. -/
lemma seven_sigma_lt_ten_usigma_five_fourth_thirteen_nineteen {b c : ℕ}
    (hb : 0 < b) (hc : 0 < c) :
    7 * σ 1 (5 ^ 4) * σ 1 (13 ^ b) * σ 1 (19 ^ c) <
      10 * usigma (5 ^ 4) * usigma (13 ^ b) * usigma (19 ^ c) := by
  have hp13 : Nat.Prime 13 := by decide
  have hp19 : Nat.Prime 19 := by decide
  rw [sigma_five_pow_four, usigma_five_pow_four]
  have h13 := sigma_lt_cap_usigma hp13 hb
  have h19 := sigma_lt_cap_usigma hp19 hc
  have hu13 : 0 < usigma (13 ^ b) := by
    rw [usigma_prime_pow hp13 hb]
    exact Nat.add_pos_left (by decide : 0 < 1) _
  have hcap := seven_mul_five_fourth_thirteen_nineteen_cap
  have hlt := seven_ten_of_two_caps_times_const (A := 12) (B := 13)
    (X := σ 1 (13 ^ b)) (Y := usigma (13 ^ b)) (C := 18) (D := 19)
    (P := σ 1 (19 ^ c)) (Q := usigma (19 ^ c)) (S := 626) (T := 781)
    h13 h19 hcap (by decide : 0 < 13) hu13 (by decide : 0 < 781)
  have hL : 7 * 781 * σ 1 (13 ^ b) * σ 1 (19 ^ c) =
      7 * σ 1 (13 ^ b) * σ 1 (19 ^ c) * 781 := by ring
  have hR : 10 * 626 * usigma (13 ^ b) * usigma (19 ^ c) =
      10 * usigma (13 ^ b) * usigma (19 ^ c) * 626 := by ring
  rw [hL, hR]
  exact hlt

lemma seven_mul_five_thirteen_nineteen_sq_cap :
    7 * 5 * 13 * 381 ≤ 10 * 4 * 12 * 362 := by
  norm_num

/-- `ρ(5^a) ρ(13^b) ρ(361) < 10/7`. -/
lemma seven_sigma_lt_ten_usigma_five_thirteen_nineteen_sq {a b : ℕ}
    (ha : 0 < a) (hb : 0 < b) :
    7 * σ 1 (5 ^ a) * σ 1 (13 ^ b) * σ 1 (19 ^ 2) <
      10 * usigma (5 ^ a) * usigma (13 ^ b) * usigma (19 ^ 2) := by
  have hp19 : Nat.Prime 19 := by decide
  have hσ19 : σ 1 (19 ^ 2) = 381 := by
    rw [sigma_prime_pow_two hp19]
    decide
  have hu19 : usigma (19 ^ 2) = 362 := by
    simpa using usigma_prime_pow hp19 (by decide : 0 < 2)
  rw [hσ19, hu19]
  have h5 := four_sigma_lt_five_usigma ha
  have h13 := sigma_lt_cap_usigma (by decide : Nat.Prime 13) hb
  have hu5 : 0 < usigma (5 ^ a) := by
    rw [usigma_prime_pow Nat.prime_five ha]
    exact Nat.add_pos_left (by decide : 0 < 1) _
  have hcap := seven_mul_five_thirteen_nineteen_sq_cap
  have hlt := seven_ten_of_two_caps_times_const (A := 4) (B := 5)
    (X := σ 1 (5 ^ a)) (Y := usigma (5 ^ a)) (C := 12) (D := 13)
    (P := σ 1 (13 ^ b)) (Q := usigma (13 ^ b)) (S := 362) (T := 381)
    h5 h13 hcap (by decide : 0 < 5) hu5 (by decide : 0 < 381)
  exact hlt

lemma sigma_five_pow_five : σ 1 (5 ^ 5) = 3906 := by
  rw [sigma_prime_pow_div Nat.prime_five]
  norm_num

lemma usigma_five_pow_five : usigma (5 ^ 5) = 3126 := by
  rw [usigma_prime_pow Nat.prime_five (by decide : 0 < 5)]
  decide

lemma sigma_five_pow_six : σ 1 (5 ^ 6) = 19531 := by
  rw [sigma_prime_pow_div Nat.prime_five]
  norm_num

lemma usigma_five_pow_six : usigma (5 ^ 6) = 15626 := by
  rw [usigma_prime_pow Nat.prime_five (by decide : 0 < 6)]
  decide

lemma sigma_thirteen_pow_three : σ 1 (13 ^ 3) = 2380 := by
  rw [sigma_prime_pow_div (by decide : Nat.Prime 13)]
  norm_num

lemma usigma_thirteen_pow_three : usigma (13 ^ 3) = 2198 := by
  rw [usigma_prime_pow (by decide : Nat.Prime 13) (by decide : 0 < 3)]
  decide

lemma sigma_nineteen_pow_three : σ 1 (19 ^ 3) = 7240 := by
  rw [sigma_prime_pow_div (by decide : Nat.Prime 19)]
  norm_num

lemma usigma_nineteen_pow_three : usigma (19 ^ 3) = 6860 := by
  rw [usigma_prime_pow (by decide : Nat.Prime 19) (by decide : 0 < 3)]
  decide

lemma seven_mul_five_thirteen_cube_nineteen_cube_cap :
    7 * 5 * 2380 * 7240 ≤ 10 * 4 * 2198 * 6860 := by
  norm_num

/-- `ρ(5^a) ρ(2197) ρ(6859) < 10/7`. -/
lemma seven_sigma_lt_ten_usigma_five_thirteen_cube_nineteen_cube {a : ℕ}
    (ha : 0 < a) :
    7 * σ 1 (5 ^ a) * σ 1 (13 ^ 3) * σ 1 (19 ^ 3) <
      10 * usigma (5 ^ a) * usigma (13 ^ 3) * usigma (19 ^ 3) := by
  rw [sigma_thirteen_pow_three, usigma_thirteen_pow_three,
    sigma_nineteen_pow_three, usigma_nineteen_pow_three]
  have h5 := four_sigma_lt_five_usigma ha
  have hpos : 0 < 7 * 2380 * 7240 := by norm_num
  have hprod : 4 * σ 1 (5 ^ a) * (7 * 2380 * 7240) <
      5 * usigma (5 ^ a) * (7 * 2380 * 7240) :=
    Nat.mul_lt_mul_of_pos_right h5 hpos
  have hnum := seven_mul_five_thirteen_cube_nineteen_cube_cap
  have h10 : 5 * usigma (5 ^ a) * (7 * 2380 * 7240) ≤
      4 * usigma (5 ^ a) * (10 * 2198 * 6860) := by
    have := Nat.mul_le_mul_right (usigma (5 ^ a)) hnum
    have hL : 7 * 5 * 2380 * 7240 * usigma (5 ^ a) =
        5 * usigma (5 ^ a) * (7 * 2380 * 7240) := by ring
    have hR : 10 * 4 * 2198 * 6860 * usigma (5 ^ a) =
        4 * usigma (5 ^ a) * (10 * 2198 * 6860) := by ring
    have hthis : 7 * 5 * 2380 * 7240 * usigma (5 ^ a) ≤
        10 * 4 * 2198 * 6860 * usigma (5 ^ a) := by
      simpa [mul_assoc, mul_left_comm, mul_comm] using this
    rw [hL, hR] at hthis
    exact hthis
  have hlt : 4 * σ 1 (5 ^ a) * (7 * 2380 * 7240) <
      4 * usigma (5 ^ a) * (10 * 2198 * 6860) :=
    lt_of_lt_of_le hprod h10
  have hcancel : 4 * (7 * σ 1 (5 ^ a) * 2380 * 7240) <
      4 * (10 * usigma (5 ^ a) * 2198 * 6860) := by
    have h1 : 4 * (7 * σ 1 (5 ^ a) * 2380 * 7240) =
        4 * σ 1 (5 ^ a) * (7 * 2380 * 7240) := by ring
    have h2 : 4 * (10 * usigma (5 ^ a) * 2198 * 6860) =
        4 * usigma (5 ^ a) * (10 * 2198 * 6860) := by ring
    rw [h1, h2]
    exact hlt
  exact Nat.lt_of_mul_lt_mul_left hcancel

lemma seven_mul_five_fifth_thirteen_cube_nineteen_cap :
    7 * 3906 * 2380 * 19 ≤ 10 * 3126 * 2198 * 18 := by
  norm_num

/-- `ρ(5^5) ρ(2197) ρ(19^c) < 10/7`. -/
lemma seven_sigma_lt_ten_usigma_five_fifth_thirteen_cube_nineteen {c : ℕ}
    (hc : 0 < c) :
    7 * σ 1 (5 ^ 5) * σ 1 (13 ^ 3) * σ 1 (19 ^ c) <
      10 * usigma (5 ^ 5) * usigma (13 ^ 3) * usigma (19 ^ c) := by
  have hp19 : Nat.Prime 19 := by decide
  rw [sigma_five_pow_five, usigma_five_pow_five, sigma_thirteen_pow_three,
    usigma_thirteen_pow_three]
  have h19 := sigma_lt_cap_usigma hp19 hc
  have hnum := seven_mul_five_fifth_thirteen_cube_nineteen_cap
  have hprod : 18 * σ 1 (19 ^ c) * (7 * 3906 * 2380) <
      19 * usigma (19 ^ c) * (7 * 3906 * 2380) :=
    Nat.mul_lt_mul_of_pos_right h19 (by norm_num : 0 < 7 * 3906 * 2380)
  have h10 : 19 * usigma (19 ^ c) * (7 * 3906 * 2380) ≤
      18 * usigma (19 ^ c) * (10 * 3126 * 2198) := by
    have := Nat.mul_le_mul_right (usigma (19 ^ c)) hnum
    have hL : 7 * 3906 * 2380 * 19 * usigma (19 ^ c) =
        19 * usigma (19 ^ c) * (7 * 3906 * 2380) := by ring
    have hR : 10 * 3126 * 2198 * 18 * usigma (19 ^ c) =
        18 * usigma (19 ^ c) * (10 * 3126 * 2198) := by ring
    have hthis : 7 * 3906 * 2380 * 19 * usigma (19 ^ c) ≤
        10 * 3126 * 2198 * 18 * usigma (19 ^ c) := by
      simpa [mul_assoc, mul_left_comm, mul_comm] using this
    rw [hL, hR] at hthis
    exact hthis
  have hlt : 18 * σ 1 (19 ^ c) * (7 * 3906 * 2380) <
      18 * usigma (19 ^ c) * (10 * 3126 * 2198) :=
    lt_of_lt_of_le hprod h10
  have hcancel : 18 * (7 * 3906 * 2380 * σ 1 (19 ^ c)) <
      18 * (10 * 3126 * 2198 * usigma (19 ^ c)) := by
    have h1 : 18 * (7 * 3906 * 2380 * σ 1 (19 ^ c)) =
        18 * σ 1 (19 ^ c) * (7 * 3906 * 2380) := by ring
    have h2 : 18 * (10 * 3126 * 2198 * usigma (19 ^ c)) =
        18 * usigma (19 ^ c) * (10 * 3126 * 2198) := by ring
    rw [h1, h2]
    exact hlt
  exact Nat.lt_of_mul_lt_mul_left hcancel

lemma five_fifth_thirteen_fourth_nineteen_cube_overshoot :
    10 * usigma (5 ^ 5) * usigma (13 ^ 4) * usigma (19 ^ 3) <
      7 * σ 1 (5 ^ 5) * σ 1 (13 ^ 4) * σ 1 (19 ^ 3) := by
  have hp13 : Nat.Prime 13 := by decide
  have hu13 : usigma (13 ^ 4) = 1 + 13 ^ 4 :=
    usigma_prime_pow hp13 (by decide : 0 < 4)
  have hσ13 : σ 1 (13 ^ 4) = (13 ^ 5 - 1) / 12 := sigma_prime_pow_div hp13
  rw [usigma_five_pow_five, sigma_five_pow_five, hu13, hσ13,
    usigma_nineteen_pow_three, sigma_nineteen_pow_three]
  norm_num

lemma five_sixth_thirteen_cube_nineteen_fourth_overshoot :
    10 * usigma (5 ^ 6) * usigma (13 ^ 3) * usigma (19 ^ 4) <
      7 * σ 1 (5 ^ 6) * σ 1 (13 ^ 3) * σ 1 (19 ^ 4) := by
  have hp19 : Nat.Prime 19 := by decide
  have hu19 : usigma (19 ^ 4) = 1 + 19 ^ 4 :=
    usigma_prime_pow hp19 (by decide : 0 < 4)
  have hσ19 : σ 1 (19 ^ 4) = (19 ^ 5 - 1) / 18 := sigma_prime_pow_div hp19
  rw [usigma_five_pow_six, sigma_five_pow_six, usigma_thirteen_pow_three,
    sigma_thirteen_pow_three, hu19, hσ19]
  norm_num

/-- `{5, 13, 19}` cannot fill leftover `10/7`. -/
lemma not_seven_sigma_eq_ten_usigma_five_thirteen_nineteen {a b c : ℕ}
    (ha : 2 ≤ a) (hb : 2 ≤ b) (hc : 2 ≤ c) :
    ¬ 7 * σ 1 (5 ^ a) * σ 1 (13 ^ b) * σ 1 (19 ^ c) =
        10 * usigma (5 ^ a) * usigma (13 ^ b) * usigma (19 ^ c) := by
  intro heq
  rcases eq_or_lt_of_le ha with ha2 | ha3
  · rw [← ha2] at heq
    exact (seven_sigma_lt_ten_usigma_five_sq_thirteen_nineteen
      (by omega) (by omega)).ne heq
  · have ha3' : 3 ≤ a := Nat.succ_le_of_lt ha3
    rcases eq_or_lt_of_le ha3' with ha3eq | ha4
    · rw [← ha3eq] at heq
      exact (seven_sigma_lt_ten_usigma_five_cube_thirteen_nineteen
        (by omega) (by omega)).ne heq
    · have ha4' : 4 ≤ a := Nat.succ_le_of_lt ha4
      rcases eq_or_lt_of_le hb with hb2 | hb3
      · rw [← hb2] at heq
        exact (seven_sigma_lt_ten_usigma_five_thirteen_sq_nineteen
          (by omega) (by omega)).ne heq
      · have hb3' : 3 ≤ b := Nat.succ_le_of_lt hb3
        rcases eq_or_lt_of_le ha4' with ha4eq | ha5
        · rw [← ha4eq] at heq
          exact (seven_sigma_lt_ten_usigma_five_fourth_thirteen_nineteen
            (by omega) (by omega)).ne heq
        · have ha5' : 5 ≤ a := Nat.succ_le_of_lt ha5
          rcases eq_or_lt_of_le hc with hc2 | hc3
          · rw [← hc2] at heq
            exact (seven_sigma_lt_ten_usigma_five_thirteen_nineteen_sq
              (by omega) (by omega)).ne heq
          · have hc3' : 3 ≤ c := Nat.succ_le_of_lt hc3
            rcases eq_or_lt_of_le hb3' with hb3eq | hb4
            · rw [← hb3eq] at heq
              rcases eq_or_lt_of_le hc3' with hc3eq | hc4
              · rw [← hc3eq] at heq
                exact (seven_sigma_lt_ten_usigma_five_thirteen_cube_nineteen_cube
                  (by omega)).ne heq
              · rcases eq_or_lt_of_le ha5' with ha5eq | ha6
                · rw [← ha5eq] at heq
                  exact (seven_sigma_lt_ten_usigma_five_fifth_thirteen_cube_nineteen
                    (by omega)).ne heq
                · have hover := ten_seven_overshoot_mono_three Nat.prime_five
                      (by decide : Nat.Prime 13) (by decide : Nat.Prime 19)
                      (by decide : 0 < 6) (by decide : 0 < 3) (by decide : 0 < 4)
                      (Nat.succ_le_of_lt ha6) (le_refl _) (Nat.succ_le_of_lt hc4)
                      five_sixth_thirteen_cube_nineteen_fourth_overshoot
                  rw [← heq] at hover
                  exact lt_irrefl _ hover
            · have hover := ten_seven_overshoot_mono_three Nat.prime_five
                  (by decide : Nat.Prime 13) (by decide : Nat.Prime 19)
                  (by decide : 0 < 5) (by decide : 0 < 4) (by decide : 0 < 3)
                  ha5' (Nat.succ_le_of_lt hb4) hc3'
                  five_fifth_thirteen_fourth_nineteen_cube_overshoot
              rw [← heq] at hover
              exact lt_irrefl _ hover

lemma prime_ge_two_twenty_four_ge_two_twenty_seven {p : ℕ} (hp : p.Prime)
    (h : 224 ≤ p) : 227 ≤ p := by
  have hmem : p = 224 ∨ p = 225 ∨ p = 226 ∨ 227 ≤ p := by omega
  rcases hmem with rfl | rfl | rfl | h227
  · have : 224 = 2 * 112 := rfl
    exact False.elim (Nat.not_prime_mul (by decide : (2 : ℕ) ≠ 1)
      (by decide : (112 : ℕ) ≠ 1) (this ▸ hp))
  · have : 225 = 15 * 15 := rfl
    exact False.elim (Nat.not_prime_mul (by decide : (15 : ℕ) ≠ 1)
      (by decide : (15 : ℕ) ≠ 1) (this ▸ hp))
  · have : 226 = 2 * 113 := rfl
    exact False.elim (Nat.not_prime_mul (by decide : (2 : ℕ) ≠ 1)
      (by decide : (113 : ℕ) ≠ 1) (this ▸ hp))
  · exact h227

/-- `ρ(625) ρ(49) ρ(p^2) > 10/7` for `23 ≤ p ≤ 223`. -/
lemma five_fourth_forty_nine_sq_overshoot {p : ℕ} (hp : p.Prime)
    (h23 : 23 ≤ p) (h223 : p ≤ 223) :
    10 * usigma (5 ^ 4) * usigma (7 ^ 2) * usigma (p ^ 2) <
      7 * σ 1 (5 ^ 4) * σ 1 (7 ^ 2) * σ 1 (p ^ 2) := by
  have hp7 : Nat.Prime 7 := by decide
  have hu7 : usigma (7 ^ 2) = 50 := by
    simpa using usigma_prime_pow hp7 (by decide : 0 < 2)
  have hσ7 : σ 1 (7 ^ 2) = 57 := by
    rw [sigma_prime_pow_two hp7]
    decide
  rw [usigma_five_pow_four, sigma_five_pow_four, hu7, hσ7,
    usigma_prime_pow hp (by decide : 0 < 2), sigma_prime_pow_two hp]
  have hquad : 1381 * p * p + 1381 < 311619 * p := by
    have hle : 1381 * p * p ≤ 1381 * 223 * p := by
      have : p * p ≤ 223 * p := Nat.mul_le_mul_right p h223
      nlinarith
    have h1023 : 1381 * 223 * p + 1381 < 311619 * p := by
      have : 1381 < 3656 * p := by nlinarith
      nlinarith
    omega
  have hL : ((10 * 626 * 50 * (1 + p ^ 2) : ℕ) : ℤ) =
      10 * 626 * 50 * (1 + (p : ℤ) ^ 2) := by push_cast; rfl
  have hR : ((7 * 781 * 57 * (1 + p + p ^ 2) : ℕ) : ℤ) =
      7 * 781 * 57 * (1 + (p : ℤ) + (p : ℤ) ^ 2) := by push_cast; rfl
  have hint : (10 : ℤ) * 626 * 50 * (1 + p ^ 2) <
      7 * 781 * 57 * (1 + p + p ^ 2) := by
    have h247 : (1381 : ℤ) * p * p + 1381 < 311619 * p := by exact_mod_cast hquad
    nlinarith
  exact Nat.cast_lt.mp (by rw [hL, hR]; exact hint)

lemma five_fourth_forty_nine_pow_ge_two_overshoot {p k : ℕ} (hp : p.Prime)
    (h23 : 23 ≤ p) (h223 : p ≤ 223) (hk : 2 ≤ k) :
    10 * usigma (5 ^ 4) * usigma (7 ^ 2) * usigma (p ^ k) <
      7 * σ 1 (5 ^ 4) * σ 1 (7 ^ 2) * σ 1 (p ^ k) :=
  ten_seven_overshoot_mono_three Nat.prime_five (by decide : Nat.Prime 7) hp
    (by decide : 0 < 4) (by decide : 0 < 2) (by decide : 0 < 2)
    (le_refl _) (le_refl _) hk
    (five_fourth_forty_nine_sq_overshoot hp h23 h223)

/-- `ρ(625) ρ(49) cap(p) < 10/7` for every `p ≥ 227`. -/
lemma seven_mul_five_fourth_forty_nine_cap {p : ℕ} (hp : 227 ≤ p) :
    7 * 781 * 57 * p ≤ 10 * 626 * 50 * (p - 1) := by
  have hp1 : 1 ≤ p := by omega
  have hp' : (227 : ℤ) ≤ p := Int.ofNat_le.mpr hp
  have hL : ((7 * 781 * 57 * p : ℕ) : ℤ) = 7 * 781 * 57 * (p : ℤ) := by
    push_cast; rfl
  have hR : ((10 * 626 * 50 * (p - 1) : ℕ) : ℤ) =
      10 * 626 * 50 * ((p : ℤ) - 1) := by
    rw [Nat.cast_mul, Nat.cast_mul, Nat.cast_mul, Nat.cast_sub hp1]
    push_cast; rfl
  have : (7 : ℤ) * 781 * 57 * p ≤ 10 * 626 * 50 * (p - 1) := by nlinarith
  exact Nat.cast_le.mp (by rw [hL, hR]; exact this)

lemma seven_sigma_lt_ten_usigma_five_fourth_seven_sq_large {p k : ℕ}
    (hp : p.Prime) (hp227 : 227 ≤ p) (hk : 0 < k) :
    7 * σ 1 (5 ^ 4) * σ 1 (7 ^ 2) * σ 1 (p ^ k) <
      10 * usigma (5 ^ 4) * usigma (7 ^ 2) * usigma (p ^ k) := by
  have hp7 : Nat.Prime 7 := by decide
  have hσ7 : σ 1 (7 ^ 2) = 57 := by
    rw [sigma_prime_pow_two hp7]
    decide
  have hu7 : usigma (7 ^ 2) = 50 := by
    simpa using usigma_prime_pow hp7 (by decide : 0 < 2)
  rw [sigma_five_pow_four, usigma_five_pow_four, hσ7, hu7]
  have hcp := sigma_lt_cap_usigma hp hk
  have hnum := seven_mul_five_fourth_forty_nine_cap hp227
  have hprod : (p - 1) * σ 1 (p ^ k) * (7 * 781 * 57) <
      p * usigma (p ^ k) * (7 * 781 * 57) :=
    Nat.mul_lt_mul_of_pos_right hcp (by norm_num : 0 < 7 * 781 * 57)
  have h10 : p * usigma (p ^ k) * (7 * 781 * 57) ≤
      (p - 1) * usigma (p ^ k) * (10 * 626 * 50) := by
    have := Nat.mul_le_mul_right (usigma (p ^ k)) hnum
    have hL : 7 * 781 * 57 * p * usigma (p ^ k) =
        p * usigma (p ^ k) * (7 * 781 * 57) := by ring
    have hR : 10 * 626 * 50 * (p - 1) * usigma (p ^ k) =
        (p - 1) * usigma (p ^ k) * (10 * 626 * 50) := by ring
    have hthis : 7 * 781 * 57 * p * usigma (p ^ k) ≤
        10 * 626 * 50 * (p - 1) * usigma (p ^ k) := by
      simpa [mul_assoc, mul_left_comm, mul_comm] using this
    rw [hL, hR] at hthis
    exact hthis
  have hlt : (p - 1) * σ 1 (p ^ k) * (7 * 781 * 57) <
      (p - 1) * usigma (p ^ k) * (10 * 626 * 50) :=
    lt_of_lt_of_le hprod h10
  have hcancel : (p - 1) * (7 * 781 * 57 * σ 1 (p ^ k)) <
      (p - 1) * (10 * 626 * 50 * usigma (p ^ k)) := by
    have h1 : (p - 1) * (7 * 781 * 57 * σ 1 (p ^ k)) =
        (p - 1) * σ 1 (p ^ k) * (7 * 781 * 57) := by ring
    have h2 : (p - 1) * (10 * 626 * 50 * usigma (p ^ k)) =
        (p - 1) * usigma (p ^ k) * (10 * 626 * 50) := by ring
    rw [h1, h2]
    exact hlt
  exact Nat.lt_of_mul_lt_mul_left hcancel

/-- `{5^4, 7^2, p^k}` cannot fill leftover `10/7` for `p ≥ 23` and `k ≥ 2`. -/
lemma not_seven_sigma_eq_ten_usigma_five_fourth_seven_sq {p k : ℕ}
    (hp : p.Prime) (hp23 : 23 ≤ p) (hk : 2 ≤ k) :
    ¬ 7 * σ 1 (5 ^ 4) * σ 1 (7 ^ 2) * σ 1 (p ^ k) =
        10 * usigma (5 ^ 4) * usigma (7 ^ 2) * usigma (p ^ k) := by
  intro heq
  rcases le_or_gt p 223 with h223 | h224
  · exact (five_fourth_forty_nine_pow_ge_two_overshoot hp hp23 h223 hk).ne'
      heq
  · have : 227 ≤ p := prime_ge_two_twenty_four_ge_two_twenty_seven hp (by omega)
    exact (seven_sigma_lt_ten_usigma_five_fourth_seven_sq_large hp this
      (by omega)).ne heq

lemma not_prime_of_eq_mul {n a b : ℕ} (h : n = a * b)
    (ha : a ≠ 1) (hb : b ≠ 1) (hp : n.Prime) : False :=
  Nat.not_prime_mul ha hb (h ▸ hp)

lemma prime_ge_three_thirty_eight_ge_three_forty_seven {p : ℕ} (hp : p.Prime)
    (h : 338 ≤ p) : 347 ≤ p := by
  rcases le_or_gt p 346 with h346 | h347
  · have hmem : p = 338 ∨ p = 339 ∨ p = 340 ∨ p = 341 ∨ p = 342 ∨ p = 343 ∨
        p = 344 ∨ p = 345 ∨ p = 346 := by omega
    rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact False.elim (not_prime_of_eq_mul (rfl : 338 = 2 * 169)
        (by decide : (2 : ℕ) ≠ 1) (by decide : (169 : ℕ) ≠ 1) hp)
    · exact False.elim (not_prime_of_eq_mul (rfl : 339 = 3 * 113)
        (by decide : (3 : ℕ) ≠ 1) (by decide : (113 : ℕ) ≠ 1) hp)
    · exact False.elim (not_prime_of_eq_mul (rfl : 340 = 2 * 170)
        (by decide : (2 : ℕ) ≠ 1) (by decide : (170 : ℕ) ≠ 1) hp)
    · exact False.elim (not_prime_of_eq_mul (rfl : 341 = 11 * 31)
        (by decide : (11 : ℕ) ≠ 1) (by decide : (31 : ℕ) ≠ 1) hp)
    · exact False.elim (not_prime_of_eq_mul (rfl : 342 = 2 * 171)
        (by decide : (2 : ℕ) ≠ 1) (by decide : (171 : ℕ) ≠ 1) hp)
    · exact False.elim (not_prime_of_eq_mul (rfl : 343 = 7 * 49)
        (by decide : (7 : ℕ) ≠ 1) (by decide : (49 : ℕ) ≠ 1) hp)
    · exact False.elim (not_prime_of_eq_mul (rfl : 344 = 2 * 172)
        (by decide : (2 : ℕ) ≠ 1) (by decide : (172 : ℕ) ≠ 1) hp)
    · exact False.elim (not_prime_of_eq_mul (rfl : 345 = 3 * 115)
        (by decide : (3 : ℕ) ≠ 1) (by decide : (115 : ℕ) ≠ 1) hp)
    · exact False.elim (not_prime_of_eq_mul (rfl : 346 = 2 * 173)
        (by decide : (2 : ℕ) ≠ 1) (by decide : (173 : ℕ) ≠ 1) hp)
  · exact Nat.succ_le_of_lt h347

/-- `ρ(5^5) ρ(49) ρ(p^2) > 10/7` for `23 ≤ p ≤ 337`. -/
lemma five_fifth_forty_nine_sq_overshoot {p : ℕ} (hp : p.Prime)
    (h23 : 23 ≤ p) (h337 : p ≤ 337) :
    10 * usigma (5 ^ 5) * usigma (7 ^ 2) * usigma (p ^ 2) <
      7 * σ 1 (5 ^ 5) * σ 1 (7 ^ 2) * σ 1 (p ^ 2) := by
  have hp7 : Nat.Prime 7 := by decide
  have hu7 : usigma (7 ^ 2) = 50 := by
    simpa using usigma_prime_pow hp7 (by decide : 0 < 2)
  have hσ7 : σ 1 (7 ^ 2) = 57 := by
    rw [sigma_prime_pow_two hp7]
    decide
  rw [usigma_five_pow_five, sigma_five_pow_five, hu7, hσ7,
    usigma_prime_pow hp (by decide : 0 < 2), sigma_prime_pow_two hp]
  have hquad : 4506 * p * p + 4506 < 1558494 * p := by
    have hle : 4506 * p * p ≤ 4506 * 337 * p := by
      have : p * p ≤ 337 * p := Nat.mul_le_mul_right p h337
      nlinarith
    have h1023 : 4506 * 337 * p + 4506 < 1558494 * p := by
      have : 4506 < 39972 * p := by nlinarith
      nlinarith
    omega
  have hL : ((10 * 3126 * 50 * (1 + p ^ 2) : ℕ) : ℤ) =
      10 * 3126 * 50 * (1 + (p : ℤ) ^ 2) := by push_cast; rfl
  have hR : ((7 * 3906 * 57 * (1 + p + p ^ 2) : ℕ) : ℤ) =
      7 * 3906 * 57 * (1 + (p : ℤ) + (p : ℤ) ^ 2) := by push_cast; rfl
  have hint : (10 : ℤ) * 3126 * 50 * (1 + p ^ 2) <
      7 * 3906 * 57 * (1 + p + p ^ 2) := by
    have h247 : (4506 : ℤ) * p * p + 4506 < 1558494 * p := by exact_mod_cast hquad
    nlinarith
  exact Nat.cast_lt.mp (by rw [hL, hR]; exact hint)

lemma five_fifth_forty_nine_pow_ge_two_overshoot {p k : ℕ} (hp : p.Prime)
    (h23 : 23 ≤ p) (h337 : p ≤ 337) (hk : 2 ≤ k) :
    10 * usigma (5 ^ 5) * usigma (7 ^ 2) * usigma (p ^ k) <
      7 * σ 1 (5 ^ 5) * σ 1 (7 ^ 2) * σ 1 (p ^ k) :=
  ten_seven_overshoot_mono_three Nat.prime_five (by decide : Nat.Prime 7) hp
    (by decide : 0 < 5) (by decide : 0 < 2) (by decide : 0 < 2)
    (le_refl _) (le_refl _) hk
    (five_fifth_forty_nine_sq_overshoot hp h23 h337)

/-- `ρ(5^5) ρ(49) cap(p) < 10/7` for every `p ≥ 347`. -/
lemma seven_mul_five_fifth_forty_nine_cap {p : ℕ} (hp : 347 ≤ p) :
    7 * 3906 * 57 * p ≤ 10 * 3126 * 50 * (p - 1) := by
  have hp1 : 1 ≤ p := by omega
  have hp' : (347 : ℤ) ≤ p := Int.ofNat_le.mpr hp
  have hL : ((7 * 3906 * 57 * p : ℕ) : ℤ) = 7 * 3906 * 57 * (p : ℤ) := by
    push_cast; rfl
  have hR : ((10 * 3126 * 50 * (p - 1) : ℕ) : ℤ) =
      10 * 3126 * 50 * ((p : ℤ) - 1) := by
    rw [Nat.cast_mul, Nat.cast_mul, Nat.cast_mul, Nat.cast_sub hp1]
    push_cast; rfl
  have : (7 : ℤ) * 3906 * 57 * p ≤ 10 * 3126 * 50 * (p - 1) := by nlinarith
  exact Nat.cast_le.mp (by rw [hL, hR]; exact this)

lemma seven_sigma_lt_ten_usigma_five_fifth_seven_sq_large {p k : ℕ}
    (hp : p.Prime) (hp347 : 347 ≤ p) (hk : 0 < k) :
    7 * σ 1 (5 ^ 5) * σ 1 (7 ^ 2) * σ 1 (p ^ k) <
      10 * usigma (5 ^ 5) * usigma (7 ^ 2) * usigma (p ^ k) := by
  have hp7 : Nat.Prime 7 := by decide
  have hσ7 : σ 1 (7 ^ 2) = 57 := by
    rw [sigma_prime_pow_two hp7]
    decide
  have hu7 : usigma (7 ^ 2) = 50 := by
    simpa using usigma_prime_pow hp7 (by decide : 0 < 2)
  rw [sigma_five_pow_five, usigma_five_pow_five, hσ7, hu7]
  have hcp := sigma_lt_cap_usigma hp hk
  have hnum := seven_mul_five_fifth_forty_nine_cap hp347
  have hprod : (p - 1) * σ 1 (p ^ k) * (7 * 3906 * 57) <
      p * usigma (p ^ k) * (7 * 3906 * 57) :=
    Nat.mul_lt_mul_of_pos_right hcp (by norm_num : 0 < 7 * 3906 * 57)
  have h10 : p * usigma (p ^ k) * (7 * 3906 * 57) ≤
      (p - 1) * usigma (p ^ k) * (10 * 3126 * 50) := by
    have := Nat.mul_le_mul_right (usigma (p ^ k)) hnum
    have hL : 7 * 3906 * 57 * p * usigma (p ^ k) =
        p * usigma (p ^ k) * (7 * 3906 * 57) := by ring
    have hR : 10 * 3126 * 50 * (p - 1) * usigma (p ^ k) =
        (p - 1) * usigma (p ^ k) * (10 * 3126 * 50) := by ring
    have hthis : 7 * 3906 * 57 * p * usigma (p ^ k) ≤
        10 * 3126 * 50 * (p - 1) * usigma (p ^ k) := by
      simpa [mul_assoc, mul_left_comm, mul_comm] using this
    rw [hL, hR] at hthis
    exact hthis
  have hlt : (p - 1) * σ 1 (p ^ k) * (7 * 3906 * 57) <
      (p - 1) * usigma (p ^ k) * (10 * 3126 * 50) :=
    lt_of_lt_of_le hprod h10
  have hcancel : (p - 1) * (7 * 3906 * 57 * σ 1 (p ^ k)) <
      (p - 1) * (10 * 3126 * 50 * usigma (p ^ k)) := by
    have h1 : (p - 1) * (7 * 3906 * 57 * σ 1 (p ^ k)) =
        (p - 1) * σ 1 (p ^ k) * (7 * 3906 * 57) := by ring
    have h2 : (p - 1) * (10 * 3126 * 50 * usigma (p ^ k)) =
        (p - 1) * usigma (p ^ k) * (10 * 3126 * 50) := by ring
    rw [h1, h2]
    exact hlt
  exact Nat.lt_of_mul_lt_mul_left hcancel

/-- `{5^5, 7^2, p^k}` cannot fill leftover `10/7` for `p ≥ 23` and `k ≥ 2`. -/
lemma not_seven_sigma_eq_ten_usigma_five_fifth_seven_sq {p k : ℕ}
    (hp : p.Prime) (hp23 : 23 ≤ p) (hk : 2 ≤ k) :
    ¬ 7 * σ 1 (5 ^ 5) * σ 1 (7 ^ 2) * σ 1 (p ^ k) =
        10 * usigma (5 ^ 5) * usigma (7 ^ 2) * usigma (p ^ k) := by
  intro heq
  rcases le_or_gt p 337 with h337 | h338
  · exact (five_fifth_forty_nine_pow_ge_two_overshoot hp hp23 h337 hk).ne'
      heq
  · have : 347 ≤ p := prime_ge_three_thirty_eight_ge_three_forty_seven hp
      (by omega)
    exact (seven_sigma_lt_ten_usigma_five_fifth_seven_sq_large hp this
      (by omega)).ne heq

lemma prime_ge_three_eighty_four_ge_three_eighty_nine {p : ℕ} (hp : p.Prime)
    (h : 384 ≤ p) : 389 ≤ p := by
  rcases le_or_gt p 388 with h388 | h389
  · have hmem : p = 384 ∨ p = 385 ∨ p = 386 ∨ p = 387 ∨ p = 388 := by omega
    rcases hmem with rfl | rfl | rfl | rfl | rfl
    · exact False.elim (not_prime_of_eq_mul (rfl : 384 = 2 * 192)
        (by decide : (2 : ℕ) ≠ 1) (by decide : (192 : ℕ) ≠ 1) hp)
    · exact False.elim (not_prime_of_eq_mul (rfl : 385 = 5 * 77)
        (by decide : (5 : ℕ) ≠ 1) (by decide : (77 : ℕ) ≠ 1) hp)
    · exact False.elim (not_prime_of_eq_mul (rfl : 386 = 2 * 193)
        (by decide : (2 : ℕ) ≠ 1) (by decide : (193 : ℕ) ≠ 1) hp)
    · exact False.elim (not_prime_of_eq_mul (rfl : 387 = 3 * 129)
        (by decide : (3 : ℕ) ≠ 1) (by decide : (129 : ℕ) ≠ 1) hp)
    · exact False.elim (not_prime_of_eq_mul (rfl : 388 = 2 * 194)
        (by decide : (2 : ℕ) ≠ 1) (by decide : (194 : ℕ) ≠ 1) hp)
  · exact Nat.succ_le_of_lt h389

/-- `ρ(5^6) ρ(49) ρ(p^2) > 10/7` for `23 ≤ p ≤ 383`. -/
lemma five_sixth_forty_nine_sq_overshoot {p : ℕ} (hp : p.Prime)
    (h23 : 23 ≤ p) (h383 : p ≤ 383) :
    10 * usigma (5 ^ 6) * usigma (7 ^ 2) * usigma (p ^ 2) <
      7 * σ 1 (5 ^ 6) * σ 1 (7 ^ 2) * σ 1 (p ^ 2) := by
  have hp7 : Nat.Prime 7 := by decide
  have hu7 : usigma (7 ^ 2) = 50 := by
    simpa using usigma_prime_pow hp7 (by decide : 0 < 2)
  have hσ7 : σ 1 (7 ^ 2) = 57 := by
    rw [sigma_prime_pow_two hp7]
    decide
  rw [usigma_five_pow_six, sigma_five_pow_six, hu7, hσ7,
    usigma_prime_pow hp (by decide : 0 < 2), sigma_prime_pow_two hp]
  have hquad : 20131 * p * p + 20131 < 7792869 * p := by
    have hle : 20131 * p * p ≤ 20131 * 383 * p := by
      have : p * p ≤ 383 * p := Nat.mul_le_mul_right p h383
      nlinarith
    have h1023 : 20131 * 383 * p + 20131 < 7792869 * p := by
      have : 20131 < 82696 * p := by nlinarith
      nlinarith
    omega
  have hL : ((10 * 15626 * 50 * (1 + p ^ 2) : ℕ) : ℤ) =
      10 * 15626 * 50 * (1 + (p : ℤ) ^ 2) := by push_cast; rfl
  have hR : ((7 * 19531 * 57 * (1 + p + p ^ 2) : ℕ) : ℤ) =
      7 * 19531 * 57 * (1 + (p : ℤ) + (p : ℤ) ^ 2) := by push_cast; rfl
  have hint : (10 : ℤ) * 15626 * 50 * (1 + p ^ 2) <
      7 * 19531 * 57 * (1 + p + p ^ 2) := by
    have h247 : (20131 : ℤ) * p * p + 20131 < 7792869 * p := by
      exact_mod_cast hquad
    nlinarith
  exact Nat.cast_lt.mp (by rw [hL, hR]; exact hint)

lemma five_sixth_forty_nine_pow_ge_two_overshoot {p k : ℕ} (hp : p.Prime)
    (h23 : 23 ≤ p) (h383 : p ≤ 383) (hk : 2 ≤ k) :
    10 * usigma (5 ^ 6) * usigma (7 ^ 2) * usigma (p ^ k) <
      7 * σ 1 (5 ^ 6) * σ 1 (7 ^ 2) * σ 1 (p ^ k) :=
  ten_seven_overshoot_mono_three Nat.prime_five (by decide : Nat.Prime 7) hp
    (by decide : 0 < 6) (by decide : 0 < 2) (by decide : 0 < 2)
    (le_refl _) (le_refl _) hk
    (five_sixth_forty_nine_sq_overshoot hp h23 h383)

/-- `ρ(5^6) ρ(49) cap(p) < 10/7` for every `p ≥ 389`. -/
lemma seven_mul_five_sixth_forty_nine_cap {p : ℕ} (hp : 389 ≤ p) :
    7 * 19531 * 57 * p ≤ 10 * 15626 * 50 * (p - 1) := by
  have hp1 : 1 ≤ p := by omega
  have hp' : (389 : ℤ) ≤ p := Int.ofNat_le.mpr hp
  have hL : ((7 * 19531 * 57 * p : ℕ) : ℤ) = 7 * 19531 * 57 * (p : ℤ) := by
    push_cast; rfl
  have hR : ((10 * 15626 * 50 * (p - 1) : ℕ) : ℤ) =
      10 * 15626 * 50 * ((p : ℤ) - 1) := by
    rw [Nat.cast_mul, Nat.cast_mul, Nat.cast_mul, Nat.cast_sub hp1]
    push_cast; rfl
  have : (7 : ℤ) * 19531 * 57 * p ≤ 10 * 15626 * 50 * (p - 1) := by nlinarith
  exact Nat.cast_le.mp (by rw [hL, hR]; exact this)

lemma seven_sigma_lt_ten_usigma_five_sixth_seven_sq_large {p k : ℕ}
    (hp : p.Prime) (hp389 : 389 ≤ p) (hk : 0 < k) :
    7 * σ 1 (5 ^ 6) * σ 1 (7 ^ 2) * σ 1 (p ^ k) <
      10 * usigma (5 ^ 6) * usigma (7 ^ 2) * usigma (p ^ k) := by
  have hp7 : Nat.Prime 7 := by decide
  have hσ7 : σ 1 (7 ^ 2) = 57 := by
    rw [sigma_prime_pow_two hp7]
    decide
  have hu7 : usigma (7 ^ 2) = 50 := by
    simpa using usigma_prime_pow hp7 (by decide : 0 < 2)
  rw [sigma_five_pow_six, usigma_five_pow_six, hσ7, hu7]
  have hcp := sigma_lt_cap_usigma hp hk
  have hnum := seven_mul_five_sixth_forty_nine_cap hp389
  have hprod : (p - 1) * σ 1 (p ^ k) * (7 * 19531 * 57) <
      p * usigma (p ^ k) * (7 * 19531 * 57) :=
    Nat.mul_lt_mul_of_pos_right hcp (by norm_num : 0 < 7 * 19531 * 57)
  have h10 : p * usigma (p ^ k) * (7 * 19531 * 57) ≤
      (p - 1) * usigma (p ^ k) * (10 * 15626 * 50) := by
    have := Nat.mul_le_mul_right (usigma (p ^ k)) hnum
    have hL : 7 * 19531 * 57 * p * usigma (p ^ k) =
        p * usigma (p ^ k) * (7 * 19531 * 57) := by ring
    have hR : 10 * 15626 * 50 * (p - 1) * usigma (p ^ k) =
        (p - 1) * usigma (p ^ k) * (10 * 15626 * 50) := by ring
    have hthis : 7 * 19531 * 57 * p * usigma (p ^ k) ≤
        10 * 15626 * 50 * (p - 1) * usigma (p ^ k) := by
      simpa [mul_assoc, mul_left_comm, mul_comm] using this
    rw [hL, hR] at hthis
    exact hthis
  have hlt : (p - 1) * σ 1 (p ^ k) * (7 * 19531 * 57) <
      (p - 1) * usigma (p ^ k) * (10 * 15626 * 50) :=
    lt_of_lt_of_le hprod h10
  have hcancel : (p - 1) * (7 * 19531 * 57 * σ 1 (p ^ k)) <
      (p - 1) * (10 * 15626 * 50 * usigma (p ^ k)) := by
    have h1 : (p - 1) * (7 * 19531 * 57 * σ 1 (p ^ k)) =
        (p - 1) * σ 1 (p ^ k) * (7 * 19531 * 57) := by ring
    have h2 : (p - 1) * (10 * 15626 * 50 * usigma (p ^ k)) =
        (p - 1) * usigma (p ^ k) * (10 * 15626 * 50) := by ring
    rw [h1, h2]
    exact hlt
  exact Nat.lt_of_mul_lt_mul_left hcancel

/-- `{5^6, 7^2, p^k}` cannot fill leftover `10/7` for `p ≥ 23` and `k ≥ 2`. -/
lemma not_seven_sigma_eq_ten_usigma_five_sixth_seven_sq {p k : ℕ}
    (hp : p.Prime) (hp23 : 23 ≤ p) (hk : 2 ≤ k) :
    ¬ 7 * σ 1 (5 ^ 6) * σ 1 (7 ^ 2) * σ 1 (p ^ k) =
        10 * usigma (5 ^ 6) * usigma (7 ^ 2) * usigma (p ^ k) := by
  intro heq
  rcases le_or_gt p 383 with h383 | h384
  · exact (five_sixth_forty_nine_pow_ge_two_overshoot hp hp23 h383 hk).ne'
      heq
  · have : 389 ≤ p := prime_ge_three_eighty_four_ge_three_eighty_nine hp
      (by omega)
    exact (seven_sigma_lt_ten_usigma_five_sixth_seven_sq_large hp this
      (by omega)).ne heq

lemma sigma_five_pow_seven : σ 1 (5 ^ 7) = 97656 := by
  rw [sigma_prime_pow_div Nat.prime_five]
  norm_num

lemma usigma_five_pow_seven : usigma (5 ^ 7) = 78126 := by
  rw [usigma_prime_pow Nat.prime_five (by decide : 0 < 7)]
  decide

lemma sigma_five_pow_eight : σ 1 (5 ^ 8) = 488281 := by
  rw [sigma_prime_pow_div Nat.prime_five]
  norm_num

lemma usigma_five_pow_eight : usigma (5 ^ 8) = 390626 := by
  rw [usigma_prime_pow Nat.prime_five (by decide : 0 < 8)]
  decide

/-- `ρ(5^a) ρ(49) cap(p) < 10/7` for every `p ≥ 401`. -/
lemma seven_mul_five_forty_nine_cap {p : ℕ} (hp : 401 ≤ p) :
    7 * 5 * p * 57 ≤ 10 * 4 * (p - 1) * 50 := by
  have hp1 : 1 ≤ p := by omega
  have hp' : (401 : ℤ) ≤ p := Int.ofNat_le.mpr hp
  have hL : ((7 * 5 * p * 57 : ℕ) : ℤ) = (35 : ℤ) * p * 57 := by
    rw [Nat.cast_mul, Nat.cast_mul, Nat.cast_mul]; rfl
  have hR : ((10 * 4 * (p - 1) * 50 : ℕ) : ℤ) =
      (40 : ℤ) * ((p : ℤ) - 1) * 50 := by
    rw [Nat.cast_mul, Nat.cast_mul, Nat.cast_mul, Nat.cast_sub hp1]
    rfl
  have : (35 : ℤ) * p * 57 ≤ 40 * (p - 1) * 50 := by nlinarith
  exact Nat.cast_le.mp (by rw [hL, hR]; exact this)

lemma seven_sigma_lt_ten_usigma_five_seven_sq_cap_large {p a k : ℕ}
    (hp : p.Prime) (hp401 : 401 ≤ p) (ha : 0 < a) (hk : 0 < k) :
    7 * σ 1 (5 ^ a) * σ 1 (7 ^ 2) * σ 1 (p ^ k) <
      10 * usigma (5 ^ a) * usigma (7 ^ 2) * usigma (p ^ k) := by
  have hp7 : Nat.Prime 7 := by decide
  have hσ7 : σ 1 (7 ^ 2) = 57 := by
    rw [sigma_prime_pow_two hp7]
    decide
  have hu7 : usigma (7 ^ 2) = 50 := by
    simpa using usigma_prime_pow hp7 (by decide : 0 < 2)
  rw [hσ7, hu7]
  have h5 := four_sigma_lt_five_usigma ha
  have hpcap := sigma_lt_cap_usigma hp hk
  have hu5 : 0 < usigma (5 ^ a) := by
    rw [usigma_prime_pow Nat.prime_five ha]
    exact Nat.add_pos_left (by decide : 0 < 1) _
  have hcap := seven_mul_five_forty_nine_cap hp401
  have hlt := seven_ten_of_two_caps_times_const (A := 4) (B := 5)
    (X := σ 1 (5 ^ a)) (Y := usigma (5 ^ a)) (C := p - 1) (D := p)
    (P := σ 1 (p ^ k)) (Q := usigma (p ^ k)) (S := 50) (T := 57)
    h5 hpcap hcap (by decide : 0 < 5) hu5 (by decide : 0 < 57)
  have hL : 7 * σ 1 (5 ^ a) * 57 * σ 1 (p ^ k) =
      7 * σ 1 (5 ^ a) * σ 1 (p ^ k) * 57 := by ring
  have hR : 10 * usigma (5 ^ a) * 50 * usigma (p ^ k) =
      10 * usigma (5 ^ a) * usigma (p ^ k) * 50 := by ring
  rw [hL, hR]
  exact hlt

/-- `ρ(5^7) ρ(49) ρ(p^2) > 10/7` for `23 ≤ p ≤ 389`. -/
lemma five_seventh_forty_nine_sq_overshoot {p : ℕ} (hp : p.Prime)
    (h23 : 23 ≤ p) (h389 : p ≤ 389) :
    10 * usigma (5 ^ 7) * usigma (7 ^ 2) * usigma (p ^ 2) <
      7 * σ 1 (5 ^ 7) * σ 1 (7 ^ 2) * σ 1 (p ^ 2) := by
  have hp7 : Nat.Prime 7 := by decide
  have hu7 : usigma (7 ^ 2) = 50 := by
    simpa using usigma_prime_pow hp7 (by decide : 0 < 2)
  have hσ7 : σ 1 (7 ^ 2) = 57 := by
    rw [sigma_prime_pow_two hp7]
    decide
  rw [usigma_five_pow_seven, sigma_five_pow_seven, hu7, hσ7,
    usigma_prime_pow hp (by decide : 0 < 2), sigma_prime_pow_two hp]
  have hquad : 98256 * p * p + 98256 < 38964744 * p := by
    have hle : 98256 * p * p ≤ 98256 * 389 * p := by
      have : p * p ≤ 389 * p := Nat.mul_le_mul_right p h389
      nlinarith
    have h1023 : 98256 * 389 * p + 98256 < 38964744 * p := by
      have : 98256 < 743160 * p := by nlinarith
      nlinarith
    omega
  have hL : ((10 * 78126 * 50 * (1 + p ^ 2) : ℕ) : ℤ) =
      10 * 78126 * 50 * (1 + (p : ℤ) ^ 2) := by push_cast; rfl
  have hR : ((7 * 97656 * 57 * (1 + p + p ^ 2) : ℕ) : ℤ) =
      7 * 97656 * 57 * (1 + (p : ℤ) + (p : ℤ) ^ 2) := by push_cast; rfl
  have hint : (10 : ℤ) * 78126 * 50 * (1 + p ^ 2) <
      7 * 97656 * 57 * (1 + p + p ^ 2) := by
    have h247 : (98256 : ℤ) * p * p + 98256 < 38964744 * p := by
      exact_mod_cast hquad
    nlinarith
  exact Nat.cast_lt.mp (by rw [hL, hR]; exact hint)

lemma five_seventh_forty_nine_pow_ge_two_overshoot {p k : ℕ} (hp : p.Prime)
    (h23 : 23 ≤ p) (h389 : p ≤ 389) (hk : 2 ≤ k) :
    10 * usigma (5 ^ 7) * usigma (7 ^ 2) * usigma (p ^ k) <
      7 * σ 1 (5 ^ 7) * σ 1 (7 ^ 2) * σ 1 (p ^ k) :=
  ten_seven_overshoot_mono_three Nat.prime_five (by decide : Nat.Prime 7) hp
    (by decide : 0 < 7) (by decide : 0 < 2) (by decide : 0 < 2)
    (le_refl _) (le_refl _) hk
    (five_seventh_forty_nine_sq_overshoot hp h23 h389)

lemma prime_eq_three_ninety_seven_or_ge_four_oh_one {p : ℕ} (hp : p.Prime)
    (h : 390 ≤ p) : p = 397 ∨ 401 ≤ p := by
  rcases le_or_gt p 396 with h396 | h397
  · have hmem : p = 390 ∨ p = 391 ∨ p = 392 ∨ p = 393 ∨ p = 394 ∨ p = 395 ∨
        p = 396 := by omega
    rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact False.elim (not_prime_of_eq_mul (rfl : 390 = 2 * 195)
        (by decide : (2 : ℕ) ≠ 1) (by decide : (195 : ℕ) ≠ 1) hp)
    · exact False.elim (not_prime_of_eq_mul (rfl : 391 = 17 * 23)
        (by decide : (17 : ℕ) ≠ 1) (by decide : (23 : ℕ) ≠ 1) hp)
    · exact False.elim (not_prime_of_eq_mul (rfl : 392 = 2 * 196)
        (by decide : (2 : ℕ) ≠ 1) (by decide : (196 : ℕ) ≠ 1) hp)
    · exact False.elim (not_prime_of_eq_mul (rfl : 393 = 3 * 131)
        (by decide : (3 : ℕ) ≠ 1) (by decide : (131 : ℕ) ≠ 1) hp)
    · exact False.elim (not_prime_of_eq_mul (rfl : 394 = 2 * 197)
        (by decide : (2 : ℕ) ≠ 1) (by decide : (197 : ℕ) ≠ 1) hp)
    · exact False.elim (not_prime_of_eq_mul (rfl : 395 = 5 * 79)
        (by decide : (5 : ℕ) ≠ 1) (by decide : (79 : ℕ) ≠ 1) hp)
    · exact False.elim (not_prime_of_eq_mul (rfl : 396 = 2 * 198)
        (by decide : (2 : ℕ) ≠ 1) (by decide : (198 : ℕ) ≠ 1) hp)
  · have h397' : 397 ≤ p := Nat.succ_le_of_lt h397
    rcases eq_or_lt_of_le h397' with rfl | h398
    · exact Or.inl rfl
    · have h398 : 398 ≤ p := Nat.succ_le_of_lt h398
      rcases le_or_gt p 400 with h400 | h401
      · have hmem : p = 398 ∨ p = 399 ∨ p = 400 := by omega
        rcases hmem with rfl | rfl | rfl
        · exact False.elim (not_prime_of_eq_mul (rfl : 398 = 2 * 199)
            (by decide : (2 : ℕ) ≠ 1) (by decide : (199 : ℕ) ≠ 1) hp)
        · exact False.elim (not_prime_of_eq_mul (rfl : 399 = 3 * 133)
            (by decide : (3 : ℕ) ≠ 1) (by decide : (133 : ℕ) ≠ 1) hp)
        · exact False.elim (not_prime_of_eq_mul (rfl : 400 = 2 * 200)
            (by decide : (2 : ℕ) ≠ 1) (by decide : (200 : ℕ) ≠ 1) hp)
      · exact Or.inr (Nat.succ_le_of_lt h401)

lemma seven_sigma_lt_ten_usigma_five_seventh_seven_sq_three_ninety_seven_sq :
    7 * σ 1 (5 ^ 7) * σ 1 (7 ^ 2) * σ 1 (397 ^ 2) <
      10 * usigma (5 ^ 7) * usigma (7 ^ 2) * usigma (397 ^ 2) := by
  have hp : Nat.Prime 397 := by norm_num
  have hp7 : Nat.Prime 7 := by decide
  have hσ7 : σ 1 (7 ^ 2) = 57 := by
    rw [sigma_prime_pow_two hp7]
    decide
  have hu7 : usigma (7 ^ 2) = 50 := by
    simpa using usigma_prime_pow hp7 (by decide : 0 < 2)
  rw [sigma_five_pow_seven, usigma_five_pow_seven, hσ7, hu7,
    sigma_prime_pow_two hp, usigma_prime_pow hp (by decide : 0 < 2)]
  norm_num

lemma five_seventh_forty_nine_three_ninety_seven_cube_overshoot :
    10 * usigma (5 ^ 7) * usigma (7 ^ 2) * usigma (397 ^ 3) <
      7 * σ 1 (5 ^ 7) * σ 1 (7 ^ 2) * σ 1 (397 ^ 3) := by
  have hp : Nat.Prime 397 := by norm_num
  have hp7 : Nat.Prime 7 := by decide
  have hσ7 : σ 1 (7 ^ 2) = 57 := by
    rw [sigma_prime_pow_two hp7]
    decide
  have hu7 : usigma (7 ^ 2) = 50 := by
    simpa using usigma_prime_pow hp7 (by decide : 0 < 2)
  have hu : usigma (397 ^ 3) = 1 + 397 ^ 3 :=
    usigma_prime_pow hp (by decide : 0 < 3)
  have hσ : σ 1 (397 ^ 3) = (397 ^ 4 - 1) / 396 := sigma_prime_pow_div hp
  rw [usigma_five_pow_seven, sigma_five_pow_seven, hu7, hσ7, hu, hσ]
  norm_num

lemma five_eighth_forty_nine_three_ninety_seven_sq_overshoot :
    10 * usigma (5 ^ 8) * usigma (7 ^ 2) * usigma (397 ^ 2) <
      7 * σ 1 (5 ^ 8) * σ 1 (7 ^ 2) * σ 1 (397 ^ 2) := by
  have hp : Nat.Prime 397 := by norm_num
  have hp7 : Nat.Prime 7 := by decide
  have hσ7 : σ 1 (7 ^ 2) = 57 := by
    rw [sigma_prime_pow_two hp7]
    decide
  have hu7 : usigma (7 ^ 2) = 50 := by
    simpa using usigma_prime_pow hp7 (by decide : 0 < 2)
  rw [usigma_five_pow_eight, sigma_five_pow_eight, hu7, hσ7,
    usigma_prime_pow hp (by decide : 0 < 2), sigma_prime_pow_two hp]
  norm_num

/-- `{5^a, 7^2, p^k}` with `a ≥ 7` cannot fill leftover `10/7` for `p ≥ 23`
and `k ≥ 2`. -/
lemma not_seven_sigma_eq_ten_usigma_five_pow_ge_seven_seven_sq {p k a : ℕ}
    (hp : p.Prime) (hp23 : 23 ≤ p) (ha : 7 ≤ a) (hk : 2 ≤ k) :
    ¬ 7 * σ 1 (5 ^ a) * σ 1 (7 ^ 2) * σ 1 (p ^ k) =
        10 * usigma (5 ^ a) * usigma (7 ^ 2) * usigma (p ^ k) := by
  intro heq
  rcases le_or_gt p 389 with h389 | h390
  · have hover := ten_seven_overshoot_mono_three Nat.prime_five
        (by decide : Nat.Prime 7) hp
        (by decide : 0 < 7) (by decide : 0 < 2) (by decide : 0 < 2)
        ha (le_refl _) hk (five_seventh_forty_nine_sq_overshoot hp hp23 h389)
    rw [← heq] at hover
    exact lt_irrefl _ hover
  · have h390 : 390 ≤ p := by omega
    rcases prime_eq_three_ninety_seven_or_ge_four_oh_one hp h390 with rfl | h401
    · rcases eq_or_lt_of_le ha with ha7 | ha8
      · rw [← ha7] at heq
        rcases eq_or_lt_of_le hk with hk2 | hk3
        · rw [← hk2] at heq
          exact seven_sigma_lt_ten_usigma_five_seventh_seven_sq_three_ninety_seven_sq.ne
            heq
        · have hover := ten_seven_overshoot_mono_three Nat.prime_five
              (by decide : Nat.Prime 7) hp
              (by decide : 0 < 7) (by decide : 0 < 2) (by decide : 0 < 3)
              (le_refl _) (le_refl _) (Nat.succ_le_of_lt hk3)
              five_seventh_forty_nine_three_ninety_seven_cube_overshoot
          rw [← heq] at hover
          exact lt_irrefl _ hover
      · have hover := ten_seven_overshoot_mono_three Nat.prime_five
            (by decide : Nat.Prime 7) hp
            (by decide : 0 < 8) (by decide : 0 < 2) (by decide : 0 < 2)
            (Nat.succ_le_of_lt ha8) (le_refl _) hk
            five_eighth_forty_nine_three_ninety_seven_sq_overshoot
        rw [← heq] at hover
        exact lt_irrefl _ hover
    · exact (seven_sigma_lt_ten_usigma_five_seven_sq_cap_large hp h401
        (by omega) (by omega)).ne heq

lemma prime_ge_eleven_le_nineteen {p : ℕ} (hp : p.Prime)
    (h11 : 11 ≤ p) (h19 : p ≤ 19) :
    p = 11 ∨ p = 13 ∨ p = 17 ∨ p = 19 := by
  have hmem : p = 11 ∨ p = 12 ∨ p = 13 ∨ p = 14 ∨ p = 15 ∨ p = 16 ∨
      p = 17 ∨ p = 18 ∨ p = 19 := by omega
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact Or.inl rfl
  · exact False.elim ((by decide : ¬ Nat.Prime 12) hp)
  · exact Or.inr (Or.inl rfl)
  · exact False.elim ((by decide : ¬ Nat.Prime 14) hp)
  · exact False.elim ((by decide : ¬ Nat.Prime 15) hp)
  · exact False.elim ((by decide : ¬ Nat.Prime 16) hp)
  · exact Or.inr (Or.inr (Or.inl rfl))
  · exact False.elim ((by decide : ¬ Nat.Prime 18) hp)
  · exact Or.inr (Or.inr (Or.inr rfl))

lemma prime_ge_twenty_ge_twenty_three {p : ℕ} (hp : p.Prime)
    (h : 20 ≤ p) : 23 ≤ p := by
  have hmem : p = 20 ∨ p = 21 ∨ p = 22 ∨ 23 ≤ p := by omega
  rcases hmem with rfl | rfl | rfl | h23
  · exact False.elim ((by decide : ¬ Nat.Prime 20) hp)
  · exact False.elim ((by decide : ¬ Nat.Prime 21) hp)
  · exact False.elim ((by decide : ¬ Nat.Prime 22) hp)
  · exact h23

/-- `{5^a, 7^b, p^k}` cannot fill leftover `10/7` for primes `p ≥ 11` and
exponents `a,b,k ≥ 2`. -/
lemma not_seven_sigma_eq_ten_usigma_five_seven_prime {a b k p : ℕ}
    (hp : p.Prime) (hp11 : 11 ≤ p) (ha : 2 ≤ a) (hb : 2 ≤ b) (hk : 2 ≤ k) :
    ¬ 7 * σ 1 (5 ^ a) * σ 1 (7 ^ b) * σ 1 (p ^ k) =
        10 * usigma (5 ^ a) * usigma (7 ^ b) * usigma (p ^ k) := by
  rcases le_or_gt p 19 with h19 | h20
  · rcases prime_ge_eleven_le_nineteen hp hp11 h19 with rfl | rfl | rfl | rfl
    · exact not_seven_sigma_eq_ten_usigma_five_seven_eleven ha hb hk
    · exact not_seven_sigma_eq_ten_usigma_five_seven_thirteen ha hb hk
    · exact not_seven_sigma_eq_ten_usigma_five_seven_seventeen ha hb hk
    · exact not_seven_sigma_eq_ten_usigma_five_seven_nineteen ha hb hk
  · have hp23 : 23 ≤ p := prime_ge_twenty_ge_twenty_three hp (by omega)
    rcases eq_or_lt_of_le ha with ha2 | ha3
    · rw [← ha2]
      rcases eq_or_lt_of_le hb with hb2 | hb3
      · rw [← hb2]
        exact (seven_sigma_lt_ten_usigma_five_seven_sq_large hp hp23
          (by omega)).ne
      · have hb3' : 3 ≤ b := Nat.succ_le_of_lt hb3
        rcases eq_or_lt_of_le hb3' with hb3eq | hb4
        · rw [← hb3eq]
          exact not_seven_sigma_eq_ten_usigma_five_sq_seven_cube hp hp23 hk
        · exact not_seven_sigma_eq_ten_usigma_five_sq_seven_pow_ge_four hp hp23
            (Nat.succ_le_of_lt hb4) hk
    · have ha3' : 3 ≤ a := Nat.succ_le_of_lt ha3
      rcases eq_or_lt_of_le hb with hb2 | hb3
      · rw [← hb2]
        rcases eq_or_lt_of_le ha3' with ha3eq | ha4
        · rw [← ha3eq]
          exact not_seven_sigma_eq_ten_usigma_five_cube_seven_sq hp hp23 hk
        · have ha4' : 4 ≤ a := Nat.succ_le_of_lt ha4
          rcases eq_or_lt_of_le ha4' with ha4eq | ha5
          · rw [← ha4eq]
            exact not_seven_sigma_eq_ten_usigma_five_fourth_seven_sq hp hp23 hk
          · have ha5' : 5 ≤ a := Nat.succ_le_of_lt ha5
            rcases eq_or_lt_of_le ha5' with ha5eq | ha6
            · rw [← ha5eq]
              exact not_seven_sigma_eq_ten_usigma_five_fifth_seven_sq hp hp23 hk
            · have ha6' : 6 ≤ a := Nat.succ_le_of_lt ha6
              rcases eq_or_lt_of_le ha6' with ha6eq | ha7
              · rw [← ha6eq]
                exact not_seven_sigma_eq_ten_usigma_five_sixth_seven_sq hp hp23 hk
              · exact not_seven_sigma_eq_ten_usigma_five_pow_ge_seven_seven_sq
                  hp hp23 (Nat.succ_le_of_lt ha7) hk
      · exact not_seven_sigma_eq_ten_usigma_five_seven_ge_three_mul ha3'
          (Nat.succ_le_of_lt hb3) (Nat.pow_pos hp.pos).ne'

lemma not_nine_dvd_of_A_of_val_two_ge_three {n : ℕ} (hA : A n)
    (h2 : 3 ≤ padicValNat 2 n) : ¬ 9 ∣ n := by
  intro h9
  have hn : n ≠ 0 := hA.1.ne'
  have : 2 ≤ padicValNat 3 n :=
    (pow_dvd_iff_le_padicValNat (by decide : (3 : ℕ) ≠ 1) hn (k := 2)).mp
      (by simpa using h9)
  have := padicValNat_three_lt_two_of_A_of_val_two_ge_three hA h2
  omega

lemma seven_div_six_lt_six_div_five : 7 * 5 < 6 * 6 := by decide

lemma not_five_sigma_eq_six_usigma_five_pow_two :
    ¬ 5 * σ 1 (5 ^ 2) = 6 * usigma (5 ^ 2) := by
  rw [sigma_prime_pow_two Nat.prime_five, usigma_five_pow_two]
  decide

/-- Every prime `p ≥ 7` undershoots leftover `6/5`. -/
lemma five_sigma_lt_six_usigma_prime_pow_ge_seven {p k : ℕ}
    (hp : p.Prime) (hp7 : 7 ≤ p) (hk : 0 < k) :
    5 * σ 1 (p ^ k) < 6 * usigma (p ^ k) := by
  have hcap := sigma_lt_cap_usigma hp hk
  have hp6 : 6 ≤ p := le_trans (by decide : 6 ≤ 7) hp7
  have h6p : 5 * p ≤ 6 * (p - 1) := by
    have hsub : 6 * (p - 1) = 6 * p - 6 := Nat.mul_sub_left_distrib 6 p 1
    have : 5 * p + 6 ≤ 6 * p := by nlinarith
    have hle : 6 ≤ 6 * p := Nat.le_mul_of_pos_right 6 (by omega)
    omega
  have h5 : 5 * ((p - 1) * σ 1 (p ^ k)) < 5 * (p * usigma (p ^ k)) :=
    Nat.mul_lt_mul_of_pos_left hcap (by decide)
  have hle : 5 * p * usigma (p ^ k) ≤ 6 * (p - 1) * usigma (p ^ k) :=
    Nat.mul_le_mul_right _ h6p
  have hlt : (p - 1) * (5 * σ 1 (p ^ k)) < (p - 1) * (6 * usigma (p ^ k)) := by
    have h5' : 5 * (p - 1) * σ 1 (p ^ k) < 5 * p * usigma (p ^ k) := by
      simpa [mul_assoc, mul_left_comm, mul_comm] using h5
    have h5'' : 5 * (p - 1) * σ 1 (p ^ k) < 6 * (p - 1) * usigma (p ^ k) :=
      lt_of_lt_of_le h5' hle
    simpa [mul_assoc, mul_left_comm, mul_comm] using h5''
  exact Nat.lt_of_mul_lt_mul_left hlt

lemma six_usigma_lt_five_sigma_two_pow {k : ℕ} (hk : 2 ≤ k) :
    6 * usigma (2 ^ k) < 5 * σ 1 (2 ^ k) := by
  have ha0 : 0 < k := by omega
  have hu : usigma (2 ^ k) = 1 + 2 ^ k := usigma_two_pow ha0
  have hσ : σ 1 (2 ^ k) = 2 ^ (k + 1) - 1 := sigma_two_pow k
  have hP : 4 ≤ 2 ^ k := by
    have : 2 ^ 2 = 4 := by decide
    exact this ▸ Nat.pow_le_pow_right (by decide : 1 ≤ 2) hk
  have hsucc : 2 ^ (k + 1) = 2 * 2 ^ k := by rw [Nat.pow_succ']
  have hpos : 1 ≤ 2 * 2 ^ k := by nlinarith
  rw [hu, hσ, hsucc]
  have : 6 * (1 + 2 ^ k) < 5 * (2 * 2 ^ k - 1) := by
    have hL : ((6 * (1 + 2 ^ k) : ℕ) : ℤ) = 6 * (1 + (2 : ℤ) ^ k) := by
      push_cast; rfl
    have hR : ((5 * (2 * 2 ^ k - 1) : ℕ) : ℤ) = 5 * (2 * (2 : ℤ) ^ k - 1) := by
      rw [Nat.cast_mul, Nat.cast_sub hpos]
      push_cast; rfl
    have : (6 : ℤ) * (1 + 2 ^ k) < 5 * (2 * 2 ^ k - 1) := by nlinarith
    exact Nat.cast_lt.mp (by rw [hL, hR]; exact this)
  exact this

lemma five_sigma_eq_six_of_squarefree_ordCompl {m p : ℕ} (hm : m ≠ 0)
    (hp : p.Prime) (h : 5 * σ 1 m = 6 * usigma m)
    (hs : Squarefree (ordCompl[p] m)) :
    5 * σ 1 (ordProj[p] m) = 6 * usigma (ordProj[p] m) := by
  have hdecomp : ordProj[p] m * ordCompl[p] m = m :=
    Nat.ordProj_mul_ordCompl_eq_self m p
  have hc : Coprime (ordProj[p] m) (ordCompl[p] m) :=
    (Nat.coprime_ordCompl hp hm).pow_left (m.factorization p)
  have hmul : 5 * σ 1 (ordProj[p] m) * σ 1 (ordCompl[p] m) =
      6 * usigma (ordProj[p] m) * usigma (ordCompl[p] m) := by
    have := h
    rw [← hdecomp, sigma_mul_of_coprime hc, usigma_mul hc] at this
    simpa [mul_assoc, mul_left_comm, mul_comm] using this
  have hσu := (sigma_eq_usigma_iff_squarefree (Nat.ordCompl_pos p hm)).mpr hs
  rw [hσu] at hmul
  have hpos : 0 < usigma (ordCompl[p] m) := by
    rw [← hσu]
    exact sigma_pos_iff.mpr (Nat.ordCompl_pos p hm)
  exact Nat.eq_of_mul_eq_mul_right hpos hmul

/-- Leftover `6/5` cannot be a single prime power times a squarefree factor. -/
lemma not_five_sigma_of_unique_sq_prime {m p : ℕ} (hm : m ≠ 0)
    (hp : p.Prime) (h : 5 * σ 1 m = 6 * usigma m)
    (hk : 2 ≤ padicValNat p m) (hs : Squarefree (ordCompl[p] m)) : False := by
  have heq := five_sigma_eq_six_of_squarefree_ordCompl hm hp h hs
  have hproj : ordProj[p] m = p ^ padicValNat p m := by
    simp [Nat.factorization_def m hp]
  rw [hproj] at heq
  have hk0 : 0 < padicValNat p m := by omega
  rcases le_or_gt 7 p with hp7 | hp6
  · exact (five_sigma_lt_six_usigma_prime_pow_ge_seven hp hp7 hk0).ne heq
  · have hp2 : 2 ≤ p := hp.two_le
    have hle : p ≤ 6 := Nat.lt_succ_iff.mp hp6
    have hmem : p = 2 ∨ p = 3 ∨ p = 4 ∨ p = 5 ∨ p = 6 := by omega
    rcases hmem with rfl | rfl | rfl | rfl | rfl
    · have hover := six_usigma_lt_five_sigma_two_pow hk
      rw [← heq] at hover
      exact (lt_irrefl _ hover)
    · have hover := six_usigma_lt_five_sigma_three_pow hk
      rw [← heq] at hover
      exact (lt_irrefl _ hover)
    · exact (by decide : ¬ Nat.Prime 4) hp
    · rcases eq_or_lt_of_le hk with h2 | h3
      · rw [← h2] at heq
        exact not_five_sigma_eq_six_usigma_five_pow_two heq
      · have hover := six_usigma_lt_five_sigma_five_pow (Nat.succ_le_of_lt h3)
        rw [← heq] at hover
        exact (lt_irrefl _ hover)
    · exact (by decide : ¬ Nat.Prime 6) hp

/-- If two Euler-product caps multiply below leftover `6/5`, the product
of the two prime-power ratios is strictly below leftover `6/5`. -/
lemma six_five_of_two_caps {A B X Y C D P Q : ℕ}
    (hA : A * X < B * Y) (hC : C * P < D * Q)
    (hcap : 5 * B * D ≤ 6 * A * C)
    (hB : 0 < B) (hY : 0 < Y) :
    5 * X * P < 6 * Y * Q := by
  have hprod : (A * X) * (C * P) < (B * Y) * (D * Q) :=
    Nat.mul_lt_mul_of_le_of_lt (Nat.le_of_lt hA) hC (Nat.mul_pos hB hY)
  have h5 : 5 * ((A * X) * (C * P)) < 5 * ((B * Y) * (D * Q)) :=
    Nat.mul_lt_mul_of_pos_left hprod (by decide)
  have h6 : 5 * B * D * (Y * Q) ≤ 6 * A * C * (Y * Q) :=
    Nat.mul_le_mul_right (Y * Q) hcap
  have hchain : 5 * A * C * X * P < 6 * A * C * Y * Q := by
    have hL : 5 * A * C * X * P = 5 * ((A * X) * (C * P)) := by ring
    have hmid : 5 * ((B * Y) * (D * Q)) = 5 * B * D * (Y * Q) := by ring
    have hR : 5 * B * D * (Y * Q) ≤ 6 * A * C * Y * Q := by
      simpa [mul_assoc, mul_left_comm, mul_comm] using h6
    calc
      5 * A * C * X * P = 5 * ((A * X) * (C * P)) := hL
      _ < 5 * ((B * Y) * (D * Q)) := h5
      _ = 5 * B * D * (Y * Q) := hmid
      _ ≤ 6 * A * C * Y * Q := hR
  have hcancel : A * C * (5 * X * P) < A * C * (6 * Y * Q) := by
    have h1 : A * C * (5 * X * P) = 5 * A * C * X * P := by ring
    have h2 : A * C * (6 * Y * Q) = 6 * A * C * Y * Q := by ring
    rw [h1, h2]
    exact hchain
  exact Nat.lt_of_mul_lt_mul_left hcancel

/-- Three Euler-product caps strictly below leftover `6/5`. -/
lemma six_five_of_three_caps {A B X Y C D P Q E F R S : ℕ}
    (hA : A * X < B * Y) (hC : C * P < D * Q) (hE : E * R < F * S)
    (hcap : 5 * B * D * F ≤ 6 * A * C * E)
    (hB : 0 < B) (hY : 0 < Y) (hD : 0 < D) (hQ : 0 < Q) :
    5 * X * P * R < 6 * Y * Q * S := by
  have hprod12 : (A * X) * (C * P) < (B * Y) * (D * Q) :=
    Nat.mul_lt_mul_of_le_of_lt (Nat.le_of_lt hA) hC (Nat.mul_pos hB hY)
  have hprod : ((A * X) * (C * P)) * (E * R) < ((B * Y) * (D * Q)) * (F * S) :=
    Nat.mul_lt_mul_of_le_of_lt (Nat.le_of_lt hprod12) hE
      (Nat.mul_pos (Nat.mul_pos hB hY) (Nat.mul_pos hD hQ))
  have h5 : 5 * (((A * X) * (C * P)) * (E * R)) <
      5 * (((B * Y) * (D * Q)) * (F * S)) :=
    Nat.mul_lt_mul_of_pos_left hprod (by decide)
  have h6 : 5 * B * D * F * (Y * Q * S) ≤ 6 * A * C * E * (Y * Q * S) :=
    Nat.mul_le_mul_right (Y * Q * S) hcap
  have hchain : 5 * A * C * E * X * P * R < 6 * A * C * E * Y * Q * S := by
    have hL : 5 * A * C * E * X * P * R =
        5 * (((A * X) * (C * P)) * (E * R)) := by ring
    have hmid : 5 * (((B * Y) * (D * Q)) * (F * S)) =
        5 * B * D * F * (Y * Q * S) := by ring
    have hR : 5 * B * D * F * (Y * Q * S) ≤ 6 * A * C * E * Y * Q * S := by
      simpa [mul_assoc, mul_left_comm, mul_comm] using h6
    calc
      5 * A * C * E * X * P * R = 5 * (((A * X) * (C * P)) * (E * R)) := hL
      _ < 5 * (((B * Y) * (D * Q)) * (F * S)) := h5
      _ = 5 * B * D * F * (Y * Q * S) := hmid
      _ ≤ 6 * A * C * E * Y * Q * S := hR
  have hcancel : A * C * E * (5 * X * P * R) < A * C * E * (6 * Y * Q * S) := by
    have h1 : A * C * E * (5 * X * P * R) = 5 * A * C * E * X * P * R := by ring
    have h2 : A * C * E * (6 * Y * Q * S) = 6 * A * C * E * Y * Q * S := by ring
    rw [h1, h2]
    exact hchain
  exact Nat.lt_of_mul_lt_mul_left hcancel

/-- Two Euler-product caps times a constant ratio, strictly below leftover `6/5`. -/
lemma six_five_of_two_caps_times_const {A B X Y C D P Q S T : ℕ}
    (hA : A * X < B * Y) (hC : C * P < D * Q)
    (hcap : 5 * B * D * T ≤ 6 * A * C * S)
    (hB : 0 < B) (hY : 0 < Y) (hT : 0 < T) :
    5 * X * P * T < 6 * Y * Q * S := by
  have hprod : (A * X) * (C * P) < (B * Y) * (D * Q) :=
    Nat.mul_lt_mul_of_le_of_lt (Nat.le_of_lt hA) hC (Nat.mul_pos hB hY)
  have h5' : 5 * ((A * X) * (C * P)) < 5 * ((B * Y) * (D * Q)) :=
    Nat.mul_lt_mul_of_pos_left hprod (by decide)
  have h5 : 5 * ((A * X) * (C * P)) * T < 5 * ((B * Y) * (D * Q)) * T :=
    Nat.mul_lt_mul_of_pos_right h5' hT
  have h6 : 5 * B * D * T * (Y * Q) ≤ 6 * A * C * S * (Y * Q) :=
    Nat.mul_le_mul_right (Y * Q) hcap
  have hchain : 5 * A * C * X * P * T < 6 * A * C * Y * Q * S := by
    have hL : 5 * A * C * X * P * T = 5 * ((A * X) * (C * P)) * T := by ring
    have hmid : 5 * ((B * Y) * (D * Q)) * T = 5 * B * D * T * (Y * Q) := by ring
    have hR : 5 * B * D * T * (Y * Q) ≤ 6 * A * C * S * (Y * Q) := by
      simpa [mul_assoc, mul_left_comm, mul_comm] using h6
    have hR' : 6 * A * C * S * (Y * Q) = 6 * A * C * Y * Q * S := by ring
    calc
      5 * A * C * X * P * T = 5 * ((A * X) * (C * P)) * T := hL
      _ < 5 * ((B * Y) * (D * Q)) * T := h5
      _ = 5 * B * D * T * (Y * Q) := hmid
      _ ≤ 6 * A * C * S * (Y * Q) := hR
      _ = 6 * A * C * Y * Q * S := hR'
  have hcancel : A * C * (5 * X * P * T) < A * C * (6 * Y * Q * S) := by
    have h1 : A * C * (5 * X * P * T) = 5 * A * C * X * P * T := by ring
    have h2 : A * C * (6 * Y * Q * S) = 6 * A * C * Y * Q * S := by ring
    rw [h1, h2]
    exact hchain
  exact Nat.lt_of_mul_lt_mul_left hcancel

lemma five_p_q_cap_ge_eleven {p q : ℕ} (hp : 11 ≤ p) (hq : 13 ≤ q)
    (hp1 : 1 ≤ p) (hq1 : 1 ≤ q) :
    5 * p * q ≤ 6 * (p - 1) * (q - 1) := by
  have hp' : (11 : ℤ) ≤ p := Int.ofNat_le.mpr hp
  have hq' : (13 : ℤ) ≤ q := Int.ofNat_le.mpr hq
  have hL : ((5 * p * q : ℕ) : ℤ) = 5 * (p : ℤ) * q := by push_cast; rfl
  have hR : ((6 * (p - 1) * (q - 1) : ℕ) : ℤ) =
      6 * ((p : ℤ) - 1) * ((q : ℤ) - 1) := by
    rw [Nat.cast_mul, Nat.cast_mul, Nat.cast_sub hp1, Nat.cast_sub hq1]
    push_cast; rfl
  have : (5 : ℤ) * p * q ≤ 6 * (p - 1) * (q - 1) := by nlinarith
  exact Nat.cast_le.mp (by rw [hL, hR]; exact this)

/-- Two squareful primes both at least `11` undershoot leftover `6/5`. -/
lemma five_sigma_lt_six_usigma_two_large {p q a b : ℕ}
    (hp : p.Prime) (hq : q.Prime)
    (hp11 : 11 ≤ p) (hq13 : 13 ≤ q)
    (ha : 0 < a) (hb : 0 < b) :
    5 * σ 1 (p ^ a) * σ 1 (q ^ b) < 6 * usigma (p ^ a) * usigma (q ^ b) := by
  have hcp := sigma_lt_cap_usigma hp ha
  have hcq := sigma_lt_cap_usigma hq hb
  have hup : 0 < usigma (p ^ a) := by
    rw [usigma_prime_pow hp ha]
    exact Nat.add_pos_left (by decide : 0 < 1) _
  have hcap := five_p_q_cap_ge_eleven hp11 hq13 hp.one_le hq.one_le
  have := six_five_of_two_caps (A := p - 1) (B := p) (X := σ 1 (p ^ a))
    (Y := usigma (p ^ a)) (C := q - 1) (D := q) (P := σ 1 (q ^ b))
    (Q := usigma (q ^ b)) hcp hcq hcap hp.pos hup
  simpa [mul_assoc] using this

lemma twenty_five_forty_nine_overshoot_six_five :
    6 * usigma (5 ^ 2) * usigma (7 ^ 2) < 5 * σ 1 (5 ^ 2) * σ 1 (7 ^ 2) := by
  have hp7 : Nat.Prime 7 := by decide
  have hσ5 : σ 1 (5 ^ 2) = 31 := by
    rw [sigma_prime_pow_two Nat.prime_five]
    decide
  have hσ7 : σ 1 (7 ^ 2) = 57 := by
    rw [sigma_prime_pow_two hp7]
    decide
  have hu7 : usigma (7 ^ 2) = 50 := by
    simpa using usigma_prime_pow hp7 (by decide : 0 < 2)
  rw [usigma_five_pow_two, hσ5, hu7, hσ7]
  decide

/-- `{5^a, 7^b}` with `a,b ≥ 2` overshoots leftover `6/5`. -/
lemma five_seven_pow_ge_two_overshoot_six_five {a b : ℕ}
    (ha : 2 ≤ a) (hb : 2 ≤ b) :
    6 * usigma (5 ^ a) * usigma (7 ^ b) < 5 * σ 1 (5 ^ a) * σ 1 (7 ^ b) := by
  have ha0 : 0 < a := by omega
  have hb0 : 0 < b := by omega
  have hp7 : Nat.Prime 7 := by decide
  have h5 := sigma_usigma_ratio_le_of_le Nat.prime_five (by decide : 0 < 2) ha
  have h7 := sigma_usigma_ratio_le_of_le hp7 (by decide : 0 < 2) hb
  have hover := twenty_five_forty_nine_overshoot_six_five
  have hu5 : 0 < usigma (5 ^ a) := by
    rw [usigma_prime_pow Nat.prime_five ha0]
    exact Nat.add_pos_left (by decide : 0 < 1) _
  have hu7 : 0 < usigma (7 ^ b) := by
    rw [usigma_prime_pow hp7 hb0]
    exact Nat.add_pos_left (by decide : 0 < 1) _
  have hmul : σ 1 (5 ^ 2) * σ 1 (7 ^ 2) * usigma (5 ^ a) * usigma (7 ^ b) ≤
      σ 1 (5 ^ a) * σ 1 (7 ^ b) * usigma (5 ^ 2) * usigma (7 ^ 2) := by
    have h5' : σ 1 (5 ^ 2) * usigma (5 ^ a) * (σ 1 (7 ^ 2) * usigma (7 ^ b)) ≤
        σ 1 (5 ^ a) * usigma (5 ^ 2) * (σ 1 (7 ^ 2) * usigma (7 ^ b)) :=
      Nat.mul_le_mul_right _ h5
    have h7' : σ 1 (5 ^ a) * usigma (5 ^ 2) * (σ 1 (7 ^ 2) * usigma (7 ^ b)) ≤
        σ 1 (5 ^ a) * usigma (5 ^ 2) * (σ 1 (7 ^ b) * usigma (7 ^ 2)) :=
      Nat.mul_le_mul_left _ h7
    have := le_trans h5' (by simpa [mul_assoc, mul_left_comm, mul_comm] using h7')
    simpa [mul_assoc, mul_left_comm, mul_comm] using this
  have h5mul : 5 * σ 1 (5 ^ 2) * σ 1 (7 ^ 2) * usigma (5 ^ a) * usigma (7 ^ b) ≤
      5 * σ 1 (5 ^ a) * σ 1 (7 ^ b) * usigma (5 ^ 2) * usigma (7 ^ 2) := by
    simpa [mul_assoc, mul_left_comm, mul_comm] using Nat.mul_le_mul_left 5 hmul
  have h6 : 6 * usigma (5 ^ 2) * usigma (7 ^ 2) * usigma (5 ^ a) * usigma (7 ^ b) <
      5 * σ 1 (5 ^ 2) * σ 1 (7 ^ 2) * usigma (5 ^ a) * usigma (7 ^ b) := by
    have := Nat.mul_lt_mul_of_pos_right hover (mul_pos hu5 hu7)
    simpa [mul_assoc, mul_left_comm, mul_comm] using this
  have hchain : 6 * usigma (5 ^ a) * usigma (7 ^ b) * usigma (5 ^ 2) * usigma (7 ^ 2) <
      5 * σ 1 (5 ^ a) * σ 1 (7 ^ b) * usigma (5 ^ 2) * usigma (7 ^ 2) :=
    lt_of_lt_of_le (by simpa [mul_assoc, mul_left_comm, mul_comm] using h6) h5mul
  exact Nat.lt_of_mul_lt_mul_right (a := usigma (5 ^ 2) * usigma (7 ^ 2))
    (by simpa [mul_assoc, mul_left_comm, mul_comm] using hchain)

lemma not_five_sigma_eq_six_usigma_five_seven {a b : ℕ}
    (ha : 2 ≤ a) (hb : 2 ≤ b) :
    ¬ 5 * σ 1 (5 ^ a) * σ 1 (7 ^ b) = 6 * usigma (5 ^ a) * usigma (7 ^ b) :=
  (five_seven_pow_ge_two_overshoot_six_five ha hb).ne'

/-- An extra positive factor cannot repair an overshoot of leftover `6/5`. -/
lemma six_five_overshoot_mul {s t n : ℕ} (hn : n ≠ 0)
    (hover : 6 * s < 5 * t) :
    6 * s * usigma n < 5 * t * σ 1 n := by
  have hu : 0 < usigma n := usigma_pos hn
  have h1 : 6 * s * usigma n < 5 * t * usigma n :=
    Nat.mul_lt_mul_of_pos_right hover hu
  have h2 : 5 * t * usigma n ≤ 5 * t * σ 1 n :=
    Nat.mul_le_mul_left _ (usigma_le_sigma n)
  exact lt_of_lt_of_le h1 h2

/-- Raising either exponent cannot repair an overshoot of leftover `6/5`. -/
lemma six_five_overshoot_mono_two {p q a a' b b' : ℕ}
    (hp : p.Prime) (hq : q.Prime)
    (ha : 0 < a) (hb : 0 < b)
    (haa : a ≤ a') (hbb : b ≤ b')
    (hover : 6 * usigma (p ^ a) * usigma (q ^ b) <
      5 * σ 1 (p ^ a) * σ 1 (q ^ b)) :
    6 * usigma (p ^ a') * usigma (q ^ b') <
      5 * σ 1 (p ^ a') * σ 1 (q ^ b') := by
  have ha0 : 0 < a' := by omega
  have hb0 : 0 < b' := by omega
  have hp_le := sigma_usigma_ratio_le_of_le hp ha haa
  have hq_le := sigma_usigma_ratio_le_of_le hq hb hbb
  have hup' : 0 < usigma (p ^ a') := by
    rw [usigma_prime_pow hp ha0]
    exact Nat.add_pos_left (by decide : 0 < 1) _
  have huq' : 0 < usigma (q ^ b') := by
    rw [usigma_prime_pow hq hb0]
    exact Nat.add_pos_left (by decide : 0 < 1) _
  have hmul : σ 1 (p ^ a) * σ 1 (q ^ b) * usigma (p ^ a') * usigma (q ^ b') ≤
      σ 1 (p ^ a') * σ 1 (q ^ b') * usigma (p ^ a) * usigma (q ^ b) := by
    have h1 : σ 1 (p ^ a) * usigma (p ^ a') * (σ 1 (q ^ b) * usigma (q ^ b')) ≤
        σ 1 (p ^ a') * usigma (p ^ a) * (σ 1 (q ^ b) * usigma (q ^ b')) :=
      Nat.mul_le_mul_right _ hp_le
    have h2 : σ 1 (p ^ a') * usigma (p ^ a) * (σ 1 (q ^ b) * usigma (q ^ b')) ≤
        σ 1 (p ^ a') * usigma (p ^ a) * (σ 1 (q ^ b') * usigma (q ^ b)) :=
      Nat.mul_le_mul_left _ hq_le
    have := le_trans h1 (by simpa [mul_assoc, mul_left_comm, mul_comm] using h2)
    simpa [mul_assoc, mul_left_comm, mul_comm] using this
  have h5mul : 5 * σ 1 (p ^ a) * σ 1 (q ^ b) * usigma (p ^ a') * usigma (q ^ b') ≤
      5 * σ 1 (p ^ a') * σ 1 (q ^ b') * usigma (p ^ a) * usigma (q ^ b) := by
    simpa [mul_assoc, mul_left_comm, mul_comm] using Nat.mul_le_mul_left 5 hmul
  have h6 : 6 * usigma (p ^ a) * usigma (q ^ b) * usigma (p ^ a') * usigma (q ^ b') <
      5 * σ 1 (p ^ a) * σ 1 (q ^ b) * usigma (p ^ a') * usigma (q ^ b') := by
    have := Nat.mul_lt_mul_of_pos_right hover (mul_pos hup' huq')
    simpa [mul_assoc, mul_left_comm, mul_comm] using this
  have hchain : 6 * usigma (p ^ a') * usigma (q ^ b') * usigma (p ^ a) * usigma (q ^ b) <
      5 * σ 1 (p ^ a') * σ 1 (q ^ b') * usigma (p ^ a) * usigma (q ^ b) :=
    lt_of_lt_of_le (by simpa [mul_assoc, mul_left_comm, mul_comm] using h6) h5mul
  exact Nat.lt_of_mul_lt_mul_right (a := usigma (p ^ a) * usigma (q ^ b))
    (by simpa [mul_assoc, mul_left_comm, mul_comm] using hchain)

/-- `5^a` with `a ≥ 3` already overshoots leftover `6/5`, so any extra positive
factor still overshoots. -/
lemma five_pow_ge_three_mul_overshoot_six_five {a n : ℕ}
    (ha : 3 ≤ a) (hn : n ≠ 0) :
    6 * usigma (5 ^ a) * usigma n < 5 * σ 1 (5 ^ a) * σ 1 n := by
  have hover := six_usigma_lt_five_sigma_five_pow ha
  exact six_five_overshoot_mul hn hover

/-- One Euler-product cap times a constant ratio, strictly below leftover `6/5`. -/
lemma six_five_of_cap_times_const {A B X Y S T : ℕ}
    (hA : A * X < B * Y)
    (hcap : 5 * B * T ≤ 6 * A * S)
    (hT : 0 < T) :
    5 * X * T < 6 * Y * S := by
  have h5 : 5 * (A * X) * T < 5 * (B * Y) * T :=
    Nat.mul_lt_mul_of_pos_right (Nat.mul_lt_mul_of_pos_left hA (by decide : 0 < 5)) hT
  have h6 : 5 * B * T * Y ≤ 6 * A * S * Y := Nat.mul_le_mul_right Y hcap
  have hchain : 5 * A * X * T < 6 * A * Y * S := by
    have hL : 5 * A * X * T = 5 * (A * X) * T := by ring
    have hmid : 5 * (B * Y) * T = 5 * B * T * Y := by ring
    have hR' : 6 * A * S * Y = 6 * A * Y * S := by ring
    calc
      5 * A * X * T = 5 * (A * X) * T := hL
      _ < 5 * (B * Y) * T := h5
      _ = 5 * B * T * Y := hmid
      _ ≤ 6 * A * S * Y := h6
      _ = 6 * A * Y * S := hR'
  have hcancel : A * (5 * X * T) < A * (6 * Y * S) := by
    have h1 : A * (5 * X * T) = 5 * A * X * T := by ring
    have h2 : A * (6 * Y * S) = 6 * A * Y * S := by ring
    rw [h1, h2]
    exact hchain
  exact Nat.lt_of_mul_lt_mul_left hcancel

/-- `ρ(25) ρ(q^2) > 6/5` for `7 ≤ q ≤ 151`. -/
lemma five_sq_q_sq_overshoot_six_five {q : ℕ} (hq : q.Prime)
    (h7 : 7 ≤ q) (h151 : q ≤ 151) :
    6 * usigma (5 ^ 2) * usigma (q ^ 2) < 5 * σ 1 (5 ^ 2) * σ 1 (q ^ 2) := by
  have hσ5 : σ 1 (5 ^ 2) = 31 := by
    rw [sigma_prime_pow_two Nat.prime_five]
    decide
  rw [usigma_five_pow_two, hσ5, usigma_prime_pow hq (by decide : 0 < 2),
    sigma_prime_pow_two hq]
  have hsq : q ^ 2 ≤ 151 * q := by
    rw [pow_two]
    exact Nat.mul_le_mul_right q h151
  have h155 : q ^ 2 + 1 < 155 * q := by
    have : 151 * q + 1 < 155 * q := by
      have h28 : 28 ≤ 4 * q := Nat.mul_le_mul_left 4 h7
      have : 1 < 4 * q := lt_of_lt_of_le (by decide : 1 < 28) h28
      nlinarith
    omega
  have hL : ((6 * 26 * (1 + q ^ 2) : ℕ) : ℤ) =
      (6 : ℤ) * 26 * (1 + (q : ℤ) ^ 2) := by push_cast; rfl
  have hR : ((5 * 31 * (1 + q + q ^ 2) : ℕ) : ℤ) =
      (5 : ℤ) * 31 * (1 + (q : ℤ) + (q : ℤ) ^ 2) := by push_cast; rfl
  have hint : (6 : ℤ) * 26 * (1 + q ^ 2) < 5 * 31 * (1 + q + q ^ 2) := by
    have : ((q ^ 2 + 1 : ℕ) : ℤ) < 155 * q := by exact_mod_cast h155
    nlinarith
  exact Nat.cast_lt.mp (by rw [hL, hR]; exact hint)

lemma five_sq_q_pow_ge_two_overshoot_six_five {q b : ℕ} (hq : q.Prime)
    (h7 : 7 ≤ q) (h151 : q ≤ 151) (hb : 2 ≤ b) :
    6 * usigma (5 ^ 2) * usigma (q ^ b) < 5 * σ 1 (5 ^ 2) * σ 1 (q ^ b) :=
  six_five_overshoot_mono_two Nat.prime_five hq
    (by decide : 0 < 2) (by decide : 0 < 2) (le_refl _) hb
    (five_sq_q_sq_overshoot_six_five hq h7 h151)

/-- `ρ(25) cap(p) < 6/5` for every `p ≥ 157`. -/
lemma five_mul_twenty_five_cap {p : ℕ} (hp : 157 ≤ p) (hp1 : 1 ≤ p) :
    5 * p * 31 ≤ 6 * (p - 1) * 26 := by
  have hp' : (157 : ℤ) ≤ p := Int.ofNat_le.mpr hp
  have hL : ((5 * p * 31 : ℕ) : ℤ) = 5 * (p : ℤ) * 31 := by push_cast; rfl
  have hR : ((6 * (p - 1) * 26 : ℕ) : ℤ) = 6 * ((p : ℤ) - 1) * 26 := by
    rw [Nat.cast_mul, Nat.cast_mul, Nat.cast_sub hp1]
    push_cast; rfl
  have : (5 : ℤ) * p * 31 ≤ 6 * (p - 1) * 26 := by nlinarith
  exact Nat.cast_le.mp (by rw [hL, hR]; exact this)

lemma five_sigma_lt_six_usigma_five_sq_large {p k : ℕ}
    (hp : p.Prime) (hp157 : 157 ≤ p) (hk : 0 < k) :
    5 * σ 1 (5 ^ 2) * σ 1 (p ^ k) < 6 * usigma (5 ^ 2) * usigma (p ^ k) := by
  have hσ5 : σ 1 (5 ^ 2) = 31 := by
    rw [sigma_prime_pow_two Nat.prime_five]
    decide
  rw [hσ5, usigma_five_pow_two]
  have hcp := sigma_lt_cap_usigma hp hk
  have hcap := five_mul_twenty_five_cap hp157 hp.one_le
  have hthis := six_five_of_cap_times_const (A := p - 1) (B := p)
    (X := σ 1 (p ^ k)) (Y := usigma (p ^ k)) (S := 26) (T := 31)
    hcp hcap (by decide : 0 < 31)
  have hL : 5 * σ 1 (p ^ k) * 31 = 5 * 31 * σ 1 (p ^ k) := by ring
  have hR : 6 * usigma (p ^ k) * 26 = 6 * 26 * usigma (p ^ k) := by ring
  rw [← hL, ← hR]
  exact hthis

lemma prime_ge_one_fifty_two_ge_one_fifty_seven {p : ℕ} (hp : p.Prime)
    (h : 152 ≤ p) : 157 ≤ p := by
  rcases le_or_gt p 156 with h156 | h157
  · have hmem : p = 152 ∨ p = 153 ∨ p = 154 ∨ p = 155 ∨ p = 156 := by omega
    rcases hmem with rfl | rfl | rfl | rfl | rfl
    · exact False.elim (not_prime_of_eq_mul (rfl : 152 = 2 * 76)
        (by decide : (2 : ℕ) ≠ 1) (by decide : (76 : ℕ) ≠ 1) hp)
    · exact False.elim (not_prime_of_eq_mul (rfl : 153 = 9 * 17)
        (by decide : (9 : ℕ) ≠ 1) (by decide : (17 : ℕ) ≠ 1) hp)
    · exact False.elim (not_prime_of_eq_mul (rfl : 154 = 2 * 77)
        (by decide : (2 : ℕ) ≠ 1) (by decide : (77 : ℕ) ≠ 1) hp)
    · exact False.elim (not_prime_of_eq_mul (rfl : 155 = 5 * 31)
        (by decide : (5 : ℕ) ≠ 1) (by decide : (31 : ℕ) ≠ 1) hp)
    · exact False.elim (not_prime_of_eq_mul (rfl : 156 = 2 * 78)
        (by decide : (2 : ℕ) ≠ 1) (by decide : (78 : ℕ) ≠ 1) hp)
  · exact Nat.succ_le_of_lt h157

/-- `{5^a, q^k}` cannot fill leftover `6/5` for primes `q ≥ 7` and
exponents `a,k ≥ 2`. -/
lemma not_five_sigma_eq_six_usigma_five_prime {a k q : ℕ}
    (hq : q.Prime) (hq7 : 7 ≤ q) (ha : 2 ≤ a) (hk : 2 ≤ k) :
    ¬ 5 * σ 1 (5 ^ a) * σ 1 (q ^ k) = 6 * usigma (5 ^ a) * usigma (q ^ k) := by
  intro heq
  rcases eq_or_ne q 7 with rfl | _
  · exact not_five_sigma_eq_six_usigma_five_seven ha hk heq
  rcases eq_or_lt_of_le ha with ha2 | ha3
  · rw [← ha2] at heq
    rcases le_or_gt q 151 with h151 | h152
    · exact (five_sq_q_pow_ge_two_overshoot_six_five hq hq7 h151 hk).ne' heq
    · have hp157 : 157 ≤ q :=
        prime_ge_one_fifty_two_ge_one_fifty_seven hq (by omega)
      exact (five_sigma_lt_six_usigma_five_sq_large hq hp157 (by omega)).ne heq
  · exact (five_pow_ge_three_mul_overshoot_six_five (Nat.succ_le_of_lt ha3)
      (Nat.pow_pos hq.pos).ne').ne' (by simpa [mul_assoc] using heq)

/-- `ρ(49) ρ(q^2) > 6/5` for `11 ≤ q ≤ 17`. -/
lemma seven_sq_q_sq_overshoot_six_five {q : ℕ} (hq : q.Prime)
    (h11 : 11 ≤ q) (h17 : q ≤ 17) :
    6 * usigma (7 ^ 2) * usigma (q ^ 2) < 5 * σ 1 (7 ^ 2) * σ 1 (q ^ 2) := by
  have hp7 : Nat.Prime 7 := by decide
  have hσ7 : σ 1 (7 ^ 2) = 57 := by
    rw [sigma_prime_pow_two hp7]
    decide
  have hu7 : usigma (7 ^ 2) = 50 := by
    simpa using usigma_prime_pow hp7 (by decide : 0 < 2)
  rw [hu7, hσ7, usigma_prime_pow hq (by decide : 0 < 2), sigma_prime_pow_two hq]
  have hsq : q ^ 2 ≤ 17 * q := by
    rw [pow_two]
    exact Nat.mul_le_mul_right q h17
  have h19 : q ^ 2 + 1 < 19 * q := by
    have : 17 * q + 1 < 19 * q := by
      have h22 : 22 ≤ 2 * q := Nat.mul_le_mul_left 2 h11
      have : 1 < 2 * q := lt_of_lt_of_le (by decide : 1 < 22) h22
      nlinarith
    omega
  have hL : ((6 * 50 * (1 + q ^ 2) : ℕ) : ℤ) =
      (6 : ℤ) * 50 * (1 + (q : ℤ) ^ 2) := by push_cast; rfl
  have hR : ((5 * 57 * (1 + q + q ^ 2) : ℕ) : ℤ) =
      (5 : ℤ) * 57 * (1 + (q : ℤ) + (q : ℤ) ^ 2) := by push_cast; rfl
  have hint : (6 : ℤ) * 50 * (1 + q ^ 2) < 5 * 57 * (1 + q + q ^ 2) := by
    have : ((q ^ 2 + 1 : ℕ) : ℤ) < 19 * q := by exact_mod_cast h19
    nlinarith
  exact Nat.cast_lt.mp (by rw [hL, hR]; exact hint)

lemma seven_sq_q_pow_ge_two_overshoot_six_five {q a b : ℕ} (hq : q.Prime)
    (h11 : 11 ≤ q) (h17 : q ≤ 17) (ha : 2 ≤ a) (hb : 2 ≤ b) :
    6 * usigma (7 ^ a) * usigma (q ^ b) <
      5 * σ 1 (7 ^ a) * σ 1 (q ^ b) :=
  six_five_overshoot_mono_two (by decide : Nat.Prime 7) hq
    (by decide : 0 < 2) (by decide : 0 < 2) ha hb
    (seven_sq_q_sq_overshoot_six_five hq h11 h17)

lemma forty_nine_nineteen_sq_undershoot_six_five :
    5 * σ 1 (7 ^ 2) * σ 1 (19 ^ 2) < 6 * usigma (7 ^ 2) * usigma (19 ^ 2) := by
  have hp7 : Nat.Prime 7 := by decide
  have hp19 : Nat.Prime 19 := by decide
  have hσ7 : σ 1 (7 ^ 2) = 57 := by
    rw [sigma_prime_pow_two hp7]
    decide
  have hu7 : usigma (7 ^ 2) = 50 := by
    simpa using usigma_prime_pow hp7 (by decide : 0 < 2)
  have hσ19 : σ 1 (19 ^ 2) = 381 := by
    rw [sigma_prime_pow_two hp19]
    decide
  have hu19 : usigma (19 ^ 2) = 362 := by
    simpa using usigma_prime_pow hp19 (by decide : 0 < 2)
  rw [hσ7, hu7, hσ19, hu19]
  decide

lemma forty_nine_nineteen_cube_overshoot_six_five :
    6 * usigma (7 ^ 2) * usigma (19 ^ 3) < 5 * σ 1 (7 ^ 2) * σ 1 (19 ^ 3) := by
  have hp7 : Nat.Prime 7 := by decide
  have hσ7 : σ 1 (7 ^ 2) = 57 := by
    rw [sigma_prime_pow_two hp7]
    decide
  have hu7 : usigma (7 ^ 2) = 50 := by
    simpa using usigma_prime_pow hp7 (by decide : 0 < 2)
  rw [hu7, hσ7, usigma_nineteen_pow_three, sigma_nineteen_pow_three]
  decide

lemma seven_cube_nineteen_sq_overshoot_six_five :
    6 * usigma (7 ^ 3) * usigma (19 ^ 2) < 5 * σ 1 (7 ^ 3) * σ 1 (19 ^ 2) := by
  have hp19 : Nat.Prime 19 := by decide
  have hσ19 : σ 1 (19 ^ 2) = 381 := by
    rw [sigma_prime_pow_two hp19]
    decide
  have hu19 : usigma (19 ^ 2) = 362 := by
    simpa using usigma_prime_pow hp19 (by decide : 0 < 2)
  rw [usigma_seven_pow_three, sigma_seven_pow_three, hu19, hσ19]
  decide

/-- `{7^a, 19^k}` cannot fill leftover `6/5` for `a,k ≥ 2`. -/
lemma not_five_sigma_eq_six_usigma_seven_nineteen {a k : ℕ}
    (ha : 2 ≤ a) (hk : 2 ≤ k) :
    ¬ 5 * σ 1 (7 ^ a) * σ 1 (19 ^ k) = 6 * usigma (7 ^ a) * usigma (19 ^ k) := by
  intro heq
  rcases eq_or_lt_of_le ha with ha2 | ha3
  · rw [← ha2] at heq
    rcases eq_or_lt_of_le hk with hk2 | hk3
    · rw [← hk2] at heq
      exact forty_nine_nineteen_sq_undershoot_six_five.ne heq
    · exact (six_five_overshoot_mono_two (by decide : Nat.Prime 7)
          (by decide : Nat.Prime 19)
          (by decide : 0 < 2) (by decide : 0 < 3)
          (le_refl _) (Nat.succ_le_of_lt hk3)
          forty_nine_nineteen_cube_overshoot_six_five).ne' heq
  · exact (six_five_overshoot_mono_two (by decide : Nat.Prime 7)
        (by decide : Nat.Prime 19)
        (by decide : 0 < 3) (by decide : 0 < 2)
        (Nat.succ_le_of_lt ha3) hk
        seven_cube_nineteen_sq_overshoot_six_five).ne' heq

/-- `ρ(49) cap(p) < 6/5` for every `p ≥ 23`. -/
lemma five_mul_forty_nine_cap {p : ℕ} (hp : 23 ≤ p) (hp1 : 1 ≤ p) :
    5 * p * 57 ≤ 6 * (p - 1) * 50 := by
  have hp' : (23 : ℤ) ≤ p := Int.ofNat_le.mpr hp
  have hL : ((5 * p * 57 : ℕ) : ℤ) = 5 * (p : ℤ) * 57 := by push_cast; rfl
  have hR : ((6 * (p - 1) * 50 : ℕ) : ℤ) = 6 * ((p : ℤ) - 1) * 50 := by
    rw [Nat.cast_mul, Nat.cast_mul, Nat.cast_sub hp1]
    push_cast; rfl
  have : (5 : ℤ) * p * 57 ≤ 6 * (p - 1) * 50 := by nlinarith
  exact Nat.cast_le.mp (by rw [hL, hR]; exact this)

lemma five_sigma_lt_six_usigma_seven_sq_large {p k : ℕ}
    (hp : p.Prime) (hp23 : 23 ≤ p) (hk : 0 < k) :
    5 * σ 1 (7 ^ 2) * σ 1 (p ^ k) < 6 * usigma (7 ^ 2) * usigma (p ^ k) := by
  have hp7 : Nat.Prime 7 := by decide
  have hσ7 : σ 1 (7 ^ 2) = 57 := by
    rw [sigma_prime_pow_two hp7]
    decide
  have hu7 : usigma (7 ^ 2) = 50 := by
    simpa using usigma_prime_pow hp7 (by decide : 0 < 2)
  rw [hσ7, hu7]
  have hcp := sigma_lt_cap_usigma hp hk
  have hcap := five_mul_forty_nine_cap hp23 hp.one_le
  have hthis := six_five_of_cap_times_const (A := p - 1) (B := p)
    (X := σ 1 (p ^ k)) (Y := usigma (p ^ k)) (S := 50) (T := 57)
    hcp hcap (by decide : 0 < 57)
  have hL : 5 * σ 1 (p ^ k) * 57 = 5 * 57 * σ 1 (p ^ k) := by ring
  have hR : 6 * usigma (p ^ k) * 50 = 6 * 50 * usigma (p ^ k) := by ring
  rw [← hL, ← hR]
  exact hthis

/-- `ρ(343) ρ(q^2) > 6/5` for `11 ≤ q ≤ 31`. -/
lemma seven_cube_q_sq_overshoot_six_five {q : ℕ} (hq : q.Prime)
    (h11 : 11 ≤ q) (h31 : q ≤ 31) :
    6 * usigma (7 ^ 3) * usigma (q ^ 2) < 5 * σ 1 (7 ^ 3) * σ 1 (q ^ 2) := by
  rw [usigma_seven_pow_three, sigma_seven_pow_three,
    usigma_prime_pow hq (by decide : 0 < 2), sigma_prime_pow_two hq]
  have hsq : q ^ 2 ≤ 31 * q := by
    rw [pow_two]
    exact Nat.mul_le_mul_right q h31
  have hL : ((6 * 344 * (1 + q ^ 2) : ℕ) : ℤ) =
      (6 : ℤ) * 344 * (1 + (q : ℤ) ^ 2) := by push_cast; rfl
  have hR : ((5 * 400 * (1 + q + q ^ 2) : ℕ) : ℤ) =
      (5 : ℤ) * 400 * (1 + (q : ℤ) + (q : ℤ) ^ 2) := by push_cast; rfl
  have hint : (6 : ℤ) * 344 * (1 + q ^ 2) < 5 * 400 * (1 + q + q ^ 2) := by
    have hq11 : (11 : ℤ) ≤ q := by exact_mod_cast h11
    have hq31 : (q : ℤ) ≤ 31 := by exact_mod_cast h31
    have hsq' : (q : ℤ) ^ 2 ≤ 31 * q := by exact_mod_cast hsq
    nlinarith
  exact Nat.cast_lt.mp (by rw [hL, hR]; exact hint)

lemma seven_cube_q_pow_ge_two_overshoot_six_five {q a b : ℕ} (hq : q.Prime)
    (h11 : 11 ≤ q) (h31 : q ≤ 31) (ha : 3 ≤ a) (hb : 2 ≤ b) :
    6 * usigma (7 ^ a) * usigma (q ^ b) <
      5 * σ 1 (7 ^ a) * σ 1 (q ^ b) :=
  six_five_overshoot_mono_two (by decide : Nat.Prime 7) hq
    (by decide : 0 < 3) (by decide : 0 < 2) ha hb
    (seven_cube_q_sq_overshoot_six_five hq h11 h31)

/-- Euler caps `7/6 · q/(q-1) < 6/5` for every `q ≥ 37`. -/
lemma five_seven_q_cap {q : ℕ} (hq : 37 ≤ q) (hq1 : 1 ≤ q) :
    5 * 7 * q ≤ 6 * 6 * (q - 1) := by
  have hq' : (37 : ℤ) ≤ q := Int.ofNat_le.mpr hq
  have hL : ((5 * 7 * q : ℕ) : ℤ) = 5 * 7 * (q : ℤ) := by push_cast; rfl
  have hR : ((6 * 6 * (q - 1) : ℕ) : ℤ) = 6 * 6 * ((q : ℤ) - 1) := by
    rw [Nat.cast_mul, Nat.cast_mul, Nat.cast_sub hq1]
    push_cast; rfl
  have : (5 : ℤ) * 7 * q ≤ 6 * 6 * (q - 1) := by nlinarith
  exact Nat.cast_le.mp (by rw [hL, hR]; exact this)

lemma five_sigma_lt_six_usigma_seven_large {q a b : ℕ}
    (hq : q.Prime) (hq37 : 37 ≤ q) (ha : 0 < a) (hb : 0 < b) :
    5 * σ 1 (7 ^ a) * σ 1 (q ^ b) < 6 * usigma (7 ^ a) * usigma (q ^ b) := by
  have hp7 : Nat.Prime 7 := by decide
  have hcp := sigma_lt_cap_usigma hp7 ha
  have hcq := sigma_lt_cap_usigma hq hb
  have hu7 : 0 < usigma (7 ^ a) := by
    rw [usigma_prime_pow hp7 ha]
    exact Nat.add_pos_left (by decide : 0 < 1) _
  have hcap := five_seven_q_cap hq37 hq.one_le
  have := six_five_of_two_caps (A := 6) (B := 7) (X := σ 1 (7 ^ a))
    (Y := usigma (7 ^ a)) (C := q - 1) (D := q) (P := σ 1 (q ^ b))
    (Q := usigma (q ^ b)) hcp hcq hcap (by decide : 0 < 7) hu7
  simpa [mul_assoc] using this

lemma prime_ge_eighteen_eq_nineteen {p : ℕ} (hp : p.Prime)
    (h : 18 ≤ p) (h19 : p ≤ 19) : p = 19 := by
  have hmem : p = 18 ∨ p = 19 := by omega
  rcases hmem with rfl | rfl
  · exact False.elim ((by decide : ¬ Nat.Prime 18) hp)
  · rfl

/-- `{7^a, q^k}` cannot fill leftover `6/5` for primes `q ≥ 11` and
exponents `a,k ≥ 2`. -/
lemma not_five_sigma_eq_six_usigma_seven_prime {a k q : ℕ}
    (hq : q.Prime) (hq11 : 11 ≤ q) (ha : 2 ≤ a) (hk : 2 ≤ k) :
    ¬ 5 * σ 1 (7 ^ a) * σ 1 (q ^ k) = 6 * usigma (7 ^ a) * usigma (q ^ k) := by
  intro heq
  rcases le_or_gt q 17 with h17 | h18
  · exact (seven_sq_q_pow_ge_two_overshoot_six_five hq hq11 h17 ha hk).ne' heq
  · rcases le_or_gt q 19 with h19 | h20
    · have hq19 : q = 19 := prime_ge_eighteen_eq_nineteen hq (by omega) h19
      rw [hq19] at heq
      exact not_five_sigma_eq_six_usigma_seven_nineteen ha hk heq
    · rcases le_or_gt q 31 with h31 | h32
      · rcases eq_or_lt_of_le ha with ha2 | ha3
        · rw [← ha2] at heq
          have hp23 : 23 ≤ q := prime_ge_twenty_ge_twenty_three hq (by omega)
          exact (five_sigma_lt_six_usigma_seven_sq_large hq hp23 (by omega)).ne
            heq
        · exact (seven_cube_q_pow_ge_two_overshoot_six_five hq hq11 h31
            (Nat.succ_le_of_lt ha3) hk).ne' heq
      · have hq37 : 37 ≤ q := prime_ge_thirty_two_ge_thirty_seven hq (by omega)
        exact (five_sigma_lt_six_usigma_seven_large hq hq37 (by omega)
          (by omega)).ne heq

/-- If the rest after two distinct prime powers is squarefree, leftover `6/5`
is concentrated on those two prime powers. -/
lemma five_sigma_eq_six_of_two_squareful {m p q : ℕ} (hm : m ≠ 0)
    (hp : p.Prime) (hq : q.Prime) (_hpq : p ≠ q)
    (h : 5 * σ 1 m = 6 * usigma m)
    (hs : Squarefree (ordCompl[q] (ordCompl[p] m))) :
    5 * σ 1 (ordProj[p] m) * σ 1 (ordProj[q] (ordCompl[p] m)) =
      6 * usigma (ordProj[p] m) * usigma (ordProj[q] (ordCompl[p] m)) := by
  set r := ordCompl[q] (ordCompl[p] m)
  have hm' : ordCompl[p] m ≠ 0 := (Nat.ordCompl_pos p hm).ne'
  have hdecomp_p : ordProj[p] m * ordCompl[p] m = m :=
    Nat.ordProj_mul_ordCompl_eq_self m p
  have hdecomp_q : ordProj[q] (ordCompl[p] m) * r = ordCompl[p] m :=
    Nat.ordProj_mul_ordCompl_eq_self (ordCompl[p] m) q
  have hc_p : Coprime (ordProj[p] m) (ordCompl[p] m) :=
    (Nat.coprime_ordCompl hp hm).pow_left (m.factorization p)
  have hc_q : Coprime (ordProj[q] (ordCompl[p] m)) r :=
    (Nat.coprime_ordCompl hq hm').pow_left ((ordCompl[p] m).factorization q)
  have hmul : 5 * σ 1 (ordProj[p] m) * σ 1 (ordProj[q] (ordCompl[p] m)) * σ 1 r =
      6 * usigma (ordProj[p] m) * usigma (ordProj[q] (ordCompl[p] m)) * usigma r := by
    have := h
    rw [← hdecomp_p, sigma_mul_of_coprime hc_p, usigma_mul hc_p] at this
    rw [← hdecomp_q, sigma_mul_of_coprime hc_q, usigma_mul hc_q] at this
    simpa [mul_assoc, mul_left_comm, mul_comm] using this
  have hσu := (sigma_eq_usigma_iff_squarefree (Nat.ordCompl_pos q hm')).mpr hs
  rw [hσu] at hmul
  have hpos : 0 < usigma r := by
    rw [← hσu]
    exact sigma_pos_iff.mpr (Nat.ordCompl_pos q hm')
  exact Nat.eq_of_mul_eq_mul_right hpos hmul

/-- If the rest after three distinct prime powers is squarefree, leftover
`6/5` is concentrated on those three prime powers. -/
lemma five_sigma_eq_six_of_three_squareful {m p q r : ℕ} (hm : m ≠ 0)
    (hp : p.Prime) (hq : q.Prime) (hr : r.Prime)
    (_hpq : p ≠ q) (_hpr : p ≠ r) (_hqr : q ≠ r)
    (h : 5 * σ 1 m = 6 * usigma m)
    (hs : Squarefree (ordCompl[r] (ordCompl[q] (ordCompl[p] m)))) :
    5 * σ 1 (ordProj[p] m) * σ 1 (ordProj[q] (ordCompl[p] m)) *
        σ 1 (ordProj[r] (ordCompl[q] (ordCompl[p] m))) =
      6 * usigma (ordProj[p] m) * usigma (ordProj[q] (ordCompl[p] m)) *
        usigma (ordProj[r] (ordCompl[q] (ordCompl[p] m))) := by
  set t := ordCompl[r] (ordCompl[q] (ordCompl[p] m))
  have hm' : ordCompl[p] m ≠ 0 := (Nat.ordCompl_pos p hm).ne'
  have hm'' : ordCompl[q] (ordCompl[p] m) ≠ 0 :=
    (Nat.ordCompl_pos q hm').ne'
  have hdecomp_p : ordProj[p] m * ordCompl[p] m = m :=
    Nat.ordProj_mul_ordCompl_eq_self m p
  have hdecomp_q : ordProj[q] (ordCompl[p] m) * ordCompl[q] (ordCompl[p] m) =
      ordCompl[p] m :=
    Nat.ordProj_mul_ordCompl_eq_self (ordCompl[p] m) q
  have hdecomp_r : ordProj[r] (ordCompl[q] (ordCompl[p] m)) * t =
      ordCompl[q] (ordCompl[p] m) :=
    Nat.ordProj_mul_ordCompl_eq_self (ordCompl[q] (ordCompl[p] m)) r
  have hc_p : Coprime (ordProj[p] m) (ordCompl[p] m) :=
    (Nat.coprime_ordCompl hp hm).pow_left (m.factorization p)
  have hc_q : Coprime (ordProj[q] (ordCompl[p] m))
      (ordCompl[q] (ordCompl[p] m)) :=
    (Nat.coprime_ordCompl hq hm').pow_left ((ordCompl[p] m).factorization q)
  have hc_r : Coprime (ordProj[r] (ordCompl[q] (ordCompl[p] m))) t :=
    (Nat.coprime_ordCompl hr hm'').pow_left
      ((ordCompl[q] (ordCompl[p] m)).factorization r)
  have hmul : 5 * σ 1 (ordProj[p] m) * σ 1 (ordProj[q] (ordCompl[p] m)) *
        σ 1 (ordProj[r] (ordCompl[q] (ordCompl[p] m))) * σ 1 t =
      6 * usigma (ordProj[p] m) * usigma (ordProj[q] (ordCompl[p] m)) *
        usigma (ordProj[r] (ordCompl[q] (ordCompl[p] m))) * usigma t := by
    have := h
    rw [← hdecomp_p, sigma_mul_of_coprime hc_p, usigma_mul hc_p] at this
    rw [← hdecomp_q, sigma_mul_of_coprime hc_q, usigma_mul hc_q] at this
    rw [← hdecomp_r, sigma_mul_of_coprime hc_r, usigma_mul hc_r] at this
    simpa [mul_assoc, mul_left_comm, mul_comm] using this
  have hσu := (sigma_eq_usigma_iff_squarefree (Nat.ordCompl_pos r hm'')).mpr hs
  rw [hσu] at hmul
  have hpos : 0 < usigma t := by
    rw [← hσu]
    exact sigma_pos_iff.mpr (Nat.ordCompl_pos r hm'')
  exact Nat.eq_of_mul_eq_mul_right hpos hmul

/-- Leftover `6/5` cannot be two squareful primes `p < q`, both at least `5`,
times a squarefree coprime factor. -/
lemma not_five_sigma_of_two_sq_primes {m p q : ℕ} (hm : m ≠ 0)
    (hp : p.Prime) (hq : q.Prime) (hpq : p < q) (hp5 : 5 ≤ p)
    (h : 5 * σ 1 m = 6 * usigma m)
    (hkp : 2 ≤ padicValNat p m) (hkq : 2 ≤ padicValNat q m)
    (hs : Squarefree (ordCompl[q] (ordCompl[p] m))) : False := by
  have hpq_ne : p ≠ q := Nat.ne_of_lt hpq
  have heq := five_sigma_eq_six_of_two_squareful hm hp hq hpq_ne h hs
  have hproj_p : ordProj[p] m = p ^ padicValNat p m := by
    simp [Nat.factorization_def m hp]
  have hproj_q : ordProj[q] (ordCompl[p] m) =
      q ^ padicValNat q (ordCompl[p] m) := by
    simp [Nat.factorization_def (ordCompl[p] m) hq]
  rw [hproj_q, padicValNat_ordCompl_of_ne hq hpq_ne, hproj_p] at heq
  have hp_cases : p = 5 ∨ 7 ≤ p := by
    have : p = 5 ∨ 6 ≤ p := by omega
    rcases this with rfl | h6
    · exact Or.inl rfl
    · have : p ≠ 6 := fun h6eq => (by decide : ¬ Nat.Prime 6) (h6eq ▸ hp)
      exact Or.inr (by omega)
  rcases hp_cases with rfl | hp7
  · have hq7 : 7 ≤ q := by
      have : 6 ≤ q := by omega
      have : q ≠ 6 := fun h6eq => (by decide : ¬ Nat.Prime 6) (h6eq ▸ hq)
      omega
    exact not_five_sigma_eq_six_usigma_five_prime hq hq7 hkp hkq heq
  · have hq11 : 11 ≤ q := by
      have : 8 ≤ q := by omega
      have hmem : q = 8 ∨ q = 9 ∨ q = 10 ∨ 11 ≤ q := by omega
      rcases hmem with rfl | rfl | rfl | h11
      · cases (by decide : ¬ Nat.Prime 8) hq
      · cases (by decide : ¬ Nat.Prime 9) hq
      · cases (by decide : ¬ Nat.Prime 10) hq
      · exact h11
    have hp_cases' : p = 7 ∨ 11 ≤ p := by
      have hmem : p = 7 ∨ p = 8 ∨ p = 9 ∨ p = 10 ∨ 11 ≤ p := by omega
      rcases hmem with rfl | rfl | rfl | rfl | h11
      · exact Or.inl rfl
      · cases (by decide : ¬ Nat.Prime 8) hp
      · cases (by decide : ¬ Nat.Prime 9) hp
      · cases (by decide : ¬ Nat.Prime 10) hp
      · exact Or.inr h11
    rcases hp_cases' with rfl | hp11
    · exact not_five_sigma_eq_six_usigma_seven_prime hq hq11 hkp hkq heq
    · have hq13 : 13 ≤ q := by
        have : 12 ≤ q := by omega
        have hmem : q = 12 ∨ 13 ≤ q := by omega
        rcases hmem with rfl | h13
        · cases (by decide : ¬ Nat.Prime 12) hq
        · exact h13
      exact (five_sigma_lt_six_usigma_two_large hp hq hp11 hq13
        (by omega) (by omega)).ne heq

/-- If `8m` is in `A` with `m` odd, leftover `6/5` cannot be two squareful
primes `p < q` both at least `5` times a squarefree coprime factor. -/
lemma not_A_of_eight_mul_two_sq_primes {m p q : ℕ} (hm : Odd m) (hA : A (8 * m))
    (hp : p.Prime) (hq : q.Prime) (hpq : p < q) (hp5 : 5 ≤ p)
    (hkp : 2 ≤ padicValNat p m) (hkq : 2 ≤ padicValNat q m)
    (hs : Squarefree (ordCompl[q] (ordCompl[p] m))) : False := by
  have hm0 : m ≠ 0 := Nat.pos_iff_ne_zero.mp hm.pos
  have h := five_sigma_eq_six_usigma_of_A_eight_mul hm hA
  exact not_five_sigma_of_two_sq_primes hm0 hp hq hpq hp5 h hkp hkq hs

lemma not_five_sigma_eq_six_of_squarefree {m : ℕ} (hm : 0 < m)
    (hs : Squarefree m) (h : 5 * σ 1 m = 6 * usigma m) : False := by
  have hσu := (sigma_eq_usigma_iff_squarefree hm).mpr hs
  rw [hσu] at h
  have : 5 = 6 := Nat.eq_of_mul_eq_mul_right (usigma_pos hm.ne') h
  contradiction

/-- `{5^a, 7^b}` with `a,b ≥ 2` already overshoots leftover `6/5`, so any extra
positive factor still overshoots. This includes every ω≥3 kernel containing
both `5` and `7` as squareful primes. -/
lemma five_seven_pow_ge_two_mul_overshoot_six_five {a b n : ℕ}
    (ha : 2 ≤ a) (hb : 2 ≤ b) (hn : n ≠ 0) :
    6 * usigma (5 ^ a) * usigma (7 ^ b) * usigma n <
      5 * σ 1 (5 ^ a) * σ 1 (7 ^ b) * σ 1 n := by
  have hover := five_seven_pow_ge_two_overshoot_six_five ha hb
  have h := six_five_overshoot_mul (s := usigma (5 ^ a) * usigma (7 ^ b))
      (t := σ 1 (5 ^ a) * σ 1 (7 ^ b)) hn (by
        have hL : 6 * (usigma (5 ^ a) * usigma (7 ^ b)) =
            6 * usigma (5 ^ a) * usigma (7 ^ b) := by ring
        have hR : 5 * (σ 1 (5 ^ a) * σ 1 (7 ^ b)) =
            5 * σ 1 (5 ^ a) * σ 1 (7 ^ b) := by ring
        rw [hL, hR]
        exact hover)
  have hL : 6 * (usigma (5 ^ a) * usigma (7 ^ b)) * usigma n =
      6 * usigma (5 ^ a) * usigma (7 ^ b) * usigma n := by ring
  have hR : 5 * (σ 1 (5 ^ a) * σ 1 (7 ^ b)) * σ 1 n =
      5 * σ 1 (5 ^ a) * σ 1 (7 ^ b) * σ 1 n := by ring
  rw [← hL, ← hR]
  exact h

lemma not_five_sigma_eq_six_usigma_five_seven_mul {a b n : ℕ}
    (ha : 2 ≤ a) (hb : 2 ≤ b) (hn : n ≠ 0) :
    ¬ 5 * σ 1 (5 ^ a) * σ 1 (7 ^ b) * σ 1 n =
        6 * usigma (5 ^ a) * usigma (7 ^ b) * usigma n :=
  (five_seven_pow_ge_two_mul_overshoot_six_five ha hb hn).ne'

lemma usigma_thirteen_pow_two : usigma (13 ^ 2) = 170 := by
  simpa using usigma_prime_pow (by decide : Nat.Prime 13) (by decide : 0 < 2)

lemma sigma_thirteen_pow_two : σ 1 (13 ^ 2) = 183 := by
  rw [sigma_prime_pow_two (by decide : Nat.Prime 13)]
  decide

lemma usigma_seventeen_pow_two : usigma (17 ^ 2) = 290 := by
  simpa using usigma_prime_pow (by decide : Nat.Prime 17) (by decide : 0 < 2)

lemma sigma_seventeen_pow_two : σ 1 (17 ^ 2) = 307 := by
  rw [sigma_prime_pow_two (by decide : Nat.Prime 17)]
  decide

/-- Raising any of three exponents cannot repair an overshoot of leftover `6/5`. -/
lemma six_five_overshoot_mono_three {p q r a a' b b' c c' : ℕ}
    (hp : p.Prime) (hq : q.Prime) (hr : r.Prime)
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (haa : a ≤ a') (hbb : b ≤ b') (hcc : c ≤ c')
    (hover : 6 * usigma (p ^ a) * usigma (q ^ b) * usigma (r ^ c) <
      5 * σ 1 (p ^ a) * σ 1 (q ^ b) * σ 1 (r ^ c)) :
    6 * usigma (p ^ a') * usigma (q ^ b') * usigma (r ^ c') <
      5 * σ 1 (p ^ a') * σ 1 (q ^ b') * σ 1 (r ^ c') := by
  have ha0 : 0 < a' := by omega
  have hb0 : 0 < b' := by omega
  have hc0 : 0 < c' := by omega
  have hp_le := sigma_usigma_ratio_le_of_le hp ha haa
  have hq_le := sigma_usigma_ratio_le_of_le hq hb hbb
  have hr_le := sigma_usigma_ratio_le_of_le hr hc hcc
  have hup' : 0 < usigma (p ^ a') := by
    rw [usigma_prime_pow hp ha0]
    exact Nat.add_pos_left (by decide : 0 < 1) _
  have huq' : 0 < usigma (q ^ b') := by
    rw [usigma_prime_pow hq hb0]
    exact Nat.add_pos_left (by decide : 0 < 1) _
  have hur' : 0 < usigma (r ^ c') := by
    rw [usigma_prime_pow hr hc0]
    exact Nat.add_pos_left (by decide : 0 < 1) _
  have hmul : σ 1 (p ^ a) * σ 1 (q ^ b) * σ 1 (r ^ c) *
        usigma (p ^ a') * usigma (q ^ b') * usigma (r ^ c') ≤
      σ 1 (p ^ a') * σ 1 (q ^ b') * σ 1 (r ^ c') *
        usigma (p ^ a) * usigma (q ^ b) * usigma (r ^ c) := by
    have h1 : σ 1 (p ^ a) * usigma (p ^ a') *
          (σ 1 (q ^ b) * usigma (q ^ b') * (σ 1 (r ^ c) * usigma (r ^ c'))) ≤
        σ 1 (p ^ a') * usigma (p ^ a) *
          (σ 1 (q ^ b) * usigma (q ^ b') * (σ 1 (r ^ c) * usigma (r ^ c'))) :=
      Nat.mul_le_mul_right _ hp_le
    have h2 : σ 1 (p ^ a') * usigma (p ^ a) *
          (σ 1 (q ^ b) * usigma (q ^ b') * (σ 1 (r ^ c) * usigma (r ^ c'))) ≤
        σ 1 (p ^ a') * usigma (p ^ a) *
          (σ 1 (q ^ b') * usigma (q ^ b) * (σ 1 (r ^ c) * usigma (r ^ c'))) :=
      Nat.mul_le_mul_left _ (Nat.mul_le_mul_right _ hq_le)
    have h3 : σ 1 (p ^ a') * usigma (p ^ a) *
          (σ 1 (q ^ b') * usigma (q ^ b) * (σ 1 (r ^ c) * usigma (r ^ c'))) ≤
        σ 1 (p ^ a') * usigma (p ^ a) *
          (σ 1 (q ^ b') * usigma (q ^ b) * (σ 1 (r ^ c') * usigma (r ^ c))) :=
      Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ hr_le)
    have h12 := le_trans h1 (by simpa [mul_assoc, mul_left_comm, mul_comm] using h2)
    have h123 := le_trans h12 (by simpa [mul_assoc, mul_left_comm, mul_comm] using h3)
    simpa [mul_assoc, mul_left_comm, mul_comm] using h123
  have h5mul : 5 * σ 1 (p ^ a) * σ 1 (q ^ b) * σ 1 (r ^ c) *
        usigma (p ^ a') * usigma (q ^ b') * usigma (r ^ c') ≤
      5 * σ 1 (p ^ a') * σ 1 (q ^ b') * σ 1 (r ^ c') *
        usigma (p ^ a) * usigma (q ^ b) * usigma (r ^ c) := by
    simpa [mul_assoc, mul_left_comm, mul_comm] using Nat.mul_le_mul_left 5 hmul
  have h6 : 6 * usigma (p ^ a) * usigma (q ^ b) * usigma (r ^ c) *
        usigma (p ^ a') * usigma (q ^ b') * usigma (r ^ c') <
      5 * σ 1 (p ^ a) * σ 1 (q ^ b) * σ 1 (r ^ c) *
        usigma (p ^ a') * usigma (q ^ b') * usigma (r ^ c') := by
    have := Nat.mul_lt_mul_of_pos_right hover (mul_pos hup' (mul_pos huq' hur'))
    simpa [mul_assoc, mul_left_comm, mul_comm] using this
  have hchain : 6 * usigma (p ^ a') * usigma (q ^ b') * usigma (r ^ c') *
        usigma (p ^ a) * usigma (q ^ b) * usigma (r ^ c) <
      5 * σ 1 (p ^ a') * σ 1 (q ^ b') * σ 1 (r ^ c') *
        usigma (p ^ a) * usigma (q ^ b) * usigma (r ^ c) :=
    lt_of_lt_of_le (by simpa [mul_assoc, mul_left_comm, mul_comm] using h6) h5mul
  exact Nat.lt_of_mul_lt_mul_right
    (a := usigma (p ^ a) * usigma (q ^ b) * usigma (r ^ c))
    (by simpa [mul_assoc, mul_left_comm, mul_comm] using hchain)

/-- `ρ(121) ρ(169) ρ(p^2) > 6/5` for `17 ≤ p ≤ 43`. -/
lemma eleven_thirteen_sq_p_sq_overshoot_six_five {p : ℕ} (hp : p.Prime)
    (h17 : 17 ≤ p) (h43 : p ≤ 43) :
    6 * usigma (11 ^ 2) * usigma (13 ^ 2) * usigma (p ^ 2) <
      5 * σ 1 (11 ^ 2) * σ 1 (13 ^ 2) * σ 1 (p ^ 2) := by
  rw [usigma_eleven_pow_two, sigma_eleven_pow_two,
    usigma_thirteen_pow_two, sigma_thirteen_pow_two,
    usigma_prime_pow hp (by decide : 0 < 2), sigma_prime_pow_two hp]
  have hsq : p ^ 2 ≤ 43 * p := by
    rw [pow_two]
    exact Nat.mul_le_mul_right p h43
  have hL : ((6 * 122 * 170 * (1 + p ^ 2) : ℕ) : ℤ) =
      (6 : ℤ) * 122 * 170 * (1 + (p : ℤ) ^ 2) := by push_cast; rfl
  have hR : ((5 * 133 * 183 * (1 + p + p ^ 2) : ℕ) : ℤ) =
      (5 : ℤ) * 133 * 183 * (1 + (p : ℤ) + (p : ℤ) ^ 2) := by push_cast; rfl
  have hint : (6 : ℤ) * 122 * 170 * (1 + p ^ 2) <
      5 * 133 * 183 * (1 + p + p ^ 2) := by
    have hp17 : (17 : ℤ) ≤ p := by exact_mod_cast h17
    have hp43 : (p : ℤ) ≤ 43 := by exact_mod_cast h43
    have hsq' : (p : ℤ) ^ 2 ≤ 43 * p := by exact_mod_cast hsq
    nlinarith
  exact Nat.cast_lt.mp (by rw [hL, hR]; exact hint)

lemma eleven_thirteen_sq_p_pow_ge_two_overshoot_six_five {p a b k : ℕ}
    (hp : p.Prime) (h17 : 17 ≤ p) (h43 : p ≤ 43)
    (ha : 2 ≤ a) (hb : 2 ≤ b) (hk : 2 ≤ k) :
    6 * usigma (11 ^ a) * usigma (13 ^ b) * usigma (p ^ k) <
      5 * σ 1 (11 ^ a) * σ 1 (13 ^ b) * σ 1 (p ^ k) :=
  six_five_overshoot_mono_three (by decide : Nat.Prime 11)
    (by decide : Nat.Prime 13) hp
    (by decide : 0 < 2) (by decide : 0 < 2) (by decide : 0 < 2)
    ha hb hk
    (eleven_thirteen_sq_p_sq_overshoot_six_five hp h17 h43)

/-- `ρ(121) ρ(169) cap(p) < 6/5` for every `p ≥ 47`. -/
lemma five_mul_eleven_sq_thirteen_sq_cap {p : ℕ} (hp : 47 ≤ p) (hp1 : 1 ≤ p) :
    5 * p * 133 * 183 ≤ 6 * (p - 1) * 122 * 170 := by
  have hp' : (47 : ℤ) ≤ p := Int.ofNat_le.mpr hp
  have hL : ((5 * p * 133 * 183 : ℕ) : ℤ) =
      (5 : ℤ) * p * 133 * 183 := by
    rw [Nat.cast_mul, Nat.cast_mul, Nat.cast_mul]; rfl
  have hR : ((6 * (p - 1) * 122 * 170 : ℕ) : ℤ) =
      (6 : ℤ) * ((p : ℤ) - 1) * 122 * 170 := by
    rw [Nat.cast_mul, Nat.cast_mul, Nat.cast_mul, Nat.cast_sub hp1]
    rfl
  have : (5 : ℤ) * p * 133 * 183 ≤ 6 * (p - 1) * 122 * 170 := by nlinarith
  exact Nat.cast_le.mp (by rw [hL, hR]; exact this)

lemma five_sigma_lt_six_usigma_eleven_thirteen_sq_large {p k : ℕ}
    (hp : p.Prime) (hp47 : 47 ≤ p) (hk : 0 < k) :
    5 * σ 1 (11 ^ 2) * σ 1 (13 ^ 2) * σ 1 (p ^ k) <
      6 * usigma (11 ^ 2) * usigma (13 ^ 2) * usigma (p ^ k) := by
  rw [sigma_eleven_pow_two, usigma_eleven_pow_two,
    sigma_thirteen_pow_two, usigma_thirteen_pow_two]
  have hcp := sigma_lt_cap_usigma hp hk
  have hcap := five_mul_eleven_sq_thirteen_sq_cap hp47 hp.one_le
  have hthis := six_five_of_cap_times_const (A := p - 1) (B := p)
    (X := σ 1 (p ^ k)) (Y := usigma (p ^ k)) (S := 122 * 170) (T := 133 * 183)
    hcp (by
      have hL : 5 * p * (133 * 183) = 5 * p * 133 * 183 := by ring
      have hR : 6 * (p - 1) * (122 * 170) = 6 * (p - 1) * 122 * 170 := by ring
      rw [hL, hR]
      exact hcap) (by decide : 0 < 133 * 183)
  have hL : 5 * σ 1 (p ^ k) * (133 * 183) =
      5 * 133 * 183 * σ 1 (p ^ k) := by ring
  have hR : 6 * usigma (p ^ k) * (122 * 170) =
      6 * 122 * 170 * usigma (p ^ k) := by ring
  rw [← hL, ← hR]
  exact hthis

lemma prime_ge_forty_four_ge_forty_seven {p : ℕ} (hp : p.Prime)
    (h : 44 ≤ p) : 47 ≤ p := by
  have hmem : p = 44 ∨ p = 45 ∨ p = 46 ∨ 47 ≤ p := by omega
  rcases hmem with rfl | rfl | rfl | h47
  · exact False.elim ((by decide : ¬ Nat.Prime 44) hp)
  · exact False.elim ((by decide : ¬ Nat.Prime 45) hp)
  · exact False.elim ((by decide : ¬ Nat.Prime 46) hp)
  · exact h47

/-- `{11^2, 13^2, p^k}` cannot fill leftover `6/5` for primes `p ≥ 17` and
`k ≥ 2`. If also `p ≤ 43`, every exponent triple `a,b,k ≥ 2` overshoots. -/
lemma not_five_sigma_eq_six_usigma_eleven_thirteen_sq {p k : ℕ}
    (hp : p.Prime) (hp17 : 17 ≤ p) (hk : 2 ≤ k) :
    ¬ 5 * σ 1 (11 ^ 2) * σ 1 (13 ^ 2) * σ 1 (p ^ k) =
        6 * usigma (11 ^ 2) * usigma (13 ^ 2) * usigma (p ^ k) := by
  intro heq
  rcases le_or_gt p 43 with h43 | h44
  · exact (eleven_thirteen_sq_p_pow_ge_two_overshoot_six_five hp hp17 h43
      (by decide : 2 ≤ 2) (by decide : 2 ≤ 2) hk).ne' heq
  · have hp47 : 47 ≤ p := prime_ge_forty_four_ge_forty_seven hp (by omega)
    exact (five_sigma_lt_six_usigma_eleven_thirteen_sq_large hp hp47
      (by omega)).ne heq

lemma not_five_sigma_eq_six_usigma_eleven_thirteen_small {p a b k : ℕ}
    (hp : p.Prime) (hp17 : 17 ≤ p) (h43 : p ≤ 43)
    (ha : 2 ≤ a) (hb : 2 ≤ b) (hk : 2 ≤ k) :
    ¬ 5 * σ 1 (11 ^ a) * σ 1 (13 ^ b) * σ 1 (p ^ k) =
        6 * usigma (11 ^ a) * usigma (13 ^ b) * usigma (p ^ k) :=
  (eleven_thirteen_sq_p_pow_ge_two_overshoot_six_five hp hp17 h43 ha hb hk).ne'

/-- If the rest after three distinct prime powers is squarefree, leftover
`10/7` is concentrated on those three prime powers. -/
lemma seven_sigma_eq_ten_of_three_squareful {m p q r : ℕ} (hm : m ≠ 0)
    (hp : p.Prime) (hq : q.Prime) (hr : r.Prime)
    (_hpq : p ≠ q) (_hpr : p ≠ r) (_hqr : q ≠ r)
    (h : 7 * σ 1 m = 10 * usigma m)
    (hs : Squarefree (ordCompl[r] (ordCompl[q] (ordCompl[p] m)))) :
    7 * σ 1 (ordProj[p] m) * σ 1 (ordProj[q] (ordCompl[p] m)) *
        σ 1 (ordProj[r] (ordCompl[q] (ordCompl[p] m))) =
      10 * usigma (ordProj[p] m) * usigma (ordProj[q] (ordCompl[p] m)) *
        usigma (ordProj[r] (ordCompl[q] (ordCompl[p] m))) := by
  set t := ordCompl[r] (ordCompl[q] (ordCompl[p] m))
  have hm' : ordCompl[p] m ≠ 0 := (Nat.ordCompl_pos p hm).ne'
  have hm'' : ordCompl[q] (ordCompl[p] m) ≠ 0 :=
    (Nat.ordCompl_pos q hm').ne'
  have hdecomp_p : ordProj[p] m * ordCompl[p] m = m :=
    Nat.ordProj_mul_ordCompl_eq_self m p
  have hdecomp_q : ordProj[q] (ordCompl[p] m) * ordCompl[q] (ordCompl[p] m) =
      ordCompl[p] m :=
    Nat.ordProj_mul_ordCompl_eq_self (ordCompl[p] m) q
  have hdecomp_r : ordProj[r] (ordCompl[q] (ordCompl[p] m)) * t =
      ordCompl[q] (ordCompl[p] m) :=
    Nat.ordProj_mul_ordCompl_eq_self (ordCompl[q] (ordCompl[p] m)) r
  have hc_p : Coprime (ordProj[p] m) (ordCompl[p] m) :=
    (Nat.coprime_ordCompl hp hm).pow_left (m.factorization p)
  have hc_q : Coprime (ordProj[q] (ordCompl[p] m))
      (ordCompl[q] (ordCompl[p] m)) :=
    (Nat.coprime_ordCompl hq hm').pow_left ((ordCompl[p] m).factorization q)
  have hc_r : Coprime (ordProj[r] (ordCompl[q] (ordCompl[p] m))) t :=
    (Nat.coprime_ordCompl hr hm'').pow_left
      ((ordCompl[q] (ordCompl[p] m)).factorization r)
  have hmul : 7 * σ 1 (ordProj[p] m) * σ 1 (ordProj[q] (ordCompl[p] m)) *
        σ 1 (ordProj[r] (ordCompl[q] (ordCompl[p] m))) * σ 1 t =
      10 * usigma (ordProj[p] m) * usigma (ordProj[q] (ordCompl[p] m)) *
        usigma (ordProj[r] (ordCompl[q] (ordCompl[p] m))) * usigma t := by
    have := h
    rw [← hdecomp_p, sigma_mul_of_coprime hc_p, usigma_mul hc_p] at this
    rw [← hdecomp_q, sigma_mul_of_coprime hc_q, usigma_mul hc_q] at this
    rw [← hdecomp_r, sigma_mul_of_coprime hc_r, usigma_mul hc_r] at this
    simpa [mul_assoc, mul_left_comm, mul_comm] using this
  have hσu := (sigma_eq_usigma_iff_squarefree (Nat.ordCompl_pos r hm'')).mpr hs
  rw [hσu] at hmul
  have hpos : 0 < usigma t := by
    rw [← hσu]
    exact sigma_pos_iff.mpr (Nat.ordCompl_pos r hm'')
  exact Nat.eq_of_mul_eq_mul_right hpos hmul

set_option maxHeartbeats 800000 in
/-- If the rest after four distinct prime powers is squarefree, leftover
`10/7` is concentrated on those four prime powers. -/
lemma seven_sigma_eq_ten_of_four_squareful {m p q r s : ℕ} (hm : m ≠ 0)
    (hp : p.Prime) (hq : q.Prime) (hr : r.Prime) (hs : s.Prime)
    (_hpq : p ≠ q) (_hpr : p ≠ r) (_hps : p ≠ s)
    (_hqr : q ≠ r) (_hqs : q ≠ s) (_hrs : r ≠ s)
    (h : 7 * σ 1 m = 10 * usigma m)
    (hsf : Squarefree
      (ordCompl[s] (ordCompl[r] (ordCompl[q] (ordCompl[p] m))))) :
    7 * σ 1 (ordProj[p] m) * σ 1 (ordProj[q] (ordCompl[p] m)) *
        σ 1 (ordProj[r] (ordCompl[q] (ordCompl[p] m))) *
        σ 1 (ordProj[s] (ordCompl[r] (ordCompl[q] (ordCompl[p] m)))) =
      10 * usigma (ordProj[p] m) * usigma (ordProj[q] (ordCompl[p] m)) *
        usigma (ordProj[r] (ordCompl[q] (ordCompl[p] m))) *
        usigma (ordProj[s] (ordCompl[r] (ordCompl[q] (ordCompl[p] m)))) := by
  set t := ordCompl[s] (ordCompl[r] (ordCompl[q] (ordCompl[p] m)))
  have hm' : ordCompl[p] m ≠ 0 := (Nat.ordCompl_pos p hm).ne'
  have hm'' : ordCompl[q] (ordCompl[p] m) ≠ 0 :=
    (Nat.ordCompl_pos q hm').ne'
  have hm''' : ordCompl[r] (ordCompl[q] (ordCompl[p] m)) ≠ 0 :=
    (Nat.ordCompl_pos r hm'').ne'
  have hdecomp_p : ordProj[p] m * ordCompl[p] m = m :=
    Nat.ordProj_mul_ordCompl_eq_self m p
  have hdecomp_q : ordProj[q] (ordCompl[p] m) * ordCompl[q] (ordCompl[p] m) =
      ordCompl[p] m :=
    Nat.ordProj_mul_ordCompl_eq_self (ordCompl[p] m) q
  have hdecomp_r : ordProj[r] (ordCompl[q] (ordCompl[p] m)) *
      ordCompl[r] (ordCompl[q] (ordCompl[p] m)) =
      ordCompl[q] (ordCompl[p] m) :=
    Nat.ordProj_mul_ordCompl_eq_self (ordCompl[q] (ordCompl[p] m)) r
  have hdecomp_s : ordProj[s] (ordCompl[r] (ordCompl[q] (ordCompl[p] m))) * t =
      ordCompl[r] (ordCompl[q] (ordCompl[p] m)) :=
    Nat.ordProj_mul_ordCompl_eq_self (ordCompl[r] (ordCompl[q] (ordCompl[p] m))) s
  have hc_p : Coprime (ordProj[p] m) (ordCompl[p] m) :=
    (Nat.coprime_ordCompl hp hm).pow_left (m.factorization p)
  have hc_q : Coprime (ordProj[q] (ordCompl[p] m))
      (ordCompl[q] (ordCompl[p] m)) :=
    (Nat.coprime_ordCompl hq hm').pow_left ((ordCompl[p] m).factorization q)
  have hc_r : Coprime (ordProj[r] (ordCompl[q] (ordCompl[p] m)))
      (ordCompl[r] (ordCompl[q] (ordCompl[p] m))) :=
    (Nat.coprime_ordCompl hr hm'').pow_left
      ((ordCompl[q] (ordCompl[p] m)).factorization r)
  have hc_s : Coprime (ordProj[s] (ordCompl[r] (ordCompl[q] (ordCompl[p] m))))
      t :=
    (Nat.coprime_ordCompl hs hm''').pow_left
      ((ordCompl[r] (ordCompl[q] (ordCompl[p] m))).factorization s)
  have hmul : 7 * σ 1 (ordProj[p] m) * σ 1 (ordProj[q] (ordCompl[p] m)) *
        σ 1 (ordProj[r] (ordCompl[q] (ordCompl[p] m))) *
        σ 1 (ordProj[s] (ordCompl[r] (ordCompl[q] (ordCompl[p] m)))) * σ 1 t =
      10 * usigma (ordProj[p] m) * usigma (ordProj[q] (ordCompl[p] m)) *
        usigma (ordProj[r] (ordCompl[q] (ordCompl[p] m))) *
        usigma (ordProj[s] (ordCompl[r] (ordCompl[q] (ordCompl[p] m)))) *
        usigma t := by
    have := h
    rw [← hdecomp_p, sigma_mul_of_coprime hc_p, usigma_mul hc_p] at this
    rw [← hdecomp_q, sigma_mul_of_coprime hc_q, usigma_mul hc_q] at this
    rw [← hdecomp_r, sigma_mul_of_coprime hc_r, usigma_mul hc_r] at this
    rw [← hdecomp_s, sigma_mul_of_coprime hc_s, usigma_mul hc_s] at this
    convert this using 1 <;> ring
  have hσu := (sigma_eq_usigma_iff_squarefree (Nat.ordCompl_pos s hm''')).mpr hsf
  rw [hσu] at hmul
  have hpos : 0 < usigma t := by
    rw [← hσu]
    exact sigma_pos_iff.mpr (Nat.ordCompl_pos s hm''')
  exact Nat.eq_of_mul_eq_mul_right hpos hmul

/-- Leftover `10/7` cannot be three squareful primes `7 ≤ p < q < r` times a
squarefree coprime factor. -/
lemma not_seven_sigma_of_three_sq_primes_ge_seven {m p q r : ℕ} (hm : m ≠ 0)
    (hp : p.Prime) (hq : q.Prime) (hr : r.Prime)
    (hpq : p < q) (hqr : q < r) (hp7 : 7 ≤ p)
    (h : 7 * σ 1 m = 10 * usigma m)
    (hkp : 2 ≤ padicValNat p m) (hkq : 2 ≤ padicValNat q m)
    (hkr : 2 ≤ padicValNat r m)
    (hs : Squarefree (ordCompl[r] (ordCompl[q] (ordCompl[p] m)))) : False := by
  have hpq_ne : p ≠ q := Nat.ne_of_lt hpq
  have hpr_ne : p ≠ r := Nat.ne_of_lt (lt_trans hpq hqr)
  have hqr_ne : q ≠ r := Nat.ne_of_lt hqr
  have heq := seven_sigma_eq_ten_of_three_squareful hm hp hq hr hpq_ne hpr_ne
    hqr_ne h hs
  have hproj_p : ordProj[p] m = p ^ padicValNat p m := by
    simp [Nat.factorization_def m hp]
  have hproj_q : ordProj[q] (ordCompl[p] m) =
      q ^ padicValNat q (ordCompl[p] m) := by
    simp [Nat.factorization_def (ordCompl[p] m) hq]
  have hproj_r : ordProj[r] (ordCompl[q] (ordCompl[p] m)) =
      r ^ padicValNat r (ordCompl[q] (ordCompl[p] m)) := by
    simp [Nat.factorization_def (ordCompl[q] (ordCompl[p] m)) hr]
  rw [hproj_r, padicValNat_ordCompl_of_ne hr hqr_ne,
    padicValNat_ordCompl_of_ne hr hpr_ne, hproj_q,
    padicValNat_ordCompl_of_ne hq hpq_ne, hproj_p] at heq
  have hq11 : 11 ≤ q := by
    have : 8 ≤ q := by omega
    have hmem : q = 8 ∨ q = 9 ∨ q = 10 ∨ 11 ≤ q := by omega
    rcases hmem with rfl | rfl | rfl | h11
    · cases (by decide : ¬ Nat.Prime 8) hq
    · cases (by decide : ¬ Nat.Prime 9) hq
    · cases (by decide : ¬ Nat.Prime 10) hq
    · exact h11
  have hr13 : 13 ≤ r := by
    have : 12 ≤ r := by omega
    have hmem : r = 12 ∨ 13 ≤ r := by omega
    rcases hmem with rfl | h13
    · cases (by decide : ¬ Nat.Prime 12) hr
    · exact h13
  exact (seven_sigma_lt_ten_usigma_three_large hp hq hr hp7 hq11 hr13
    (by omega) (by omega) (by omega)).ne heq

/-- Leftover `10/7` cannot be three squareful primes `5 < 7 < r` with `r ≥ 11`
times a squarefree coprime factor. -/
lemma not_seven_sigma_of_three_sq_primes_five_seven {m r : ℕ} (hm : m ≠ 0)
    (hr : r.Prime) (hr11 : 11 ≤ r)
    (h : 7 * σ 1 m = 10 * usigma m)
    (hk5 : 2 ≤ padicValNat 5 m) (hk7 : 2 ≤ padicValNat 7 m)
    (hkr : 2 ≤ padicValNat r m)
    (hs : Squarefree (ordCompl[r] (ordCompl[7] (ordCompl[5] m)))) : False := by
  have hp5 : Nat.Prime 5 := Nat.prime_five
  have hp7 : Nat.Prime 7 := by decide
  have hpq_ne : (5 : ℕ) ≠ 7 := by decide
  have hpr_ne : (5 : ℕ) ≠ r := Nat.ne_of_lt (lt_of_lt_of_le (by decide : 5 < 11) hr11)
  have hqr_ne : (7 : ℕ) ≠ r := Nat.ne_of_lt (lt_of_lt_of_le (by decide : 7 < 11) hr11)
  have heq := seven_sigma_eq_ten_of_three_squareful hm hp5 hp7 hr hpq_ne hpr_ne
    hqr_ne h hs
  have hproj_p : ordProj[5] m = 5 ^ padicValNat 5 m := by
    simp [Nat.factorization_def m hp5]
  have hproj_q : ordProj[7] (ordCompl[5] m) =
      7 ^ padicValNat 7 (ordCompl[5] m) := by
    simp [Nat.factorization_def (ordCompl[5] m) hp7]
  have hproj_r : ordProj[r] (ordCompl[7] (ordCompl[5] m)) =
      r ^ padicValNat r (ordCompl[7] (ordCompl[5] m)) := by
    simp [Nat.factorization_def (ordCompl[7] (ordCompl[5] m)) hr]
  rw [hproj_r, padicValNat_ordCompl_of_ne hr hqr_ne,
    padicValNat_ordCompl_of_ne hr hpr_ne, hproj_q,
    padicValNat_ordCompl_of_ne hp7 hpq_ne, hproj_p] at heq
  exact not_seven_sigma_eq_ten_usigma_five_seven_prime hr hr11 hk5 hk7 hkr heq

lemma prime_ge_twenty_four_ge_twenty_nine {p : ℕ} (hp : p.Prime)
    (h : 24 ≤ p) : 29 ≤ p := by
  have hmem : p = 24 ∨ p = 25 ∨ p = 26 ∨ p = 27 ∨ p = 28 ∨ 29 ≤ p := by omega
  rcases hmem with rfl | rfl | rfl | rfl | rfl | h29
  · exact False.elim ((by decide : ¬ Nat.Prime 24) hp)
  · exact False.elim ((by decide : ¬ Nat.Prime 25) hp)
  · exact False.elim ((by decide : ¬ Nat.Prime 26) hp)
  · exact False.elim ((by decide : ¬ Nat.Prime 27) hp)
  · exact False.elim ((by decide : ¬ Nat.Prime 28) hp)
  · exact h29

/-- Leftover `10/7` cannot be three squareful primes `5 < 11 < r` times a
squarefree coprime factor. -/
lemma not_seven_sigma_of_three_sq_primes_five_eleven {m r : ℕ} (hm : m ≠ 0)
    (hr : r.Prime) (hr13 : 13 ≤ r)
    (h : 7 * σ 1 m = 10 * usigma m)
    (hk5 : 2 ≤ padicValNat 5 m) (hk11 : 2 ≤ padicValNat 11 m)
    (hkr : 2 ≤ padicValNat r m)
    (hs : Squarefree (ordCompl[r] (ordCompl[11] (ordCompl[5] m)))) : False := by
  have hp5 : Nat.Prime 5 := Nat.prime_five
  have hp11 : Nat.Prime 11 := by decide
  have hpq_ne : (5 : ℕ) ≠ 11 := by decide
  have hpr_ne : (5 : ℕ) ≠ r := Nat.ne_of_lt (lt_of_lt_of_le (by decide : 5 < 13) hr13)
  have hqr_ne : (11 : ℕ) ≠ r := Nat.ne_of_lt (lt_of_lt_of_le (by decide : 11 < 13) hr13)
  have heq := seven_sigma_eq_ten_of_three_squareful hm hp5 hp11 hr hpq_ne hpr_ne
    hqr_ne h hs
  have hproj_p : ordProj[5] m = 5 ^ padicValNat 5 m := by
    simp [Nat.factorization_def m hp5]
  have hproj_q : ordProj[11] (ordCompl[5] m) =
      11 ^ padicValNat 11 (ordCompl[5] m) := by
    simp [Nat.factorization_def (ordCompl[5] m) hp11]
  have hproj_r : ordProj[r] (ordCompl[11] (ordCompl[5] m)) =
      r ^ padicValNat r (ordCompl[11] (ordCompl[5] m)) := by
    simp [Nat.factorization_def (ordCompl[11] (ordCompl[5] m)) hr]
  rw [hproj_r, padicValNat_ordCompl_of_ne hr hqr_ne,
    padicValNat_ordCompl_of_ne hr hpr_ne, hproj_q,
    padicValNat_ordCompl_of_ne hp11 hpq_ne, hproj_p] at heq
  rcases le_or_gt r 19 with h19 | h20
  · rcases prime_ge_eleven_le_nineteen hr (by omega) h19 with rfl | rfl | rfl | rfl
    · exact (by omega : False)
    · exact not_seven_sigma_eq_ten_usigma_five_eleven_thirteen hk5 hk11 hkr heq
    · exact not_seven_sigma_eq_ten_usigma_five_eleven_seventeen hk5 hk11 hkr heq
    · exact not_seven_sigma_eq_ten_usigma_five_eleven_nineteen hk5 hk11 hkr heq
  · have hr23 : 23 ≤ r := prime_ge_twenty_ge_twenty_three hr (by omega)
    rcases le_or_gt r 23 with h23 | h24
    · have hr23eq : r = 23 := le_antisymm h23 hr23
      rw [hr23eq] at heq hkr
      exact not_seven_sigma_eq_ten_usigma_five_eleven_twenty_three hk5 hk11 hkr heq
    · have hp29 : 29 ≤ r := prime_ge_twenty_four_ge_twenty_nine hr (by omega)
      exact (seven_sigma_lt_ten_usigma_five_eleven_large hr hp29
        (by omega) (by omega) (by omega)).ne heq

lemma prime_ge_fourteen_ge_seventeen {p : ℕ} (hp : p.Prime)
    (h : 14 ≤ p) : 17 ≤ p := by
  have hmem : p = 14 ∨ p = 15 ∨ p = 16 ∨ 17 ≤ p := by omega
  rcases hmem with rfl | rfl | rfl | h17
  · exact False.elim ((by decide : ¬ Nat.Prime 14) hp)
  · exact False.elim ((by decide : ¬ Nat.Prime 15) hp)
  · exact False.elim ((by decide : ¬ Nat.Prime 16) hp)
  · exact h17

/-- Leftover `10/7` cannot be three squareful primes `5 < 13 < r` times a
squarefree coprime factor. -/
lemma not_seven_sigma_of_three_sq_primes_five_thirteen {m r : ℕ} (hm : m ≠ 0)
    (hr : r.Prime) (hr17 : 17 ≤ r)
    (h : 7 * σ 1 m = 10 * usigma m)
    (hk5 : 2 ≤ padicValNat 5 m) (hk13 : 2 ≤ padicValNat 13 m)
    (hkr : 2 ≤ padicValNat r m)
    (hs : Squarefree (ordCompl[r] (ordCompl[13] (ordCompl[5] m)))) : False := by
  have hp5 : Nat.Prime 5 := Nat.prime_five
  have hp13 : Nat.Prime 13 := by decide
  have hpq_ne : (5 : ℕ) ≠ 13 := by decide
  have hpr_ne : (5 : ℕ) ≠ r := Nat.ne_of_lt (lt_of_lt_of_le (by decide : 5 < 17) hr17)
  have hqr_ne : (13 : ℕ) ≠ r := Nat.ne_of_lt (lt_of_lt_of_le (by decide : 13 < 17) hr17)
  have heq := seven_sigma_eq_ten_of_three_squareful hm hp5 hp13 hr hpq_ne hpr_ne
    hqr_ne h hs
  have hproj_p : ordProj[5] m = 5 ^ padicValNat 5 m := by
    simp [Nat.factorization_def m hp5]
  have hproj_q : ordProj[13] (ordCompl[5] m) =
      13 ^ padicValNat 13 (ordCompl[5] m) := by
    simp [Nat.factorization_def (ordCompl[5] m) hp13]
  have hproj_r : ordProj[r] (ordCompl[13] (ordCompl[5] m)) =
      r ^ padicValNat r (ordCompl[13] (ordCompl[5] m)) := by
    simp [Nat.factorization_def (ordCompl[13] (ordCompl[5] m)) hr]
  rw [hproj_r, padicValNat_ordCompl_of_ne hr hqr_ne,
    padicValNat_ordCompl_of_ne hr hpr_ne, hproj_q,
    padicValNat_ordCompl_of_ne hp13 hpq_ne, hproj_p] at heq
  rcases le_or_gt r 19 with h19 | h20
  · rcases prime_ge_eleven_le_nineteen hr (by omega) h19 with rfl | rfl | rfl | rfl
    · exact (by omega : False)
    · exact (by omega : False)
    · exact not_seven_sigma_eq_ten_usigma_five_thirteen_seventeen hk5 hk13 hkr heq
    · exact not_seven_sigma_eq_ten_usigma_five_thirteen_nineteen hk5 hk13 hkr heq
  · have hr23 : 23 ≤ r := prime_ge_twenty_ge_twenty_three hr (by omega)
    exact (seven_sigma_lt_ten_usigma_five_thirteen_large hr hr23
      (by omega) (by omega) (by omega)).ne heq

/-- Leftover `10/7` cannot be three squareful primes `5 < 17 < r` times a
squarefree coprime factor. -/
lemma not_seven_sigma_of_three_sq_primes_five_seventeen {m r : ℕ} (hm : m ≠ 0)
    (hr : r.Prime) (hr19 : 19 ≤ r)
    (h : 7 * σ 1 m = 10 * usigma m)
    (hk5 : 2 ≤ padicValNat 5 m) (hk17 : 2 ≤ padicValNat 17 m)
    (hkr : 2 ≤ padicValNat r m)
    (hs : Squarefree (ordCompl[r] (ordCompl[17] (ordCompl[5] m)))) : False := by
  have hp5 : Nat.Prime 5 := Nat.prime_five
  have hp17 : Nat.Prime 17 := by decide
  have hpq_ne : (5 : ℕ) ≠ 17 := by decide
  have hpr_ne : (5 : ℕ) ≠ r := Nat.ne_of_lt (lt_of_lt_of_le (by decide : 5 < 19) hr19)
  have hqr_ne : (17 : ℕ) ≠ r := Nat.ne_of_lt (lt_of_lt_of_le (by decide : 17 < 19) hr19)
  have heq := seven_sigma_eq_ten_of_three_squareful hm hp5 hp17 hr hpq_ne hpr_ne
    hqr_ne h hs
  have hproj_p : ordProj[5] m = 5 ^ padicValNat 5 m := by
    simp [Nat.factorization_def m hp5]
  have hproj_q : ordProj[17] (ordCompl[5] m) =
      17 ^ padicValNat 17 (ordCompl[5] m) := by
    simp [Nat.factorization_def (ordCompl[5] m) hp17]
  have hproj_r : ordProj[r] (ordCompl[17] (ordCompl[5] m)) =
      r ^ padicValNat r (ordCompl[17] (ordCompl[5] m)) := by
    simp [Nat.factorization_def (ordCompl[17] (ordCompl[5] m)) hr]
  rw [hproj_r, padicValNat_ordCompl_of_ne hr hqr_ne,
    padicValNat_ordCompl_of_ne hr hpr_ne, hproj_q,
    padicValNat_ordCompl_of_ne hp17 hpq_ne, hproj_p] at heq
  exact (seven_sigma_lt_ten_usigma_five_seventeen_large hr hr19
    (by omega) (by omega) (by omega)).ne heq

/-- Leftover `10/7` cannot be three squareful primes `5 < q < r` with
`19 ≤ q` times a squarefree coprime factor. -/
lemma not_seven_sigma_of_three_sq_primes_five_large {m q r : ℕ} (hm : m ≠ 0)
    (hq : q.Prime) (hr : r.Prime) (hq19 : 19 ≤ q) (hqr : q < r)
    (h : 7 * σ 1 m = 10 * usigma m)
    (hk5 : 2 ≤ padicValNat 5 m) (hkq : 2 ≤ padicValNat q m)
    (hkr : 2 ≤ padicValNat r m)
    (hs : Squarefree (ordCompl[r] (ordCompl[q] (ordCompl[5] m)))) : False := by
  have hp5 : Nat.Prime 5 := Nat.prime_five
  have hpq_ne : (5 : ℕ) ≠ q :=
    Nat.ne_of_lt (lt_of_lt_of_le (by decide : 5 < 19) hq19)
  have hpr_ne : (5 : ℕ) ≠ r :=
    Nat.ne_of_lt (lt_of_lt_of_le (lt_of_lt_of_le (by decide : 5 < 19) hq19)
      (Nat.le_of_lt hqr))
  have hqr_ne : q ≠ r := Nat.ne_of_lt hqr
  have heq := seven_sigma_eq_ten_of_three_squareful hm hp5 hq hr hpq_ne hpr_ne
    hqr_ne h hs
  have hproj_p : ordProj[5] m = 5 ^ padicValNat 5 m := by
    simp [Nat.factorization_def m hp5]
  have hproj_q : ordProj[q] (ordCompl[5] m) =
      q ^ padicValNat q (ordCompl[5] m) := by
    simp [Nat.factorization_def (ordCompl[5] m) hq]
  have hproj_r : ordProj[r] (ordCompl[q] (ordCompl[5] m)) =
      r ^ padicValNat r (ordCompl[q] (ordCompl[5] m)) := by
    simp [Nat.factorization_def (ordCompl[q] (ordCompl[5] m)) hr]
  rw [hproj_r, padicValNat_ordCompl_of_ne hr hqr_ne,
    padicValNat_ordCompl_of_ne hr hpr_ne, hproj_q,
    padicValNat_ordCompl_of_ne hq hpq_ne, hproj_p] at heq
  exact (seven_sigma_lt_ten_usigma_five_two_large hq hr hq19 hqr
    (by omega) (by omega) (by omega)).ne heq

/-- Leftover `10/7` cannot be three squareful primes `5 < q < r` with
`11 ≤ q` times a squarefree coprime factor. -/
lemma not_seven_sigma_of_three_sq_primes_five {m q r : ℕ} (hm : m ≠ 0)
    (hq : q.Prime) (hr : r.Prime) (hq11 : 11 ≤ q) (hqr : q < r)
    (h : 7 * σ 1 m = 10 * usigma m)
    (hk5 : 2 ≤ padicValNat 5 m) (hkq : 2 ≤ padicValNat q m)
    (hkr : 2 ≤ padicValNat r m)
    (hs : Squarefree (ordCompl[r] (ordCompl[q] (ordCompl[5] m)))) : False := by
  rcases le_or_gt q 19 with h19 | h20
  · rcases prime_ge_eleven_le_nineteen hq hq11 h19 with rfl | rfl | rfl | rfl
    · have hr13 : 13 ≤ r := by
        have : 12 ≤ r := by omega
        rcases eq_or_lt_of_le this with rfl | h13
        · exact False.elim ((by decide : ¬ Nat.Prime 12) hr)
        · exact Nat.succ_le_of_lt h13
      exact not_seven_sigma_of_three_sq_primes_five_eleven hm hr hr13 h hk5 hkq
        hkr hs
    · have hr17 : 17 ≤ r := prime_ge_fourteen_ge_seventeen hr (by omega)
      exact not_seven_sigma_of_three_sq_primes_five_thirteen hm hr hr17 h hk5 hkq
        hkr hs
    · have hr19 : 19 ≤ r := by
        have : 18 ≤ r := by omega
        rcases eq_or_lt_of_le this with rfl | h19'
        · exact False.elim ((by decide : ¬ Nat.Prime 18) hr)
        · exact Nat.succ_le_of_lt h19'
      exact not_seven_sigma_of_three_sq_primes_five_seventeen hm hr hr19 h hk5 hkq
        hkr hs
    · exact not_seven_sigma_of_three_sq_primes_five_large hm hq hr (by omega)
        hqr h hk5 hkq hkr hs
  · have hq19 : 19 ≤ q := Nat.le_of_lt h20
    exact not_seven_sigma_of_three_sq_primes_five_large hm hq hr hq19 hqr h hk5
      hkq hkr hs

/-- Leftover `6/5` cannot be three squareful primes `11,13,p` with
`17 ≤ p ≤ 43` times a squarefree coprime factor. -/
lemma not_five_sigma_of_three_sq_primes_eleven_thirteen_small {m p : ℕ}
    (hm : m ≠ 0) (hp : p.Prime) (hp17 : 17 ≤ p) (h43 : p ≤ 43)
    (h : 5 * σ 1 m = 6 * usigma m)
    (hk11 : 2 ≤ padicValNat 11 m) (hk13 : 2 ≤ padicValNat 13 m)
    (hkp : 2 ≤ padicValNat p m)
    (hs : Squarefree (ordCompl[p] (ordCompl[13] (ordCompl[11] m)))) : False := by
  have hp11 : Nat.Prime 11 := by decide
  have hp13 : Nat.Prime 13 := by decide
  have hpq_ne : (11 : ℕ) ≠ 13 := by decide
  have hpr_ne : (11 : ℕ) ≠ p :=
    Nat.ne_of_lt (lt_of_lt_of_le (by decide : 11 < 17) hp17)
  have hqr_ne : (13 : ℕ) ≠ p :=
    Nat.ne_of_lt (lt_of_lt_of_le (by decide : 13 < 17) hp17)
  have heq := five_sigma_eq_six_of_three_squareful hm hp11 hp13 hp hpq_ne hpr_ne
    hqr_ne h hs
  have hproj_p : ordProj[11] m = 11 ^ padicValNat 11 m := by
    simp [Nat.factorization_def m hp11]
  have hproj_q : ordProj[13] (ordCompl[11] m) =
      13 ^ padicValNat 13 (ordCompl[11] m) := by
    simp [Nat.factorization_def (ordCompl[11] m) hp13]
  have hproj_r : ordProj[p] (ordCompl[13] (ordCompl[11] m)) =
      p ^ padicValNat p (ordCompl[13] (ordCompl[11] m)) := by
    simp [Nat.factorization_def (ordCompl[13] (ordCompl[11] m)) hp]
  rw [hproj_r, padicValNat_ordCompl_of_ne hp hqr_ne,
    padicValNat_ordCompl_of_ne hp hpr_ne, hproj_q,
    padicValNat_ordCompl_of_ne hp13 hpq_ne, hproj_p] at heq
  exact not_five_sigma_eq_six_usigma_eleven_thirteen_small hp hp17 h43 hk11 hk13
    hkp heq

/-- `ρ(121) ρ(289) ρ(p^2) > 6/5` for `19 ≤ p ≤ 23`. -/
lemma eleven_seventeen_sq_p_sq_overshoot_six_five {p : ℕ} (hp : p.Prime)
    (h19 : 19 ≤ p) (h23 : p ≤ 23) :
    6 * usigma (11 ^ 2) * usigma (17 ^ 2) * usigma (p ^ 2) <
      5 * σ 1 (11 ^ 2) * σ 1 (17 ^ 2) * σ 1 (p ^ 2) := by
  rw [usigma_eleven_pow_two, sigma_eleven_pow_two,
    usigma_seventeen_pow_two, sigma_seventeen_pow_two,
    usigma_prime_pow hp (by decide : 0 < 2), sigma_prime_pow_two hp]
  have hsq : p ^ 2 ≤ 23 * p := by
    rw [pow_two]
    exact Nat.mul_le_mul_right p h23
  have hL : ((6 * 122 * 290 * (1 + p ^ 2) : ℕ) : ℤ) =
      (6 : ℤ) * 122 * 290 * (1 + (p : ℤ) ^ 2) := by push_cast; rfl
  have hR : ((5 * 133 * 307 * (1 + p + p ^ 2) : ℕ) : ℤ) =
      (5 : ℤ) * 133 * 307 * (1 + (p : ℤ) + (p : ℤ) ^ 2) := by push_cast; rfl
  have hint : (6 : ℤ) * 122 * 290 * (1 + p ^ 2) <
      5 * 133 * 307 * (1 + p + p ^ 2) := by
    have hp19 : (19 : ℤ) ≤ p := by exact_mod_cast h19
    have hp23 : (p : ℤ) ≤ 23 := by exact_mod_cast h23
    have hsq' : (p : ℤ) ^ 2 ≤ 23 * p := by exact_mod_cast hsq
    nlinarith
  exact Nat.cast_lt.mp (by rw [hL, hR]; exact hint)

lemma eleven_seventeen_sq_p_pow_ge_two_overshoot_six_five {p a b k : ℕ}
    (hp : p.Prime) (h19 : 19 ≤ p) (h23 : p ≤ 23)
    (ha : 2 ≤ a) (hb : 2 ≤ b) (hk : 2 ≤ k) :
    6 * usigma (11 ^ a) * usigma (17 ^ b) * usigma (p ^ k) <
      5 * σ 1 (11 ^ a) * σ 1 (17 ^ b) * σ 1 (p ^ k) :=
  six_five_overshoot_mono_three (by decide : Nat.Prime 11)
    (by decide : Nat.Prime 17) hp
    (by decide : 0 < 2) (by decide : 0 < 2) (by decide : 0 < 2)
    ha hb hk
    (eleven_seventeen_sq_p_sq_overshoot_six_five hp h19 h23)

lemma not_five_sigma_eq_six_usigma_eleven_seventeen_small {p a b k : ℕ}
    (hp : p.Prime) (hp19 : 19 ≤ p) (h23 : p ≤ 23)
    (ha : 2 ≤ a) (hb : 2 ≤ b) (hk : 2 ≤ k) :
    ¬ 5 * σ 1 (11 ^ a) * σ 1 (17 ^ b) * σ 1 (p ^ k) =
        6 * usigma (11 ^ a) * usigma (17 ^ b) * usigma (p ^ k) :=
  (eleven_seventeen_sq_p_pow_ge_two_overshoot_six_five hp hp19 h23 ha hb hk).ne'

lemma five_eleven_seventeen_cap {p : ℕ} (hp : 41 ≤ p) :
    5 * 11 * 17 * p ≤ 6 * 10 * 16 * (p - 1) := by
  have hp1 : 1 ≤ p := by omega
  have hp' : (41 : ℤ) ≤ p := Int.ofNat_le.mpr hp
  have hL : ((5 * 11 * 17 * p : ℕ) : ℤ) = 935 * (p : ℤ) := by push_cast; rfl
  have hR : ((6 * 10 * 16 * (p - 1) : ℕ) : ℤ) = 960 * ((p : ℤ) - 1) := by
    rw [Nat.cast_mul, Nat.cast_mul, Nat.cast_mul, Nat.cast_sub hp1]
    push_cast; rfl
  have : (935 : ℤ) * p ≤ 960 * (p - 1) := by nlinarith
  exact Nat.cast_le.mp (by rw [hL, hR]; exact this)

/-- `{11, 17, p}` with `p ≥ 41` cannot fill leftover `6/5`. -/
lemma five_sigma_lt_six_usigma_eleven_seventeen_large {p a b c : ℕ}
    (hp : p.Prime) (hp41 : 41 ≤ p) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    5 * σ 1 (11 ^ a) * σ 1 (17 ^ b) * σ 1 (p ^ c) <
      6 * usigma (11 ^ a) * usigma (17 ^ b) * usigma (p ^ c) := by
  have h11 := sigma_lt_cap_usigma (by decide : Nat.Prime 11) ha
  have h17 := sigma_lt_cap_usigma (by decide : Nat.Prime 17) hb
  have hpcap := sigma_lt_cap_usigma hp hc
  have hu11 : 0 < usigma (11 ^ a) := by
    rw [usigma_prime_pow (by decide : Nat.Prime 11) ha]
    exact Nat.add_pos_left (by decide : 0 < 1) _
  have hu17 : 0 < usigma (17 ^ b) := by
    rw [usigma_prime_pow (by decide : Nat.Prime 17) hb]
    exact Nat.add_pos_left (by decide : 0 < 1) _
  have hcap := five_eleven_seventeen_cap hp41
  have := six_five_of_three_caps (A := 10) (B := 11) (X := σ 1 (11 ^ a))
    (Y := usigma (11 ^ a)) (C := 16) (D := 17) (P := σ 1 (17 ^ b))
    (Q := usigma (17 ^ b)) (E := p - 1) (F := p) (R := σ 1 (p ^ c))
    (S := usigma (p ^ c)) h11 h17 hpcap hcap (by decide : 0 < 11) hu11
    (by decide : 0 < 17) hu17
  simpa [mul_assoc] using this

lemma prime_ge_thirty_eight_ge_forty_one {p : ℕ} (hp : p.Prime)
    (h : 38 ≤ p) : 41 ≤ p := by
  have hmem : p = 38 ∨ p = 39 ∨ p = 40 ∨ 41 ≤ p := by omega
  rcases hmem with rfl | rfl | rfl | h41
  · exact False.elim ((by decide : ¬ Nat.Prime 38) hp)
  · exact False.elim ((by decide : ¬ Nat.Prime 39) hp)
  · exact False.elim ((by decide : ¬ Nat.Prime 40) hp)
  · exact h41

/-- Leftover `6/5` cannot be three squareful primes `11,17,p` with
`19 ≤ p ≤ 23` times a squarefree coprime factor. -/
lemma not_five_sigma_of_three_sq_primes_eleven_seventeen_small {m p : ℕ}
    (hm : m ≠ 0) (hp : p.Prime) (hp19 : 19 ≤ p) (h23 : p ≤ 23)
    (h : 5 * σ 1 m = 6 * usigma m)
    (hk11 : 2 ≤ padicValNat 11 m) (hk17 : 2 ≤ padicValNat 17 m)
    (hkp : 2 ≤ padicValNat p m)
    (hs : Squarefree (ordCompl[p] (ordCompl[17] (ordCompl[11] m)))) : False := by
  have hp11 : Nat.Prime 11 := by decide
  have hp17 : Nat.Prime 17 := by decide
  have hpq_ne : (11 : ℕ) ≠ 17 := by decide
  have hpr_ne : (11 : ℕ) ≠ p :=
    Nat.ne_of_lt (lt_of_lt_of_le (by decide : 11 < 19) hp19)
  have hqr_ne : (17 : ℕ) ≠ p :=
    Nat.ne_of_lt (lt_of_lt_of_le (by decide : 17 < 19) hp19)
  have heq := five_sigma_eq_six_of_three_squareful hm hp11 hp17 hp hpq_ne hpr_ne
    hqr_ne h hs
  have hproj_p : ordProj[11] m = 11 ^ padicValNat 11 m := by
    simp [Nat.factorization_def m hp11]
  have hproj_q : ordProj[17] (ordCompl[11] m) =
      17 ^ padicValNat 17 (ordCompl[11] m) := by
    simp [Nat.factorization_def (ordCompl[11] m) hp17]
  have hproj_r : ordProj[p] (ordCompl[17] (ordCompl[11] m)) =
      p ^ padicValNat p (ordCompl[17] (ordCompl[11] m)) := by
    simp [Nat.factorization_def (ordCompl[17] (ordCompl[11] m)) hp]
  rw [hproj_r, padicValNat_ordCompl_of_ne hp hqr_ne,
    padicValNat_ordCompl_of_ne hp hpr_ne, hproj_q,
    padicValNat_ordCompl_of_ne hp17 hpq_ne, hproj_p] at heq
  exact not_five_sigma_eq_six_usigma_eleven_seventeen_small hp hp19 h23 hk11 hk17
    hkp heq

/-- Leftover `6/5` cannot be three squareful primes `11,17,p` with
`p ≥ 41` times a squarefree coprime factor. -/
lemma not_five_sigma_of_three_sq_primes_eleven_seventeen_large {m p : ℕ}
    (hm : m ≠ 0) (hp : p.Prime) (hp41 : 41 ≤ p)
    (h : 5 * σ 1 m = 6 * usigma m)
    (hk11 : 2 ≤ padicValNat 11 m) (hk17 : 2 ≤ padicValNat 17 m)
    (hkp : 2 ≤ padicValNat p m)
    (hs : Squarefree (ordCompl[p] (ordCompl[17] (ordCompl[11] m)))) : False := by
  have hp11 : Nat.Prime 11 := by decide
  have hp17 : Nat.Prime 17 := by decide
  have hpq_ne : (11 : ℕ) ≠ 17 := by decide
  have hpr_ne : (11 : ℕ) ≠ p :=
    Nat.ne_of_lt (lt_of_lt_of_le (by decide : 11 < 41) hp41)
  have hqr_ne : (17 : ℕ) ≠ p :=
    Nat.ne_of_lt (lt_of_lt_of_le (by decide : 17 < 41) hp41)
  have heq := five_sigma_eq_six_of_three_squareful hm hp11 hp17 hp hpq_ne hpr_ne
    hqr_ne h hs
  have hproj_p : ordProj[11] m = 11 ^ padicValNat 11 m := by
    simp [Nat.factorization_def m hp11]
  have hproj_q : ordProj[17] (ordCompl[11] m) =
      17 ^ padicValNat 17 (ordCompl[11] m) := by
    simp [Nat.factorization_def (ordCompl[11] m) hp17]
  have hproj_r : ordProj[p] (ordCompl[17] (ordCompl[11] m)) =
      p ^ padicValNat p (ordCompl[17] (ordCompl[11] m)) := by
    simp [Nat.factorization_def (ordCompl[17] (ordCompl[11] m)) hp]
  rw [hproj_r, padicValNat_ordCompl_of_ne hp hqr_ne,
    padicValNat_ordCompl_of_ne hp hpr_ne, hproj_q,
    padicValNat_ordCompl_of_ne hp17 hpq_ne, hproj_p] at heq
  exact (five_sigma_lt_six_usigma_eleven_seventeen_large hp hp41
    (by omega) (by omega) (by omega)).ne heq

lemma five_mul_eleven_sq_seventeen_cap {p : ℕ} (hp : 29 ≤ p) (hp1 : 1 ≤ p) :
    5 * 17 * p * 133 ≤ 6 * 16 * (p - 1) * 122 := by
  have hp' : (29 : ℤ) ≤ p := Int.ofNat_le.mpr hp
  have hL : ((5 * 17 * p * 133 : ℕ) : ℤ) =
      (5 : ℤ) * 17 * p * 133 := by
    rw [Nat.cast_mul, Nat.cast_mul, Nat.cast_mul]; rfl
  have hR : ((6 * 16 * (p - 1) * 122 : ℕ) : ℤ) =
      (6 : ℤ) * 16 * ((p : ℤ) - 1) * 122 := by
    rw [Nat.cast_mul, Nat.cast_mul, Nat.cast_mul, Nat.cast_sub hp1]
    rfl
  have : (5 : ℤ) * 17 * p * 133 ≤ 6 * 16 * (p - 1) * 122 := by nlinarith
  exact Nat.cast_le.mp (by rw [hL, hR]; exact this)

/-- `{11^2, 17^b, p^k}` undershoots leftover `6/5` for `p ≥ 29`. -/
lemma five_sigma_lt_six_usigma_eleven_sq_seventeen_large {p b k : ℕ}
    (hp : p.Prime) (hp29 : 29 ≤ p) (hb : 0 < b) (hk : 0 < k) :
    5 * σ 1 (11 ^ 2) * σ 1 (17 ^ b) * σ 1 (p ^ k) <
      6 * usigma (11 ^ 2) * usigma (17 ^ b) * usigma (p ^ k) := by
  rw [sigma_eleven_pow_two, usigma_eleven_pow_two]
  have h17 := sigma_lt_cap_usigma (by decide : Nat.Prime 17) hb
  have hpcap := sigma_lt_cap_usigma hp hk
  have hu17 : 0 < usigma (17 ^ b) := by
    rw [usigma_prime_pow (by decide : Nat.Prime 17) hb]
    exact Nat.add_pos_left (by decide : 0 < 1) _
  have hcap := five_mul_eleven_sq_seventeen_cap hp29 hp.one_le
  have hthis := six_five_of_two_caps_times_const (A := 16) (B := 17)
    (X := σ 1 (17 ^ b)) (Y := usigma (17 ^ b)) (C := p - 1) (D := p)
    (P := σ 1 (p ^ k)) (Q := usigma (p ^ k)) (S := 122) (T := 133)
    h17 hpcap hcap (by decide : 0 < 17) hu17 (by decide : 0 < 133)
  have hL : 5 * σ 1 (17 ^ b) * σ 1 (p ^ k) * 133 =
      5 * 133 * σ 1 (17 ^ b) * σ 1 (p ^ k) := by ring
  have hR : 6 * usigma (17 ^ b) * usigma (p ^ k) * 122 =
      6 * 122 * usigma (17 ^ b) * usigma (p ^ k) := by ring
  rw [← hL, ← hR]
  exact hthis

/-- `ρ(1331) ρ(289) ρ(p^2) > 6/5` for `29 ≤ p ≤ 31`. -/
lemma eleven_cube_seventeen_sq_p_sq_overshoot_six_five {p : ℕ} (hp : p.Prime)
    (h29 : 29 ≤ p) (h31 : p ≤ 31) :
    6 * usigma (11 ^ 3) * usigma (17 ^ 2) * usigma (p ^ 2) <
      5 * σ 1 (11 ^ 3) * σ 1 (17 ^ 2) * σ 1 (p ^ 2) := by
  have hp11 : Nat.Prime 11 := by decide
  have hu11 : usigma (11 ^ 3) = 1332 := by
    rw [usigma_prime_pow hp11 (by decide : 0 < 3)]
    decide
  have hσ11 : σ 1 (11 ^ 3) = 1464 := by
    rw [sigma_prime_pow_div hp11]
    norm_num
  rw [hu11, hσ11, usigma_seventeen_pow_two, sigma_seventeen_pow_two,
    usigma_prime_pow hp (by decide : 0 < 2), sigma_prime_pow_two hp]
  have hsq : p ^ 2 ≤ 31 * p := by
    rw [pow_two]
    exact Nat.mul_le_mul_right p h31
  have hL : ((6 * 1332 * 290 * (1 + p ^ 2) : ℕ) : ℤ) =
      (6 : ℤ) * 1332 * 290 * (1 + (p : ℤ) ^ 2) := by push_cast; rfl
  have hR : ((5 * 1464 * 307 * (1 + p + p ^ 2) : ℕ) : ℤ) =
      (5 : ℤ) * 1464 * 307 * (1 + (p : ℤ) + (p : ℤ) ^ 2) := by push_cast; rfl
  have hint : (6 : ℤ) * 1332 * 290 * (1 + p ^ 2) <
      5 * 1464 * 307 * (1 + p + p ^ 2) := by
    have hp29 : (29 : ℤ) ≤ p := by exact_mod_cast h29
    have hp31 : (p : ℤ) ≤ 31 := by exact_mod_cast h31
    have hsq' : (p : ℤ) ^ 2 ≤ 31 * p := by exact_mod_cast hsq
    nlinarith
  exact Nat.cast_lt.mp (by rw [hL, hR]; exact hint)

lemma eleven_cube_seventeen_sq_p_pow_ge_two_overshoot_six_five {p a b k : ℕ}
    (hp : p.Prime) (h29 : 29 ≤ p) (h31 : p ≤ 31)
    (ha : 3 ≤ a) (hb : 2 ≤ b) (hk : 2 ≤ k) :
    6 * usigma (11 ^ a) * usigma (17 ^ b) * usigma (p ^ k) <
      5 * σ 1 (11 ^ a) * σ 1 (17 ^ b) * σ 1 (p ^ k) :=
  six_five_overshoot_mono_three (by decide : Nat.Prime 11)
    (by decide : Nat.Prime 17) hp
    (by decide : 0 < 3) (by decide : 0 < 2) (by decide : 0 < 2)
    ha hb hk
    (eleven_cube_seventeen_sq_p_sq_overshoot_six_five hp h29 h31)

lemma not_five_sigma_eq_six_usigma_eleven_seventeen_mid {p a b k : ℕ}
    (hp : p.Prime) (hp29 : 29 ≤ p) (h31 : p ≤ 31)
    (ha : 2 ≤ a) (hb : 2 ≤ b) (hk : 2 ≤ k) :
    ¬ 5 * σ 1 (11 ^ a) * σ 1 (17 ^ b) * σ 1 (p ^ k) =
        6 * usigma (11 ^ a) * usigma (17 ^ b) * usigma (p ^ k) := by
  intro heq
  rcases eq_or_lt_of_le ha with ha2 | ha3
  · rw [← ha2] at heq
    exact (five_sigma_lt_six_usigma_eleven_sq_seventeen_large hp hp29
      (by omega) (by omega)).ne heq
  · exact (eleven_cube_seventeen_sq_p_pow_ge_two_overshoot_six_five hp hp29 h31
      (Nat.succ_le_of_lt ha3) hb hk).ne' heq

/-- Leftover `6/5` cannot be three squareful primes `11,17,p` with
`29 ≤ p ≤ 31` times a squarefree coprime factor. -/
lemma not_five_sigma_of_three_sq_primes_eleven_seventeen_mid {m p : ℕ}
    (hm : m ≠ 0) (hp : p.Prime) (hp29 : 29 ≤ p) (h31 : p ≤ 31)
    (h : 5 * σ 1 m = 6 * usigma m)
    (hk11 : 2 ≤ padicValNat 11 m) (hk17 : 2 ≤ padicValNat 17 m)
    (hkp : 2 ≤ padicValNat p m)
    (hs : Squarefree (ordCompl[p] (ordCompl[17] (ordCompl[11] m)))) : False := by
  have hp11 : Nat.Prime 11 := by decide
  have hp17 : Nat.Prime 17 := by decide
  have hpq_ne : (11 : ℕ) ≠ 17 := by decide
  have hpr_ne : (11 : ℕ) ≠ p :=
    Nat.ne_of_lt (lt_of_lt_of_le (by decide : 11 < 29) hp29)
  have hqr_ne : (17 : ℕ) ≠ p :=
    Nat.ne_of_lt (lt_of_lt_of_le (by decide : 17 < 29) hp29)
  have heq := five_sigma_eq_six_of_three_squareful hm hp11 hp17 hp hpq_ne hpr_ne
    hqr_ne h hs
  have hproj_p : ordProj[11] m = 11 ^ padicValNat 11 m := by
    simp [Nat.factorization_def m hp11]
  have hproj_q : ordProj[17] (ordCompl[11] m) =
      17 ^ padicValNat 17 (ordCompl[11] m) := by
    simp [Nat.factorization_def (ordCompl[11] m) hp17]
  have hproj_r : ordProj[p] (ordCompl[17] (ordCompl[11] m)) =
      p ^ padicValNat p (ordCompl[17] (ordCompl[11] m)) := by
    simp [Nat.factorization_def (ordCompl[17] (ordCompl[11] m)) hp]
  rw [hproj_r, padicValNat_ordCompl_of_ne hp hqr_ne,
    padicValNat_ordCompl_of_ne hp hpr_ne, hproj_q,
    padicValNat_ordCompl_of_ne hp17 hpq_ne, hproj_p] at heq
  exact not_five_sigma_eq_six_usigma_eleven_seventeen_mid hp hp29 h31 hk11 hk17
    hkp heq

lemma prime_thirty_seven : Nat.Prime 37 := by norm_num

lemma five_mul_eleven_seventeen_sq_thirty_seven_cap :
    5 * 11 * 37 * 307 ≤ 6 * 10 * 36 * 290 := by
  norm_num

/-- `{11^a, 17^2, 37^k}` undershoots leftover `6/5`. -/
lemma five_sigma_lt_six_usigma_eleven_seventeen_sq_thirty_seven {a k : ℕ}
    (ha : 0 < a) (hk : 0 < k) :
    5 * σ 1 (11 ^ a) * σ 1 (17 ^ 2) * σ 1 (37 ^ k) <
      6 * usigma (11 ^ a) * usigma (17 ^ 2) * usigma (37 ^ k) := by
  rw [sigma_seventeen_pow_two, usigma_seventeen_pow_two]
  have h11 := sigma_lt_cap_usigma (by decide : Nat.Prime 11) ha
  have h37 := sigma_lt_cap_usigma prime_thirty_seven hk
  have hu11 : 0 < usigma (11 ^ a) := by
    rw [usigma_prime_pow (by decide : Nat.Prime 11) ha]
    exact Nat.add_pos_left (by decide : 0 < 1) _
  have hthis := six_five_of_two_caps_times_const (A := 10) (B := 11)
    (X := σ 1 (11 ^ a)) (Y := usigma (11 ^ a)) (C := 36) (D := 37)
    (P := σ 1 (37 ^ k)) (Q := usigma (37 ^ k)) (S := 290) (T := 307)
    h11 h37 five_mul_eleven_seventeen_sq_thirty_seven_cap
    (by decide : 0 < 11) hu11 (by decide : 0 < 307)
  have hL : 5 * σ 1 (11 ^ a) * σ 1 (37 ^ k) * 307 =
      5 * σ 1 (11 ^ a) * 307 * σ 1 (37 ^ k) := by ring
  have hR : 6 * usigma (11 ^ a) * usigma (37 ^ k) * 290 =
      6 * usigma (11 ^ a) * 290 * usigma (37 ^ k) := by ring
  rw [← hL, ← hR]
  exact hthis

lemma usigma_seventeen_pow_three : usigma (17 ^ 3) = 4914 := by
  rw [usigma_prime_pow (by decide : Nat.Prime 17) (by decide : 0 < 3)]
  decide

lemma sigma_seventeen_pow_three : σ 1 (17 ^ 3) = 5220 := by
  rw [sigma_prime_pow_div (by decide : Nat.Prime 17)]
  norm_num

lemma usigma_seventeen_pow_four : usigma (17 ^ 4) = 83522 := by
  rw [usigma_prime_pow (by decide : Nat.Prime 17) (by decide : 0 < 4)]
  decide

lemma sigma_seventeen_pow_four : σ 1 (17 ^ 4) = 88741 := by
  rw [sigma_prime_pow_div (by decide : Nat.Prime 17)]
  norm_num

lemma usigma_eleven_pow_three : usigma (11 ^ 3) = 1332 := by
  rw [usigma_prime_pow (by decide : Nat.Prime 11) (by decide : 0 < 3)]
  decide

lemma sigma_eleven_pow_three : σ 1 (11 ^ 3) = 1464 := by
  rw [sigma_prime_pow_div (by decide : Nat.Prime 11)]
  norm_num

lemma usigma_eleven_pow_four : usigma (11 ^ 4) = 14642 := by
  rw [usigma_prime_pow (by decide : Nat.Prime 11) (by decide : 0 < 4)]
  decide

lemma sigma_eleven_pow_four : σ 1 (11 ^ 4) = 16105 := by
  rw [sigma_prime_pow_div (by decide : Nat.Prime 11)]
  norm_num

lemma usigma_eleven_pow_five : usigma (11 ^ 5) = 161052 := by
  rw [usigma_prime_pow (by decide : Nat.Prime 11) (by decide : 0 < 5)]
  decide

lemma sigma_eleven_pow_five : σ 1 (11 ^ 5) = 177156 := by
  rw [sigma_prime_pow_div (by decide : Nat.Prime 11)]
  norm_num

lemma usigma_thirty_seven_pow_two : usigma (37 ^ 2) = 1370 := by
  rw [usigma_prime_pow prime_thirty_seven (by decide : 0 < 2)]
  decide

lemma sigma_thirty_seven_pow_two : σ 1 (37 ^ 2) = 1407 := by
  rw [sigma_prime_pow_two prime_thirty_seven]
  decide

lemma usigma_thirty_seven_pow_three : usigma (37 ^ 3) = 50654 := by
  rw [usigma_prime_pow prime_thirty_seven (by decide : 0 < 3)]
  decide

lemma sigma_thirty_seven_pow_three : σ 1 (37 ^ 3) = 52060 := by
  rw [sigma_prime_pow_div prime_thirty_seven]
  norm_num

lemma five_mul_eleven_cube_seventeen_cube_thirty_seven_cap :
    5 * 37 * 1464 * 5220 ≤ 6 * 36 * 1332 * 4914 := by
  norm_num

/-- `{11^3, 17^3, 37^k}` undershoots leftover `6/5`. -/
lemma five_sigma_lt_six_usigma_eleven_cube_seventeen_cube_thirty_seven {k : ℕ}
    (hk : 0 < k) :
    5 * σ 1 (11 ^ 3) * σ 1 (17 ^ 3) * σ 1 (37 ^ k) <
      6 * usigma (11 ^ 3) * usigma (17 ^ 3) * usigma (37 ^ k) := by
  rw [sigma_eleven_pow_three, usigma_eleven_pow_three,
    sigma_seventeen_pow_three, usigma_seventeen_pow_three]
  have h37 := sigma_lt_cap_usigma prime_thirty_seven hk
  have hthis := six_five_of_cap_times_const (A := 36) (B := 37)
    (X := σ 1 (37 ^ k)) (Y := usigma (37 ^ k)) (S := 1332 * 4914)
    (T := 1464 * 5220) h37 (by
      have hL : 5 * 37 * (1464 * 5220) = 5 * 37 * 1464 * 5220 := by ring
      have hR : 6 * 36 * (1332 * 4914) = 6 * 36 * 1332 * 4914 := by ring
      rw [hL, hR]
      exact five_mul_eleven_cube_seventeen_cube_thirty_seven_cap)
    (by decide : 0 < 1464 * 5220)
  have hL : 5 * σ 1 (37 ^ k) * (1464 * 5220) =
      5 * 1464 * 5220 * σ 1 (37 ^ k) := by ring
  have hR : 6 * usigma (37 ^ k) * (1332 * 4914) =
      6 * 1332 * 4914 * usigma (37 ^ k) := by ring
  rw [← hL, ← hR]
  exact hthis

lemma five_mul_eleven_cube_thirty_seven_sq_seventeen_cap :
    5 * 17 * 1464 * 1407 ≤ 6 * 16 * 1332 * 1370 := by
  norm_num

/-- `{11^3, 17^b, 37^2}` undershoots leftover `6/5`. -/
lemma five_sigma_lt_six_usigma_eleven_cube_thirty_seven_sq {b : ℕ}
    (hb : 0 < b) :
    5 * σ 1 (11 ^ 3) * σ 1 (17 ^ b) * σ 1 (37 ^ 2) <
      6 * usigma (11 ^ 3) * usigma (17 ^ b) * usigma (37 ^ 2) := by
  rw [sigma_eleven_pow_three, usigma_eleven_pow_three,
    sigma_thirty_seven_pow_two, usigma_thirty_seven_pow_two]
  have h17 := sigma_lt_cap_usigma (by decide : Nat.Prime 17) hb
  have hu17 : 0 < usigma (17 ^ b) := by
    rw [usigma_prime_pow (by decide : Nat.Prime 17) hb]
    exact Nat.add_pos_left (by decide : 0 < 1) _
  have hthis := six_five_of_cap_times_const (A := 16) (B := 17)
    (X := σ 1 (17 ^ b)) (Y := usigma (17 ^ b)) (S := 1332 * 1370)
    (T := 1464 * 1407) h17 (by
      have hL : 5 * 17 * (1464 * 1407) = 5 * 17 * 1464 * 1407 := by ring
      have hR : 6 * 16 * (1332 * 1370) = 6 * 16 * 1332 * 1370 := by ring
      rw [hL, hR]
      exact five_mul_eleven_cube_thirty_seven_sq_seventeen_cap)
    (by decide : 0 < 1464 * 1407)
  have hL : 5 * σ 1 (17 ^ b) * (1464 * 1407) =
      5 * 1464 * σ 1 (17 ^ b) * 1407 := by ring
  have hR : 6 * usigma (17 ^ b) * (1332 * 1370) =
      6 * 1332 * usigma (17 ^ b) * 1370 := by ring
  rw [← hL, ← hR]
  exact hthis

lemma eleven_cube_seventeen_fourth_thirty_seven_cube_overshoot :
    6 * usigma (11 ^ 3) * usigma (17 ^ 4) * usigma (37 ^ 3) <
      5 * σ 1 (11 ^ 3) * σ 1 (17 ^ 4) * σ 1 (37 ^ 3) := by
  rw [usigma_eleven_pow_three, sigma_eleven_pow_three,
    usigma_seventeen_pow_four, sigma_seventeen_pow_four,
    usigma_thirty_seven_pow_three, sigma_thirty_seven_pow_three]
  norm_num

lemma eleven_fourth_seventeen_cube_thirty_seven_sq_under :
    5 * σ 1 (11 ^ 4) * σ 1 (17 ^ 3) * σ 1 (37 ^ 2) <
      6 * usigma (11 ^ 4) * usigma (17 ^ 3) * usigma (37 ^ 2) := by
  rw [sigma_eleven_pow_four, usigma_eleven_pow_four,
    sigma_seventeen_pow_three, usigma_seventeen_pow_three,
    sigma_thirty_seven_pow_two, usigma_thirty_seven_pow_two]
  norm_num

lemma eleven_fourth_seventeen_cube_thirty_seven_cube_overshoot :
    6 * usigma (11 ^ 4) * usigma (17 ^ 3) * usigma (37 ^ 3) <
      5 * σ 1 (11 ^ 4) * σ 1 (17 ^ 3) * σ 1 (37 ^ 3) := by
  rw [usigma_eleven_pow_four, sigma_eleven_pow_four,
    usigma_seventeen_pow_three, sigma_seventeen_pow_three,
    usigma_thirty_seven_pow_three, sigma_thirty_seven_pow_three]
  norm_num

lemma eleven_fifth_seventeen_cube_thirty_seven_sq_overshoot :
    6 * usigma (11 ^ 5) * usigma (17 ^ 3) * usigma (37 ^ 2) <
      5 * σ 1 (11 ^ 5) * σ 1 (17 ^ 3) * σ 1 (37 ^ 2) := by
  rw [usigma_eleven_pow_five, sigma_eleven_pow_five,
    usigma_seventeen_pow_three, sigma_seventeen_pow_three,
    usigma_thirty_seven_pow_two, sigma_thirty_seven_pow_two]
  norm_num

lemma eleven_fourth_seventeen_fourth_thirty_seven_sq_overshoot :
    6 * usigma (11 ^ 4) * usigma (17 ^ 4) * usigma (37 ^ 2) <
      5 * σ 1 (11 ^ 4) * σ 1 (17 ^ 4) * σ 1 (37 ^ 2) := by
  rw [usigma_eleven_pow_four, sigma_eleven_pow_four,
    usigma_seventeen_pow_four, sigma_seventeen_pow_four,
    usigma_thirty_seven_pow_two, sigma_thirty_seven_pow_two]
  norm_num

lemma not_five_sigma_eq_six_usigma_eleven_seventeen_thirty_seven {a b k : ℕ}
    (ha : 2 ≤ a) (hb : 2 ≤ b) (hk : 2 ≤ k) :
    ¬ 5 * σ 1 (11 ^ a) * σ 1 (17 ^ b) * σ 1 (37 ^ k) =
        6 * usigma (11 ^ a) * usigma (17 ^ b) * usigma (37 ^ k) := by
  intro heq
  rcases eq_or_lt_of_le ha with ha2 | ha3
  · rw [← ha2] at heq
    exact (five_sigma_lt_six_usigma_eleven_sq_seventeen_large prime_thirty_seven
      (by decide : 29 ≤ 37) (by omega) (by omega)).ne heq
  · have ha3' : 3 ≤ a := Nat.succ_le_of_lt ha3
    rcases eq_or_lt_of_le hb with hb2 | hb3
    · rw [← hb2] at heq
      exact (five_sigma_lt_six_usigma_eleven_seventeen_sq_thirty_seven
        (by omega) (by omega)).ne heq
    · have hb3' : 3 ≤ b := Nat.succ_le_of_lt hb3
      rcases eq_or_lt_of_le ha3' with ha3eq | ha4
      · rw [← ha3eq] at heq
        rcases eq_or_lt_of_le hb3' with hb3eq | hb4
        · rw [← hb3eq] at heq
          exact (five_sigma_lt_six_usigma_eleven_cube_seventeen_cube_thirty_seven
            (by omega)).ne heq
        · have hb4' : 4 ≤ b := Nat.succ_le_of_lt hb4
          rcases eq_or_lt_of_le hk with hk2 | hk3
          · rw [← hk2] at heq
            exact (five_sigma_lt_six_usigma_eleven_cube_thirty_seven_sq
              (by omega)).ne heq
          · have hover := six_five_overshoot_mono_three
                (by decide : Nat.Prime 11) (by decide : Nat.Prime 17)
                prime_thirty_seven
                (by decide : 0 < 3) (by decide : 0 < 4) (by decide : 0 < 3)
                (le_refl _) hb4' (Nat.succ_le_of_lt hk3)
                eleven_cube_seventeen_fourth_thirty_seven_cube_overshoot
            rw [← heq] at hover
            exact lt_irrefl _ hover
      · have ha4' : 4 ≤ a := Nat.succ_le_of_lt ha4
        rcases eq_or_lt_of_le ha4' with ha4eq | ha5
        · rw [← ha4eq] at heq
          rcases eq_or_lt_of_le hb3' with hb3eq | hb4
          · rw [← hb3eq] at heq
            rcases eq_or_lt_of_le hk with hk2 | hk3
            · rw [← hk2] at heq
              exact eleven_fourth_seventeen_cube_thirty_seven_sq_under.ne heq
            · have hover := six_five_overshoot_mono_three
                  (by decide : Nat.Prime 11) (by decide : Nat.Prime 17)
                  prime_thirty_seven
                  (by decide : 0 < 4) (by decide : 0 < 3) (by decide : 0 < 3)
                  (le_refl _) (le_refl _) (Nat.succ_le_of_lt hk3)
                  eleven_fourth_seventeen_cube_thirty_seven_cube_overshoot
              rw [← heq] at hover
              exact lt_irrefl _ hover
          · have hover := six_five_overshoot_mono_three
                (by decide : Nat.Prime 11) (by decide : Nat.Prime 17)
                prime_thirty_seven
                (by decide : 0 < 4) (by decide : 0 < 4) (by decide : 0 < 2)
                (le_refl _) (Nat.succ_le_of_lt hb4) hk
                eleven_fourth_seventeen_fourth_thirty_seven_sq_overshoot
            rw [← heq] at hover
            exact lt_irrefl _ hover
        · have ha5' : 5 ≤ a := Nat.succ_le_of_lt ha5
          rcases eq_or_lt_of_le hb3' with hb3eq | hb4
          · rw [← hb3eq] at heq
            have hover := six_five_overshoot_mono_three
                (by decide : Nat.Prime 11) (by decide : Nat.Prime 17)
                prime_thirty_seven
                (by decide : 0 < 5) (by decide : 0 < 3) (by decide : 0 < 2)
                ha5' (le_refl _) hk
                eleven_fifth_seventeen_cube_thirty_seven_sq_overshoot
            rw [← heq] at hover
            exact lt_irrefl _ hover
          · have hover := six_five_overshoot_mono_three
                (by decide : Nat.Prime 11) (by decide : Nat.Prime 17)
                prime_thirty_seven
                (by decide : 0 < 4) (by decide : 0 < 4) (by decide : 0 < 2)
                ha4' (Nat.succ_le_of_lt hb4) hk
                eleven_fourth_seventeen_fourth_thirty_seven_sq_overshoot
            rw [← heq] at hover
            exact lt_irrefl _ hover

/-- Leftover `6/5` cannot be three squareful primes `11,17,37` times a
squarefree coprime factor. -/
lemma not_five_sigma_of_three_sq_primes_eleven_seventeen_thirty_seven {m : ℕ}
    (hm : m ≠ 0) (h : 5 * σ 1 m = 6 * usigma m)
    (hk11 : 2 ≤ padicValNat 11 m) (hk17 : 2 ≤ padicValNat 17 m)
    (hk37 : 2 ≤ padicValNat 37 m)
    (hs : Squarefree (ordCompl[37] (ordCompl[17] (ordCompl[11] m)))) : False := by
  have hp11 : Nat.Prime 11 := by decide
  have hp17 : Nat.Prime 17 := by decide
  have hp37 := prime_thirty_seven
  have hpq_ne : (11 : ℕ) ≠ 17 := by decide
  have hpr_ne : (11 : ℕ) ≠ 37 := by decide
  have hqr_ne : (17 : ℕ) ≠ 37 := by decide
  have heq := five_sigma_eq_six_of_three_squareful hm hp11 hp17 hp37 hpq_ne
    hpr_ne hqr_ne h hs
  have hproj_p : ordProj[11] m = 11 ^ padicValNat 11 m := by
    simp [Nat.factorization_def m hp11]
  have hproj_q : ordProj[17] (ordCompl[11] m) =
      17 ^ padicValNat 17 (ordCompl[11] m) := by
    simp [Nat.factorization_def (ordCompl[11] m) hp17]
  have hproj_r : ordProj[37] (ordCompl[17] (ordCompl[11] m)) =
      37 ^ padicValNat 37 (ordCompl[17] (ordCompl[11] m)) := by
    simp [Nat.factorization_def (ordCompl[17] (ordCompl[11] m)) hp37]
  rw [hproj_r, padicValNat_ordCompl_of_ne hp37 hqr_ne,
    padicValNat_ordCompl_of_ne hp37 hpr_ne, hproj_q,
    padicValNat_ordCompl_of_ne hp17 hpq_ne, hproj_p] at heq
  exact not_five_sigma_eq_six_usigma_eleven_seventeen_thirty_seven hk11 hk17 hk37
    heq

/-- Leftover `6/5` cannot be three squareful primes `11,17,p` with `p ≥ 19`
times a squarefree coprime factor. -/
lemma not_five_sigma_of_three_sq_primes_eleven_seventeen {m p : ℕ}
    (hm : m ≠ 0) (hp : p.Prime) (hp19 : 19 ≤ p)
    (h : 5 * σ 1 m = 6 * usigma m)
    (hk11 : 2 ≤ padicValNat 11 m) (hk17 : 2 ≤ padicValNat 17 m)
    (hkp : 2 ≤ padicValNat p m)
    (hs : Squarefree (ordCompl[p] (ordCompl[17] (ordCompl[11] m)))) : False := by
  rcases le_or_gt p 23 with h23 | h24
  · exact not_five_sigma_of_three_sq_primes_eleven_seventeen_small hm hp hp19
      h23 h hk11 hk17 hkp hs
  · have hp29 : 29 ≤ p := prime_ge_twenty_four_ge_twenty_nine hp (by omega)
    rcases le_or_gt p 31 with h31 | h32
    · exact not_five_sigma_of_three_sq_primes_eleven_seventeen_mid hm hp hp29 h31
        h hk11 hk17 hkp hs
    · have hp37 : 37 ≤ p := prime_ge_thirty_two_ge_thirty_seven hp (by omega)
      rcases le_or_gt p 37 with h37 | h38
      · have hp37eq : p = 37 := le_antisymm h37 hp37
        subst p
        exact not_five_sigma_of_three_sq_primes_eleven_seventeen_thirty_seven hm h
          hk11 hk17 hkp hs
      · have hp41 : 41 ≤ p := prime_ge_thirty_eight_ge_forty_one hp (by omega)
        exact not_five_sigma_of_three_sq_primes_eleven_seventeen_large hm hp hp41
          h hk11 hk17 hkp hs

lemma five_eleven_thirteen_cap {p : ℕ} (hp : 149 ≤ p) :
    5 * 11 * 13 * p ≤ 6 * 10 * 12 * (p - 1) := by
  have hp1 : 1 ≤ p := by omega
  have hp' : (149 : ℤ) ≤ p := Int.ofNat_le.mpr hp
  have hL : ((5 * 11 * 13 * p : ℕ) : ℤ) =
      (5 : ℤ) * 11 * 13 * p := by
    rw [Nat.cast_mul, Nat.cast_mul, Nat.cast_mul]; rfl
  have hR : ((6 * 10 * 12 * (p - 1) : ℕ) : ℤ) =
      (6 : ℤ) * 10 * 12 * ((p : ℤ) - 1) := by
    rw [Nat.cast_mul, Nat.cast_mul, Nat.cast_mul, Nat.cast_sub hp1]
    rfl
  have : (5 : ℤ) * 11 * 13 * p ≤ 6 * 10 * 12 * (p - 1) := by nlinarith
  exact Nat.cast_le.mp (by rw [hL, hR]; exact this)

/-- `{11, 13, p}` with `p ≥ 149` cannot fill leftover `6/5`. -/
lemma five_sigma_lt_six_usigma_eleven_thirteen_large {p a b c : ℕ}
    (hp : p.Prime) (hp149 : 149 ≤ p) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    5 * σ 1 (11 ^ a) * σ 1 (13 ^ b) * σ 1 (p ^ c) <
      6 * usigma (11 ^ a) * usigma (13 ^ b) * usigma (p ^ c) := by
  have h11 := sigma_lt_cap_usigma (by decide : Nat.Prime 11) ha
  have h13 := sigma_lt_cap_usigma (by decide : Nat.Prime 13) hb
  have hpcap := sigma_lt_cap_usigma hp hc
  have hu11 : 0 < usigma (11 ^ a) := by
    rw [usigma_prime_pow (by decide : Nat.Prime 11) ha]
    exact Nat.add_pos_left (by decide : 0 < 1) _
  have hu13 : 0 < usigma (13 ^ b) := by
    rw [usigma_prime_pow (by decide : Nat.Prime 13) hb]
    exact Nat.add_pos_left (by decide : 0 < 1) _
  have hcap := five_eleven_thirteen_cap hp149
  have := six_five_of_three_caps (A := 10) (B := 11) (X := σ 1 (11 ^ a))
    (Y := usigma (11 ^ a)) (C := 12) (D := 13) (P := σ 1 (13 ^ b))
    (Q := usigma (13 ^ b)) (E := p - 1) (F := p) (R := σ 1 (p ^ c))
    (S := usigma (p ^ c)) h11 h13 hpcap hcap (by decide : 0 < 11) hu11
    (by decide : 0 < 13) hu13
  simpa [mul_assoc] using this

lemma prime_ge_one_forty_four_ge_one_forty_nine {p : ℕ} (hp : p.Prime)
    (h : 144 ≤ p) : 149 ≤ p := by
  have hmem : p = 144 ∨ p = 145 ∨ p = 146 ∨ p = 147 ∨ p = 148 ∨ 149 ≤ p :=
    by omega
  rcases hmem with rfl | rfl | rfl | rfl | rfl | h149
  · exact False.elim ((by decide : ¬ Nat.Prime 144) hp)
  · exact False.elim ((by decide : ¬ Nat.Prime 145) hp)
  · exact False.elim ((by decide : ¬ Nat.Prime 146) hp)
  · exact False.elim ((by decide : ¬ Nat.Prime 147) hp)
  · exact False.elim ((by decide : ¬ Nat.Prime 148) hp)
  · exact h149

/-- Leftover `6/5` cannot be three squareful primes `11,13,p` with
`p ≥ 149` times a squarefree coprime factor. -/
lemma not_five_sigma_of_three_sq_primes_eleven_thirteen_large {m p : ℕ}
    (hm : m ≠ 0) (hp : p.Prime) (hp149 : 149 ≤ p)
    (h : 5 * σ 1 m = 6 * usigma m)
    (hk11 : 2 ≤ padicValNat 11 m) (hk13 : 2 ≤ padicValNat 13 m)
    (hkp : 2 ≤ padicValNat p m)
    (hs : Squarefree (ordCompl[p] (ordCompl[13] (ordCompl[11] m)))) : False := by
  have hp11 : Nat.Prime 11 := by decide
  have hp13 : Nat.Prime 13 := by decide
  have hpq_ne : (11 : ℕ) ≠ 13 := by decide
  have hpr_ne : (11 : ℕ) ≠ p :=
    Nat.ne_of_lt (lt_of_lt_of_le (by decide : 11 < 149) hp149)
  have hqr_ne : (13 : ℕ) ≠ p :=
    Nat.ne_of_lt (lt_of_lt_of_le (by decide : 13 < 149) hp149)
  have heq := five_sigma_eq_six_of_three_squareful hm hp11 hp13 hp hpq_ne hpr_ne
    hqr_ne h hs
  have hproj_p : ordProj[11] m = 11 ^ padicValNat 11 m := by
    simp [Nat.factorization_def m hp11]
  have hproj_q : ordProj[13] (ordCompl[11] m) =
      13 ^ padicValNat 13 (ordCompl[11] m) := by
    simp [Nat.factorization_def (ordCompl[11] m) hp13]
  have hproj_r : ordProj[p] (ordCompl[13] (ordCompl[11] m)) =
      p ^ padicValNat p (ordCompl[13] (ordCompl[11] m)) := by
    simp [Nat.factorization_def (ordCompl[13] (ordCompl[11] m)) hp]
  rw [hproj_r, padicValNat_ordCompl_of_ne hp hqr_ne,
    padicValNat_ordCompl_of_ne hp hpr_ne, hproj_q,
    padicValNat_ordCompl_of_ne hp13 hpq_ne, hproj_p] at heq
  exact (five_sigma_lt_six_usigma_eleven_thirteen_large hp hp149
    (by omega) (by omega) (by omega)).ne heq

/-- Leftover `10/7` cannot be four squareful primes `7 ≤ p < q < r < s` with
`s ≥ 41` times a squarefree coprime factor. -/
lemma not_seven_sigma_of_four_sq_primes_ge_seven {m p q r s : ℕ} (hm : m ≠ 0)
    (hp : p.Prime) (hq : q.Prime) (hr : r.Prime) (hs : s.Prime)
    (hpq : p < q) (hqr : q < r) (hrs : r < s) (hp7 : 7 ≤ p) (hs41 : 41 ≤ s)
    (h : 7 * σ 1 m = 10 * usigma m)
    (hkp : 2 ≤ padicValNat p m) (hkq : 2 ≤ padicValNat q m)
    (hkr : 2 ≤ padicValNat r m) (hks : 2 ≤ padicValNat s m)
    (hsf : Squarefree
      (ordCompl[s] (ordCompl[r] (ordCompl[q] (ordCompl[p] m))))) : False := by
  have hpq_ne : p ≠ q := Nat.ne_of_lt hpq
  have hpr_ne : p ≠ r := Nat.ne_of_lt (lt_trans hpq hqr)
  have hps_ne : p ≠ s :=
    Nat.ne_of_lt (lt_trans (lt_trans hpq hqr) hrs)
  have hqr_ne : q ≠ r := Nat.ne_of_lt hqr
  have hqs_ne : q ≠ s := Nat.ne_of_lt (lt_trans hqr hrs)
  have hrs_ne : r ≠ s := Nat.ne_of_lt hrs
  have heq := seven_sigma_eq_ten_of_four_squareful hm hp hq hr hs hpq_ne hpr_ne
    hps_ne hqr_ne hqs_ne hrs_ne h hsf
  have hproj_p : ordProj[p] m = p ^ padicValNat p m := by
    simp [Nat.factorization_def m hp]
  have hproj_q : ordProj[q] (ordCompl[p] m) =
      q ^ padicValNat q (ordCompl[p] m) := by
    simp [Nat.factorization_def (ordCompl[p] m) hq]
  have hproj_r : ordProj[r] (ordCompl[q] (ordCompl[p] m)) =
      r ^ padicValNat r (ordCompl[q] (ordCompl[p] m)) := by
    simp [Nat.factorization_def (ordCompl[q] (ordCompl[p] m)) hr]
  have hproj_s : ordProj[s] (ordCompl[r] (ordCompl[q] (ordCompl[p] m))) =
      s ^ padicValNat s (ordCompl[r] (ordCompl[q] (ordCompl[p] m))) := by
    simp [Nat.factorization_def (ordCompl[r] (ordCompl[q] (ordCompl[p] m))) hs]
  rw [hproj_s, padicValNat_ordCompl_of_ne hs hrs_ne,
    padicValNat_ordCompl_of_ne hs hqs_ne, padicValNat_ordCompl_of_ne hs hps_ne,
    hproj_r, padicValNat_ordCompl_of_ne hr hqr_ne,
    padicValNat_ordCompl_of_ne hr hpr_ne, hproj_q,
    padicValNat_ordCompl_of_ne hq hpq_ne, hproj_p] at heq
  have hq11 : 11 ≤ q := by
    have : 8 ≤ q := by omega
    have hmem : q = 8 ∨ q = 9 ∨ q = 10 ∨ 11 ≤ q := by omega
    rcases hmem with rfl | rfl | rfl | h11
    · cases (by decide : ¬ Nat.Prime 8) hq
    · cases (by decide : ¬ Nat.Prime 9) hq
    · cases (by decide : ¬ Nat.Prime 10) hq
    · exact h11
  have hr13 : 13 ≤ r := by
    have : 12 ≤ r := by omega
    have hmem : r = 12 ∨ 13 ≤ r := by omega
    rcases hmem with rfl | h13
    · cases (by decide : ¬ Nat.Prime 12) hr
    · exact h13
  exact (seven_sigma_lt_ten_usigma_four_large hp hq hr hs hp7 hq11 hr13 hs41
    (by omega) (by omega) (by omega) (by omega)).ne heq

lemma five_mul_eleven_sq_thirteen_cap {p : ℕ} (hp : 67 ≤ p) (hp1 : 1 ≤ p) :
    5 * 13 * p * 133 ≤ 6 * 12 * (p - 1) * 122 := by
  have hp' : (67 : ℤ) ≤ p := Int.ofNat_le.mpr hp
  have hL : ((5 * 13 * p * 133 : ℕ) : ℤ) =
      (5 : ℤ) * 13 * p * 133 := by
    rw [Nat.cast_mul, Nat.cast_mul, Nat.cast_mul]; rfl
  have hR : ((6 * 12 * (p - 1) * 122 : ℕ) : ℤ) =
      (6 : ℤ) * 12 * ((p : ℤ) - 1) * 122 := by
    rw [Nat.cast_mul, Nat.cast_mul, Nat.cast_mul, Nat.cast_sub hp1]
    rfl
  have : (5 : ℤ) * 13 * p * 133 ≤ 6 * 12 * (p - 1) * 122 := by nlinarith
  exact Nat.cast_le.mp (by rw [hL, hR]; exact this)

/-- `{11^2, 13^b, p^k}` undershoots leftover `6/5` for `p ≥ 67`. -/
lemma five_sigma_lt_six_usigma_eleven_sq_thirteen_large {p b k : ℕ}
    (hp : p.Prime) (hp67 : 67 ≤ p) (hb : 0 < b) (hk : 0 < k) :
    5 * σ 1 (11 ^ 2) * σ 1 (13 ^ b) * σ 1 (p ^ k) <
      6 * usigma (11 ^ 2) * usigma (13 ^ b) * usigma (p ^ k) := by
  rw [sigma_eleven_pow_two, usigma_eleven_pow_two]
  have h13 := sigma_lt_cap_usigma (by decide : Nat.Prime 13) hb
  have hpcap := sigma_lt_cap_usigma hp hk
  have hu13 : 0 < usigma (13 ^ b) := by
    rw [usigma_prime_pow (by decide : Nat.Prime 13) hb]
    exact Nat.add_pos_left (by decide : 0 < 1) _
  have hcap := five_mul_eleven_sq_thirteen_cap hp67 hp.one_le
  have hthis := six_five_of_two_caps_times_const (A := 12) (B := 13)
    (X := σ 1 (13 ^ b)) (Y := usigma (13 ^ b)) (C := p - 1) (D := p)
    (P := σ 1 (p ^ k)) (Q := usigma (p ^ k)) (S := 122) (T := 133)
    h13 hpcap hcap (by decide : 0 < 13) hu13 (by decide : 0 < 133)
  have hL : 5 * σ 1 (13 ^ b) * σ 1 (p ^ k) * 133 =
      5 * 133 * σ 1 (13 ^ b) * σ 1 (p ^ k) := by ring
  have hR : 6 * usigma (13 ^ b) * usigma (p ^ k) * 122 =
      6 * 122 * usigma (13 ^ b) * usigma (p ^ k) := by ring
  rw [← hL, ← hR]
  exact hthis

lemma prime_ge_sixty_four_ge_sixty_seven {p : ℕ} (hp : p.Prime)
    (h : 64 ≤ p) : 67 ≤ p := by
  have hmem : p = 64 ∨ p = 65 ∨ p = 66 ∨ 67 ≤ p := by omega
  rcases hmem with rfl | rfl | rfl | h67
  · exact False.elim ((by decide : ¬ Nat.Prime 64) hp)
  · exact False.elim ((by decide : ¬ Nat.Prime 65) hp)
  · exact False.elim ((by decide : ¬ Nat.Prime 66) hp)
  · exact h67

/-- Leftover `6/5` cannot be three squareful primes `11^2, 13, p` with
`p ≥ 67` times a squarefree coprime factor. -/
lemma not_five_sigma_of_three_sq_primes_eleven_sq_thirteen_large {m p : ℕ}
    (hm : m ≠ 0) (hp : p.Prime) (hp67 : 67 ≤ p)
    (h : 5 * σ 1 m = 6 * usigma m)
    (hk11 : padicValNat 11 m = 2) (hk13 : 2 ≤ padicValNat 13 m)
    (hkp : 2 ≤ padicValNat p m)
    (hs : Squarefree (ordCompl[p] (ordCompl[13] (ordCompl[11] m)))) : False := by
  have hp11 : Nat.Prime 11 := by decide
  have hp13 : Nat.Prime 13 := by decide
  have hpq_ne : (11 : ℕ) ≠ 13 := by decide
  have hpr_ne : (11 : ℕ) ≠ p :=
    Nat.ne_of_lt (lt_of_lt_of_le (by decide : 11 < 67) hp67)
  have hqr_ne : (13 : ℕ) ≠ p :=
    Nat.ne_of_lt (lt_of_lt_of_le (by decide : 13 < 67) hp67)
  have heq := five_sigma_eq_six_of_three_squareful hm hp11 hp13 hp hpq_ne hpr_ne
    hqr_ne h hs
  have hproj_p : ordProj[11] m = 11 ^ padicValNat 11 m := by
    simp [Nat.factorization_def m hp11]
  have hproj_q : ordProj[13] (ordCompl[11] m) =
      13 ^ padicValNat 13 (ordCompl[11] m) := by
    simp [Nat.factorization_def (ordCompl[11] m) hp13]
  have hproj_r : ordProj[p] (ordCompl[13] (ordCompl[11] m)) =
      p ^ padicValNat p (ordCompl[13] (ordCompl[11] m)) := by
    simp [Nat.factorization_def (ordCompl[13] (ordCompl[11] m)) hp]
  rw [hproj_r, padicValNat_ordCompl_of_ne hp hqr_ne,
    padicValNat_ordCompl_of_ne hp hpr_ne, hproj_q,
    padicValNat_ordCompl_of_ne hp13 hpq_ne, hproj_p, hk11] at heq
  exact (five_sigma_lt_six_usigma_eleven_sq_thirteen_large hp hp67
    (by omega) (by omega)).ne heq

lemma five_mul_twenty_five_q_r_cap {q r : ℕ} (hq : 313 ≤ q) (hqr : q < r) :
    5 * q * r * 31 ≤ 6 * (q - 1) * (r - 1) * 26 := by
  have hq1 : 1 ≤ q := by omega
  have hr1 : 1 ≤ r := by omega
  have hq' : (313 : ℤ) ≤ q := Int.ofNat_le.mpr hq
  have hr' : (q : ℤ) + 1 ≤ r := Int.ofNat_le.mpr (Nat.succ_le_of_lt hqr)
  have hL : ((5 * q * r * 31 : ℕ) : ℤ) =
      (5 : ℤ) * q * r * 31 := by
    rw [Nat.cast_mul, Nat.cast_mul, Nat.cast_mul]; rfl
  have hR : ((6 * (q - 1) * (r - 1) * 26 : ℕ) : ℤ) =
      (6 : ℤ) * ((q : ℤ) - 1) * ((r : ℤ) - 1) * 26 := by
    rw [Nat.cast_mul, Nat.cast_mul, Nat.cast_mul, Nat.cast_sub hq1, Nat.cast_sub hr1]
    rfl
  have : (5 : ℤ) * q * r * 31 ≤ 6 * (q - 1) * (r - 1) * 26 := by nlinarith
  exact Nat.cast_le.mp (by rw [hL, hR]; exact this)

/-- `{5^2, q^b, r^c}` undershoots leftover `6/5` for `313 ≤ q < r`. -/
lemma five_sigma_lt_six_usigma_five_sq_two_large {q r b c : ℕ}
    (hq : q.Prime) (hr : r.Prime) (hq313 : 313 ≤ q) (hqr : q < r)
    (hb : 0 < b) (hc : 0 < c) :
    5 * σ 1 (5 ^ 2) * σ 1 (q ^ b) * σ 1 (r ^ c) <
      6 * usigma (5 ^ 2) * usigma (q ^ b) * usigma (r ^ c) := by
  have hσ5 : σ 1 (5 ^ 2) = 31 := by
    rw [sigma_prime_pow_two Nat.prime_five]
    decide
  rw [hσ5, usigma_five_pow_two]
  have hqcap := sigma_lt_cap_usigma hq hb
  have hrcap := sigma_lt_cap_usigma hr hc
  have huq : 0 < usigma (q ^ b) := by
    rw [usigma_prime_pow hq hb]
    exact Nat.add_pos_left (by decide : 0 < 1) _
  have hcap := five_mul_twenty_five_q_r_cap hq313 hqr
  have hthis := six_five_of_two_caps_times_const (A := q - 1) (B := q)
    (X := σ 1 (q ^ b)) (Y := usigma (q ^ b)) (C := r - 1) (D := r)
    (P := σ 1 (r ^ c)) (Q := usigma (r ^ c)) (S := 26) (T := 31)
    hqcap hrcap hcap (by omega : 0 < q) huq (by decide : 0 < 31)
  have hL : 5 * σ 1 (q ^ b) * σ 1 (r ^ c) * 31 =
      5 * 31 * σ 1 (q ^ b) * σ 1 (r ^ c) := by ring
  have hR : 6 * usigma (q ^ b) * usigma (r ^ c) * 26 =
      6 * 26 * usigma (q ^ b) * usigma (r ^ c) := by ring
  rw [← hL, ← hR]
  exact hthis

/-- Leftover `6/5` cannot be three squareful primes `5^2 < q < r` with
`313 ≤ q` times a squarefree coprime factor. -/
lemma not_five_sigma_of_three_sq_primes_five_sq_two_large {m q r : ℕ}
    (hm : m ≠ 0) (hq : q.Prime) (hr : r.Prime) (hq313 : 313 ≤ q) (hqr : q < r)
    (h : 5 * σ 1 m = 6 * usigma m)
    (hk5 : padicValNat 5 m = 2) (hkq : 2 ≤ padicValNat q m)
    (hkr : 2 ≤ padicValNat r m)
    (hs : Squarefree (ordCompl[r] (ordCompl[q] (ordCompl[5] m)))) : False := by
  have hp5 : Nat.Prime 5 := Nat.prime_five
  have hpq_ne : (5 : ℕ) ≠ q :=
    Nat.ne_of_lt (lt_of_lt_of_le (by decide : 5 < 313) hq313)
  have hpr_ne : (5 : ℕ) ≠ r :=
    Nat.ne_of_lt (lt_of_lt_of_le (lt_of_lt_of_le (by decide : 5 < 313) hq313)
      (Nat.le_of_lt hqr))
  have hqr_ne : q ≠ r := Nat.ne_of_lt hqr
  have heq := five_sigma_eq_six_of_three_squareful hm hp5 hq hr hpq_ne hpr_ne
    hqr_ne h hs
  have hproj_p : ordProj[5] m = 5 ^ padicValNat 5 m := by
    simp [Nat.factorization_def m hp5]
  have hproj_q : ordProj[q] (ordCompl[5] m) =
      q ^ padicValNat q (ordCompl[5] m) := by
    simp [Nat.factorization_def (ordCompl[5] m) hq]
  have hproj_r : ordProj[r] (ordCompl[q] (ordCompl[5] m)) =
      r ^ padicValNat r (ordCompl[q] (ordCompl[5] m)) := by
    simp [Nat.factorization_def (ordCompl[q] (ordCompl[5] m)) hr]
  rw [hproj_r, padicValNat_ordCompl_of_ne hr hqr_ne,
    padicValNat_ordCompl_of_ne hr hpr_ne, hproj_q,
    padicValNat_ordCompl_of_ne hq hpq_ne, hproj_p, hk5] at heq
  exact (five_sigma_lt_six_usigma_five_sq_two_large hq hr hq313 hqr
    (by omega) (by omega)).ne heq

lemma five_seven_q_r_cap {q r : ℕ} (hq : 71 ≤ q) (hqr : q < r) :
    5 * 7 * q * r ≤ 6 * 6 * (q - 1) * (r - 1) := by
  have hq1 : 1 ≤ q := by omega
  have hr1 : 1 ≤ r := by omega
  have hq' : (71 : ℤ) ≤ q := Int.ofNat_le.mpr hq
  have hr' : (q : ℤ) + 1 ≤ r := Int.ofNat_le.mpr (Nat.succ_le_of_lt hqr)
  have hL : ((5 * 7 * q * r : ℕ) : ℤ) =
      (5 : ℤ) * 7 * q * r := by
    rw [Nat.cast_mul, Nat.cast_mul, Nat.cast_mul]; rfl
  have hR : ((6 * 6 * (q - 1) * (r - 1) : ℕ) : ℤ) =
      (6 : ℤ) * 6 * ((q : ℤ) - 1) * ((r : ℤ) - 1) := by
    rw [Nat.cast_mul, Nat.cast_mul, Nat.cast_mul, Nat.cast_sub hq1, Nat.cast_sub hr1]
    rfl
  have : (5 : ℤ) * 7 * q * r ≤ 6 * 6 * (q - 1) * (r - 1) := by nlinarith
  exact Nat.cast_le.mp (by rw [hL, hR]; exact this)

/-- `{7^a, q^b, r^c}` undershoots leftover `6/5` for `71 ≤ q < r`. -/
lemma five_sigma_lt_six_usigma_seven_two_large {q r a b c : ℕ}
    (hq : q.Prime) (hr : r.Prime) (hq71 : 71 ≤ q) (hqr : q < r)
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    5 * σ 1 (7 ^ a) * σ 1 (q ^ b) * σ 1 (r ^ c) <
      6 * usigma (7 ^ a) * usigma (q ^ b) * usigma (r ^ c) := by
  have hp7 : Nat.Prime 7 := by decide
  have h7 := sigma_lt_cap_usigma hp7 ha
  have hqcap := sigma_lt_cap_usigma hq hb
  have hrcap := sigma_lt_cap_usigma hr hc
  have hu7 : 0 < usigma (7 ^ a) := by
    rw [usigma_prime_pow hp7 ha]
    exact Nat.add_pos_left (by decide : 0 < 1) _
  have huq : 0 < usigma (q ^ b) := by
    rw [usigma_prime_pow hq hb]
    exact Nat.add_pos_left (by decide : 0 < 1) _
  have hcap := five_seven_q_r_cap hq71 hqr
  have := six_five_of_three_caps (A := 6) (B := 7) (X := σ 1 (7 ^ a))
    (Y := usigma (7 ^ a)) (C := q - 1) (D := q) (P := σ 1 (q ^ b))
    (Q := usigma (q ^ b)) (E := r - 1) (F := r) (R := σ 1 (r ^ c))
    (S := usigma (r ^ c)) h7 hqcap hrcap hcap (by decide : 0 < 7) hu7
    hq.pos huq
  simpa [mul_assoc] using this

/-- Leftover `6/5` cannot be three squareful primes `7 < q < r` with
`71 ≤ q` times a squarefree coprime factor. -/
lemma not_five_sigma_of_three_sq_primes_seven_two_large {m q r : ℕ}
    (hm : m ≠ 0) (hq : q.Prime) (hr : r.Prime) (hq71 : 71 ≤ q) (hqr : q < r)
    (h : 5 * σ 1 m = 6 * usigma m)
    (hk7 : 2 ≤ padicValNat 7 m) (hkq : 2 ≤ padicValNat q m)
    (hkr : 2 ≤ padicValNat r m)
    (hs : Squarefree (ordCompl[r] (ordCompl[q] (ordCompl[7] m)))) : False := by
  have hp7 : Nat.Prime 7 := by decide
  have hpq_ne : (7 : ℕ) ≠ q :=
    Nat.ne_of_lt (lt_of_lt_of_le (by decide : 7 < 71) hq71)
  have hpr_ne : (7 : ℕ) ≠ r :=
    Nat.ne_of_lt (lt_of_lt_of_le (lt_of_lt_of_le (by decide : 7 < 71) hq71)
      (Nat.le_of_lt hqr))
  have hqr_ne : q ≠ r := Nat.ne_of_lt hqr
  have heq := five_sigma_eq_six_of_three_squareful hm hp7 hq hr hpq_ne hpr_ne
    hqr_ne h hs
  have hproj_p : ordProj[7] m = 7 ^ padicValNat 7 m := by
    simp [Nat.factorization_def m hp7]
  have hproj_q : ordProj[q] (ordCompl[7] m) =
      q ^ padicValNat q (ordCompl[7] m) := by
    simp [Nat.factorization_def (ordCompl[7] m) hq]
  have hproj_r : ordProj[r] (ordCompl[q] (ordCompl[7] m)) =
      r ^ padicValNat r (ordCompl[q] (ordCompl[7] m)) := by
    simp [Nat.factorization_def (ordCompl[q] (ordCompl[7] m)) hr]
  rw [hproj_r, padicValNat_ordCompl_of_ne hr hqr_ne,
    padicValNat_ordCompl_of_ne hr hpr_ne, hproj_q,
    padicValNat_ordCompl_of_ne hq hpq_ne, hproj_p] at heq
  exact (five_sigma_lt_six_usigma_seven_two_large hq hr hq71 hqr
    (by omega) (by omega) (by omega)).ne heq

/-- `{7^a, q^b, r^c}` overshoots leftover `6/5` whenever `11 ≤ q ≤ 17`, because
the two-prime squares `{7^2, q^2}` already overshoot. -/
lemma seven_sq_q_pow_r_pow_ge_two_overshoot_six_five {q r a b c : ℕ}
    (hq : q.Prime) (hr : r.Prime)
    (h11 : 11 ≤ q) (h17 : q ≤ 17)
    (ha : 2 ≤ a) (hb : 2 ≤ b) (_hc : 0 < c) :
    6 * usigma (7 ^ a) * usigma (q ^ b) * usigma (r ^ c) <
      5 * σ 1 (7 ^ a) * σ 1 (q ^ b) * σ 1 (r ^ c) := by
  have hover := seven_sq_q_pow_ge_two_overshoot_six_five hq h11 h17 ha hb
  have h := six_five_overshoot_mul (s := usigma (7 ^ a) * usigma (q ^ b))
      (t := σ 1 (7 ^ a) * σ 1 (q ^ b)) (n := r ^ c)
      (Nat.pow_pos hr.pos).ne' (by simpa [mul_assoc] using hover)
  simpa [mul_assoc] using h

/-- Leftover `6/5` cannot be three squareful primes `7 < q < r` with
`11 ≤ q ≤ 17` times a squarefree coprime factor. -/
lemma not_five_sigma_of_three_sq_primes_seven_q_le_seventeen {m q r : ℕ}
    (hm : m ≠ 0) (hq : q.Prime) (hr : r.Prime)
    (hq11 : 11 ≤ q) (hq17 : q ≤ 17) (hqr : q < r)
    (h : 5 * σ 1 m = 6 * usigma m)
    (hk7 : 2 ≤ padicValNat 7 m) (hkq : 2 ≤ padicValNat q m)
    (hkr : 2 ≤ padicValNat r m)
    (hs : Squarefree (ordCompl[r] (ordCompl[q] (ordCompl[7] m)))) : False := by
  have hp7 : Nat.Prime 7 := by decide
  have hpq_ne : (7 : ℕ) ≠ q :=
    Nat.ne_of_lt (lt_of_lt_of_le (by decide : 7 < 11) hq11)
  have hpr_ne : (7 : ℕ) ≠ r :=
    Nat.ne_of_lt (lt_of_lt_of_le (by decide : 7 < 11)
      (le_trans hq11 (Nat.le_of_lt hqr)))
  have hqr_ne : q ≠ r := Nat.ne_of_lt hqr
  have heq := five_sigma_eq_six_of_three_squareful hm hp7 hq hr hpq_ne hpr_ne
    hqr_ne h hs
  have hproj_p : ordProj[7] m = 7 ^ padicValNat 7 m := by
    simp [Nat.factorization_def m hp7]
  have hproj_q : ordProj[q] (ordCompl[7] m) =
      q ^ padicValNat q (ordCompl[7] m) := by
    simp [Nat.factorization_def (ordCompl[7] m) hq]
  have hproj_r : ordProj[r] (ordCompl[q] (ordCompl[7] m)) =
      r ^ padicValNat r (ordCompl[q] (ordCompl[7] m)) := by
    simp [Nat.factorization_def (ordCompl[q] (ordCompl[7] m)) hr]
  rw [hproj_r, padicValNat_ordCompl_of_ne hr hqr_ne,
    padicValNat_ordCompl_of_ne hr hpr_ne, hproj_q,
    padicValNat_ordCompl_of_ne hq hpq_ne, hproj_p] at heq
  have hover :=
    seven_sq_q_pow_r_pow_ge_two_overshoot_six_five (c := padicValNat r m)
      hq hr hq11 hq17 hk7 hkq
      (lt_of_lt_of_le (by decide : (0 : ℕ) < 2) hkr)
  rw [← heq] at hover
  exact lt_irrefl _ hover

lemma forty_nine_nineteen_sq_r_sq_overshoot_six_five {r : ℕ}
    (hr : r.Prime) (h23 : 23 ≤ r) (h7237 : r ≤ 7237) :
    6 * usigma (7 ^ 2) * usigma (19 ^ 2) * usigma (r ^ 2) <
      5 * σ 1 (7 ^ 2) * σ 1 (19 ^ 2) * σ 1 (r ^ 2) := by
  have hp7 : Nat.Prime 7 := by decide
  have hp19 : Nat.Prime 19 := by decide
  have hσ7 : σ 1 (7 ^ 2) = 57 := by
    rw [sigma_prime_pow_two hp7]
    decide
  have hu7 : usigma (7 ^ 2) = 50 := by
    simpa using usigma_prime_pow hp7 (by decide : 0 < 2)
  have hσ19 : σ 1 (19 ^ 2) = 381 := by
    rw [sigma_prime_pow_two hp19]
    decide
  have hu19 : usigma (19 ^ 2) = 362 := by
    simpa using usigma_prime_pow hp19 (by decide : 0 < 2)
  rw [hσ7, hu7, hσ19, hu19,
    sigma_prime_pow_two hr, usigma_prime_pow hr (by decide : 0 < 2)]
  have hsq : r ^ 2 ≤ 7237 * r := by
    rw [pow_two]
    exact Nat.mul_le_mul_right r h7237
  have h15 : 15 * (1 + r ^ 2) < 108585 * r := by
    have h1 : 15 * (1 + r ^ 2) ≤ 15 * (1 + 7237 * r) :=
      Nat.mul_le_mul_left 15 (Nat.add_le_add_left hsq 1)
    have h2 : 15 * (1 + 7237 * r) = 15 + 108555 * r := by
      have : 15 * 7237 = 108555 := by decide
      ring
    have h3 : 15 + 108555 * r < 108585 * r := by
      have : 15 < 30 * r :=
        lt_of_lt_of_le (by decide : 15 < 690) (Nat.mul_le_mul_left 30 h23)
      omega
    calc
      15 * (1 + r ^ 2) ≤ 15 * (1 + 7237 * r) := h1
      _ = 15 + 108555 * r := h2
      _ < 108585 * r := h3
  have hL : 6 * 50 * 362 * (1 + r ^ 2) = 108600 * (1 + r ^ 2) := by ring
  have hR : 5 * 57 * 381 * (1 + r + r ^ 2) = 108585 * (1 + r + r ^ 2) := by ring
  have hmain : 108600 * (1 + r ^ 2) < 108585 * (1 + r + r ^ 2) := by
    have h1 : 108600 * (1 + r ^ 2) =
        108585 * (1 + r ^ 2) + 15 * (1 + r ^ 2) := by ring
    have h2 : 108585 * (1 + r + r ^ 2) =
        108585 * (1 + r ^ 2) + 108585 * r := by ring
    rw [h1, h2]
    exact Nat.add_lt_add_left h15 _
  rw [hL, hR]
  exact hmain

lemma seven_nineteen_r_pow_ge_two_overshoot_six_five {r a b c : ℕ}
    (hr : r.Prime) (h23 : 23 ≤ r) (h7237 : r ≤ 7237)
    (ha : 2 ≤ a) (hb : 2 ≤ b) (hc : 2 ≤ c) :
    6 * usigma (7 ^ a) * usigma (19 ^ b) * usigma (r ^ c) <
      5 * σ 1 (7 ^ a) * σ 1 (19 ^ b) * σ 1 (r ^ c) :=
  six_five_overshoot_mono_three (by decide : Nat.Prime 7)
    (by decide : Nat.Prime 19) hr
    (by decide : 0 < 2) (by decide : 0 < 2) (by decide : 0 < 2)
    ha hb hc (forty_nine_nineteen_sq_r_sq_overshoot_six_five hr h23 h7237)

lemma seven_cube_nineteen_r_overshoot_six_five {r a b c : ℕ}
    (hr : r.Prime) (ha : 3 ≤ a) (hb : 2 ≤ b) (_hc : 0 < c) :
    6 * usigma (7 ^ a) * usigma (19 ^ b) * usigma (r ^ c) <
      5 * σ 1 (7 ^ a) * σ 1 (19 ^ b) * σ 1 (r ^ c) := by
  have hover := six_five_overshoot_mono_two (by decide : Nat.Prime 7)
    (by decide : Nat.Prime 19)
    (by decide : 0 < 3) (by decide : 0 < 2) ha hb
    seven_cube_nineteen_sq_overshoot_six_five
  have h := six_five_overshoot_mul (s := usigma (7 ^ a) * usigma (19 ^ b))
      (t := σ 1 (7 ^ a) * σ 1 (19 ^ b)) (n := r ^ c)
      (Nat.pow_pos hr.pos).ne' (by simpa [mul_assoc] using hover)
  simpa [mul_assoc] using h

lemma forty_nine_nineteen_cube_r_overshoot_six_five {r a b c : ℕ}
    (hr : r.Prime) (ha : 2 ≤ a) (hb : 3 ≤ b) (_hc : 0 < c) :
    6 * usigma (7 ^ a) * usigma (19 ^ b) * usigma (r ^ c) <
      5 * σ 1 (7 ^ a) * σ 1 (19 ^ b) * σ 1 (r ^ c) := by
  have hover := six_five_overshoot_mono_two (by decide : Nat.Prime 7)
    (by decide : Nat.Prime 19)
    (by decide : 0 < 2) (by decide : 0 < 3) ha hb
    forty_nine_nineteen_cube_overshoot_six_five
  have h := six_five_overshoot_mul (s := usigma (7 ^ a) * usigma (19 ^ b))
      (t := σ 1 (7 ^ a) * σ 1 (19 ^ b)) (n := r ^ c)
      (Nat.pow_pos hr.pos).ne' (by simpa [mul_assoc] using hover)
  simpa [mul_assoc] using h

lemma five_mul_forty_nine_nineteen_sq_cap {r : ℕ} (hr : 7243 ≤ r) :
    5 * r * 57 * 381 ≤ 6 * (r - 1) * 50 * 362 := by
  have h15 : 108600 ≤ 15 * r := by
    have hmul : 15 * 7243 ≤ 15 * r := Nat.mul_le_mul_left 15 hr
    have hnum : 15 * 7243 = 108645 := by decide
    omega
  have hL : 5 * r * 57 * 381 = 108585 * r := by ring
  have hR : 6 * (r - 1) * 50 * 362 = 108600 * (r - 1) := by ring
  have hmain : 108585 * r ≤ 108600 * (r - 1) := by
    have heq : 108585 * r + 15 * r = 108600 * r := by ring
    have hsub : 108585 * r = 108600 * r - 15 * r :=
      (Nat.sub_eq_of_eq_add heq.symm).symm
    have hle : 108600 * r - 15 * r ≤ 108600 * r - 108600 :=
      Nat.sub_le_sub_left h15 _
    have hrw : 108600 * r - 108600 = 108600 * (r - 1) := by
      simpa using (Nat.mul_sub_left_distrib 108600 r 1).symm
    calc
      108585 * r = 108600 * r - 15 * r := hsub
      _ ≤ 108600 * r - 108600 := hle
      _ = 108600 * (r - 1) := hrw
  rw [hL, hR]
  exact hmain

lemma five_sigma_lt_six_usigma_seven_sq_nineteen_sq_large {r k : ℕ}
    (hr : r.Prime) (hr7243 : 7243 ≤ r) (hk : 0 < k) :
    5 * σ 1 (7 ^ 2) * σ 1 (19 ^ 2) * σ 1 (r ^ k) <
      6 * usigma (7 ^ 2) * usigma (19 ^ 2) * usigma (r ^ k) := by
  have hp7 : Nat.Prime 7 := by decide
  have hp19 : Nat.Prime 19 := by decide
  have hσ7 : σ 1 (7 ^ 2) = 57 := by
    rw [sigma_prime_pow_two hp7]
    decide
  have hu7 : usigma (7 ^ 2) = 50 := by
    simpa using usigma_prime_pow hp7 (by decide : 0 < 2)
  have hσ19 : σ 1 (19 ^ 2) = 381 := by
    rw [sigma_prime_pow_two hp19]
    decide
  have hu19 : usigma (19 ^ 2) = 362 := by
    simpa using usigma_prime_pow hp19 (by decide : 0 < 2)
  rw [hσ7, hu7, hσ19, hu19]
  have hcp := sigma_lt_cap_usigma hr hk
  have hthis := six_five_of_cap_times_const (A := r - 1) (B := r)
    (X := σ 1 (r ^ k)) (Y := usigma (r ^ k)) (S := 50 * 362) (T := 57 * 381)
    hcp (by
      have hL : 5 * r * (57 * 381) = 5 * r * 57 * 381 := by ring
      have hR : 6 * (r - 1) * (50 * 362) = 6 * (r - 1) * 50 * 362 := by ring
      rw [hL, hR]
      exact five_mul_forty_nine_nineteen_sq_cap hr7243)
    (by decide : 0 < 57 * 381)
  convert hthis using 1 <;> ring

lemma prime_ge_seven_two_three_eight_ge_seven_two_four_three {p : ℕ}
    (hp : p.Prime) (h : 7238 ≤ p) : 7243 ≤ p := by
  have hmem : p = 7238 ∨ p = 7239 ∨ p = 7240 ∨ p = 7241 ∨ p = 7242 ∨
      7243 ≤ p := by omega
  rcases hmem with rfl | rfl | rfl | rfl | rfl | h7243
  · exact False.elim (not_prime_of_eq_mul (rfl : 7238 = 2 * 3619)
      (by decide : (2 : ℕ) ≠ 1) (by decide : (3619 : ℕ) ≠ 1) hp)
  · exact False.elim (not_prime_of_eq_mul (rfl : 7239 = 3 * 2413)
      (by decide : (3 : ℕ) ≠ 1) (by decide : (2413 : ℕ) ≠ 1) hp)
  · exact False.elim (not_prime_of_eq_mul (rfl : 7240 = 2 * 3620)
      (by decide : (2 : ℕ) ≠ 1) (by decide : (3620 : ℕ) ≠ 1) hp)
  · exact False.elim (not_prime_of_eq_mul (rfl : 7241 = 13 * 557)
      (by decide : (13 : ℕ) ≠ 1) (by decide : (557 : ℕ) ≠ 1) hp)
  · exact False.elim (not_prime_of_eq_mul (rfl : 7242 = 2 * 3621)
      (by decide : (2 : ℕ) ≠ 1) (by decide : (3621 : ℕ) ≠ 1) hp)
  · exact h7243

/-- Leftover `6/5` cannot be three squareful primes `7,19,r` with
`r ≥ 23` times a squarefree coprime factor. -/
lemma not_five_sigma_of_three_sq_primes_seven_nineteen {m r : ℕ}
    (hm : m ≠ 0) (hr : r.Prime) (hr23 : 23 ≤ r)
    (h : 5 * σ 1 m = 6 * usigma m)
    (hk7 : 2 ≤ padicValNat 7 m) (hk19 : 2 ≤ padicValNat 19 m)
    (hkr : 2 ≤ padicValNat r m)
    (hs : Squarefree (ordCompl[r] (ordCompl[19] (ordCompl[7] m)))) : False := by
  have hp7 : Nat.Prime 7 := by decide
  have hp19 : Nat.Prime 19 := by decide
  have hpq_ne : (7 : ℕ) ≠ 19 := by decide
  have hpr_ne : (7 : ℕ) ≠ r :=
    Nat.ne_of_lt (lt_of_lt_of_le (by decide : 7 < 23) hr23)
  have hqr_ne : (19 : ℕ) ≠ r :=
    Nat.ne_of_lt (lt_of_lt_of_le (by decide : 19 < 23) hr23)
  have heq := five_sigma_eq_six_of_three_squareful hm hp7 hp19 hr hpq_ne hpr_ne
    hqr_ne h hs
  have hproj_p : ordProj[7] m = 7 ^ padicValNat 7 m := by
    simp [Nat.factorization_def m hp7]
  have hproj_q : ordProj[19] (ordCompl[7] m) =
      19 ^ padicValNat 19 (ordCompl[7] m) := by
    simp [Nat.factorization_def (ordCompl[7] m) hp19]
  have hproj_r : ordProj[r] (ordCompl[19] (ordCompl[7] m)) =
      r ^ padicValNat r (ordCompl[19] (ordCompl[7] m)) := by
    simp [Nat.factorization_def (ordCompl[19] (ordCompl[7] m)) hr]
  rw [hproj_r, padicValNat_ordCompl_of_ne hr hqr_ne,
    padicValNat_ordCompl_of_ne hr hpr_ne, hproj_q,
    padicValNat_ordCompl_of_ne hp19 hpq_ne, hproj_p] at heq
  rcases eq_or_lt_of_le hk7 with h7eq | h73
  · rw [← h7eq] at heq
    rcases eq_or_lt_of_le hk19 with h19eq | h193
    · rw [← h19eq] at heq
      rcases le_or_gt r 7237 with hsmall | hlarge
      · have hover := seven_nineteen_r_pow_ge_two_overshoot_six_five hr hr23
          hsmall (le_refl _) (le_refl _) hkr
        rw [← heq] at hover
        exact lt_irrefl _ hover
      · have hr7243 : 7243 ≤ r :=
          prime_ge_seven_two_three_eight_ge_seven_two_four_three hr
            (Nat.succ_le_of_lt hlarge)
        exact (five_sigma_lt_six_usigma_seven_sq_nineteen_sq_large hr hr7243
          (by omega)).ne heq
    · have hover := forty_nine_nineteen_cube_r_overshoot_six_five (c := padicValNat r m)
        hr (le_refl _) (Nat.succ_le_of_lt h193)
        (lt_of_lt_of_le (by decide : (0 : ℕ) < 2) hkr)
      rw [← heq] at hover
      exact lt_irrefl _ hover
  · have hover := seven_cube_nineteen_r_overshoot_six_five (c := padicValNat r m)
      hr (Nat.succ_le_of_lt h73) hk19
      (lt_of_lt_of_le (by decide : (0 : ℕ) < 2) hkr)
    rw [← heq] at hover
    exact lt_irrefl _ hover

lemma five_eleven_twenty_three_twenty_nine_cap :
    5 * 11 * 23 * 29 ≤ 6 * 10 * 22 * 28 := by decide

/-- Euler `p/(p-1) · q/(q-1) · r/(r-1) ≤ 6/5` for `11 ≤ p`, `23 ≤ q`,
and `29 ≤ r`. -/
lemma five_p_q_r_cap_ge_eleven_twenty_three {p q r : ℕ}
    (hp : 11 ≤ p) (hq : 23 ≤ q) (hr : 29 ≤ r) :
    5 * p * q * r ≤ 6 * (p - 1) * (q - 1) * (r - 1) := by
  have hp10 : p * 10 ≤ 11 * (p - 1) := cap_ratio_anti (by decide : 2 ≤ 11) hp
  have hq22 : q * 22 ≤ 23 * (q - 1) := cap_ratio_anti (by decide : 2 ≤ 23) hq
  have hr28 : r * 28 ≤ 29 * (r - 1) := cap_ratio_anti (by decide : 2 ≤ 29) hr
  have hprod : p * q * r * 10 * 22 * 28 ≤
      11 * 23 * 29 * (p - 1) * (q - 1) * (r - 1) := by
    have h1 : p * 10 * (q * 22) * (r * 28) ≤
        11 * (p - 1) * (23 * (q - 1)) * (29 * (r - 1)) :=
      Nat.mul_le_mul (Nat.mul_le_mul hp10 hq22) hr28
    simpa [mul_assoc, mul_left_comm, mul_comm] using h1
  have h5 : 5 * p * q * r * 10 * 22 * 28 ≤
      5 * 11 * 23 * 29 * (p - 1) * (q - 1) * (r - 1) := by
    simpa [mul_assoc, mul_left_comm, mul_comm] using Nat.mul_le_mul_left 5 hprod
  have h6 : 5 * 11 * 23 * 29 * (p - 1) * (q - 1) * (r - 1) ≤
      6 * 10 * 22 * 28 * (p - 1) * (q - 1) * (r - 1) := by
    simpa [mul_assoc, mul_left_comm, mul_comm] using
      Nat.mul_le_mul_right ((p - 1) * (q - 1) * (r - 1))
        five_eleven_twenty_three_twenty_nine_cap
  have hchain : 5 * p * q * r * 10 * 22 * 28 ≤
      6 * 10 * 22 * 28 * (p - 1) * (q - 1) * (r - 1) :=
    le_trans h5 (by simpa [mul_assoc, mul_left_comm, mul_comm] using h6)
  have hcancel : 10 * 22 * 28 * (5 * p * q * r) ≤
      10 * 22 * 28 * (6 * (p - 1) * (q - 1) * (r - 1)) := by
    have h1 : 10 * 22 * 28 * (5 * p * q * r) =
        5 * p * q * r * 10 * 22 * 28 := by ring
    have h2 : 10 * 22 * 28 * (6 * (p - 1) * (q - 1) * (r - 1)) =
        6 * 10 * 22 * 28 * (p - 1) * (q - 1) * (r - 1) := by ring
    rw [h1, h2]
    exact hchain
  exact Nat.le_of_mul_le_mul_left hcancel (by decide : 0 < 10 * 22 * 28)

/-- Three squareful primes `11 ≤ p < q < r` with `q ≥ 23` undershoot leftover
`6/5`. -/
lemma five_sigma_lt_six_usigma_three_ge_eleven_twenty_three {p q r a b c : ℕ}
    (hp : p.Prime) (hq : q.Prime) (hr : r.Prime)
    (hp11 : 11 ≤ p) (hq23 : 23 ≤ q) (hr29 : 29 ≤ r)
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    5 * σ 1 (p ^ a) * σ 1 (q ^ b) * σ 1 (r ^ c) <
      6 * usigma (p ^ a) * usigma (q ^ b) * usigma (r ^ c) := by
  have hcp := sigma_lt_cap_usigma hp ha
  have hcq := sigma_lt_cap_usigma hq hb
  have hcr := sigma_lt_cap_usigma hr hc
  have hup : 0 < usigma (p ^ a) := by
    rw [usigma_prime_pow hp ha]
    exact Nat.add_pos_left (by decide : 0 < 1) _
  have huq : 0 < usigma (q ^ b) := by
    rw [usigma_prime_pow hq hb]
    exact Nat.add_pos_left (by decide : 0 < 1) _
  have hcap := five_p_q_r_cap_ge_eleven_twenty_three hp11 hq23 hr29
  have := six_five_of_three_caps (A := p - 1) (B := p) (X := σ 1 (p ^ a))
    (Y := usigma (p ^ a)) (C := q - 1) (D := q) (P := σ 1 (q ^ b))
    (Q := usigma (q ^ b)) (E := r - 1) (F := r) (R := σ 1 (r ^ c))
    (S := usigma (r ^ c)) hcp hcq hcr hcap hp.pos hup hq.pos huq
  simpa [mul_assoc] using this

/-- Leftover `6/5` cannot be three squareful primes `11 ≤ p < q < r` with
`q ≥ 23` times a squarefree coprime factor. -/
lemma not_five_sigma_of_three_sq_primes_ge_eleven_twenty_three {m p q r : ℕ}
    (hm : m ≠ 0) (hp : p.Prime) (hq : q.Prime) (hr : r.Prime)
    (hpq : p < q) (hqr : q < r) (hp11 : 11 ≤ p) (hq23 : 23 ≤ q)
    (h : 5 * σ 1 m = 6 * usigma m)
    (hkp : 2 ≤ padicValNat p m) (hkq : 2 ≤ padicValNat q m)
    (hkr : 2 ≤ padicValNat r m)
    (hs : Squarefree (ordCompl[r] (ordCompl[q] (ordCompl[p] m)))) : False := by
  have hpq_ne : p ≠ q := Nat.ne_of_lt hpq
  have hpr_ne : p ≠ r := Nat.ne_of_lt (lt_trans hpq hqr)
  have hqr_ne : q ≠ r := Nat.ne_of_lt hqr
  have hr29 : 29 ≤ r :=
    prime_ge_twenty_four_ge_twenty_nine hr (by omega)
  have heq := five_sigma_eq_six_of_three_squareful hm hp hq hr hpq_ne hpr_ne
    hqr_ne h hs
  have hproj_p : ordProj[p] m = p ^ padicValNat p m := by
    simp [Nat.factorization_def m hp]
  have hproj_q : ordProj[q] (ordCompl[p] m) =
      q ^ padicValNat q (ordCompl[p] m) := by
    simp [Nat.factorization_def (ordCompl[p] m) hq]
  have hproj_r : ordProj[r] (ordCompl[q] (ordCompl[p] m)) =
      r ^ padicValNat r (ordCompl[q] (ordCompl[p] m)) := by
    simp [Nat.factorization_def (ordCompl[q] (ordCompl[p] m)) hr]
  rw [hproj_r, padicValNat_ordCompl_of_ne hr hqr_ne,
    padicValNat_ordCompl_of_ne hr hpr_ne, hproj_q,
    padicValNat_ordCompl_of_ne hq hpq_ne, hproj_p] at heq
  exact (five_sigma_lt_six_usigma_three_ge_eleven_twenty_three hp hq hr hp11
    hq23 hr29 (by omega) (by omega) (by omega)).ne heq

lemma five_thirteen_nineteen_twenty_three_cap :
    5 * 13 * 19 * 23 ≤ 6 * 12 * 18 * 22 := by decide

/-- Euler `p/(p-1) · q/(q-1) · r/(r-1) ≤ 6/5` for `13 ≤ p`, `19 ≤ q`,
and `23 ≤ r`. -/
lemma five_p_q_r_cap_ge_thirteen_nineteen {p q r : ℕ}
    (hp : 13 ≤ p) (hq : 19 ≤ q) (hr : 23 ≤ r) :
    5 * p * q * r ≤ 6 * (p - 1) * (q - 1) * (r - 1) := by
  have hp12 : p * 12 ≤ 13 * (p - 1) := cap_ratio_anti (by decide : 2 ≤ 13) hp
  have hq18 : q * 18 ≤ 19 * (q - 1) := cap_ratio_anti (by decide : 2 ≤ 19) hq
  have hr22 : r * 22 ≤ 23 * (r - 1) := cap_ratio_anti (by decide : 2 ≤ 23) hr
  have hprod : p * q * r * 12 * 18 * 22 ≤
      13 * 19 * 23 * (p - 1) * (q - 1) * (r - 1) := by
    have h1 : p * 12 * (q * 18) * (r * 22) ≤
        13 * (p - 1) * (19 * (q - 1)) * (23 * (r - 1)) :=
      Nat.mul_le_mul (Nat.mul_le_mul hp12 hq18) hr22
    simpa [mul_assoc, mul_left_comm, mul_comm] using h1
  have h5 : 5 * p * q * r * 12 * 18 * 22 ≤
      5 * 13 * 19 * 23 * (p - 1) * (q - 1) * (r - 1) := by
    simpa [mul_assoc, mul_left_comm, mul_comm] using Nat.mul_le_mul_left 5 hprod
  have h6 : 5 * 13 * 19 * 23 * (p - 1) * (q - 1) * (r - 1) ≤
      6 * 12 * 18 * 22 * (p - 1) * (q - 1) * (r - 1) := by
    simpa [mul_assoc, mul_left_comm, mul_comm] using
      Nat.mul_le_mul_right ((p - 1) * (q - 1) * (r - 1))
        five_thirteen_nineteen_twenty_three_cap
  have hchain : 5 * p * q * r * 12 * 18 * 22 ≤
      6 * 12 * 18 * 22 * (p - 1) * (q - 1) * (r - 1) :=
    le_trans h5 (by simpa [mul_assoc, mul_left_comm, mul_comm] using h6)
  have hcancel : 12 * 18 * 22 * (5 * p * q * r) ≤
      12 * 18 * 22 * (6 * (p - 1) * (q - 1) * (r - 1)) := by
    have h1 : 12 * 18 * 22 * (5 * p * q * r) =
        5 * p * q * r * 12 * 18 * 22 := by ring
    have h2 : 12 * 18 * 22 * (6 * (p - 1) * (q - 1) * (r - 1)) =
        6 * 12 * 18 * 22 * (p - 1) * (q - 1) * (r - 1) := by ring
    rw [h1, h2]
    exact hchain
  exact Nat.le_of_mul_le_mul_left hcancel (by decide : 0 < 12 * 18 * 22)

/-- Three squareful primes `13 ≤ p < q < r` with `q ≥ 19` undershoot leftover
`6/5`. -/
lemma five_sigma_lt_six_usigma_three_ge_thirteen_nineteen {p q r a b c : ℕ}
    (hp : p.Prime) (hq : q.Prime) (hr : r.Prime)
    (hp13 : 13 ≤ p) (hq19 : 19 ≤ q) (hr23 : 23 ≤ r)
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    5 * σ 1 (p ^ a) * σ 1 (q ^ b) * σ 1 (r ^ c) <
      6 * usigma (p ^ a) * usigma (q ^ b) * usigma (r ^ c) := by
  have hcp := sigma_lt_cap_usigma hp ha
  have hcq := sigma_lt_cap_usigma hq hb
  have hcr := sigma_lt_cap_usigma hr hc
  have hup : 0 < usigma (p ^ a) := by
    rw [usigma_prime_pow hp ha]
    exact Nat.add_pos_left (by decide : 0 < 1) _
  have huq : 0 < usigma (q ^ b) := by
    rw [usigma_prime_pow hq hb]
    exact Nat.add_pos_left (by decide : 0 < 1) _
  have hcap := five_p_q_r_cap_ge_thirteen_nineteen hp13 hq19 hr23
  have := six_five_of_three_caps (A := p - 1) (B := p) (X := σ 1 (p ^ a))
    (Y := usigma (p ^ a)) (C := q - 1) (D := q) (P := σ 1 (q ^ b))
    (Q := usigma (q ^ b)) (E := r - 1) (F := r) (R := σ 1 (r ^ c))
    (S := usigma (r ^ c)) hcp hcq hcr hcap hp.pos hup hq.pos huq
  simpa [mul_assoc] using this

/-- Leftover `6/5` cannot be three squareful primes `13 ≤ p < q < r` with
`q ≥ 19` times a squarefree coprime factor. -/
lemma not_five_sigma_of_three_sq_primes_ge_thirteen_nineteen {m p q r : ℕ}
    (hm : m ≠ 0) (hp : p.Prime) (hq : q.Prime) (hr : r.Prime)
    (hpq : p < q) (hqr : q < r) (hp13 : 13 ≤ p) (hq19 : 19 ≤ q)
    (h : 5 * σ 1 m = 6 * usigma m)
    (hkp : 2 ≤ padicValNat p m) (hkq : 2 ≤ padicValNat q m)
    (hkr : 2 ≤ padicValNat r m)
    (hs : Squarefree (ordCompl[r] (ordCompl[q] (ordCompl[p] m)))) : False := by
  have hpq_ne : p ≠ q := Nat.ne_of_lt hpq
  have hpr_ne : p ≠ r := Nat.ne_of_lt (lt_trans hpq hqr)
  have hqr_ne : q ≠ r := Nat.ne_of_lt hqr
  have hr23 : 23 ≤ r :=
    prime_ge_twenty_ge_twenty_three hr (by omega)
  have heq := five_sigma_eq_six_of_three_squareful hm hp hq hr hpq_ne hpr_ne
    hqr_ne h hs
  have hproj_p : ordProj[p] m = p ^ padicValNat p m := by
    simp [Nat.factorization_def m hp]
  have hproj_q : ordProj[q] (ordCompl[p] m) =
      q ^ padicValNat q (ordCompl[p] m) := by
    simp [Nat.factorization_def (ordCompl[p] m) hq]
  have hproj_r : ordProj[r] (ordCompl[q] (ordCompl[p] m)) =
      r ^ padicValNat r (ordCompl[q] (ordCompl[p] m)) := by
    simp [Nat.factorization_def (ordCompl[q] (ordCompl[p] m)) hr]
  rw [hproj_r, padicValNat_ordCompl_of_ne hr hqr_ne,
    padicValNat_ordCompl_of_ne hr hpr_ne, hproj_q,
    padicValNat_ordCompl_of_ne hq hpq_ne, hproj_p] at heq
  exact (five_sigma_lt_six_usigma_three_ge_thirteen_nineteen hp hq hr hp13
    hq19 hr23 (by omega) (by omega) (by omega)).ne heq

lemma five_eleven_nineteen_cap {p : ℕ} (hp : 31 ≤ p) :
    5 * 11 * 19 * p ≤ 6 * 10 * 18 * (p - 1) := by
  have hp1 : 1 ≤ p := by omega
  have hp' : (31 : ℤ) ≤ p := Int.ofNat_le.mpr hp
  have hL : ((5 * 11 * 19 * p : ℕ) : ℤ) =
      (5 : ℤ) * 11 * 19 * p := by
    rw [Nat.cast_mul, Nat.cast_mul, Nat.cast_mul]; rfl
  have hR : ((6 * 10 * 18 * (p - 1) : ℕ) : ℤ) =
      (6 : ℤ) * 10 * 18 * ((p : ℤ) - 1) := by
    rw [Nat.cast_mul, Nat.cast_mul, Nat.cast_mul, Nat.cast_sub hp1]
    rfl
  have : (5 : ℤ) * 11 * 19 * p ≤ 6 * 10 * 18 * (p - 1) := by nlinarith
  exact Nat.cast_le.mp (by rw [hL, hR]; exact this)

/-- `{11, 19, p}` with `p ≥ 31` cannot fill leftover `6/5`. -/
lemma five_sigma_lt_six_usigma_eleven_nineteen_large {p a b c : ℕ}
    (hp : p.Prime) (hp31 : 31 ≤ p) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    5 * σ 1 (11 ^ a) * σ 1 (19 ^ b) * σ 1 (p ^ c) <
      6 * usigma (11 ^ a) * usigma (19 ^ b) * usigma (p ^ c) := by
  have h11 := sigma_lt_cap_usigma (by decide : Nat.Prime 11) ha
  have h19 := sigma_lt_cap_usigma (by decide : Nat.Prime 19) hb
  have hpcap := sigma_lt_cap_usigma hp hc
  have hu11 : 0 < usigma (11 ^ a) := by
    rw [usigma_prime_pow (by decide : Nat.Prime 11) ha]
    exact Nat.add_pos_left (by decide : 0 < 1) _
  have hu19 : 0 < usigma (19 ^ b) := by
    rw [usigma_prime_pow (by decide : Nat.Prime 19) hb]
    exact Nat.add_pos_left (by decide : 0 < 1) _
  have hcap := five_eleven_nineteen_cap hp31
  have := six_five_of_three_caps (A := 10) (B := 11) (X := σ 1 (11 ^ a))
    (Y := usigma (11 ^ a)) (C := 18) (D := 19) (P := σ 1 (19 ^ b))
    (Q := usigma (19 ^ b)) (E := p - 1) (F := p) (R := σ 1 (p ^ c))
    (S := usigma (p ^ c)) h11 h19 hpcap hcap (by decide : 0 < 11) hu11
    (by decide : 0 < 19) hu19
  simpa [mul_assoc] using this

/-- Leftover `6/5` cannot be three squareful primes `11,19,p` with
`p ≥ 31` times a squarefree coprime factor. -/
lemma not_five_sigma_of_three_sq_primes_eleven_nineteen_large {m p : ℕ}
    (hm : m ≠ 0) (hp : p.Prime) (hp31 : 31 ≤ p)
    (h : 5 * σ 1 m = 6 * usigma m)
    (hk11 : 2 ≤ padicValNat 11 m) (hk19 : 2 ≤ padicValNat 19 m)
    (hkp : 2 ≤ padicValNat p m)
    (hs : Squarefree (ordCompl[p] (ordCompl[19] (ordCompl[11] m)))) : False := by
  have hp11 : Nat.Prime 11 := by decide
  have hp19 : Nat.Prime 19 := by decide
  have hpq_ne : (11 : ℕ) ≠ 19 := by decide
  have hpr_ne : (11 : ℕ) ≠ p :=
    Nat.ne_of_lt (lt_of_lt_of_le (by decide : 11 < 31) hp31)
  have hqr_ne : (19 : ℕ) ≠ p :=
    Nat.ne_of_lt (lt_of_lt_of_le (by decide : 19 < 31) hp31)
  have heq := five_sigma_eq_six_of_three_squareful hm hp11 hp19 hp hpq_ne hpr_ne
    hqr_ne h hs
  have hproj_p : ordProj[11] m = 11 ^ padicValNat 11 m := by
    simp [Nat.factorization_def m hp11]
  have hproj_q : ordProj[19] (ordCompl[11] m) =
      19 ^ padicValNat 19 (ordCompl[11] m) := by
    simp [Nat.factorization_def (ordCompl[11] m) hp19]
  have hproj_r : ordProj[p] (ordCompl[19] (ordCompl[11] m)) =
      p ^ padicValNat p (ordCompl[19] (ordCompl[11] m)) := by
    simp [Nat.factorization_def (ordCompl[19] (ordCompl[11] m)) hp]
  rw [hproj_r, padicValNat_ordCompl_of_ne hp hqr_ne,
    padicValNat_ordCompl_of_ne hp hpr_ne, hproj_q,
    padicValNat_ordCompl_of_ne hp19 hpq_ne, hproj_p] at heq
  exact (five_sigma_lt_six_usigma_eleven_nineteen_large hp hp31
    (by omega) (by omega) (by omega)).ne heq

/-- `ρ(121) ρ(13^3) ρ(p^2) > 6/5` for `47 ≤ p ≤ 59`. -/
lemma eleven_sq_thirteen_cube_p_sq_overshoot_six_five {p : ℕ} (hp : p.Prime)
    (h47 : 47 ≤ p) (h59 : p ≤ 59) :
    6 * usigma (11 ^ 2) * usigma (13 ^ 3) * usigma (p ^ 2) <
      5 * σ 1 (11 ^ 2) * σ 1 (13 ^ 3) * σ 1 (p ^ 2) := by
  rw [usigma_eleven_pow_two, sigma_eleven_pow_two,
    usigma_thirteen_pow_three, sigma_thirteen_pow_three,
    usigma_prime_pow hp (by decide : 0 < 2), sigma_prime_pow_two hp]
  have hsq : p ^ 2 ≤ 59 * p := by
    rw [pow_two]
    exact Nat.mul_le_mul_right p h59
  have hL : ((6 * 122 * 2198 * (1 + p ^ 2) : ℕ) : ℤ) =
      (6 : ℤ) * 122 * 2198 * (1 + (p : ℤ) ^ 2) := by push_cast; rfl
  have hR : ((5 * 133 * 2380 * (1 + p + p ^ 2) : ℕ) : ℤ) =
      (5 : ℤ) * 133 * 2380 * (1 + (p : ℤ) + (p : ℤ) ^ 2) := by push_cast; rfl
  have hint : (6 : ℤ) * 122 * 2198 * (1 + p ^ 2) <
      5 * 133 * 2380 * (1 + p + p ^ 2) := by
    have hp47 : (47 : ℤ) ≤ p := by exact_mod_cast h47
    have hp59 : (p : ℤ) ≤ 59 := by exact_mod_cast h59
    have hsq' : (p : ℤ) ^ 2 ≤ 59 * p := by exact_mod_cast hsq
    nlinarith
  exact Nat.cast_lt.mp (by rw [hL, hR]; exact hint)

lemma eleven_sq_thirteen_cube_p_pow_ge_two_overshoot_six_five {p a b k : ℕ}
    (hp : p.Prime) (h47 : 47 ≤ p) (h59 : p ≤ 59)
    (ha : 2 ≤ a) (hb : 3 ≤ b) (hk : 2 ≤ k) :
    6 * usigma (11 ^ a) * usigma (13 ^ b) * usigma (p ^ k) <
      5 * σ 1 (11 ^ a) * σ 1 (13 ^ b) * σ 1 (p ^ k) :=
  six_five_overshoot_mono_three (by decide : Nat.Prime 11)
    (by decide : Nat.Prime 13) hp
    (by decide : 0 < 2) (by decide : 0 < 3) (by decide : 0 < 2)
    ha hb hk
    (eleven_sq_thirteen_cube_p_sq_overshoot_six_five hp h47 h59)

/-- `ρ(11^3) ρ(169) ρ(p^2) > 6/5` for `47 ≤ p ≤ 67`. -/
lemma eleven_cube_thirteen_sq_p_sq_overshoot_six_five {p : ℕ} (hp : p.Prime)
    (h47 : 47 ≤ p) (h67 : p ≤ 67) :
    6 * usigma (11 ^ 3) * usigma (13 ^ 2) * usigma (p ^ 2) <
      5 * σ 1 (11 ^ 3) * σ 1 (13 ^ 2) * σ 1 (p ^ 2) := by
  rw [usigma_eleven_pow_three, sigma_eleven_pow_three,
    usigma_thirteen_pow_two, sigma_thirteen_pow_two,
    usigma_prime_pow hp (by decide : 0 < 2), sigma_prime_pow_two hp]
  have hsq : p ^ 2 ≤ 67 * p := by
    rw [pow_two]
    exact Nat.mul_le_mul_right p h67
  have hL : ((6 * 1332 * 170 * (1 + p ^ 2) : ℕ) : ℤ) =
      (6 : ℤ) * 1332 * 170 * (1 + (p : ℤ) ^ 2) := by push_cast; rfl
  have hR : ((5 * 1464 * 183 * (1 + p + p ^ 2) : ℕ) : ℤ) =
      (5 : ℤ) * 1464 * 183 * (1 + (p : ℤ) + (p : ℤ) ^ 2) := by push_cast; rfl
  have hint : (6 : ℤ) * 1332 * 170 * (1 + p ^ 2) <
      5 * 1464 * 183 * (1 + p + p ^ 2) := by
    have hp47 : (47 : ℤ) ≤ p := by exact_mod_cast h47
    have hp67 : (p : ℤ) ≤ 67 := by exact_mod_cast h67
    have hsq' : (p : ℤ) ^ 2 ≤ 67 * p := by exact_mod_cast hsq
    nlinarith
  exact Nat.cast_lt.mp (by rw [hL, hR]; exact hint)

lemma eleven_cube_thirteen_sq_p_pow_ge_two_overshoot_six_five {p a b k : ℕ}
    (hp : p.Prime) (h47 : 47 ≤ p) (h67 : p ≤ 67)
    (ha : 3 ≤ a) (hb : 2 ≤ b) (hk : 2 ≤ k) :
    6 * usigma (11 ^ a) * usigma (13 ^ b) * usigma (p ^ k) <
      5 * σ 1 (11 ^ a) * σ 1 (13 ^ b) * σ 1 (p ^ k) :=
  six_five_overshoot_mono_three (by decide : Nat.Prime 11)
    (by decide : Nat.Prime 13) hp
    (by decide : 0 < 3) (by decide : 0 < 2) (by decide : 0 < 2)
    ha hb hk
    (eleven_cube_thirteen_sq_p_sq_overshoot_six_five hp h47 h67)

lemma five_mul_thirteen_sq_eleven_cap {p : ℕ} (hp : 79 ≤ p) (hp1 : 1 ≤ p) :
    5 * 11 * p * 183 ≤ 6 * 10 * (p - 1) * 170 := by
  have hp' : (79 : ℤ) ≤ p := Int.ofNat_le.mpr hp
  have hL : ((5 * 11 * p * 183 : ℕ) : ℤ) =
      (5 : ℤ) * 11 * p * 183 := by
    rw [Nat.cast_mul, Nat.cast_mul, Nat.cast_mul]; rfl
  have hR : ((6 * 10 * (p - 1) * 170 : ℕ) : ℤ) =
      (6 : ℤ) * 10 * ((p : ℤ) - 1) * 170 := by
    rw [Nat.cast_mul, Nat.cast_mul, Nat.cast_mul, Nat.cast_sub hp1]
    rfl
  have : (5 : ℤ) * 11 * p * 183 ≤ 6 * 10 * (p - 1) * 170 := by nlinarith
  exact Nat.cast_le.mp (by rw [hL, hR]; exact this)

/-- `{11^a, 13^2, p^k}` undershoots leftover `6/5` for `p ≥ 79`. -/
lemma five_sigma_lt_six_usigma_thirteen_sq_eleven_large {p a k : ℕ}
    (hp : p.Prime) (hp79 : 79 ≤ p) (ha : 0 < a) (hk : 0 < k) :
    5 * σ 1 (11 ^ a) * σ 1 (13 ^ 2) * σ 1 (p ^ k) <
      6 * usigma (11 ^ a) * usigma (13 ^ 2) * usigma (p ^ k) := by
  rw [sigma_thirteen_pow_two, usigma_thirteen_pow_two]
  have h11 := sigma_lt_cap_usigma (by decide : Nat.Prime 11) ha
  have hpcap := sigma_lt_cap_usigma hp hk
  have hu11 : 0 < usigma (11 ^ a) := by
    rw [usigma_prime_pow (by decide : Nat.Prime 11) ha]
    exact Nat.add_pos_left (by decide : 0 < 1) _
  have hcap := five_mul_thirteen_sq_eleven_cap hp79 hp.one_le
  have hthis := six_five_of_two_caps_times_const (A := 10) (B := 11)
    (X := σ 1 (11 ^ a)) (Y := usigma (11 ^ a)) (C := p - 1) (D := p)
    (P := σ 1 (p ^ k)) (Q := usigma (p ^ k)) (S := 170) (T := 183)
    h11 hpcap hcap (by decide : 0 < 11) hu11 (by decide : 0 < 183)
  convert hthis using 1 <;> ring

/-- Leftover `6/5` cannot be three squareful primes `11,13,p` with
`47 ≤ p ≤ 59` times a squarefree coprime factor. -/
lemma not_five_sigma_of_three_sq_primes_eleven_thirteen_mid_small {m p : ℕ}
    (hm : m ≠ 0) (hp : p.Prime) (hp47 : 47 ≤ p) (h59 : p ≤ 59)
    (h : 5 * σ 1 m = 6 * usigma m)
    (hk11 : 2 ≤ padicValNat 11 m) (hk13 : 2 ≤ padicValNat 13 m)
    (hkp : 2 ≤ padicValNat p m)
    (hs : Squarefree (ordCompl[p] (ordCompl[13] (ordCompl[11] m)))) : False := by
  have hp11 : Nat.Prime 11 := by decide
  have hp13 : Nat.Prime 13 := by decide
  have hpq_ne : (11 : ℕ) ≠ 13 := by decide
  have hpr_ne : (11 : ℕ) ≠ p :=
    Nat.ne_of_lt (lt_of_lt_of_le (by decide : 11 < 47) hp47)
  have hqr_ne : (13 : ℕ) ≠ p :=
    Nat.ne_of_lt (lt_of_lt_of_le (by decide : 13 < 47) hp47)
  have heq := five_sigma_eq_six_of_three_squareful hm hp11 hp13 hp hpq_ne hpr_ne
    hqr_ne h hs
  have hproj_p : ordProj[11] m = 11 ^ padicValNat 11 m := by
    simp [Nat.factorization_def m hp11]
  have hproj_q : ordProj[13] (ordCompl[11] m) =
      13 ^ padicValNat 13 (ordCompl[11] m) := by
    simp [Nat.factorization_def (ordCompl[11] m) hp13]
  have hproj_r : ordProj[p] (ordCompl[13] (ordCompl[11] m)) =
      p ^ padicValNat p (ordCompl[13] (ordCompl[11] m)) := by
    simp [Nat.factorization_def (ordCompl[13] (ordCompl[11] m)) hp]
  rw [hproj_r, padicValNat_ordCompl_of_ne hp hqr_ne,
    padicValNat_ordCompl_of_ne hp hpr_ne, hproj_q,
    padicValNat_ordCompl_of_ne hp13 hpq_ne, hproj_p] at heq
  rcases eq_or_lt_of_le hk13 with h13eq | h13
  · rw [← h13eq] at heq
    rcases eq_or_lt_of_le hk11 with h11eq | h11
    · rw [← h11eq] at heq
      exact (five_sigma_lt_six_usigma_eleven_thirteen_sq_large hp hp47
        (by omega)).ne heq
    · exact (eleven_cube_thirteen_sq_p_pow_ge_two_overshoot_six_five hp hp47
        (le_trans h59 (by decide : 59 ≤ 67)) (Nat.succ_le_of_lt h11)
        (by omega) (by omega)).ne' heq
  · exact (eleven_sq_thirteen_cube_p_pow_ge_two_overshoot_six_five hp hp47 h59
      hk11 (Nat.succ_le_of_lt h13) (by omega)).ne' heq

/-- Leftover `6/5` cannot be three squareful primes `11, 13^2, p` with
`p ≥ 79` times a squarefree coprime factor. -/
lemma not_five_sigma_of_three_sq_primes_thirteen_sq_eleven_large {m p : ℕ}
    (hm : m ≠ 0) (hp : p.Prime) (hp79 : 79 ≤ p)
    (h : 5 * σ 1 m = 6 * usigma m)
    (hk11 : 2 ≤ padicValNat 11 m) (hk13 : padicValNat 13 m = 2)
    (hkp : 2 ≤ padicValNat p m)
    (hs : Squarefree (ordCompl[p] (ordCompl[13] (ordCompl[11] m)))) : False := by
  have hp11 : Nat.Prime 11 := by decide
  have hp13 : Nat.Prime 13 := by decide
  have hpq_ne : (11 : ℕ) ≠ 13 := by decide
  have hpr_ne : (11 : ℕ) ≠ p :=
    Nat.ne_of_lt (lt_of_lt_of_le (by decide : 11 < 79) hp79)
  have hqr_ne : (13 : ℕ) ≠ p :=
    Nat.ne_of_lt (lt_of_lt_of_le (by decide : 13 < 79) hp79)
  have heq := five_sigma_eq_six_of_three_squareful hm hp11 hp13 hp hpq_ne hpr_ne
    hqr_ne h hs
  have hproj_p : ordProj[11] m = 11 ^ padicValNat 11 m := by
    simp [Nat.factorization_def m hp11]
  have hproj_q : ordProj[13] (ordCompl[11] m) =
      13 ^ padicValNat 13 (ordCompl[11] m) := by
    simp [Nat.factorization_def (ordCompl[11] m) hp13]
  have hproj_r : ordProj[p] (ordCompl[13] (ordCompl[11] m)) =
      p ^ padicValNat p (ordCompl[13] (ordCompl[11] m)) := by
    simp [Nat.factorization_def (ordCompl[13] (ordCompl[11] m)) hp]
  rw [hproj_r, padicValNat_ordCompl_of_ne hp hqr_ne,
    padicValNat_ordCompl_of_ne hp hpr_ne, hproj_q,
    padicValNat_ordCompl_of_ne hp13 hpq_ne, hproj_p, hk13] at heq
  exact (five_sigma_lt_six_usigma_thirteen_sq_eleven_large hp hp79
    (by omega) (by omega)).ne heq

lemma prime_sixty_one : Nat.Prime 61 := by norm_num

lemma prime_sixty_seven : Nat.Prime 67 := by norm_num

lemma usigma_sixty_one_pow_two : usigma (61 ^ 2) = 3722 := by
  rw [usigma_prime_pow prime_sixty_one (by decide : 0 < 2)]
  decide

lemma sigma_sixty_one_pow_two : σ 1 (61 ^ 2) = 3783 := by
  rw [sigma_prime_pow_two prime_sixty_one]
  decide

lemma usigma_sixty_one_pow_three : usigma (61 ^ 3) = 226982 := by
  rw [usigma_prime_pow prime_sixty_one (by decide : 0 < 3)]
  norm_num

lemma sigma_sixty_one_pow_three : σ 1 (61 ^ 3) = 230764 := by
  rw [sigma_prime_pow_div prime_sixty_one]
  norm_num

lemma usigma_thirteen_pow_four : usigma (13 ^ 4) = 28562 := by
  rw [usigma_prime_pow (by decide : Nat.Prime 13) (by decide : 0 < 4)]
  decide

lemma sigma_thirteen_pow_four : σ 1 (13 ^ 4) = 30941 := by
  rw [sigma_prime_pow_div (by decide : Nat.Prime 13)]
  norm_num

lemma eleven_sq_thirteen_cube_sixty_one_sq_under :
    5 * σ 1 (11 ^ 2) * σ 1 (13 ^ 3) * σ 1 (61 ^ 2) <
      6 * usigma (11 ^ 2) * usigma (13 ^ 3) * usigma (61 ^ 2) := by
  rw [sigma_eleven_pow_two, usigma_eleven_pow_two,
    sigma_thirteen_pow_three, usigma_thirteen_pow_three,
    sigma_sixty_one_pow_two, usigma_sixty_one_pow_two]
  norm_num

lemma eleven_sq_thirteen_cube_sixty_one_cube_overshoot :
    6 * usigma (11 ^ 2) * usigma (13 ^ 3) * usigma (61 ^ 3) <
      5 * σ 1 (11 ^ 2) * σ 1 (13 ^ 3) * σ 1 (61 ^ 3) := by
  rw [usigma_eleven_pow_two, sigma_eleven_pow_two,
    usigma_thirteen_pow_three, sigma_thirteen_pow_three,
    usigma_sixty_one_pow_three, sigma_sixty_one_pow_three]
  norm_num

lemma eleven_sq_thirteen_fourth_sixty_one_sq_overshoot :
    6 * usigma (11 ^ 2) * usigma (13 ^ 4) * usigma (61 ^ 2) <
      5 * σ 1 (11 ^ 2) * σ 1 (13 ^ 4) * σ 1 (61 ^ 2) := by
  rw [usigma_eleven_pow_two, sigma_eleven_pow_two,
    usigma_thirteen_pow_four, sigma_thirteen_pow_four,
    usigma_sixty_one_pow_two, sigma_sixty_one_pow_two]
  norm_num

lemma prime_ge_sixty_ge_sixty_one {p : ℕ} (hp : p.Prime) (h : 60 ≤ p) :
    61 ≤ p := by
  have hmem : p = 60 ∨ 61 ≤ p := by omega
  rcases hmem with rfl | h61
  · exact False.elim ((by decide : ¬ Nat.Prime 60) hp)
  · exact h61

/-- Leftover `6/5` cannot be three squareful primes `11,13,61` times a
squarefree coprime factor. -/
lemma not_five_sigma_of_three_sq_primes_eleven_thirteen_sixty_one {m : ℕ}
    (hm : m ≠ 0) (h : 5 * σ 1 m = 6 * usigma m)
    (hk11 : 2 ≤ padicValNat 11 m) (hk13 : 2 ≤ padicValNat 13 m)
    (hkp : 2 ≤ padicValNat 61 m)
    (hs : Squarefree (ordCompl[61] (ordCompl[13] (ordCompl[11] m)))) :
    False := by
  have hp11 : Nat.Prime 11 := by decide
  have hp13 : Nat.Prime 13 := by decide
  have hp61 := prime_sixty_one
  have hpq_ne : (11 : ℕ) ≠ 13 := by decide
  have hpr_ne : (11 : ℕ) ≠ 61 := by decide
  have hqr_ne : (13 : ℕ) ≠ 61 := by decide
  have heq := five_sigma_eq_six_of_three_squareful hm hp11 hp13 hp61 hpq_ne
    hpr_ne hqr_ne h hs
  have hproj_p : ordProj[11] m = 11 ^ padicValNat 11 m := by
    simp [Nat.factorization_def m hp11]
  have hproj_q : ordProj[13] (ordCompl[11] m) =
      13 ^ padicValNat 13 (ordCompl[11] m) := by
    simp [Nat.factorization_def (ordCompl[11] m) hp13]
  have hproj_r : ordProj[61] (ordCompl[13] (ordCompl[11] m)) =
      61 ^ padicValNat 61 (ordCompl[13] (ordCompl[11] m)) := by
    simp [Nat.factorization_def (ordCompl[13] (ordCompl[11] m)) hp61]
  rw [hproj_r, padicValNat_ordCompl_of_ne hp61 hqr_ne,
    padicValNat_ordCompl_of_ne hp61 hpr_ne, hproj_q,
    padicValNat_ordCompl_of_ne hp13 hpq_ne, hproj_p] at heq
  rcases eq_or_lt_of_le hk11 with h11eq | h11
  · rw [← h11eq] at heq
    rcases eq_or_lt_of_le hk13 with h13eq | h13
    · rw [← h13eq] at heq
      exact (five_sigma_lt_six_usigma_eleven_thirteen_sq_large hp61
        (by decide : 47 ≤ 61) (by omega)).ne heq
    · have hb3 : 3 ≤ padicValNat 13 m := Nat.succ_le_of_lt h13
      rcases eq_or_lt_of_le hb3 with h13eq3 | h13_4
      · rw [← h13eq3] at heq
        rcases eq_or_lt_of_le hkp with hkeq | hk3
        · rw [← hkeq] at heq
          exact eleven_sq_thirteen_cube_sixty_one_sq_under.ne heq
        · have hover := six_five_overshoot_mono_three hp11 hp13 hp61
            (by decide : 0 < 2) (by decide : 0 < 3) (by decide : 0 < 3)
            (le_refl _) (le_refl _) (Nat.succ_le_of_lt hk3)
            eleven_sq_thirteen_cube_sixty_one_cube_overshoot
          rw [← heq] at hover
          exact lt_irrefl _ hover
      · have hover := six_five_overshoot_mono_three hp11 hp13 hp61
          (by decide : 0 < 2) (by decide : 0 < 4) (by decide : 0 < 2)
          (le_refl _) (Nat.succ_le_of_lt h13_4) hkp
          eleven_sq_thirteen_fourth_sixty_one_sq_overshoot
        rw [← heq] at hover
        exact lt_irrefl _ hover
  · exact (eleven_cube_thirteen_sq_p_pow_ge_two_overshoot_six_five hp61
      (by decide : 47 ≤ 61) (by decide : 61 ≤ 67) (Nat.succ_le_of_lt h11)
      hk13 hkp).ne' heq

/-- Leftover `6/5` cannot be three squareful primes `11,13,67` times a
squarefree coprime factor. -/
lemma not_five_sigma_of_three_sq_primes_eleven_thirteen_sixty_seven {m : ℕ}
    (hm : m ≠ 0) (h : 5 * σ 1 m = 6 * usigma m)
    (hk11 : 2 ≤ padicValNat 11 m) (hk13 : 2 ≤ padicValNat 13 m)
    (hkp : 2 ≤ padicValNat 67 m)
    (hs : Squarefree (ordCompl[67] (ordCompl[13] (ordCompl[11] m)))) :
    False := by
  have hp11 : Nat.Prime 11 := by decide
  have hp13 : Nat.Prime 13 := by decide
  have hp67 := prime_sixty_seven
  have hpq_ne : (11 : ℕ) ≠ 13 := by decide
  have hpr_ne : (11 : ℕ) ≠ 67 := by decide
  have hqr_ne : (13 : ℕ) ≠ 67 := by decide
  have heq := five_sigma_eq_six_of_three_squareful hm hp11 hp13 hp67 hpq_ne
    hpr_ne hqr_ne h hs
  have hproj_p : ordProj[11] m = 11 ^ padicValNat 11 m := by
    simp [Nat.factorization_def m hp11]
  have hproj_q : ordProj[13] (ordCompl[11] m) =
      13 ^ padicValNat 13 (ordCompl[11] m) := by
    simp [Nat.factorization_def (ordCompl[11] m) hp13]
  have hproj_r : ordProj[67] (ordCompl[13] (ordCompl[11] m)) =
      67 ^ padicValNat 67 (ordCompl[13] (ordCompl[11] m)) := by
    simp [Nat.factorization_def (ordCompl[13] (ordCompl[11] m)) hp67]
  rw [hproj_r, padicValNat_ordCompl_of_ne hp67 hqr_ne,
    padicValNat_ordCompl_of_ne hp67 hpr_ne, hproj_q,
    padicValNat_ordCompl_of_ne hp13 hpq_ne, hproj_p] at heq
  rcases eq_or_lt_of_le hk11 with h11eq | h11
  · rw [← h11eq] at heq
    exact (five_sigma_lt_six_usigma_eleven_sq_thirteen_large hp67
      (by decide : 67 ≤ 67) (by omega) (by omega)).ne heq
  · exact (eleven_cube_thirteen_sq_p_pow_ge_two_overshoot_six_five hp67
      (by decide : 47 ≤ 67) (by decide : 67 ≤ 67) (Nat.succ_le_of_lt h11)
      hk13 hkp).ne' heq

/-- Leftover `6/5` cannot be three squareful primes `11,13,p` with
`47 ≤ p ≤ 67` times a squarefree coprime factor. -/
lemma not_five_sigma_of_three_sq_primes_eleven_thirteen_mid {m p : ℕ}
    (hm : m ≠ 0) (hp : p.Prime) (hp47 : 47 ≤ p) (h67 : p ≤ 67)
    (h : 5 * σ 1 m = 6 * usigma m)
    (hk11 : 2 ≤ padicValNat 11 m) (hk13 : 2 ≤ padicValNat 13 m)
    (hkp : 2 ≤ padicValNat p m)
    (hs : Squarefree (ordCompl[p] (ordCompl[13] (ordCompl[11] m)))) : False := by
  rcases le_or_gt p 59 with h59 | h60
  · exact not_five_sigma_of_three_sq_primes_eleven_thirteen_mid_small hm hp
      hp47 h59 h hk11 hk13 hkp hs
  · have hp61 : 61 ≤ p := prime_ge_sixty_ge_sixty_one hp (by omega)
    rcases le_or_gt p 61 with h61 | h62
    · have hp61eq : p = 61 := le_antisymm h61 hp61
      subst p
      exact not_five_sigma_of_three_sq_primes_eleven_thirteen_sixty_one hm h
        hk11 hk13 hkp hs
    · have hp67 : 67 ≤ p := by
        have : 62 ≤ p := by omega
        have hmem :
            p = 62 ∨ p = 63 ∨ p = 64 ∨ p = 65 ∨ p = 66 ∨ 67 ≤ p := by omega
        rcases hmem with rfl | rfl | rfl | rfl | rfl | h67'
        · exact False.elim ((by decide : ¬ Nat.Prime 62) hp)
        · exact False.elim ((by decide : ¬ Nat.Prime 63) hp)
        · exact False.elim ((by decide : ¬ Nat.Prime 64) hp)
        · exact False.elim ((by decide : ¬ Nat.Prime 65) hp)
        · exact False.elim ((by decide : ¬ Nat.Prime 66) hp)
        · exact h67'
      have hp67eq : p = 67 := le_antisymm h67 hp67
      subst p
      exact not_five_sigma_of_three_sq_primes_eleven_thirteen_sixty_seven hm h
        hk11 hk13 hkp hs

lemma prime_seventy_one : Nat.Prime 71 := by norm_num

lemma usigma_seventy_one_pow_two : usigma (71 ^ 2) = 5042 := by
  rw [usigma_prime_pow prime_seventy_one (by decide : 0 < 2)]
  decide

lemma sigma_seventy_one_pow_two : σ 1 (71 ^ 2) = 5113 := by
  rw [sigma_prime_pow_two prime_seventy_one]
  decide

lemma usigma_seventy_one_pow_three : usigma (71 ^ 3) = 357912 := by
  rw [usigma_prime_pow prime_seventy_one (by decide : 0 < 3)]
  norm_num

lemma sigma_seventy_one_pow_three : σ 1 (71 ^ 3) = 363024 := by
  rw [sigma_prime_pow_div prime_seventy_one]
  norm_num

lemma eleven_cube_thirteen_sq_seventy_one_sq_under :
    5 * σ 1 (11 ^ 3) * σ 1 (13 ^ 2) * σ 1 (71 ^ 2) <
      6 * usigma (11 ^ 3) * usigma (13 ^ 2) * usigma (71 ^ 2) := by
  rw [sigma_eleven_pow_three, usigma_eleven_pow_three,
    sigma_thirteen_pow_two, usigma_thirteen_pow_two,
    sigma_seventy_one_pow_two, usigma_seventy_one_pow_two]
  norm_num

lemma eleven_cube_thirteen_sq_seventy_one_cube_overshoot :
    6 * usigma (11 ^ 3) * usigma (13 ^ 2) * usigma (71 ^ 3) <
      5 * σ 1 (11 ^ 3) * σ 1 (13 ^ 2) * σ 1 (71 ^ 3) := by
  rw [usigma_eleven_pow_three, sigma_eleven_pow_three,
    usigma_thirteen_pow_two, sigma_thirteen_pow_two,
    usigma_seventy_one_pow_three, sigma_seventy_one_pow_three]
  norm_num

lemma eleven_fourth_thirteen_sq_seventy_one_sq_overshoot :
    6 * usigma (11 ^ 4) * usigma (13 ^ 2) * usigma (71 ^ 2) <
      5 * σ 1 (11 ^ 4) * σ 1 (13 ^ 2) * σ 1 (71 ^ 2) := by
  rw [usigma_eleven_pow_four, sigma_eleven_pow_four,
    usigma_thirteen_pow_two, sigma_thirteen_pow_two,
    usigma_seventy_one_pow_two, sigma_seventy_one_pow_two]
  norm_num

lemma eleven_cube_thirteen_cube_seventy_one_sq_overshoot :
    6 * usigma (11 ^ 3) * usigma (13 ^ 3) * usigma (71 ^ 2) <
      5 * σ 1 (11 ^ 3) * σ 1 (13 ^ 3) * σ 1 (71 ^ 2) := by
  rw [usigma_eleven_pow_three, sigma_eleven_pow_three,
    usigma_thirteen_pow_three, sigma_thirteen_pow_three,
    usigma_seventy_one_pow_two, sigma_seventy_one_pow_two]
  norm_num

/-- Leftover `6/5` cannot be three squareful primes `11,13,71` times a
squarefree coprime factor. -/
lemma not_five_sigma_of_three_sq_primes_eleven_thirteen_seventy_one {m : ℕ}
    (hm : m ≠ 0) (h : 5 * σ 1 m = 6 * usigma m)
    (hk11 : 2 ≤ padicValNat 11 m) (hk13 : 2 ≤ padicValNat 13 m)
    (hkp : 2 ≤ padicValNat 71 m)
    (hs : Squarefree (ordCompl[71] (ordCompl[13] (ordCompl[11] m)))) :
    False := by
  have hp11 : Nat.Prime 11 := by decide
  have hp13 : Nat.Prime 13 := by decide
  have hp71 := prime_seventy_one
  have hpq_ne : (11 : ℕ) ≠ 13 := by decide
  have hpr_ne : (11 : ℕ) ≠ 71 := by decide
  have hqr_ne : (13 : ℕ) ≠ 71 := by decide
  have heq := five_sigma_eq_six_of_three_squareful hm hp11 hp13 hp71 hpq_ne
    hpr_ne hqr_ne h hs
  have hproj_p : ordProj[11] m = 11 ^ padicValNat 11 m := by
    simp [Nat.factorization_def m hp11]
  have hproj_q : ordProj[13] (ordCompl[11] m) =
      13 ^ padicValNat 13 (ordCompl[11] m) := by
    simp [Nat.factorization_def (ordCompl[11] m) hp13]
  have hproj_r : ordProj[71] (ordCompl[13] (ordCompl[11] m)) =
      71 ^ padicValNat 71 (ordCompl[13] (ordCompl[11] m)) := by
    simp [Nat.factorization_def (ordCompl[13] (ordCompl[11] m)) hp71]
  rw [hproj_r, padicValNat_ordCompl_of_ne hp71 hqr_ne,
    padicValNat_ordCompl_of_ne hp71 hpr_ne, hproj_q,
    padicValNat_ordCompl_of_ne hp13 hpq_ne, hproj_p] at heq
  rcases eq_or_lt_of_le hk11 with h11eq | h11
  · rw [← h11eq] at heq
    exact (five_sigma_lt_six_usigma_eleven_sq_thirteen_large hp71
      (by decide : 67 ≤ 71) (by omega) (by omega)).ne heq
  · have ha3 : 3 ≤ padicValNat 11 m := Nat.succ_le_of_lt h11
    rcases eq_or_lt_of_le hk13 with h13eq | h13
    · rw [← h13eq] at heq
      rcases eq_or_lt_of_le ha3 with ha3eq | ha4
      · rw [← ha3eq] at heq
        rcases eq_or_lt_of_le hkp with hkeq | hk3
        · rw [← hkeq] at heq
          exact eleven_cube_thirteen_sq_seventy_one_sq_under.ne heq
        · have hover := six_five_overshoot_mono_three hp11 hp13 hp71
            (by decide : 0 < 3) (by decide : 0 < 2) (by decide : 0 < 3)
            (le_refl _) (le_refl _) (Nat.succ_le_of_lt hk3)
            eleven_cube_thirteen_sq_seventy_one_cube_overshoot
          rw [← heq] at hover
          exact lt_irrefl _ hover
      · have hover := six_five_overshoot_mono_three hp11 hp13 hp71
          (by decide : 0 < 4) (by decide : 0 < 2) (by decide : 0 < 2)
          (Nat.succ_le_of_lt ha4) (le_refl _) hkp
          eleven_fourth_thirteen_sq_seventy_one_sq_overshoot
        rw [← heq] at hover
        exact lt_irrefl _ hover
    · have hover := six_five_overshoot_mono_three hp11 hp13 hp71
        (by decide : 0 < 3) (by decide : 0 < 3) (by decide : 0 < 2)
        ha3 (Nat.succ_le_of_lt h13) hkp
        eleven_cube_thirteen_cube_seventy_one_sq_overshoot
      rw [← heq] at hover
      exact lt_irrefl _ hover

lemma prime_seventy_three : Nat.Prime 73 := by norm_num

lemma usigma_seventy_three_pow_two : usigma (73 ^ 2) = 5330 := by
  rw [usigma_prime_pow prime_seventy_three (by decide : 0 < 2)]
  decide

lemma sigma_seventy_three_pow_two : σ 1 (73 ^ 2) = 5403 := by
  rw [sigma_prime_pow_two prime_seventy_three]
  decide

lemma five_mul_eleven_cube_thirteen_sq_seventy_three_cap :
    5 * 73 * 1464 * 183 ≤ 6 * 72 * 1332 * 170 := by
  norm_num

/-- `{11^3, 13^2, 73^k}` undershoots leftover `6/5`. -/
lemma five_sigma_lt_six_usigma_eleven_cube_thirteen_sq_seventy_three {k : ℕ}
    (hk : 0 < k) :
    5 * σ 1 (11 ^ 3) * σ 1 (13 ^ 2) * σ 1 (73 ^ k) <
      6 * usigma (11 ^ 3) * usigma (13 ^ 2) * usigma (73 ^ k) := by
  rw [sigma_eleven_pow_three, usigma_eleven_pow_three,
    sigma_thirteen_pow_two, usigma_thirteen_pow_two]
  have h73 := sigma_lt_cap_usigma prime_seventy_three hk
  have hthis := six_five_of_cap_times_const (A := 72) (B := 73)
    (X := σ 1 (73 ^ k)) (Y := usigma (73 ^ k)) (S := 1332 * 170)
    (T := 1464 * 183) h73 (by
      have hL : 5 * 73 * (1464 * 183) = 5 * 73 * 1464 * 183 := by ring
      have hR : 6 * 72 * (1332 * 170) = 6 * 72 * 1332 * 170 := by ring
      rw [hL, hR]
      exact five_mul_eleven_cube_thirteen_sq_seventy_three_cap)
    (by decide : 0 < 1464 * 183)
  convert hthis using 1 <;> ring

lemma eleven_fourth_thirteen_sq_seventy_three_sq_overshoot :
    6 * usigma (11 ^ 4) * usigma (13 ^ 2) * usigma (73 ^ 2) <
      5 * σ 1 (11 ^ 4) * σ 1 (13 ^ 2) * σ 1 (73 ^ 2) := by
  rw [usigma_eleven_pow_four, sigma_eleven_pow_four,
    usigma_thirteen_pow_two, sigma_thirteen_pow_two,
    usigma_seventy_three_pow_two, sigma_seventy_three_pow_two]
  norm_num

lemma eleven_cube_thirteen_cube_seventy_three_sq_overshoot :
    6 * usigma (11 ^ 3) * usigma (13 ^ 3) * usigma (73 ^ 2) <
      5 * σ 1 (11 ^ 3) * σ 1 (13 ^ 3) * σ 1 (73 ^ 2) := by
  rw [usigma_eleven_pow_three, sigma_eleven_pow_three,
    usigma_thirteen_pow_three, sigma_thirteen_pow_three,
    usigma_seventy_three_pow_two, sigma_seventy_three_pow_two]
  norm_num

/-- Leftover `6/5` cannot be three squareful primes `11,13,73` times a
squarefree coprime factor. -/
lemma not_five_sigma_of_three_sq_primes_eleven_thirteen_seventy_three {m : ℕ}
    (hm : m ≠ 0) (h : 5 * σ 1 m = 6 * usigma m)
    (hk11 : 2 ≤ padicValNat 11 m) (hk13 : 2 ≤ padicValNat 13 m)
    (hkp : 2 ≤ padicValNat 73 m)
    (hs : Squarefree (ordCompl[73] (ordCompl[13] (ordCompl[11] m)))) :
    False := by
  have hp11 : Nat.Prime 11 := by decide
  have hp13 : Nat.Prime 13 := by decide
  have hp73 := prime_seventy_three
  have hpq_ne : (11 : ℕ) ≠ 13 := by decide
  have hpr_ne : (11 : ℕ) ≠ 73 := by decide
  have hqr_ne : (13 : ℕ) ≠ 73 := by decide
  have heq := five_sigma_eq_six_of_three_squareful hm hp11 hp13 hp73 hpq_ne
    hpr_ne hqr_ne h hs
  have hproj_p : ordProj[11] m = 11 ^ padicValNat 11 m := by
    simp [Nat.factorization_def m hp11]
  have hproj_q : ordProj[13] (ordCompl[11] m) =
      13 ^ padicValNat 13 (ordCompl[11] m) := by
    simp [Nat.factorization_def (ordCompl[11] m) hp13]
  have hproj_r : ordProj[73] (ordCompl[13] (ordCompl[11] m)) =
      73 ^ padicValNat 73 (ordCompl[13] (ordCompl[11] m)) := by
    simp [Nat.factorization_def (ordCompl[13] (ordCompl[11] m)) hp73]
  rw [hproj_r, padicValNat_ordCompl_of_ne hp73 hqr_ne,
    padicValNat_ordCompl_of_ne hp73 hpr_ne, hproj_q,
    padicValNat_ordCompl_of_ne hp13 hpq_ne, hproj_p] at heq
  rcases eq_or_lt_of_le hk11 with h11eq | h11
  · rw [← h11eq] at heq
    exact (five_sigma_lt_six_usigma_eleven_sq_thirteen_large hp73
      (by decide : 67 ≤ 73) (by omega) (by omega)).ne heq
  · have ha3 : 3 ≤ padicValNat 11 m := Nat.succ_le_of_lt h11
    rcases eq_or_lt_of_le hk13 with h13eq | h13
    · rw [← h13eq] at heq
      rcases eq_or_lt_of_le ha3 with ha3eq | ha4
      · rw [← ha3eq] at heq
        exact (five_sigma_lt_six_usigma_eleven_cube_thirteen_sq_seventy_three
          (by omega)).ne heq
      · have hover := six_five_overshoot_mono_three hp11 hp13 hp73
          (by decide : 0 < 4) (by decide : 0 < 2) (by decide : 0 < 2)
          (Nat.succ_le_of_lt ha4) (le_refl _) hkp
          eleven_fourth_thirteen_sq_seventy_three_sq_overshoot
        rw [← heq] at hover
        exact lt_irrefl _ hover
    · have hover := six_five_overshoot_mono_three hp11 hp13 hp73
        (by decide : 0 < 3) (by decide : 0 < 3) (by decide : 0 < 2)
        ha3 (Nat.succ_le_of_lt h13) hkp
        eleven_cube_thirteen_cube_seventy_three_sq_overshoot
      rw [← heq] at hover
      exact lt_irrefl _ hover

/-- `ρ(11^3) ρ(13^3) ρ(p^2) > 6/5` for `79 ≤ p ≤ 113`. -/
lemma eleven_cube_thirteen_cube_p_sq_overshoot_six_five {p : ℕ} (hp : p.Prime)
    (h79 : 79 ≤ p) (h113 : p ≤ 113) :
    6 * usigma (11 ^ 3) * usigma (13 ^ 3) * usigma (p ^ 2) <
      5 * σ 1 (11 ^ 3) * σ 1 (13 ^ 3) * σ 1 (p ^ 2) := by
  rw [usigma_eleven_pow_three, sigma_eleven_pow_three,
    usigma_thirteen_pow_three, sigma_thirteen_pow_three,
    usigma_prime_pow hp (by decide : 0 < 2), sigma_prime_pow_two hp]
  have hsq : p ^ 2 ≤ 113 * p := by
    rw [pow_two]
    exact Nat.mul_le_mul_right p h113
  have hL : ((6 * 1332 * 2198 * (1 + p ^ 2) : ℕ) : ℤ) =
      (6 : ℤ) * 1332 * 2198 * (1 + (p : ℤ) ^ 2) := by push_cast; rfl
  have hR : ((5 * 1464 * 2380 * (1 + p + p ^ 2) : ℕ) : ℤ) =
      (5 : ℤ) * 1464 * 2380 * (1 + (p : ℤ) + (p : ℤ) ^ 2) := by push_cast; rfl
  have hint : (6 : ℤ) * 1332 * 2198 * (1 + p ^ 2) <
      5 * 1464 * 2380 * (1 + p + p ^ 2) := by
    have hp79 : (79 : ℤ) ≤ p := by exact_mod_cast h79
    have hp113 : (p : ℤ) ≤ 113 := by exact_mod_cast h113
    have hsq' : (p : ℤ) ^ 2 ≤ 113 * p := by exact_mod_cast hsq
    nlinarith
  exact Nat.cast_lt.mp (by rw [hL, hR]; exact hint)

lemma eleven_cube_thirteen_cube_p_pow_ge_two_overshoot_six_five {p a b k : ℕ}
    (hp : p.Prime) (h79 : 79 ≤ p) (h113 : p ≤ 113)
    (ha : 3 ≤ a) (hb : 3 ≤ b) (hk : 2 ≤ k) :
    6 * usigma (11 ^ a) * usigma (13 ^ b) * usigma (p ^ k) <
      5 * σ 1 (11 ^ a) * σ 1 (13 ^ b) * σ 1 (p ^ k) :=
  six_five_overshoot_mono_three (by decide : Nat.Prime 11)
    (by decide : Nat.Prime 13) hp
    (by decide : 0 < 3) (by decide : 0 < 3) (by decide : 0 < 2)
    ha hb hk
    (eleven_cube_thirteen_cube_p_sq_overshoot_six_five hp h79 h113)

/-- Leftover `6/5` cannot be three squareful primes `11,13,p` with
`79 ≤ p ≤ 113` times a squarefree coprime factor. -/
lemma not_five_sigma_of_three_sq_primes_eleven_thirteen_mid_large {m p : ℕ}
    (hm : m ≠ 0) (hp : p.Prime) (hp79 : 79 ≤ p) (h113 : p ≤ 113)
    (h : 5 * σ 1 m = 6 * usigma m)
    (hk11 : 2 ≤ padicValNat 11 m) (hk13 : 2 ≤ padicValNat 13 m)
    (hkp : 2 ≤ padicValNat p m)
    (hs : Squarefree (ordCompl[p] (ordCompl[13] (ordCompl[11] m)))) : False := by
  have hp11 : Nat.Prime 11 := by decide
  have hp13 : Nat.Prime 13 := by decide
  have hpq_ne : (11 : ℕ) ≠ 13 := by decide
  have hpr_ne : (11 : ℕ) ≠ p :=
    Nat.ne_of_lt (lt_of_lt_of_le (by decide : 11 < 79) hp79)
  have hqr_ne : (13 : ℕ) ≠ p :=
    Nat.ne_of_lt (lt_of_lt_of_le (by decide : 13 < 79) hp79)
  have heq := five_sigma_eq_six_of_three_squareful hm hp11 hp13 hp hpq_ne hpr_ne
    hqr_ne h hs
  have hproj_p : ordProj[11] m = 11 ^ padicValNat 11 m := by
    simp [Nat.factorization_def m hp11]
  have hproj_q : ordProj[13] (ordCompl[11] m) =
      13 ^ padicValNat 13 (ordCompl[11] m) := by
    simp [Nat.factorization_def (ordCompl[11] m) hp13]
  have hproj_r : ordProj[p] (ordCompl[13] (ordCompl[11] m)) =
      p ^ padicValNat p (ordCompl[13] (ordCompl[11] m)) := by
    simp [Nat.factorization_def (ordCompl[13] (ordCompl[11] m)) hp]
  rw [hproj_r, padicValNat_ordCompl_of_ne hp hqr_ne,
    padicValNat_ordCompl_of_ne hp hpr_ne, hproj_q,
    padicValNat_ordCompl_of_ne hp13 hpq_ne, hproj_p] at heq
  rcases eq_or_lt_of_le hk11 with h11eq | h11
  · rw [← h11eq] at heq
    exact (five_sigma_lt_six_usigma_eleven_sq_thirteen_large hp
      (le_trans (by decide : 67 ≤ 79) hp79) (by omega) (by omega)).ne heq
  · rcases eq_or_lt_of_le hk13 with h13eq | h13
    · rw [← h13eq] at heq
      exact (five_sigma_lt_six_usigma_thirteen_sq_eleven_large hp hp79
        (by omega) (by omega)).ne heq
    · exact (eleven_cube_thirteen_cube_p_pow_ge_two_overshoot_six_five hp hp79
        h113 (Nat.succ_le_of_lt h11) (Nat.succ_le_of_lt h13) hkp).ne' heq

lemma five_mul_eleven_cube_thirteen_cap {p : ℕ} (hp : 131 ≤ p) (hp1 : 1 ≤ p) :
    5 * 13 * p * 1464 ≤ 6 * 12 * (p - 1) * 1332 := by
  have hp' : (131 : ℤ) ≤ p := Int.ofNat_le.mpr hp
  have hL : ((5 * 13 * p * 1464 : ℕ) : ℤ) =
      (5 : ℤ) * 13 * p * 1464 := by
    rw [Nat.cast_mul, Nat.cast_mul, Nat.cast_mul]; rfl
  have hR : ((6 * 12 * (p - 1) * 1332 : ℕ) : ℤ) =
      (6 : ℤ) * 12 * ((p : ℤ) - 1) * 1332 := by
    rw [Nat.cast_mul, Nat.cast_mul, Nat.cast_mul, Nat.cast_sub hp1]
    rfl
  have : (5 : ℤ) * 13 * p * 1464 ≤ 6 * 12 * (p - 1) * 1332 := by nlinarith
  exact Nat.cast_le.mp (by rw [hL, hR]; exact this)

/-- `{11^3, 13^b, p^k}` undershoots leftover `6/5` for `p ≥ 131`. -/
lemma five_sigma_lt_six_usigma_eleven_cube_thirteen_large {p b k : ℕ}
    (hp : p.Prime) (hp131 : 131 ≤ p) (hb : 0 < b) (hk : 0 < k) :
    5 * σ 1 (11 ^ 3) * σ 1 (13 ^ b) * σ 1 (p ^ k) <
      6 * usigma (11 ^ 3) * usigma (13 ^ b) * usigma (p ^ k) := by
  rw [sigma_eleven_pow_three, usigma_eleven_pow_three]
  have h13 := sigma_lt_cap_usigma (by decide : Nat.Prime 13) hb
  have hpcap := sigma_lt_cap_usigma hp hk
  have hu13 : 0 < usigma (13 ^ b) := by
    rw [usigma_prime_pow (by decide : Nat.Prime 13) hb]
    exact Nat.add_pos_left (by decide : 0 < 1) _
  have hcap := five_mul_eleven_cube_thirteen_cap hp131 hp.one_le
  have hthis := six_five_of_two_caps_times_const (A := 12) (B := 13)
    (X := σ 1 (13 ^ b)) (Y := usigma (13 ^ b)) (C := p - 1) (D := p)
    (P := σ 1 (p ^ k)) (Q := usigma (p ^ k)) (S := 1332) (T := 1464)
    h13 hpcap hcap (by decide : 0 < 13) hu13 (by decide : 0 < 1464)
  convert hthis using 1 <;> ring

/-- Leftover `6/5` cannot be three squareful primes `11^3, 13, p` with
`p ≥ 131` times a squarefree coprime factor. -/
lemma not_five_sigma_of_three_sq_primes_eleven_cube_thirteen_large {m p : ℕ}
    (hm : m ≠ 0) (hp : p.Prime) (hp131 : 131 ≤ p)
    (h : 5 * σ 1 m = 6 * usigma m)
    (hk11 : padicValNat 11 m = 3) (hk13 : 2 ≤ padicValNat 13 m)
    (hkp : 2 ≤ padicValNat p m)
    (hs : Squarefree (ordCompl[p] (ordCompl[13] (ordCompl[11] m)))) : False := by
  have hp11 : Nat.Prime 11 := by decide
  have hp13 : Nat.Prime 13 := by decide
  have hpq_ne : (11 : ℕ) ≠ 13 := by decide
  have hpr_ne : (11 : ℕ) ≠ p :=
    Nat.ne_of_lt (lt_of_lt_of_le (by decide : 11 < 131) hp131)
  have hqr_ne : (13 : ℕ) ≠ p :=
    Nat.ne_of_lt (lt_of_lt_of_le (by decide : 13 < 131) hp131)
  have heq := five_sigma_eq_six_of_three_squareful hm hp11 hp13 hp hpq_ne hpr_ne
    hqr_ne h hs
  have hproj_p : ordProj[11] m = 11 ^ padicValNat 11 m := by
    simp [Nat.factorization_def m hp11]
  have hproj_q : ordProj[13] (ordCompl[11] m) =
      13 ^ padicValNat 13 (ordCompl[11] m) := by
    simp [Nat.factorization_def (ordCompl[11] m) hp13]
  have hproj_r : ordProj[p] (ordCompl[13] (ordCompl[11] m)) =
      p ^ padicValNat p (ordCompl[13] (ordCompl[11] m)) := by
    simp [Nat.factorization_def (ordCompl[13] (ordCompl[11] m)) hp]
  rw [hproj_r, padicValNat_ordCompl_of_ne hp hqr_ne,
    padicValNat_ordCompl_of_ne hp hpr_ne, hproj_q,
    padicValNat_ordCompl_of_ne hp13 hpq_ne, hproj_p, hk11] at heq
  exact (five_sigma_lt_six_usigma_eleven_cube_thirteen_large hp hp131
    (by omega) (by omega)).ne heq

lemma prime_one_twenty_seven : Nat.Prime 127 := by norm_num

lemma usigma_one_twenty_seven_pow_two : usigma (127 ^ 2) = 16130 := by
  rw [usigma_prime_pow prime_one_twenty_seven (by decide : 0 < 2)]
  decide

lemma sigma_one_twenty_seven_pow_two : σ 1 (127 ^ 2) = 16257 := by
  rw [sigma_prime_pow_two prime_one_twenty_seven]
  decide

lemma five_mul_eleven_cube_thirteen_cube_one_twenty_seven_cap :
    5 * 127 * 1464 * 2380 ≤ 6 * 126 * 1332 * 2198 := by
  norm_num

/-- `{11^3, 13^3, 127^k}` undershoots leftover `6/5`. -/
lemma five_sigma_lt_six_usigma_eleven_cube_thirteen_cube_one_twenty_seven
    {k : ℕ} (hk : 0 < k) :
    5 * σ 1 (11 ^ 3) * σ 1 (13 ^ 3) * σ 1 (127 ^ k) <
      6 * usigma (11 ^ 3) * usigma (13 ^ 3) * usigma (127 ^ k) := by
  rw [sigma_eleven_pow_three, usigma_eleven_pow_three,
    sigma_thirteen_pow_three, usigma_thirteen_pow_three]
  have h127 := sigma_lt_cap_usigma prime_one_twenty_seven hk
  have hthis := six_five_of_cap_times_const (A := 126) (B := 127)
    (X := σ 1 (127 ^ k)) (Y := usigma (127 ^ k)) (S := 1332 * 2198)
    (T := 1464 * 2380) h127 (by
      have hL : 5 * 127 * (1464 * 2380) = 5 * 127 * 1464 * 2380 := by ring
      have hR : 6 * 126 * (1332 * 2198) = 6 * 126 * 1332 * 2198 := by ring
      rw [hL, hR]
      exact five_mul_eleven_cube_thirteen_cube_one_twenty_seven_cap)
    (by decide : 0 < 1464 * 2380)
  convert hthis using 1 <;> ring

lemma eleven_cube_thirteen_fourth_one_twenty_seven_sq_overshoot :
    6 * usigma (11 ^ 3) * usigma (13 ^ 4) * usigma (127 ^ 2) <
      5 * σ 1 (11 ^ 3) * σ 1 (13 ^ 4) * σ 1 (127 ^ 2) := by
  rw [usigma_eleven_pow_three, sigma_eleven_pow_three,
    usigma_thirteen_pow_four, sigma_thirteen_pow_four,
    usigma_one_twenty_seven_pow_two, sigma_one_twenty_seven_pow_two]
  norm_num

lemma eleven_fourth_thirteen_cube_one_twenty_seven_sq_overshoot :
    6 * usigma (11 ^ 4) * usigma (13 ^ 3) * usigma (127 ^ 2) <
      5 * σ 1 (11 ^ 4) * σ 1 (13 ^ 3) * σ 1 (127 ^ 2) := by
  rw [usigma_eleven_pow_four, sigma_eleven_pow_four,
    usigma_thirteen_pow_three, sigma_thirteen_pow_three,
    usigma_one_twenty_seven_pow_two, sigma_one_twenty_seven_pow_two]
  norm_num

/-- Leftover `6/5` cannot be three squareful primes `11,13,127` times a
squarefree coprime factor. -/
lemma not_five_sigma_of_three_sq_primes_eleven_thirteen_one_twenty_seven
    {m : ℕ} (hm : m ≠ 0) (h : 5 * σ 1 m = 6 * usigma m)
    (hk11 : 2 ≤ padicValNat 11 m) (hk13 : 2 ≤ padicValNat 13 m)
    (hkp : 2 ≤ padicValNat 127 m)
    (hs : Squarefree (ordCompl[127] (ordCompl[13] (ordCompl[11] m)))) :
    False := by
  have hp11 : Nat.Prime 11 := by decide
  have hp13 : Nat.Prime 13 := by decide
  have hp127 := prime_one_twenty_seven
  have hpq_ne : (11 : ℕ) ≠ 13 := by decide
  have hpr_ne : (11 : ℕ) ≠ 127 := by decide
  have hqr_ne : (13 : ℕ) ≠ 127 := by decide
  have heq := five_sigma_eq_six_of_three_squareful hm hp11 hp13 hp127 hpq_ne
    hpr_ne hqr_ne h hs
  have hproj_p : ordProj[11] m = 11 ^ padicValNat 11 m := by
    simp [Nat.factorization_def m hp11]
  have hproj_q : ordProj[13] (ordCompl[11] m) =
      13 ^ padicValNat 13 (ordCompl[11] m) := by
    simp [Nat.factorization_def (ordCompl[11] m) hp13]
  have hproj_r : ordProj[127] (ordCompl[13] (ordCompl[11] m)) =
      127 ^ padicValNat 127 (ordCompl[13] (ordCompl[11] m)) := by
    simp [Nat.factorization_def (ordCompl[13] (ordCompl[11] m)) hp127]
  rw [hproj_r, padicValNat_ordCompl_of_ne hp127 hqr_ne,
    padicValNat_ordCompl_of_ne hp127 hpr_ne, hproj_q,
    padicValNat_ordCompl_of_ne hp13 hpq_ne, hproj_p] at heq
  rcases eq_or_lt_of_le hk11 with h11eq | h11
  · rw [← h11eq] at heq
    exact (five_sigma_lt_six_usigma_eleven_sq_thirteen_large hp127
      (by decide : 67 ≤ 127) (by omega) (by omega)).ne heq
  · have ha3 : 3 ≤ padicValNat 11 m := Nat.succ_le_of_lt h11
    rcases eq_or_lt_of_le hk13 with h13eq | h13
    · rw [← h13eq] at heq
      exact (five_sigma_lt_six_usigma_thirteen_sq_eleven_large hp127
        (by decide : 79 ≤ 127) (by omega) (by omega)).ne heq
    · have hb3 : 3 ≤ padicValNat 13 m := Nat.succ_le_of_lt h13
      rcases eq_or_lt_of_le ha3 with ha3eq | ha4
      · rw [← ha3eq] at heq
        rcases eq_or_lt_of_le hb3 with hb3eq | hb4
        · rw [← hb3eq] at heq
          exact (five_sigma_lt_six_usigma_eleven_cube_thirteen_cube_one_twenty_seven
            (by omega)).ne heq
        · have hover := six_five_overshoot_mono_three hp11 hp13 hp127
            (by decide : 0 < 3) (by decide : 0 < 4) (by decide : 0 < 2)
            (le_refl _) (Nat.succ_le_of_lt hb4) hkp
            eleven_cube_thirteen_fourth_one_twenty_seven_sq_overshoot
          rw [← heq] at hover
          exact lt_irrefl _ hover
      · have hover := six_five_overshoot_mono_three hp11 hp13 hp127
          (by decide : 0 < 4) (by decide : 0 < 3) (by decide : 0 < 2)
          (Nat.succ_le_of_lt ha4) hb3 hkp
          eleven_fourth_thirteen_cube_one_twenty_seven_sq_overshoot
        rw [← heq] at hover
        exact lt_irrefl _ hover

lemma prime_one_thirty_one : Nat.Prime 131 := by norm_num

lemma usigma_one_thirty_one_pow_two : usigma (131 ^ 2) = 17162 := by
  rw [usigma_prime_pow prime_one_thirty_one (by decide : 0 < 2)]
  decide

lemma sigma_one_thirty_one_pow_two : σ 1 (131 ^ 2) = 17293 := by
  rw [sigma_prime_pow_two prime_one_thirty_one]
  decide

lemma eleven_fourth_thirteen_cube_one_thirty_one_sq_overshoot :
    6 * usigma (11 ^ 4) * usigma (13 ^ 3) * usigma (131 ^ 2) <
      5 * σ 1 (11 ^ 4) * σ 1 (13 ^ 3) * σ 1 (131 ^ 2) := by
  rw [usigma_eleven_pow_four, sigma_eleven_pow_four,
    usigma_thirteen_pow_three, sigma_thirteen_pow_three,
    usigma_one_thirty_one_pow_two, sigma_one_thirty_one_pow_two]
  norm_num

/-- Leftover `6/5` cannot be three squareful primes `11,13,131` times a
squarefree coprime factor. -/
lemma not_five_sigma_of_three_sq_primes_eleven_thirteen_one_thirty_one
    {m : ℕ} (hm : m ≠ 0) (h : 5 * σ 1 m = 6 * usigma m)
    (hk11 : 2 ≤ padicValNat 11 m) (hk13 : 2 ≤ padicValNat 13 m)
    (hkp : 2 ≤ padicValNat 131 m)
    (hs : Squarefree (ordCompl[131] (ordCompl[13] (ordCompl[11] m)))) :
    False := by
  have hp11 : Nat.Prime 11 := by decide
  have hp13 : Nat.Prime 13 := by decide
  have hp131 := prime_one_thirty_one
  have hpq_ne : (11 : ℕ) ≠ 13 := by decide
  have hpr_ne : (11 : ℕ) ≠ 131 := by decide
  have hqr_ne : (13 : ℕ) ≠ 131 := by decide
  have heq := five_sigma_eq_six_of_three_squareful hm hp11 hp13 hp131 hpq_ne
    hpr_ne hqr_ne h hs
  have hproj_p : ordProj[11] m = 11 ^ padicValNat 11 m := by
    simp [Nat.factorization_def m hp11]
  have hproj_q : ordProj[13] (ordCompl[11] m) =
      13 ^ padicValNat 13 (ordCompl[11] m) := by
    simp [Nat.factorization_def (ordCompl[11] m) hp13]
  have hproj_r : ordProj[131] (ordCompl[13] (ordCompl[11] m)) =
      131 ^ padicValNat 131 (ordCompl[13] (ordCompl[11] m)) := by
    simp [Nat.factorization_def (ordCompl[13] (ordCompl[11] m)) hp131]
  rw [hproj_r, padicValNat_ordCompl_of_ne hp131 hqr_ne,
    padicValNat_ordCompl_of_ne hp131 hpr_ne, hproj_q,
    padicValNat_ordCompl_of_ne hp13 hpq_ne, hproj_p] at heq
  rcases eq_or_lt_of_le hk11 with h11eq | h11
  · rw [← h11eq] at heq
    exact (five_sigma_lt_six_usigma_eleven_sq_thirteen_large hp131
      (by decide : 67 ≤ 131) (by omega) (by omega)).ne heq
  · have ha3 : 3 ≤ padicValNat 11 m := Nat.succ_le_of_lt h11
    rcases eq_or_lt_of_le hk13 with h13eq | h13
    · rw [← h13eq] at heq
      exact (five_sigma_lt_six_usigma_thirteen_sq_eleven_large hp131
        (by decide : 79 ≤ 131) (by omega) (by omega)).ne heq
    · have hb3 : 3 ≤ padicValNat 13 m := Nat.succ_le_of_lt h13
      rcases eq_or_lt_of_le ha3 with ha3eq | ha4
      · rw [← ha3eq] at heq
        exact (five_sigma_lt_six_usigma_eleven_cube_thirteen_large hp131
          (by decide : 131 ≤ 131) (by omega) (by omega)).ne heq
      · have hover := six_five_overshoot_mono_three hp11 hp13 hp131
          (by decide : 0 < 4) (by decide : 0 < 3) (by decide : 0 < 2)
          (Nat.succ_le_of_lt ha4) hb3 hkp
          eleven_fourth_thirteen_cube_one_thirty_one_sq_overshoot
        rw [← heq] at hover
        exact lt_irrefl _ hover

lemma five_mul_eleven_thirteen_cube_cap {p : ℕ} (hp : 137 ≤ p) (hp1 : 1 ≤ p) :
    5 * 11 * p * 2380 ≤ 6 * 10 * (p - 1) * 2198 := by
  have hp' : (137 : ℤ) ≤ p := Int.ofNat_le.mpr hp
  have hL : ((5 * 11 * p * 2380 : ℕ) : ℤ) =
      (5 : ℤ) * 11 * p * 2380 := by
    rw [Nat.cast_mul, Nat.cast_mul, Nat.cast_mul]; rfl
  have hR : ((6 * 10 * (p - 1) * 2198 : ℕ) : ℤ) =
      (6 : ℤ) * 10 * ((p : ℤ) - 1) * 2198 := by
    rw [Nat.cast_mul, Nat.cast_mul, Nat.cast_mul, Nat.cast_sub hp1]
    rfl
  have : (5 : ℤ) * 11 * p * 2380 ≤ 6 * 10 * (p - 1) * 2198 := by nlinarith
  exact Nat.cast_le.mp (by rw [hL, hR]; exact this)

/-- `{11^a, 13^3, p^k}` undershoots leftover `6/5` for `p ≥ 137`. -/
lemma five_sigma_lt_six_usigma_thirteen_cube_eleven_large {p a k : ℕ}
    (hp : p.Prime) (hp137 : 137 ≤ p) (ha : 0 < a) (hk : 0 < k) :
    5 * σ 1 (11 ^ a) * σ 1 (13 ^ 3) * σ 1 (p ^ k) <
      6 * usigma (11 ^ a) * usigma (13 ^ 3) * usigma (p ^ k) := by
  rw [sigma_thirteen_pow_three, usigma_thirteen_pow_three]
  have h11 := sigma_lt_cap_usigma (by decide : Nat.Prime 11) ha
  have hpcap := sigma_lt_cap_usigma hp hk
  have hu11 : 0 < usigma (11 ^ a) := by
    rw [usigma_prime_pow (by decide : Nat.Prime 11) ha]
    exact Nat.add_pos_left (by decide : 0 < 1) _
  have hcap := five_mul_eleven_thirteen_cube_cap hp137 hp.one_le
  have hthis := six_five_of_two_caps_times_const (A := 10) (B := 11)
    (X := σ 1 (11 ^ a)) (Y := usigma (11 ^ a)) (C := p - 1) (D := p)
    (P := σ 1 (p ^ k)) (Q := usigma (p ^ k)) (S := 2198) (T := 2380)
    h11 hpcap hcap (by decide : 0 < 11) hu11 (by decide : 0 < 2380)
  convert hthis using 1 <;> ring

/-- `ρ(11^4) ρ(13^4) ρ(p^2) > 6/5` for `137 ≤ p ≤ 139`. -/
lemma eleven_fourth_thirteen_fourth_p_sq_overshoot_six_five {p : ℕ}
    (hp : p.Prime) (h137 : 137 ≤ p) (h139 : p ≤ 139) :
    6 * usigma (11 ^ 4) * usigma (13 ^ 4) * usigma (p ^ 2) <
      5 * σ 1 (11 ^ 4) * σ 1 (13 ^ 4) * σ 1 (p ^ 2) := by
  rw [usigma_eleven_pow_four, sigma_eleven_pow_four,
    usigma_thirteen_pow_four, sigma_thirteen_pow_four,
    usigma_prime_pow hp (by decide : 0 < 2), sigma_prime_pow_two hp]
  have hsq : p ^ 2 ≤ 139 * p := by
    rw [pow_two]
    exact Nat.mul_le_mul_right p h139
  have hL : ((6 * 14642 * 28562 * (1 + p ^ 2) : ℕ) : ℤ) =
      (6 : ℤ) * 14642 * 28562 * (1 + (p : ℤ) ^ 2) := by push_cast; rfl
  have hR : ((5 * 16105 * 30941 * (1 + p + p ^ 2) : ℕ) : ℤ) =
      (5 : ℤ) * 16105 * 30941 * (1 + (p : ℤ) + (p : ℤ) ^ 2) := by push_cast; rfl
  have hint : (6 : ℤ) * 14642 * 28562 * (1 + p ^ 2) <
      5 * 16105 * 30941 * (1 + p + p ^ 2) := by
    have hp137 : (137 : ℤ) ≤ p := by exact_mod_cast h137
    have hp139 : (p : ℤ) ≤ 139 := by exact_mod_cast h139
    have hsq' : (p : ℤ) ^ 2 ≤ 139 * p := by exact_mod_cast hsq
    nlinarith
  exact Nat.cast_lt.mp (by rw [hL, hR]; exact hint)

lemma eleven_fourth_thirteen_fourth_p_pow_ge_two_overshoot_six_five
    {p a b k : ℕ} (hp : p.Prime) (h137 : 137 ≤ p) (h139 : p ≤ 139)
    (ha : 4 ≤ a) (hb : 4 ≤ b) (hk : 2 ≤ k) :
    6 * usigma (11 ^ a) * usigma (13 ^ b) * usigma (p ^ k) <
      5 * σ 1 (11 ^ a) * σ 1 (13 ^ b) * σ 1 (p ^ k) :=
  six_five_overshoot_mono_three (by decide : Nat.Prime 11)
    (by decide : Nat.Prime 13) hp
    (by decide : 0 < 4) (by decide : 0 < 4) (by decide : 0 < 2)
    ha hb hk
    (eleven_fourth_thirteen_fourth_p_sq_overshoot_six_five hp h137 h139)

lemma prime_ge_one_thirty_two_ge_one_thirty_seven {p : ℕ} (hp : p.Prime)
    (h : 132 ≤ p) : 137 ≤ p := by
  have hmem : p = 132 ∨ p = 133 ∨ p = 134 ∨ p = 135 ∨ p = 136 ∨ 137 ≤ p :=
    by omega
  rcases hmem with rfl | rfl | rfl | rfl | rfl | h137
  · exact False.elim ((by decide : ¬ Nat.Prime 132) hp)
  · exact False.elim ((by decide : ¬ Nat.Prime 133) hp)
  · exact False.elim ((by decide : ¬ Nat.Prime 134) hp)
  · exact False.elim ((by decide : ¬ Nat.Prime 135) hp)
  · exact False.elim ((by decide : ¬ Nat.Prime 136) hp)
  · exact h137

/-- Leftover `6/5` cannot be three squareful primes `11,13,p` with
`137 ≤ p ≤ 139` times a squarefree coprime factor. -/
lemma not_five_sigma_of_three_sq_primes_eleven_thirteen_end {m p : ℕ}
    (hm : m ≠ 0) (hp : p.Prime) (hp137 : 137 ≤ p) (h139 : p ≤ 139)
    (h : 5 * σ 1 m = 6 * usigma m)
    (hk11 : 2 ≤ padicValNat 11 m) (hk13 : 2 ≤ padicValNat 13 m)
    (hkp : 2 ≤ padicValNat p m)
    (hs : Squarefree (ordCompl[p] (ordCompl[13] (ordCompl[11] m)))) : False := by
  have hp11 : Nat.Prime 11 := by decide
  have hp13 : Nat.Prime 13 := by decide
  have hpq_ne : (11 : ℕ) ≠ 13 := by decide
  have hpr_ne : (11 : ℕ) ≠ p :=
    Nat.ne_of_lt (lt_of_lt_of_le (by decide : 11 < 137) hp137)
  have hqr_ne : (13 : ℕ) ≠ p :=
    Nat.ne_of_lt (lt_of_lt_of_le (by decide : 13 < 137) hp137)
  have heq := five_sigma_eq_six_of_three_squareful hm hp11 hp13 hp hpq_ne hpr_ne
    hqr_ne h hs
  have hproj_p : ordProj[11] m = 11 ^ padicValNat 11 m := by
    simp [Nat.factorization_def m hp11]
  have hproj_q : ordProj[13] (ordCompl[11] m) =
      13 ^ padicValNat 13 (ordCompl[11] m) := by
    simp [Nat.factorization_def (ordCompl[11] m) hp13]
  have hproj_r : ordProj[p] (ordCompl[13] (ordCompl[11] m)) =
      p ^ padicValNat p (ordCompl[13] (ordCompl[11] m)) := by
    simp [Nat.factorization_def (ordCompl[13] (ordCompl[11] m)) hp]
  rw [hproj_r, padicValNat_ordCompl_of_ne hp hqr_ne,
    padicValNat_ordCompl_of_ne hp hpr_ne, hproj_q,
    padicValNat_ordCompl_of_ne hp13 hpq_ne, hproj_p] at heq
  rcases eq_or_lt_of_le hk11 with h11eq | h11
  · rw [← h11eq] at heq
    exact (five_sigma_lt_six_usigma_eleven_sq_thirteen_large hp
      (le_trans (by decide : 67 ≤ 137) hp137) (by omega) (by omega)).ne heq
  · have ha3 : 3 ≤ padicValNat 11 m := Nat.succ_le_of_lt h11
    rcases eq_or_lt_of_le hk13 with h13eq | h13
    · rw [← h13eq] at heq
      exact (five_sigma_lt_six_usigma_thirteen_sq_eleven_large hp
        (le_trans (by decide : 79 ≤ 137) hp137) (by omega) (by omega)).ne heq
    · have hb3 : 3 ≤ padicValNat 13 m := Nat.succ_le_of_lt h13
      rcases eq_or_lt_of_le hb3 with hb3eq | hb4
      · rw [← hb3eq] at heq
        exact (five_sigma_lt_six_usigma_thirteen_cube_eleven_large hp hp137
          (by omega) (by omega)).ne heq
      · rcases eq_or_lt_of_le ha3 with ha3eq | ha4
        · rw [← ha3eq] at heq
          exact (five_sigma_lt_six_usigma_eleven_cube_thirteen_large hp
            (le_trans (by decide : 131 ≤ 137) hp137) (by omega)
            (by omega)).ne heq
        · exact (eleven_fourth_thirteen_fourth_p_pow_ge_two_overshoot_six_five
            hp hp137 h139 (Nat.succ_le_of_lt ha4) (Nat.succ_le_of_lt hb4)
            hkp).ne' heq

lemma prime_ge_sixty_eight_ge_seventy_one {p : ℕ} (hp : p.Prime)
    (h : 68 ≤ p) : 71 ≤ p := by
  have hmem : p = 68 ∨ p = 69 ∨ p = 70 ∨ 71 ≤ p := by omega
  rcases hmem with rfl | rfl | rfl | h71
  · exact False.elim ((by decide : ¬ Nat.Prime 68) hp)
  · exact False.elim ((by decide : ¬ Nat.Prime 69) hp)
  · exact False.elim ((by decide : ¬ Nat.Prime 70) hp)
  · exact h71

lemma prime_ge_seventy_two_ge_seventy_three {p : ℕ} (hp : p.Prime)
    (h : 72 ≤ p) : 73 ≤ p := by
  have hmem : p = 72 ∨ 73 ≤ p := by omega
  rcases hmem with rfl | h73
  · exact False.elim ((by decide : ¬ Nat.Prime 72) hp)
  · exact h73

lemma prime_ge_seventy_four_ge_seventy_nine {p : ℕ} (hp : p.Prime)
    (h : 74 ≤ p) : 79 ≤ p := by
  have hmem : p = 74 ∨ p = 75 ∨ p = 76 ∨ p = 77 ∨ p = 78 ∨ 79 ≤ p := by omega
  rcases hmem with rfl | rfl | rfl | rfl | rfl | h79
  · exact False.elim ((by decide : ¬ Nat.Prime 74) hp)
  · exact False.elim ((by decide : ¬ Nat.Prime 75) hp)
  · exact False.elim ((by decide : ¬ Nat.Prime 76) hp)
  · exact False.elim ((by decide : ¬ Nat.Prime 77) hp)
  · exact False.elim ((by decide : ¬ Nat.Prime 78) hp)
  · exact h79

lemma prime_ge_one_fourteen_ge_one_twenty_seven {p : ℕ} (hp : p.Prime)
    (h : 114 ≤ p) : 127 ≤ p := by
  have hmem :
      p = 114 ∨ p = 115 ∨ p = 116 ∨ p = 117 ∨ p = 118 ∨ p = 119 ∨
        p = 120 ∨ p = 121 ∨ p = 122 ∨ p = 123 ∨ p = 124 ∨ p = 125 ∨
          p = 126 ∨ 127 ≤ p := by omega
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    | rfl | rfl | rfl | h127
  · exact False.elim ((by decide : ¬ Nat.Prime 114) hp)
  · exact False.elim ((by decide : ¬ Nat.Prime 115) hp)
  · exact False.elim ((by decide : ¬ Nat.Prime 116) hp)
  · exact False.elim ((by decide : ¬ Nat.Prime 117) hp)
  · exact False.elim ((by decide : ¬ Nat.Prime 118) hp)
  · exact False.elim ((by decide : ¬ Nat.Prime 119) hp)
  · exact False.elim ((by decide : ¬ Nat.Prime 120) hp)
  · exact False.elim ((by decide : ¬ Nat.Prime 121) hp)
  · exact False.elim ((by decide : ¬ Nat.Prime 122) hp)
  · exact False.elim ((by decide : ¬ Nat.Prime 123) hp)
  · exact False.elim ((by decide : ¬ Nat.Prime 124) hp)
  · exact False.elim ((by decide : ¬ Nat.Prime 125) hp)
  · exact False.elim ((by decide : ¬ Nat.Prime 126) hp)
  · exact h127

lemma prime_ge_one_twenty_eight_ge_one_thirty_one {p : ℕ} (hp : p.Prime)
    (h : 128 ≤ p) : 131 ≤ p := by
  have hmem : p = 128 ∨ p = 129 ∨ p = 130 ∨ 131 ≤ p := by omega
  rcases hmem with rfl | rfl | rfl | h131
  · exact False.elim ((by decide : ¬ Nat.Prime 128) hp)
  · exact False.elim ((by decide : ¬ Nat.Prime 129) hp)
  · exact False.elim ((by decide : ¬ Nat.Prime 130) hp)
  · exact h131

lemma prime_ge_one_forty_ge_one_forty_nine {p : ℕ} (hp : p.Prime)
    (h : 140 ≤ p) : 149 ≤ p := by
  have hmem :
      p = 140 ∨ p = 141 ∨ p = 142 ∨ p = 143 ∨ p = 144 ∨ p = 145 ∨
        p = 146 ∨ p = 147 ∨ p = 148 ∨ 149 ≤ p := by omega
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | h149
  · exact False.elim ((by decide : ¬ Nat.Prime 140) hp)
  · exact False.elim ((by decide : ¬ Nat.Prime 141) hp)
  · exact False.elim ((by decide : ¬ Nat.Prime 142) hp)
  · exact False.elim ((by decide : ¬ Nat.Prime 143) hp)
  · exact False.elim ((by decide : ¬ Nat.Prime 144) hp)
  · exact False.elim ((by decide : ¬ Nat.Prime 145) hp)
  · exact False.elim ((by decide : ¬ Nat.Prime 146) hp)
  · exact False.elim ((by decide : ¬ Nat.Prime 147) hp)
  · exact False.elim ((by decide : ¬ Nat.Prime 148) hp)
  · exact h149

/-- Leftover `6/5` cannot be three squareful primes `11,13,p` with
`p ≥ 17` times a squarefree coprime factor. -/
lemma not_five_sigma_of_three_sq_primes_eleven_thirteen {m p : ℕ}
    (hm : m ≠ 0) (hp : p.Prime) (hp17 : 17 ≤ p)
    (h : 5 * σ 1 m = 6 * usigma m)
    (hk11 : 2 ≤ padicValNat 11 m) (hk13 : 2 ≤ padicValNat 13 m)
    (hkp : 2 ≤ padicValNat p m)
    (hs : Squarefree (ordCompl[p] (ordCompl[13] (ordCompl[11] m)))) : False := by
  rcases le_or_gt p 43 with h43 | h44
  · exact not_five_sigma_of_three_sq_primes_eleven_thirteen_small hm hp hp17 h43
      h hk11 hk13 hkp hs
  · have hp47 : 47 ≤ p := prime_ge_forty_four_ge_forty_seven hp (by omega)
    rcases le_or_gt p 67 with h67 | h68
    · exact not_five_sigma_of_three_sq_primes_eleven_thirteen_mid hm hp hp47 h67
        h hk11 hk13 hkp hs
    · have hp71 : 71 ≤ p := prime_ge_sixty_eight_ge_seventy_one hp (by omega)
      rcases le_or_gt p 71 with h71 | h72
      · have hp71eq : p = 71 := le_antisymm h71 hp71
        subst p
        exact not_five_sigma_of_three_sq_primes_eleven_thirteen_seventy_one hm h
          hk11 hk13 hkp hs
      · have hp73 : 73 ≤ p := prime_ge_seventy_two_ge_seventy_three hp (by omega)
        rcases le_or_gt p 73 with h73 | h74
        · have hp73eq : p = 73 := le_antisymm h73 hp73
          subst p
          exact not_five_sigma_of_three_sq_primes_eleven_thirteen_seventy_three
            hm h hk11 hk13 hkp hs
        · have hp79 : 79 ≤ p := prime_ge_seventy_four_ge_seventy_nine hp
            (by omega)
          rcases le_or_gt p 113 with h113 | h114
          · exact not_five_sigma_of_three_sq_primes_eleven_thirteen_mid_large
              hm hp hp79 h113 h hk11 hk13 hkp hs
          · have hp127 : 127 ≤ p :=
              prime_ge_one_fourteen_ge_one_twenty_seven hp (by omega)
            rcases le_or_gt p 127 with h127 | h128
            · have hp127eq : p = 127 := le_antisymm h127 hp127
              subst p
              exact
                not_five_sigma_of_three_sq_primes_eleven_thirteen_one_twenty_seven
                  hm h hk11 hk13 hkp hs
            · have hp131 : 131 ≤ p :=
                prime_ge_one_twenty_eight_ge_one_thirty_one hp (by omega)
              rcases le_or_gt p 131 with h131 | h132
              · have hp131eq : p = 131 := le_antisymm h131 hp131
                subst p
                exact
                  not_five_sigma_of_three_sq_primes_eleven_thirteen_one_thirty_one
                    hm h hk11 hk13 hkp hs
              · have hp137 : 137 ≤ p :=
                  prime_ge_one_thirty_two_ge_one_thirty_seven hp (by omega)
                rcases le_or_gt p 139 with h139 | h140
                · exact not_five_sigma_of_three_sq_primes_eleven_thirteen_end
                    hm hp hp137 h139 h hk11 hk13 hkp hs
                · have hp149 : 149 ≤ p :=
                    prime_ge_one_forty_ge_one_forty_nine hp (by omega)
                  exact not_five_sigma_of_three_sq_primes_eleven_thirteen_large
                    hm hp hp149 h hk11 hk13 hkp hs

lemma five_thirteen_seventeen_cap {p : ℕ} (hp : 29 ≤ p) :
    5 * 13 * 17 * p ≤ 6 * 12 * 16 * (p - 1) := by
  have hp1 : 1 ≤ p := by omega
  have hp' : (29 : ℤ) ≤ p := Int.ofNat_le.mpr hp
  have hL : ((5 * 13 * 17 * p : ℕ) : ℤ) =
      (5 : ℤ) * 13 * 17 * p := by
    rw [Nat.cast_mul, Nat.cast_mul, Nat.cast_mul]; rfl
  have hR : ((6 * 12 * 16 * (p - 1) : ℕ) : ℤ) =
      (6 : ℤ) * 12 * 16 * ((p : ℤ) - 1) := by
    rw [Nat.cast_mul, Nat.cast_mul, Nat.cast_mul, Nat.cast_sub hp1]
    rfl
  have : (5 : ℤ) * 13 * 17 * p ≤ 6 * 12 * 16 * (p - 1) := by nlinarith
  exact Nat.cast_le.mp (by rw [hL, hR]; exact this)

/-- `{13, 17, p}` with `p ≥ 29` cannot fill leftover `6/5`. -/
lemma five_sigma_lt_six_usigma_thirteen_seventeen_large {p a b c : ℕ}
    (hp : p.Prime) (hp29 : 29 ≤ p) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    5 * σ 1 (13 ^ a) * σ 1 (17 ^ b) * σ 1 (p ^ c) <
      6 * usigma (13 ^ a) * usigma (17 ^ b) * usigma (p ^ c) := by
  have h13 := sigma_lt_cap_usigma (by decide : Nat.Prime 13) ha
  have h17 := sigma_lt_cap_usigma (by decide : Nat.Prime 17) hb
  have hpcap := sigma_lt_cap_usigma hp hc
  have hu13 : 0 < usigma (13 ^ a) := by
    rw [usigma_prime_pow (by decide : Nat.Prime 13) ha]
    exact Nat.add_pos_left (by decide : 0 < 1) _
  have hu17 : 0 < usigma (17 ^ b) := by
    rw [usigma_prime_pow (by decide : Nat.Prime 17) hb]
    exact Nat.add_pos_left (by decide : 0 < 1) _
  have hcap := five_thirteen_seventeen_cap hp29
  have := six_five_of_three_caps (A := 12) (B := 13) (X := σ 1 (13 ^ a))
    (Y := usigma (13 ^ a)) (C := 16) (D := 17) (P := σ 1 (17 ^ b))
    (Q := usigma (17 ^ b)) (E := p - 1) (F := p) (R := σ 1 (p ^ c))
    (S := usigma (p ^ c)) h13 h17 hpcap hcap (by decide : 0 < 13) hu13
    (by decide : 0 < 17) hu17
  simpa [mul_assoc] using this

/-- Leftover `6/5` cannot be three squareful primes `13,17,p` with
`p ≥ 29` times a squarefree coprime factor. -/
lemma not_five_sigma_of_three_sq_primes_thirteen_seventeen_large {m p : ℕ}
    (hm : m ≠ 0) (hp : p.Prime) (hp29 : 29 ≤ p)
    (h : 5 * σ 1 m = 6 * usigma m)
    (hk13 : 2 ≤ padicValNat 13 m) (hk17 : 2 ≤ padicValNat 17 m)
    (hkp : 2 ≤ padicValNat p m)
    (hs : Squarefree (ordCompl[p] (ordCompl[17] (ordCompl[13] m)))) : False := by
  have hp13 : Nat.Prime 13 := by decide
  have hp17 : Nat.Prime 17 := by decide
  have hpq_ne : (13 : ℕ) ≠ 17 := by decide
  have hpr_ne : (13 : ℕ) ≠ p :=
    Nat.ne_of_lt (lt_of_lt_of_le (by decide : 13 < 29) hp29)
  have hqr_ne : (17 : ℕ) ≠ p :=
    Nat.ne_of_lt (lt_of_lt_of_le (by decide : 17 < 29) hp29)
  have heq := five_sigma_eq_six_of_three_squareful hm hp13 hp17 hp hpq_ne hpr_ne
    hqr_ne h hs
  have hproj_p : ordProj[13] m = 13 ^ padicValNat 13 m := by
    simp [Nat.factorization_def m hp13]
  have hproj_q : ordProj[17] (ordCompl[13] m) =
      17 ^ padicValNat 17 (ordCompl[13] m) := by
    simp [Nat.factorization_def (ordCompl[13] m) hp17]
  have hproj_r : ordProj[p] (ordCompl[17] (ordCompl[13] m)) =
      p ^ padicValNat p (ordCompl[17] (ordCompl[13] m)) := by
    simp [Nat.factorization_def (ordCompl[17] (ordCompl[13] m)) hp]
  rw [hproj_r, padicValNat_ordCompl_of_ne hp hqr_ne,
    padicValNat_ordCompl_of_ne hp hpr_ne, hproj_q,
    padicValNat_ordCompl_of_ne hp17 hpq_ne, hproj_p] at heq
  exact (five_sigma_lt_six_usigma_thirteen_seventeen_large hp hp29
    (by omega) (by omega) (by omega)).ne heq

lemma usigma_nineteen_pow_two : usigma (19 ^ 2) = 362 := by
  rw [usigma_prime_pow (by decide : Nat.Prime 19) (by decide : 0 < 2)]
  decide

lemma sigma_nineteen_pow_two : σ 1 (19 ^ 2) = 381 := by
  rw [sigma_prime_pow_two (by decide : Nat.Prime 19)]
  decide

lemma thirteen_seventeen_nineteen_sq_under :
    5 * σ 1 (13 ^ 2) * σ 1 (17 ^ 2) * σ 1 (19 ^ 2) <
      6 * usigma (13 ^ 2) * usigma (17 ^ 2) * usigma (19 ^ 2) := by
  rw [sigma_thirteen_pow_two, usigma_thirteen_pow_two,
    sigma_seventeen_pow_two, usigma_seventeen_pow_two,
    sigma_nineteen_pow_two, usigma_nineteen_pow_two]
  decide

lemma thirteen_cube_seventeen_sq_nineteen_sq_overshoot :
    6 * usigma (13 ^ 3) * usigma (17 ^ 2) * usigma (19 ^ 2) <
      5 * σ 1 (13 ^ 3) * σ 1 (17 ^ 2) * σ 1 (19 ^ 2) := by
  rw [usigma_thirteen_pow_three, sigma_thirteen_pow_three,
    usigma_seventeen_pow_two, sigma_seventeen_pow_two,
    usigma_nineteen_pow_two, sigma_nineteen_pow_two]
  decide

lemma thirteen_sq_seventeen_cube_nineteen_sq_overshoot :
    6 * usigma (13 ^ 2) * usigma (17 ^ 3) * usigma (19 ^ 2) <
      5 * σ 1 (13 ^ 2) * σ 1 (17 ^ 3) * σ 1 (19 ^ 2) := by
  rw [usigma_thirteen_pow_two, sigma_thirteen_pow_two,
    usigma_seventeen_pow_three, sigma_seventeen_pow_three,
    usigma_nineteen_pow_two, sigma_nineteen_pow_two]
  decide

lemma thirteen_sq_seventeen_sq_nineteen_cube_overshoot :
    6 * usigma (13 ^ 2) * usigma (17 ^ 2) * usigma (19 ^ 3) <
      5 * σ 1 (13 ^ 2) * σ 1 (17 ^ 2) * σ 1 (19 ^ 3) := by
  rw [usigma_thirteen_pow_two, sigma_thirteen_pow_two,
    usigma_seventeen_pow_two, sigma_seventeen_pow_two,
    usigma_nineteen_pow_three, sigma_nineteen_pow_three]
  decide

/-- Leftover `6/5` cannot be three squareful primes `13,17,19` times a
squarefree coprime factor. -/
lemma not_five_sigma_of_three_sq_primes_thirteen_seventeen_nineteen {m : ℕ}
    (hm : m ≠ 0) (h : 5 * σ 1 m = 6 * usigma m)
    (hk13 : 2 ≤ padicValNat 13 m) (hk17 : 2 ≤ padicValNat 17 m)
    (hk19 : 2 ≤ padicValNat 19 m)
    (hs : Squarefree (ordCompl[19] (ordCompl[17] (ordCompl[13] m)))) :
    False := by
  have hp13 : Nat.Prime 13 := by decide
  have hp17 : Nat.Prime 17 := by decide
  have hp19 : Nat.Prime 19 := by decide
  have hpq_ne : (13 : ℕ) ≠ 17 := by decide
  have hpr_ne : (13 : ℕ) ≠ 19 := by decide
  have hqr_ne : (17 : ℕ) ≠ 19 := by decide
  have heq := five_sigma_eq_six_of_three_squareful hm hp13 hp17 hp19 hpq_ne
    hpr_ne hqr_ne h hs
  have hproj_p : ordProj[13] m = 13 ^ padicValNat 13 m := by
    simp [Nat.factorization_def m hp13]
  have hproj_q : ordProj[17] (ordCompl[13] m) =
      17 ^ padicValNat 17 (ordCompl[13] m) := by
    simp [Nat.factorization_def (ordCompl[13] m) hp17]
  have hproj_r : ordProj[19] (ordCompl[17] (ordCompl[13] m)) =
      19 ^ padicValNat 19 (ordCompl[17] (ordCompl[13] m)) := by
    simp [Nat.factorization_def (ordCompl[17] (ordCompl[13] m)) hp19]
  rw [hproj_r, padicValNat_ordCompl_of_ne hp19 hqr_ne,
    padicValNat_ordCompl_of_ne hp19 hpr_ne, hproj_q,
    padicValNat_ordCompl_of_ne hp17 hpq_ne, hproj_p] at heq
  rcases eq_or_lt_of_le hk13 with h13eq | h13
  · rw [← h13eq] at heq
    rcases eq_or_lt_of_le hk17 with h17eq | h17
    · rw [← h17eq] at heq
      rcases eq_or_lt_of_le hk19 with h19eq | h19
      · rw [← h19eq] at heq
        exact thirteen_seventeen_nineteen_sq_under.ne heq
      · have hover := six_five_overshoot_mono_three hp13 hp17 hp19
          (by decide : 0 < 2) (by decide : 0 < 2) (by decide : 0 < 3)
          (le_refl _) (le_refl _) (Nat.succ_le_of_lt h19)
          thirteen_sq_seventeen_sq_nineteen_cube_overshoot
        rw [← heq] at hover
        exact lt_irrefl _ hover
    · have hover := six_five_overshoot_mono_three hp13 hp17 hp19
        (by decide : 0 < 2) (by decide : 0 < 3) (by decide : 0 < 2)
        (le_refl _) (Nat.succ_le_of_lt h17) hk19
        thirteen_sq_seventeen_cube_nineteen_sq_overshoot
      rw [← heq] at hover
      exact lt_irrefl _ hover
  · have hover := six_five_overshoot_mono_three hp13 hp17 hp19
      (by decide : 0 < 3) (by decide : 0 < 2) (by decide : 0 < 2)
      (Nat.succ_le_of_lt h13) hk17 hk19
      thirteen_cube_seventeen_sq_nineteen_sq_overshoot
    rw [← heq] at hover
    exact lt_irrefl _ hover

lemma five_mul_thirteen_sq_seventeen_twenty_three_cap :
    5 * 17 * 23 * 183 ≤ 6 * 16 * 22 * 170 := by
  decide

lemma five_mul_seventeen_sq_thirteen_twenty_three_cap :
    5 * 13 * 23 * 307 ≤ 6 * 12 * 22 * 290 := by
  decide

/-- `{13^2, 17^b, 23^k}` undershoots leftover `6/5`. -/
lemma five_sigma_lt_six_usigma_thirteen_sq_seventeen_twenty_three {b k : ℕ}
    (hb : 0 < b) (hk : 0 < k) :
    5 * σ 1 (13 ^ 2) * σ 1 (17 ^ b) * σ 1 (23 ^ k) <
      6 * usigma (13 ^ 2) * usigma (17 ^ b) * usigma (23 ^ k) := by
  rw [sigma_thirteen_pow_two, usigma_thirteen_pow_two]
  have h17 := sigma_lt_cap_usigma (by decide : Nat.Prime 17) hb
  have h23 := sigma_lt_cap_usigma (by decide : Nat.Prime 23) hk
  have hu17 : 0 < usigma (17 ^ b) := by
    rw [usigma_prime_pow (by decide : Nat.Prime 17) hb]
    exact Nat.add_pos_left (by decide : 0 < 1) _
  have hthis := six_five_of_two_caps_times_const (A := 16) (B := 17)
    (X := σ 1 (17 ^ b)) (Y := usigma (17 ^ b)) (C := 22) (D := 23)
    (P := σ 1 (23 ^ k)) (Q := usigma (23 ^ k)) (S := 170) (T := 183)
    h17 h23 five_mul_thirteen_sq_seventeen_twenty_three_cap
    (by decide : 0 < 17) hu17 (by decide : 0 < 183)
  convert hthis using 1 <;> ring

/-- `{13^a, 17^2, 23^k}` undershoots leftover `6/5`. -/
lemma five_sigma_lt_six_usigma_seventeen_sq_thirteen_twenty_three {a k : ℕ}
    (ha : 0 < a) (hk : 0 < k) :
    5 * σ 1 (13 ^ a) * σ 1 (17 ^ 2) * σ 1 (23 ^ k) <
      6 * usigma (13 ^ a) * usigma (17 ^ 2) * usigma (23 ^ k) := by
  rw [sigma_seventeen_pow_two, usigma_seventeen_pow_two]
  have h13 := sigma_lt_cap_usigma (by decide : Nat.Prime 13) ha
  have h23 := sigma_lt_cap_usigma (by decide : Nat.Prime 23) hk
  have hu13 : 0 < usigma (13 ^ a) := by
    rw [usigma_prime_pow (by decide : Nat.Prime 13) ha]
    exact Nat.add_pos_left (by decide : 0 < 1) _
  have hthis := six_five_of_two_caps_times_const (A := 12) (B := 13)
    (X := σ 1 (13 ^ a)) (Y := usigma (13 ^ a)) (C := 22) (D := 23)
    (P := σ 1 (23 ^ k)) (Q := usigma (23 ^ k)) (S := 290) (T := 307)
    h13 h23 five_mul_seventeen_sq_thirteen_twenty_three_cap
    (by decide : 0 < 13) hu13 (by decide : 0 < 307)
  convert hthis using 1 <;> ring

lemma thirteen_cube_seventeen_cube_twenty_three_sq_overshoot :
    6 * usigma (13 ^ 3) * usigma (17 ^ 3) * usigma (23 ^ 2) <
      5 * σ 1 (13 ^ 3) * σ 1 (17 ^ 3) * σ 1 (23 ^ 2) := by
  rw [usigma_thirteen_pow_three, sigma_thirteen_pow_three,
    usigma_seventeen_pow_three, sigma_seventeen_pow_three]
  have hσ : σ 1 (23 ^ 2) = 553 := by
    rw [sigma_prime_pow_two (by decide : Nat.Prime 23)]
    decide
  have hu : usigma (23 ^ 2) = 530 := by
    rw [usigma_prime_pow (by decide : Nat.Prime 23) (by decide : 0 < 2)]
    decide
  rw [hσ, hu]
  decide

/-- Leftover `6/5` cannot be three squareful primes `13,17,23` times a
squarefree coprime factor. -/
lemma not_five_sigma_of_three_sq_primes_thirteen_seventeen_twenty_three {m : ℕ}
    (hm : m ≠ 0) (h : 5 * σ 1 m = 6 * usigma m)
    (hk13 : 2 ≤ padicValNat 13 m) (hk17 : 2 ≤ padicValNat 17 m)
    (hk23 : 2 ≤ padicValNat 23 m)
    (hs : Squarefree (ordCompl[23] (ordCompl[17] (ordCompl[13] m)))) :
    False := by
  have hp13 : Nat.Prime 13 := by decide
  have hp17 : Nat.Prime 17 := by decide
  have hp23 : Nat.Prime 23 := by decide
  have hpq_ne : (13 : ℕ) ≠ 17 := by decide
  have hpr_ne : (13 : ℕ) ≠ 23 := by decide
  have hqr_ne : (17 : ℕ) ≠ 23 := by decide
  have heq := five_sigma_eq_six_of_three_squareful hm hp13 hp17 hp23 hpq_ne
    hpr_ne hqr_ne h hs
  have hproj_p : ordProj[13] m = 13 ^ padicValNat 13 m := by
    simp [Nat.factorization_def m hp13]
  have hproj_q : ordProj[17] (ordCompl[13] m) =
      17 ^ padicValNat 17 (ordCompl[13] m) := by
    simp [Nat.factorization_def (ordCompl[13] m) hp17]
  have hproj_r : ordProj[23] (ordCompl[17] (ordCompl[13] m)) =
      23 ^ padicValNat 23 (ordCompl[17] (ordCompl[13] m)) := by
    simp [Nat.factorization_def (ordCompl[17] (ordCompl[13] m)) hp23]
  rw [hproj_r, padicValNat_ordCompl_of_ne hp23 hqr_ne,
    padicValNat_ordCompl_of_ne hp23 hpr_ne, hproj_q,
    padicValNat_ordCompl_of_ne hp17 hpq_ne, hproj_p] at heq
  rcases eq_or_lt_of_le hk13 with h13eq | h13
  · rw [← h13eq] at heq
    exact (five_sigma_lt_six_usigma_thirteen_sq_seventeen_twenty_three
      (by omega) (by omega)).ne heq
  · rcases eq_or_lt_of_le hk17 with h17eq | h17
    · rw [← h17eq] at heq
      exact (five_sigma_lt_six_usigma_seventeen_sq_thirteen_twenty_three
        (by omega) (by omega)).ne heq
    · have hover := six_five_overshoot_mono_three hp13 hp17 hp23
        (by decide : 0 < 3) (by decide : 0 < 3) (by decide : 0 < 2)
        (Nat.succ_le_of_lt h13) (Nat.succ_le_of_lt h17) hk23
        thirteen_cube_seventeen_cube_twenty_three_sq_overshoot
      rw [← heq] at hover
      exact lt_irrefl _ hover

/-- Leftover `6/5` cannot be three squareful primes `13,17,p` with
`p ≥ 19` times a squarefree coprime factor. -/
lemma not_five_sigma_of_three_sq_primes_thirteen_seventeen {m p : ℕ}
    (hm : m ≠ 0) (hp : p.Prime) (hp19 : 19 ≤ p)
    (h : 5 * σ 1 m = 6 * usigma m)
    (hk13 : 2 ≤ padicValNat 13 m) (hk17 : 2 ≤ padicValNat 17 m)
    (hkp : 2 ≤ padicValNat p m)
    (hs : Squarefree (ordCompl[p] (ordCompl[17] (ordCompl[13] m)))) : False := by
  rcases le_or_gt p 19 with h19 | h20
  · have hp19eq : p = 19 := le_antisymm h19 hp19
    subst p
    exact not_five_sigma_of_three_sq_primes_thirteen_seventeen_nineteen hm h
      hk13 hk17 hkp hs
  · have hp23 : 23 ≤ p := prime_ge_twenty_ge_twenty_three hp (by omega)
    rcases le_or_gt p 23 with h23 | h24
    · have hp23eq : p = 23 := le_antisymm h23 hp23
      subst p
      exact not_five_sigma_of_three_sq_primes_thirteen_seventeen_twenty_three
        hm h hk13 hk17 hkp hs
    · have hp29 : 29 ≤ p := prime_ge_twenty_four_ge_twenty_nine hp (by omega)
      exact not_five_sigma_of_three_sq_primes_thirteen_seventeen_large hm hp
        hp29 h hk13 hk17 hkp hs

lemma five_mul_eleven_sq_nineteen_sq_twenty_three_cap :
    5 * 23 * 133 * 381 ≤ 6 * 22 * 122 * 362 := by
  decide

/-- `{11^2, 19^2, 23^k}` undershoots leftover `6/5`. -/
lemma five_sigma_lt_six_usigma_eleven_sq_nineteen_sq_twenty_three {k : ℕ}
    (hk : 0 < k) :
    5 * σ 1 (11 ^ 2) * σ 1 (19 ^ 2) * σ 1 (23 ^ k) <
      6 * usigma (11 ^ 2) * usigma (19 ^ 2) * usigma (23 ^ k) := by
  rw [sigma_eleven_pow_two, usigma_eleven_pow_two,
    sigma_nineteen_pow_two, usigma_nineteen_pow_two]
  have h23 := sigma_lt_cap_usigma (by decide : Nat.Prime 23) hk
  have hthis := six_five_of_cap_times_const (A := 22) (B := 23)
    (X := σ 1 (23 ^ k)) (Y := usigma (23 ^ k)) (S := 122 * 362)
    (T := 133 * 381) h23 (by
      have hL : 5 * 23 * (133 * 381) = 5 * 23 * 133 * 381 := by ring
      have hR : 6 * 22 * (122 * 362) = 6 * 22 * 122 * 362 := by ring
      rw [hL, hR]
      exact five_mul_eleven_sq_nineteen_sq_twenty_three_cap)
    (by decide : 0 < 133 * 381)
  convert hthis using 1 <;> ring

lemma eleven_cube_nineteen_sq_twenty_three_sq_overshoot :
    6 * usigma (11 ^ 3) * usigma (19 ^ 2) * usigma (23 ^ 2) <
      5 * σ 1 (11 ^ 3) * σ 1 (19 ^ 2) * σ 1 (23 ^ 2) := by
  rw [usigma_eleven_pow_three, sigma_eleven_pow_three,
    usigma_nineteen_pow_two, sigma_nineteen_pow_two]
  have hσ : σ 1 (23 ^ 2) = 553 := by
    rw [sigma_prime_pow_two (by decide : Nat.Prime 23)]
    decide
  have hu : usigma (23 ^ 2) = 530 := by
    rw [usigma_prime_pow (by decide : Nat.Prime 23) (by decide : 0 < 2)]
    decide
  rw [hσ, hu]
  decide

lemma eleven_sq_nineteen_cube_twenty_three_sq_overshoot :
    6 * usigma (11 ^ 2) * usigma (19 ^ 3) * usigma (23 ^ 2) <
      5 * σ 1 (11 ^ 2) * σ 1 (19 ^ 3) * σ 1 (23 ^ 2) := by
  rw [usigma_eleven_pow_two, sigma_eleven_pow_two,
    usigma_nineteen_pow_three, sigma_nineteen_pow_three]
  have hσ : σ 1 (23 ^ 2) = 553 := by
    rw [sigma_prime_pow_two (by decide : Nat.Prime 23)]
    decide
  have hu : usigma (23 ^ 2) = 530 := by
    rw [usigma_prime_pow (by decide : Nat.Prime 23) (by decide : 0 < 2)]
    decide
  rw [hσ, hu]
  decide

/-- Leftover `6/5` cannot be three squareful primes `11,19,23` times a
squarefree coprime factor. -/
lemma not_five_sigma_of_three_sq_primes_eleven_nineteen_twenty_three {m : ℕ}
    (hm : m ≠ 0) (h : 5 * σ 1 m = 6 * usigma m)
    (hk11 : 2 ≤ padicValNat 11 m) (hk19 : 2 ≤ padicValNat 19 m)
    (hk23 : 2 ≤ padicValNat 23 m)
    (hs : Squarefree (ordCompl[23] (ordCompl[19] (ordCompl[11] m)))) :
    False := by
  have hp11 : Nat.Prime 11 := by decide
  have hp19 : Nat.Prime 19 := by decide
  have hp23 : Nat.Prime 23 := by decide
  have hpq_ne : (11 : ℕ) ≠ 19 := by decide
  have hpr_ne : (11 : ℕ) ≠ 23 := by decide
  have hqr_ne : (19 : ℕ) ≠ 23 := by decide
  have heq := five_sigma_eq_six_of_three_squareful hm hp11 hp19 hp23 hpq_ne
    hpr_ne hqr_ne h hs
  have hproj_p : ordProj[11] m = 11 ^ padicValNat 11 m := by
    simp [Nat.factorization_def m hp11]
  have hproj_q : ordProj[19] (ordCompl[11] m) =
      19 ^ padicValNat 19 (ordCompl[11] m) := by
    simp [Nat.factorization_def (ordCompl[11] m) hp19]
  have hproj_r : ordProj[23] (ordCompl[19] (ordCompl[11] m)) =
      23 ^ padicValNat 23 (ordCompl[19] (ordCompl[11] m)) := by
    simp [Nat.factorization_def (ordCompl[19] (ordCompl[11] m)) hp23]
  rw [hproj_r, padicValNat_ordCompl_of_ne hp23 hqr_ne,
    padicValNat_ordCompl_of_ne hp23 hpr_ne, hproj_q,
    padicValNat_ordCompl_of_ne hp19 hpq_ne, hproj_p] at heq
  rcases eq_or_lt_of_le hk11 with h11eq | h11
  · rw [← h11eq] at heq
    rcases eq_or_lt_of_le hk19 with h19eq | h19
    · rw [← h19eq] at heq
      exact (five_sigma_lt_six_usigma_eleven_sq_nineteen_sq_twenty_three
        (by omega)).ne heq
    · have hover := six_five_overshoot_mono_three hp11 hp19 hp23
        (by decide : 0 < 2) (by decide : 0 < 3) (by decide : 0 < 2)
        (le_refl _) (Nat.succ_le_of_lt h19) hk23
        eleven_sq_nineteen_cube_twenty_three_sq_overshoot
      rw [← heq] at hover
      exact lt_irrefl _ hover
  · have hover := six_five_overshoot_mono_three hp11 hp19 hp23
      (by decide : 0 < 3) (by decide : 0 < 2) (by decide : 0 < 2)
      (Nat.succ_le_of_lt h11) hk19 hk23
      eleven_cube_nineteen_sq_twenty_three_sq_overshoot
    rw [← heq] at hover
    exact lt_irrefl _ hover

lemma usigma_twenty_nine_pow_two : usigma (29 ^ 2) = 842 := by
  rw [usigma_prime_pow (by decide : Nat.Prime 29) (by decide : 0 < 2)]
  decide

lemma sigma_twenty_nine_pow_two : σ 1 (29 ^ 2) = 871 := by
  rw [sigma_prime_pow_two (by decide : Nat.Prime 29)]
  decide

lemma usigma_twenty_nine_pow_three : usigma (29 ^ 3) = 24390 := by
  rw [usigma_prime_pow (by decide : Nat.Prime 29) (by decide : 0 < 3)]
  decide

lemma sigma_twenty_nine_pow_three : σ 1 (29 ^ 3) = 25260 := by
  rw [sigma_prime_pow_div (by decide : Nat.Prime 29)]
  norm_num

lemma usigma_nineteen_pow_four : usigma (19 ^ 4) = 130322 := by
  rw [usigma_prime_pow (by decide : Nat.Prime 19) (by decide : 0 < 4)]
  decide

lemma sigma_nineteen_pow_four : σ 1 (19 ^ 4) = 137561 := by
  rw [sigma_prime_pow_div (by decide : Nat.Prime 19)]
  norm_num

lemma five_mul_eleven_sq_nineteen_twenty_nine_cap :
    5 * 19 * 29 * 133 ≤ 6 * 18 * 28 * 122 := by
  decide

lemma five_mul_nineteen_sq_eleven_twenty_nine_cap :
    5 * 11 * 29 * 381 ≤ 6 * 10 * 28 * 362 := by
  decide

/-- `{11^2, 19^b, 29^k}` undershoots leftover `6/5`. -/
lemma five_sigma_lt_six_usigma_eleven_sq_nineteen_twenty_nine {b k : ℕ}
    (hb : 0 < b) (hk : 0 < k) :
    5 * σ 1 (11 ^ 2) * σ 1 (19 ^ b) * σ 1 (29 ^ k) <
      6 * usigma (11 ^ 2) * usigma (19 ^ b) * usigma (29 ^ k) := by
  rw [sigma_eleven_pow_two, usigma_eleven_pow_two]
  have h19 := sigma_lt_cap_usigma (by decide : Nat.Prime 19) hb
  have h29 := sigma_lt_cap_usigma (by decide : Nat.Prime 29) hk
  have hu19 : 0 < usigma (19 ^ b) := by
    rw [usigma_prime_pow (by decide : Nat.Prime 19) hb]
    exact Nat.add_pos_left (by decide : 0 < 1) _
  have hthis := six_five_of_two_caps_times_const (A := 18) (B := 19)
    (X := σ 1 (19 ^ b)) (Y := usigma (19 ^ b)) (C := 28) (D := 29)
    (P := σ 1 (29 ^ k)) (Q := usigma (29 ^ k)) (S := 122) (T := 133)
    h19 h29 five_mul_eleven_sq_nineteen_twenty_nine_cap
    (by decide : 0 < 19) hu19 (by decide : 0 < 133)
  convert hthis using 1 <;> ring

/-- `{11^a, 19^2, 29^k}` undershoots leftover `6/5`. -/
lemma five_sigma_lt_six_usigma_nineteen_sq_eleven_twenty_nine {a k : ℕ}
    (ha : 0 < a) (hk : 0 < k) :
    5 * σ 1 (11 ^ a) * σ 1 (19 ^ 2) * σ 1 (29 ^ k) <
      6 * usigma (11 ^ a) * usigma (19 ^ 2) * usigma (29 ^ k) := by
  rw [sigma_nineteen_pow_two, usigma_nineteen_pow_two]
  have h11 := sigma_lt_cap_usigma (by decide : Nat.Prime 11) ha
  have h29 := sigma_lt_cap_usigma (by decide : Nat.Prime 29) hk
  have hu11 : 0 < usigma (11 ^ a) := by
    rw [usigma_prime_pow (by decide : Nat.Prime 11) ha]
    exact Nat.add_pos_left (by decide : 0 < 1) _
  have hthis := six_five_of_two_caps_times_const (A := 10) (B := 11)
    (X := σ 1 (11 ^ a)) (Y := usigma (11 ^ a)) (C := 28) (D := 29)
    (P := σ 1 (29 ^ k)) (Q := usigma (29 ^ k)) (S := 362) (T := 381)
    h11 h29 five_mul_nineteen_sq_eleven_twenty_nine_cap
    (by decide : 0 < 11) hu11 (by decide : 0 < 381)
  convert hthis using 1 <;> ring

lemma eleven_cube_nineteen_cube_twenty_nine_sq_under :
    5 * σ 1 (11 ^ 3) * σ 1 (19 ^ 3) * σ 1 (29 ^ 2) <
      6 * usigma (11 ^ 3) * usigma (19 ^ 3) * usigma (29 ^ 2) := by
  rw [sigma_eleven_pow_three, usigma_eleven_pow_three,
    sigma_nineteen_pow_three, usigma_nineteen_pow_three,
    sigma_twenty_nine_pow_two, usigma_twenty_nine_pow_two]
  norm_num

lemma eleven_fourth_nineteen_cube_twenty_nine_sq_overshoot :
    6 * usigma (11 ^ 4) * usigma (19 ^ 3) * usigma (29 ^ 2) <
      5 * σ 1 (11 ^ 4) * σ 1 (19 ^ 3) * σ 1 (29 ^ 2) := by
  rw [usigma_eleven_pow_four, sigma_eleven_pow_four,
    usigma_nineteen_pow_three, sigma_nineteen_pow_three,
    usigma_twenty_nine_pow_two, sigma_twenty_nine_pow_two]
  norm_num

lemma eleven_cube_nineteen_fourth_twenty_nine_sq_overshoot :
    6 * usigma (11 ^ 3) * usigma (19 ^ 4) * usigma (29 ^ 2) <
      5 * σ 1 (11 ^ 3) * σ 1 (19 ^ 4) * σ 1 (29 ^ 2) := by
  rw [usigma_eleven_pow_three, sigma_eleven_pow_three,
    usigma_nineteen_pow_four, sigma_nineteen_pow_four,
    usigma_twenty_nine_pow_two, sigma_twenty_nine_pow_two]
  norm_num

lemma eleven_cube_nineteen_cube_twenty_nine_cube_overshoot :
    6 * usigma (11 ^ 3) * usigma (19 ^ 3) * usigma (29 ^ 3) <
      5 * σ 1 (11 ^ 3) * σ 1 (19 ^ 3) * σ 1 (29 ^ 3) := by
  rw [usigma_eleven_pow_three, sigma_eleven_pow_three,
    usigma_nineteen_pow_three, sigma_nineteen_pow_three,
    usigma_twenty_nine_pow_three, sigma_twenty_nine_pow_three]
  norm_num

/-- Leftover `6/5` cannot be three squareful primes `11,19,29` times a
squarefree coprime factor. -/
lemma not_five_sigma_of_three_sq_primes_eleven_nineteen_twenty_nine {m : ℕ}
    (hm : m ≠ 0) (h : 5 * σ 1 m = 6 * usigma m)
    (hk11 : 2 ≤ padicValNat 11 m) (hk19 : 2 ≤ padicValNat 19 m)
    (hk29 : 2 ≤ padicValNat 29 m)
    (hs : Squarefree (ordCompl[29] (ordCompl[19] (ordCompl[11] m)))) :
    False := by
  have hp11 : Nat.Prime 11 := by decide
  have hp19 : Nat.Prime 19 := by decide
  have hp29 : Nat.Prime 29 := by decide
  have hpq_ne : (11 : ℕ) ≠ 19 := by decide
  have hpr_ne : (11 : ℕ) ≠ 29 := by decide
  have hqr_ne : (19 : ℕ) ≠ 29 := by decide
  have heq := five_sigma_eq_six_of_three_squareful hm hp11 hp19 hp29 hpq_ne
    hpr_ne hqr_ne h hs
  have hproj_p : ordProj[11] m = 11 ^ padicValNat 11 m := by
    simp [Nat.factorization_def m hp11]
  have hproj_q : ordProj[19] (ordCompl[11] m) =
      19 ^ padicValNat 19 (ordCompl[11] m) := by
    simp [Nat.factorization_def (ordCompl[11] m) hp19]
  have hproj_r : ordProj[29] (ordCompl[19] (ordCompl[11] m)) =
      29 ^ padicValNat 29 (ordCompl[19] (ordCompl[11] m)) := by
    simp [Nat.factorization_def (ordCompl[19] (ordCompl[11] m)) hp29]
  rw [hproj_r, padicValNat_ordCompl_of_ne hp29 hqr_ne,
    padicValNat_ordCompl_of_ne hp29 hpr_ne, hproj_q,
    padicValNat_ordCompl_of_ne hp19 hpq_ne, hproj_p] at heq
  rcases eq_or_lt_of_le hk11 with h11eq | h11
  · rw [← h11eq] at heq
    exact (five_sigma_lt_six_usigma_eleven_sq_nineteen_twenty_nine
      (by omega) (by omega)).ne heq
  · rcases eq_or_lt_of_le hk19 with h19eq | h19
    · rw [← h19eq] at heq
      exact (five_sigma_lt_six_usigma_nineteen_sq_eleven_twenty_nine
        (by omega) (by omega)).ne heq
    · have ha3 : 3 ≤ padicValNat 11 m := Nat.succ_le_of_lt h11
      have hb3 : 3 ≤ padicValNat 19 m := Nat.succ_le_of_lt h19
      rcases eq_or_lt_of_le hk29 with h29eq | h29k
      · rw [← h29eq] at heq
        rcases eq_or_lt_of_le ha3 with h11eq3 | h114
        · rw [← h11eq3] at heq
          rcases eq_or_lt_of_le hb3 with h19eq3 | h194
          · rw [← h19eq3] at heq
            exact eleven_cube_nineteen_cube_twenty_nine_sq_under.ne heq
          · have hover := six_five_overshoot_mono_three hp11 hp19 hp29
              (by decide : 0 < 3) (by decide : 0 < 4) (by decide : 0 < 2)
              (le_refl _) (Nat.succ_le_of_lt h194) (le_refl _)
              eleven_cube_nineteen_fourth_twenty_nine_sq_overshoot
            rw [← heq] at hover
            exact lt_irrefl _ hover
        · have hover := six_five_overshoot_mono_three hp11 hp19 hp29
            (by decide : 0 < 4) (by decide : 0 < 3) (by decide : 0 < 2)
            (Nat.succ_le_of_lt h114) hb3 (le_refl _)
            eleven_fourth_nineteen_cube_twenty_nine_sq_overshoot
          rw [← heq] at hover
          exact lt_irrefl _ hover
      · have hover := six_five_overshoot_mono_three hp11 hp19 hp29
          (by decide : 0 < 3) (by decide : 0 < 3) (by decide : 0 < 3)
          ha3 hb3 (Nat.succ_le_of_lt h29k)
          eleven_cube_nineteen_cube_twenty_nine_cube_overshoot
        rw [← heq] at hover
        exact lt_irrefl _ hover

/-- Leftover `6/5` cannot be three squareful primes `11,19,p` with
`p ≥ 23` times a squarefree coprime factor. -/
lemma not_five_sigma_of_three_sq_primes_eleven_nineteen {m p : ℕ}
    (hm : m ≠ 0) (hp : p.Prime) (hp23 : 23 ≤ p)
    (h : 5 * σ 1 m = 6 * usigma m)
    (hk11 : 2 ≤ padicValNat 11 m) (hk19 : 2 ≤ padicValNat 19 m)
    (hkp : 2 ≤ padicValNat p m)
    (hs : Squarefree (ordCompl[p] (ordCompl[19] (ordCompl[11] m)))) : False := by
  rcases le_or_gt p 23 with h23 | h24
  · have hp23eq : p = 23 := le_antisymm h23 hp23
    subst p
    exact not_five_sigma_of_three_sq_primes_eleven_nineteen_twenty_three hm h
      hk11 hk19 hkp hs
  · have hp29 : 29 ≤ p := prime_ge_twenty_four_ge_twenty_nine hp (by omega)
    rcases le_or_gt p 29 with h29 | h30
    · have hp29eq : p = 29 := le_antisymm h29 hp29
      subst p
      exact not_five_sigma_of_three_sq_primes_eleven_nineteen_twenty_nine hm h
        hk11 hk19 hkp hs
    · have hp31 : 31 ≤ p := by
        have hmem : p = 30 ∨ 31 ≤ p := by omega
        rcases hmem with rfl | h31
        · exact False.elim ((by decide : ¬ Nat.Prime 30) hp)
        · exact h31
      exact not_five_sigma_of_three_sq_primes_eleven_nineteen_large hm hp hp31 h
        hk11 hk19 hkp hs

lemma prime_ge_one_ten_ge_one_thirteen {p : ℕ} (hp : p.Prime)
    (h : 110 ≤ p) : 113 ≤ p := by
  have hmem : p = 110 ∨ p = 111 ∨ p = 112 ∨ 113 ≤ p := by omega
  rcases hmem with rfl | rfl | rfl | h113
  · exact False.elim ((by decide : ¬ Nat.Prime 110) hp)
  · exact False.elim ((by decide : ¬ Nat.Prime 111) hp)
  · exact False.elim ((by decide : ¬ Nat.Prime 112) hp)
  · exact h113

lemma forty_nine_twenty_three_sq_r_sq_overshoot_six_five {r : ℕ}
    (hr : r.Prime) (h29 : 29 ≤ r) (h109 : r ≤ 109) :
    6 * usigma (7 ^ 2) * usigma (23 ^ 2) * usigma (r ^ 2) <
      5 * σ 1 (7 ^ 2) * σ 1 (23 ^ 2) * σ 1 (r ^ 2) := by
  have hp7 : Nat.Prime 7 := by decide
  have hp23 : Nat.Prime 23 := by decide
  have hσ7 : σ 1 (7 ^ 2) = 57 := by
    rw [sigma_prime_pow_two hp7]
    decide
  have hu7 : usigma (7 ^ 2) = 50 := by
    simpa using usigma_prime_pow hp7 (by decide : 0 < 2)
  have hσ23 : σ 1 (23 ^ 2) = 553 := by
    rw [sigma_prime_pow_two hp23]
    decide
  have hu23 : usigma (23 ^ 2) = 530 := by
    simpa using usigma_prime_pow hp23 (by decide : 0 < 2)
  rw [hσ7, hu7, hσ23, hu23,
    sigma_prime_pow_two hr, usigma_prime_pow hr (by decide : 0 < 2)]
  have hsq : r ^ 2 ≤ 109 * r := by
    rw [pow_two]
    exact Nat.mul_le_mul_right r h109
  have hleft : 1395 * (1 + r ^ 2) < 157605 * r := by
    have h1 : 1395 * (1 + r ^ 2) ≤ 1395 * (1 + 109 * r) :=
      Nat.mul_le_mul_left 1395 (Nat.add_le_add_left hsq 1)
    have h2 : 1395 * (1 + 109 * r) = 1395 + 152055 * r := by
      have : 1395 * 109 = 152055 := by decide
      ring
    have h3 : 1395 + 152055 * r < 157605 * r := by
      have : 1395 < 5550 * r :=
        lt_of_lt_of_le (by decide : 1395 < 160950)
          (Nat.mul_le_mul_left 5550 h29)
      omega
    calc
      1395 * (1 + r ^ 2) ≤ 1395 * (1 + 109 * r) := h1
      _ = 1395 + 152055 * r := h2
      _ < 157605 * r := h3
  have hL : 6 * 50 * 530 * (1 + r ^ 2) = 159000 * (1 + r ^ 2) := by ring
  have hR : 5 * 57 * 553 * (1 + r + r ^ 2) = 157605 * (1 + r + r ^ 2) := by ring
  have hmain : 159000 * (1 + r ^ 2) < 157605 * (1 + r + r ^ 2) := by
    have h1 : 159000 * (1 + r ^ 2) =
        157605 * (1 + r ^ 2) + 1395 * (1 + r ^ 2) := by ring
    have h2 : 157605 * (1 + r + r ^ 2) =
        157605 * (1 + r ^ 2) + 157605 * r := by ring
    rw [h1, h2]
    exact Nat.add_lt_add_left hleft _
  rw [hL, hR]
  exact hmain

lemma seven_twenty_three_r_sq_pow_ge_two_overshoot_six_five {r a b c : ℕ}
    (hr : r.Prime) (h29 : 29 ≤ r) (h109 : r ≤ 109)
    (ha : 2 ≤ a) (hb : 2 ≤ b) (hc : 2 ≤ c) :
    6 * usigma (7 ^ a) * usigma (23 ^ b) * usigma (r ^ c) <
      5 * σ 1 (7 ^ a) * σ 1 (23 ^ b) * σ 1 (r ^ c) :=
  six_five_overshoot_mono_three (by decide : Nat.Prime 7)
    (by decide : Nat.Prime 23) hr
    (by decide : 0 < 2) (by decide : 0 < 2) (by decide : 0 < 2)
    ha hb hc (forty_nine_twenty_three_sq_r_sq_overshoot_six_five hr h29 h109)

lemma usigma_twenty_three_pow_three : usigma (23 ^ 3) = 12168 := by
  rw [usigma_prime_pow (by decide : Nat.Prime 23) (by decide : 0 < 3)]
  decide

lemma sigma_twenty_three_pow_three : σ 1 (23 ^ 3) = 12720 := by
  rw [sigma_prime_pow_div (by decide : Nat.Prime 23)]
  norm_num

lemma forty_nine_twenty_three_cube_r_sq_overshoot_six_five {r : ℕ}
    (hr : r.Prime) (h29 : 29 ≤ r) (h139 : r ≤ 139) :
    6 * usigma (7 ^ 2) * usigma (23 ^ 3) * usigma (r ^ 2) <
      5 * σ 1 (7 ^ 2) * σ 1 (23 ^ 3) * σ 1 (r ^ 2) := by
  have hp7 : Nat.Prime 7 := by decide
  have hσ7 : σ 1 (7 ^ 2) = 57 := by
    rw [sigma_prime_pow_two hp7]
    decide
  have hu7 : usigma (7 ^ 2) = 50 := by
    simpa using usigma_prime_pow hp7 (by decide : 0 < 2)
  rw [hσ7, hu7, sigma_twenty_three_pow_three, usigma_twenty_three_pow_three,
    sigma_prime_pow_two hr, usigma_prime_pow hr (by decide : 0 < 2)]
  have hsq : r ^ 2 ≤ 139 * r := by
    rw [pow_two]
    exact Nat.mul_le_mul_right r h139
  have hleft : 25200 * (1 + r ^ 2) < 3625200 * r := by
    have h1 : 25200 * (1 + r ^ 2) ≤ 25200 * (1 + 139 * r) :=
      Nat.mul_le_mul_left 25200 (Nat.add_le_add_left hsq 1)
    have h2 : 25200 * (1 + 139 * r) = 25200 + 3502800 * r := by
      have : 25200 * 139 = 3502800 := by decide
      ring
    have h3 : 25200 + 3502800 * r < 3625200 * r := by
      have : 25200 < 122400 * r :=
        lt_of_lt_of_le (by decide : 25200 < 3549600)
          (Nat.mul_le_mul_left 122400 h29)
      omega
    calc
      25200 * (1 + r ^ 2) ≤ 25200 * (1 + 139 * r) := h1
      _ = 25200 + 3502800 * r := h2
      _ < 3625200 * r := h3
  have hL : 6 * 50 * 12168 * (1 + r ^ 2) = 3650400 * (1 + r ^ 2) := by ring
  have hR : 5 * 57 * 12720 * (1 + r + r ^ 2) = 3625200 * (1 + r + r ^ 2) :=
    by ring
  have hmain : 3650400 * (1 + r ^ 2) < 3625200 * (1 + r + r ^ 2) := by
    have h1 : 3650400 * (1 + r ^ 2) =
        3625200 * (1 + r ^ 2) + 25200 * (1 + r ^ 2) := by ring
    have h2 : 3625200 * (1 + r + r ^ 2) =
        3625200 * (1 + r ^ 2) + 3625200 * r := by ring
    rw [h1, h2]
    exact Nat.add_lt_add_left hleft _
  rw [hL, hR]
  exact hmain

lemma seven_sq_twenty_three_cube_r_pow_ge_two_overshoot_six_five
    {r a b c : ℕ} (hr : r.Prime) (h29 : 29 ≤ r) (h139 : r ≤ 139)
    (ha : 2 ≤ a) (hb : 3 ≤ b) (hc : 2 ≤ c) :
    6 * usigma (7 ^ a) * usigma (23 ^ b) * usigma (r ^ c) <
      5 * σ 1 (7 ^ a) * σ 1 (23 ^ b) * σ 1 (r ^ c) :=
  six_five_overshoot_mono_three (by decide : Nat.Prime 7)
    (by decide : Nat.Prime 23) hr
    (by decide : 0 < 2) (by decide : 0 < 3) (by decide : 0 < 2)
    ha hb hc (forty_nine_twenty_three_cube_r_sq_overshoot_six_five hr h29 h139)

lemma seven_cube_twenty_three_r_overshoot_six_five {r a b c : ℕ}
    (hr : r.Prime) (ha : 3 ≤ a) (hb : 2 ≤ b) (_hc : 0 < c) :
    6 * usigma (7 ^ a) * usigma (23 ^ b) * usigma (r ^ c) <
      5 * σ 1 (7 ^ a) * σ 1 (23 ^ b) * σ 1 (r ^ c) := by
  have hover := seven_cube_q_pow_ge_two_overshoot_six_five
    (by decide : Nat.Prime 23) (by decide : 11 ≤ 23) (by decide : 23 ≤ 31)
    ha hb
  have h := six_five_overshoot_mul (s := usigma (7 ^ a) * usigma (23 ^ b))
      (t := σ 1 (7 ^ a) * σ 1 (23 ^ b)) (n := r ^ c)
      (Nat.pow_pos hr.pos).ne' (by simpa [mul_assoc] using hover)
  simpa [mul_assoc] using h

lemma five_mul_forty_nine_twenty_three_sq_cap {r : ℕ} (hr : 127 ≤ r) :
    5 * r * 57 * 553 ≤ 6 * (r - 1) * 50 * 530 := by
  have hdiff : 159000 ≤ 1395 * r := by
    have hmul : 1395 * 127 ≤ 1395 * r := Nat.mul_le_mul_left 1395 hr
    have hnum : 1395 * 127 = 177165 := by decide
    omega
  have hL : 5 * r * 57 * 553 = 157605 * r := by ring
  have hR : 6 * (r - 1) * 50 * 530 = 159000 * (r - 1) := by ring
  have hmain : 157605 * r ≤ 159000 * (r - 1) := by
    have heq : 157605 * r + 1395 * r = 159000 * r := by ring
    have hsub : 157605 * r = 159000 * r - 1395 * r :=
      (Nat.sub_eq_of_eq_add heq.symm).symm
    have hle : 159000 * r - 1395 * r ≤ 159000 * r - 159000 :=
      Nat.sub_le_sub_left hdiff _
    have hrw : 159000 * r - 159000 = 159000 * (r - 1) := by
      simpa using (Nat.mul_sub_left_distrib 159000 r 1).symm
    calc
      157605 * r = 159000 * r - 1395 * r := hsub
      _ ≤ 159000 * r - 159000 := hle
      _ = 159000 * (r - 1) := hrw
  rw [hL, hR]
  exact hmain

lemma five_sigma_lt_six_usigma_seven_sq_twenty_three_sq_large {r k : ℕ}
    (hr : r.Prime) (hr127 : 127 ≤ r) (hk : 0 < k) :
    5 * σ 1 (7 ^ 2) * σ 1 (23 ^ 2) * σ 1 (r ^ k) <
      6 * usigma (7 ^ 2) * usigma (23 ^ 2) * usigma (r ^ k) := by
  have hp7 : Nat.Prime 7 := by decide
  have hp23 : Nat.Prime 23 := by decide
  have hσ7 : σ 1 (7 ^ 2) = 57 := by
    rw [sigma_prime_pow_two hp7]
    decide
  have hu7 : usigma (7 ^ 2) = 50 := by
    simpa using usigma_prime_pow hp7 (by decide : 0 < 2)
  have hσ23 : σ 1 (23 ^ 2) = 553 := by
    rw [sigma_prime_pow_two hp23]
    decide
  have hu23 : usigma (23 ^ 2) = 530 := by
    simpa using usigma_prime_pow hp23 (by decide : 0 < 2)
  rw [hσ7, hu7, hσ23, hu23]
  have hcp := sigma_lt_cap_usigma hr hk
  have hthis := six_five_of_cap_times_const (A := r - 1) (B := r)
    (X := σ 1 (r ^ k)) (Y := usigma (r ^ k)) (S := 50 * 530) (T := 57 * 553)
    hcp (by
      have hL : 5 * r * (57 * 553) = 5 * r * 57 * 553 := by ring
      have hR : 6 * (r - 1) * (50 * 530) = 6 * (r - 1) * 50 * 530 := by ring
      rw [hL, hR]
      exact five_mul_forty_nine_twenty_three_sq_cap hr127)
    (by decide : 0 < 57 * 553)
  convert hthis using 1 <;> ring

lemma five_mul_forty_nine_twenty_three_cap {r : ℕ} (hr : 149 ≤ r) :
    5 * 23 * r * 57 ≤ 6 * 22 * (r - 1) * 50 := by
  have hdiff : 6600 ≤ 45 * r := by
    have hmul : 45 * 149 ≤ 45 * r := Nat.mul_le_mul_left 45 hr
    have hnum : 45 * 149 = 6705 := by decide
    omega
  have hL : 5 * 23 * r * 57 = 6555 * r := by ring
  have hR : 6 * 22 * (r - 1) * 50 = 6600 * (r - 1) := by ring
  have hmain : 6555 * r ≤ 6600 * (r - 1) := by
    have heq : 6555 * r + 45 * r = 6600 * r := by ring
    have hsub : 6555 * r = 6600 * r - 45 * r :=
      (Nat.sub_eq_of_eq_add heq.symm).symm
    have hle : 6600 * r - 45 * r ≤ 6600 * r - 6600 :=
      Nat.sub_le_sub_left hdiff _
    have hrw : 6600 * r - 6600 = 6600 * (r - 1) := by
      simpa using (Nat.mul_sub_left_distrib 6600 r 1).symm
    calc
      6555 * r = 6600 * r - 45 * r := hsub
      _ ≤ 6600 * r - 6600 := hle
      _ = 6600 * (r - 1) := hrw
  rw [hL, hR]
  exact hmain

lemma five_sigma_lt_six_usigma_seven_sq_twenty_three_large {r b c : ℕ}
    (hr : r.Prime) (hr149 : 149 ≤ r) (hb : 0 < b) (hc : 0 < c) :
    5 * σ 1 (7 ^ 2) * σ 1 (23 ^ b) * σ 1 (r ^ c) <
      6 * usigma (7 ^ 2) * usigma (23 ^ b) * usigma (r ^ c) := by
  have hp7 : Nat.Prime 7 := by decide
  have hσ7 : σ 1 (7 ^ 2) = 57 := by
    rw [sigma_prime_pow_two hp7]
    decide
  have hu7 : usigma (7 ^ 2) = 50 := by
    simpa using usigma_prime_pow hp7 (by decide : 0 < 2)
  rw [hσ7, hu7]
  have h23 := sigma_lt_cap_usigma (by decide : Nat.Prime 23) hb
  have hrcap := sigma_lt_cap_usigma hr hc
  have hu23 : 0 < usigma (23 ^ b) := by
    rw [usigma_prime_pow (by decide : Nat.Prime 23) hb]
    exact Nat.add_pos_left (by decide : 0 < 1) _
  have hthis := six_five_of_two_caps_times_const (A := 22) (B := 23)
    (X := σ 1 (23 ^ b)) (Y := usigma (23 ^ b)) (C := r - 1) (D := r)
    (P := σ 1 (r ^ c)) (Q := usigma (r ^ c)) (S := 50) (T := 57)
    h23 hrcap (five_mul_forty_nine_twenty_three_cap hr149)
    (by decide : 0 < 23) hu23 (by decide : 0 < 57)
  convert hthis using 1 <;> ring

lemma usigma_one_thirteen_pow_two : usigma (113 ^ 2) = 12770 := by
  rw [usigma_prime_pow (by decide : Nat.Prime 113) (by decide : 0 < 2)]
  decide

lemma sigma_one_thirteen_pow_two : σ 1 (113 ^ 2) = 12883 := by
  rw [sigma_prime_pow_two (by decide : Nat.Prime 113)]
  decide

lemma usigma_one_thirteen_pow_three : usigma (113 ^ 3) = 1442898 := by
  rw [usigma_prime_pow (by decide : Nat.Prime 113) (by decide : 0 < 3)]
  decide

lemma sigma_one_thirteen_pow_three : σ 1 (113 ^ 3) = 1455780 := by
  rw [sigma_prime_pow_div (by decide : Nat.Prime 113)]
  norm_num

lemma forty_nine_twenty_three_sq_one_thirteen_sq_under :
    5 * σ 1 (7 ^ 2) * σ 1 (23 ^ 2) * σ 1 (113 ^ 2) <
      6 * usigma (7 ^ 2) * usigma (23 ^ 2) * usigma (113 ^ 2) := by
  have hp7 : Nat.Prime 7 := by decide
  have hp23 : Nat.Prime 23 := by decide
  have hσ7 : σ 1 (7 ^ 2) = 57 := by
    rw [sigma_prime_pow_two hp7]
    decide
  have hu7 : usigma (7 ^ 2) = 50 := by
    simpa using usigma_prime_pow hp7 (by decide : 0 < 2)
  have hσ23 : σ 1 (23 ^ 2) = 553 := by
    rw [sigma_prime_pow_two hp23]
    decide
  have hu23 : usigma (23 ^ 2) = 530 := by
    simpa using usigma_prime_pow hp23 (by decide : 0 < 2)
  rw [hσ7, hu7, hσ23, hu23, sigma_one_thirteen_pow_two, usigma_one_thirteen_pow_two]
  decide

lemma forty_nine_twenty_three_sq_one_thirteen_cube_overshoot :
    6 * usigma (7 ^ 2) * usigma (23 ^ 2) * usigma (113 ^ 3) <
      5 * σ 1 (7 ^ 2) * σ 1 (23 ^ 2) * σ 1 (113 ^ 3) := by
  have hp7 : Nat.Prime 7 := by decide
  have hp23 : Nat.Prime 23 := by decide
  have hσ7 : σ 1 (7 ^ 2) = 57 := by
    rw [sigma_prime_pow_two hp7]
    decide
  have hu7 : usigma (7 ^ 2) = 50 := by
    simpa using usigma_prime_pow hp7 (by decide : 0 < 2)
  have hσ23 : σ 1 (23 ^ 2) = 553 := by
    rw [sigma_prime_pow_two hp23]
    decide
  have hu23 : usigma (23 ^ 2) = 530 := by
    simpa using usigma_prime_pow hp23 (by decide : 0 < 2)
  rw [hu7, hσ7, hu23, hσ23, usigma_one_thirteen_pow_three, sigma_one_thirteen_pow_three]
  norm_num

/-- Leftover `6/5` cannot be three squareful primes `7,23,113` times a
squarefree coprime factor. -/
lemma not_five_sigma_of_three_sq_primes_seven_twenty_three_one_thirteen {m : ℕ}
    (hm : m ≠ 0) (h : 5 * σ 1 m = 6 * usigma m)
    (hk7 : 2 ≤ padicValNat 7 m) (hk23 : 2 ≤ padicValNat 23 m)
    (hk113 : 2 ≤ padicValNat 113 m)
    (hs : Squarefree (ordCompl[113] (ordCompl[23] (ordCompl[7] m)))) :
    False := by
  have hp7 : Nat.Prime 7 := by decide
  have hp23 : Nat.Prime 23 := by decide
  have hp113 : Nat.Prime 113 := by decide
  have hpq_ne : (7 : ℕ) ≠ 23 := by decide
  have hpr_ne : (7 : ℕ) ≠ 113 := by decide
  have hqr_ne : (23 : ℕ) ≠ 113 := by decide
  have heq := five_sigma_eq_six_of_three_squareful hm hp7 hp23 hp113 hpq_ne
    hpr_ne hqr_ne h hs
  have hproj_p : ordProj[7] m = 7 ^ padicValNat 7 m := by
    simp [Nat.factorization_def m hp7]
  have hproj_q : ordProj[23] (ordCompl[7] m) =
      23 ^ padicValNat 23 (ordCompl[7] m) := by
    simp [Nat.factorization_def (ordCompl[7] m) hp23]
  have hproj_r : ordProj[113] (ordCompl[23] (ordCompl[7] m)) =
      113 ^ padicValNat 113 (ordCompl[23] (ordCompl[7] m)) := by
    simp [Nat.factorization_def (ordCompl[23] (ordCompl[7] m)) hp113]
  rw [hproj_r, padicValNat_ordCompl_of_ne hp113 hqr_ne,
    padicValNat_ordCompl_of_ne hp113 hpr_ne, hproj_q,
    padicValNat_ordCompl_of_ne hp23 hpq_ne, hproj_p] at heq
  rcases eq_or_lt_of_le hk7 with h7eq | h73
  · rw [← h7eq] at heq
    rcases eq_or_lt_of_le hk23 with h23eq | h233
    · rw [← h23eq] at heq
      rcases eq_or_lt_of_le hk113 with h113eq | h113k
      · rw [← h113eq] at heq
        exact forty_nine_twenty_three_sq_one_thirteen_sq_under.ne heq
      · have hover := six_five_overshoot_mono_three hp7 hp23 hp113
          (by decide : 0 < 2) (by decide : 0 < 2) (by decide : 0 < 3)
          (le_refl _) (le_refl _) (Nat.succ_le_of_lt h113k)
          forty_nine_twenty_three_sq_one_thirteen_cube_overshoot
        rw [← heq] at hover
        exact lt_irrefl _ hover
    · have hover := seven_sq_twenty_three_cube_r_pow_ge_two_overshoot_six_five
        hp113 (by decide : 29 ≤ 113) (by decide : 113 ≤ 139)
        (le_refl _) (Nat.succ_le_of_lt h233) hk113
      rw [← heq] at hover
      exact lt_irrefl _ hover
  · have hover := seven_cube_twenty_three_r_overshoot_six_five (c := padicValNat 113 m)
      hp113 (Nat.succ_le_of_lt h73) hk23
      (lt_of_lt_of_le (by decide : (0 : ℕ) < 2) hk113)
    rw [← heq] at hover
    exact lt_irrefl _ hover

/-- Leftover `6/5` cannot be three squareful primes `7,23,r` with
`r ≥ 29` times a squarefree coprime factor. -/
lemma not_five_sigma_of_three_sq_primes_seven_twenty_three {m r : ℕ}
    (hm : m ≠ 0) (hr : r.Prime) (hr29 : 29 ≤ r)
    (h : 5 * σ 1 m = 6 * usigma m)
    (hk7 : 2 ≤ padicValNat 7 m) (hk23 : 2 ≤ padicValNat 23 m)
    (hkr : 2 ≤ padicValNat r m)
    (hs : Squarefree (ordCompl[r] (ordCompl[23] (ordCompl[7] m)))) : False := by
  have hp7 : Nat.Prime 7 := by decide
  have hp23 : Nat.Prime 23 := by decide
  have hpq_ne : (7 : ℕ) ≠ 23 := by decide
  have hpr_ne : (7 : ℕ) ≠ r :=
    Nat.ne_of_lt (lt_of_lt_of_le (by decide : 7 < 29) hr29)
  have hqr_ne : (23 : ℕ) ≠ r :=
    Nat.ne_of_lt (lt_of_lt_of_le (by decide : 23 < 29) hr29)
  have heq := five_sigma_eq_six_of_three_squareful hm hp7 hp23 hr hpq_ne hpr_ne
    hqr_ne h hs
  have hproj_p : ordProj[7] m = 7 ^ padicValNat 7 m := by
    simp [Nat.factorization_def m hp7]
  have hproj_q : ordProj[23] (ordCompl[7] m) =
      23 ^ padicValNat 23 (ordCompl[7] m) := by
    simp [Nat.factorization_def (ordCompl[7] m) hp23]
  have hproj_r : ordProj[r] (ordCompl[23] (ordCompl[7] m)) =
      r ^ padicValNat r (ordCompl[23] (ordCompl[7] m)) := by
    simp [Nat.factorization_def (ordCompl[23] (ordCompl[7] m)) hr]
  rw [hproj_r, padicValNat_ordCompl_of_ne hr hqr_ne,
    padicValNat_ordCompl_of_ne hr hpr_ne, hproj_q,
    padicValNat_ordCompl_of_ne hp23 hpq_ne, hproj_p] at heq
  rcases eq_or_lt_of_le hk7 with h7eq | h73
  · rw [← h7eq] at heq
    rcases eq_or_lt_of_le hk23 with h23eq | h233
    · rw [← h23eq] at heq
      rcases le_or_gt r 109 with h109 | h110
      · have hover := seven_twenty_three_r_sq_pow_ge_two_overshoot_six_five
          hr hr29 h109 (le_refl _) (le_refl _) hkr
        rw [← heq] at hover
        exact lt_irrefl _ hover
      · have hr113 : 113 ≤ r :=
          prime_ge_one_ten_ge_one_thirteen hr (Nat.succ_le_of_lt h110)
        rcases le_or_gt r 113 with h113 | h114
        · have hr113eq : r = 113 := le_antisymm h113 hr113
          subst r
          exact not_five_sigma_of_three_sq_primes_seven_twenty_three_one_thirteen
            hm h hk7 hk23 hkr hs
        · have hr127 : 127 ≤ r :=
            prime_ge_one_fourteen_ge_one_twenty_seven hr
              (Nat.succ_le_of_lt h114)
          exact (five_sigma_lt_six_usigma_seven_sq_twenty_three_sq_large hr
            hr127 (by omega)).ne heq
    · rcases le_or_gt r 139 with h139 | h140
      · have hover := seven_sq_twenty_three_cube_r_pow_ge_two_overshoot_six_five
          hr hr29 h139 (le_refl _) (Nat.succ_le_of_lt h233) hkr
        rw [← heq] at hover
        exact lt_irrefl _ hover
      · have hr149 : 149 ≤ r :=
          prime_ge_one_forty_ge_one_forty_nine hr (Nat.succ_le_of_lt h140)
        exact (five_sigma_lt_six_usigma_seven_sq_twenty_three_large hr hr149
          (by omega) (by omega)).ne heq
  · have hover := seven_cube_twenty_three_r_overshoot_six_five (c := padicValNat r m)
      hr (Nat.succ_le_of_lt h73) hk23
      (lt_of_lt_of_le (by decide : (0 : ℕ) < 2) hkr)
    rw [← heq] at hover
    exact lt_irrefl _ hover

lemma prime_ge_thirty_ge_thirty_one {p : ℕ} (hp : p.Prime)
    (h : 30 ≤ p) : 31 ≤ p := by
  have hmem : p = 30 ∨ 31 ≤ p := by omega
  rcases hmem with rfl | h31
  · exact False.elim ((by decide : ¬ Nat.Prime 30) hp)
  · exact h31

lemma prime_ge_fifty_four_ge_fifty_nine {p : ℕ} (hp : p.Prime)
    (h : 54 ≤ p) : 59 ≤ p := by
  have hmem : p = 54 ∨ p = 55 ∨ p = 56 ∨ p = 57 ∨ p = 58 ∨ 59 ≤ p := by omega
  rcases hmem with rfl | rfl | rfl | rfl | rfl | h59
  · exact False.elim ((by decide : ¬ Nat.Prime 54) hp)
  · exact False.elim ((by decide : ¬ Nat.Prime 55) hp)
  · exact False.elim ((by decide : ¬ Nat.Prime 56) hp)
  · exact False.elim ((by decide : ¬ Nat.Prime 57) hp)
  · exact False.elim ((by decide : ¬ Nat.Prime 58) hp)
  · exact h59

lemma prime_ge_sixty_two_ge_sixty_seven {p : ℕ} (hp : p.Prime)
    (h : 62 ≤ p) : 67 ≤ p := by
  have hmem : p = 62 ∨ p = 63 ∨ p = 64 ∨ p = 65 ∨ p = 66 ∨ 67 ≤ p := by omega
  rcases hmem with rfl | rfl | rfl | rfl | rfl | h67
  · exact False.elim ((by decide : ¬ Nat.Prime 62) hp)
  · exact False.elim ((by decide : ¬ Nat.Prime 63) hp)
  · exact False.elim ((by decide : ¬ Nat.Prime 64) hp)
  · exact False.elim ((by decide : ¬ Nat.Prime 65) hp)
  · exact False.elim ((by decide : ¬ Nat.Prime 66) hp)
  · exact h67

lemma forty_nine_twenty_nine_sq_r_sq_overshoot_six_five {r : ℕ}
    (hr : r.Prime) (h31 : 31 ≤ r) (h53 : r ≤ 53) :
    6 * usigma (7 ^ 2) * usigma (29 ^ 2) * usigma (r ^ 2) <
      5 * σ 1 (7 ^ 2) * σ 1 (29 ^ 2) * σ 1 (r ^ 2) := by
  have hp7 : Nat.Prime 7 := by decide
  have hσ7 : σ 1 (7 ^ 2) = 57 := by
    rw [sigma_prime_pow_two hp7]
    decide
  have hu7 : usigma (7 ^ 2) = 50 := by
    simpa using usigma_prime_pow hp7 (by decide : 0 < 2)
  rw [hσ7, hu7, sigma_twenty_nine_pow_two, usigma_twenty_nine_pow_two,
    sigma_prime_pow_two hr, usigma_prime_pow hr (by decide : 0 < 2)]
  have hsq : r ^ 2 ≤ 53 * r := by
    rw [pow_two]
    exact Nat.mul_le_mul_right r h53
  have hleft : 4365 * (1 + r ^ 2) < 248235 * r := by
    have h1 : 4365 * (1 + r ^ 2) ≤ 4365 * (1 + 53 * r) :=
      Nat.mul_le_mul_left 4365 (Nat.add_le_add_left hsq 1)
    have h2 : 4365 * (1 + 53 * r) = 4365 + 231345 * r := by
      have : 4365 * 53 = 231345 := by decide
      ring
    have h3 : 4365 + 231345 * r < 248235 * r := by
      have : 4365 < 16890 * r :=
        lt_of_lt_of_le (by decide : 4365 < 523590)
          (Nat.mul_le_mul_left 16890 h31)
      omega
    calc
      4365 * (1 + r ^ 2) ≤ 4365 * (1 + 53 * r) := h1
      _ = 4365 + 231345 * r := h2
      _ < 248235 * r := h3
  have hL : 6 * 50 * 842 * (1 + r ^ 2) = 252600 * (1 + r ^ 2) := by ring
  have hR : 5 * 57 * 871 * (1 + r + r ^ 2) = 248235 * (1 + r + r ^ 2) := by ring
  have hmain : 252600 * (1 + r ^ 2) < 248235 * (1 + r + r ^ 2) := by
    have h1 : 252600 * (1 + r ^ 2) =
        248235 * (1 + r ^ 2) + 4365 * (1 + r ^ 2) := by ring
    have h2 : 248235 * (1 + r + r ^ 2) =
        248235 * (1 + r ^ 2) + 248235 * r := by ring
    rw [h1, h2]
    exact Nat.add_lt_add_left hleft _
  rw [hL, hR]
  exact hmain

lemma seven_twenty_nine_r_sq_pow_ge_two_overshoot_six_five {r a b c : ℕ}
    (hr : r.Prime) (h31 : 31 ≤ r) (h53 : r ≤ 53)
    (ha : 2 ≤ a) (hb : 2 ≤ b) (hc : 2 ≤ c) :
    6 * usigma (7 ^ a) * usigma (29 ^ b) * usigma (r ^ c) <
      5 * σ 1 (7 ^ a) * σ 1 (29 ^ b) * σ 1 (r ^ c) :=
  six_five_overshoot_mono_three (by decide : Nat.Prime 7)
    (by decide : Nat.Prime 29) hr
    (by decide : 0 < 2) (by decide : 0 < 2) (by decide : 0 < 2)
    ha hb hc (forty_nine_twenty_nine_sq_r_sq_overshoot_six_five hr h31 h53)

lemma forty_nine_twenty_nine_cube_r_sq_overshoot_six_five {r : ℕ}
    (hr : r.Prime) (h31 : 31 ≤ r) (h61 : r ≤ 61) :
    6 * usigma (7 ^ 2) * usigma (29 ^ 3) * usigma (r ^ 2) <
      5 * σ 1 (7 ^ 2) * σ 1 (29 ^ 3) * σ 1 (r ^ 2) := by
  have hp7 : Nat.Prime 7 := by decide
  have hσ7 : σ 1 (7 ^ 2) = 57 := by
    rw [sigma_prime_pow_two hp7]
    decide
  have hu7 : usigma (7 ^ 2) = 50 := by
    simpa using usigma_prime_pow hp7 (by decide : 0 < 2)
  rw [hσ7, hu7, sigma_twenty_nine_pow_three, usigma_twenty_nine_pow_three,
    sigma_prime_pow_two hr, usigma_prime_pow hr (by decide : 0 < 2)]
  have hsq : r ^ 2 ≤ 61 * r := by
    rw [pow_two]
    exact Nat.mul_le_mul_right r h61
  have hleft : 117900 * (1 + r ^ 2) < 7199100 * r := by
    have h1 : 117900 * (1 + r ^ 2) ≤ 117900 * (1 + 61 * r) :=
      Nat.mul_le_mul_left 117900 (Nat.add_le_add_left hsq 1)
    have h2 : 117900 * (1 + 61 * r) = 117900 + 7191900 * r := by
      have : 117900 * 61 = 7191900 := by decide
      ring
    have h3 : 117900 + 7191900 * r < 7199100 * r := by
      have : 117900 < 7200 * r :=
        lt_of_lt_of_le (by decide : 117900 < 223200)
          (Nat.mul_le_mul_left 7200 h31)
      omega
    calc
      117900 * (1 + r ^ 2) ≤ 117900 * (1 + 61 * r) := h1
      _ = 117900 + 7191900 * r := h2
      _ < 7199100 * r := h3
  have hL : 6 * 50 * 24390 * (1 + r ^ 2) = 7317000 * (1 + r ^ 2) := by ring
  have hR : 5 * 57 * 25260 * (1 + r + r ^ 2) = 7199100 * (1 + r + r ^ 2) :=
    by ring
  have hmain : 7317000 * (1 + r ^ 2) < 7199100 * (1 + r + r ^ 2) := by
    have h1 : 7317000 * (1 + r ^ 2) =
        7199100 * (1 + r ^ 2) + 117900 * (1 + r ^ 2) := by ring
    have h2 : 7199100 * (1 + r + r ^ 2) =
        7199100 * (1 + r ^ 2) + 7199100 * r := by ring
    rw [h1, h2]
    exact Nat.add_lt_add_left hleft _
  rw [hL, hR]
  exact hmain

lemma seven_sq_twenty_nine_cube_r_pow_ge_two_overshoot_six_five
    {r a b c : ℕ} (hr : r.Prime) (h31 : 31 ≤ r) (h61 : r ≤ 61)
    (ha : 2 ≤ a) (hb : 3 ≤ b) (hc : 2 ≤ c) :
    6 * usigma (7 ^ a) * usigma (29 ^ b) * usigma (r ^ c) <
      5 * σ 1 (7 ^ a) * σ 1 (29 ^ b) * σ 1 (r ^ c) :=
  six_five_overshoot_mono_three (by decide : Nat.Prime 7)
    (by decide : Nat.Prime 29) hr
    (by decide : 0 < 2) (by decide : 0 < 3) (by decide : 0 < 2)
    ha hb hc (forty_nine_twenty_nine_cube_r_sq_overshoot_six_five hr h31 h61)

lemma seven_cube_twenty_nine_r_overshoot_six_five {r a b c : ℕ}
    (hr : r.Prime) (ha : 3 ≤ a) (hb : 2 ≤ b) (_hc : 0 < c) :
    6 * usigma (7 ^ a) * usigma (29 ^ b) * usigma (r ^ c) <
      5 * σ 1 (7 ^ a) * σ 1 (29 ^ b) * σ 1 (r ^ c) := by
  have hover := seven_cube_q_pow_ge_two_overshoot_six_five
    (by decide : Nat.Prime 29) (by decide : 11 ≤ 29) (by decide : 29 ≤ 31)
    ha hb
  have h := six_five_overshoot_mul (s := usigma (7 ^ a) * usigma (29 ^ b))
      (t := σ 1 (7 ^ a) * σ 1 (29 ^ b)) (n := r ^ c)
      (Nat.pow_pos hr.pos).ne' (by simpa [mul_assoc] using hover)
  simpa [mul_assoc] using h

lemma five_mul_forty_nine_twenty_nine_sq_cap {r : ℕ} (hr : 59 ≤ r) :
    5 * r * 57 * 871 ≤ 6 * (r - 1) * 50 * 842 := by
  have hdiff : 252600 ≤ 4365 * r := by
    have hmul : 4365 * 59 ≤ 4365 * r := Nat.mul_le_mul_left 4365 hr
    have hnum : 4365 * 59 = 257535 := by decide
    omega
  have hL : 5 * r * 57 * 871 = 248235 * r := by ring
  have hR : 6 * (r - 1) * 50 * 842 = 252600 * (r - 1) := by ring
  have hmain : 248235 * r ≤ 252600 * (r - 1) := by
    have heq : 248235 * r + 4365 * r = 252600 * r := by ring
    have hsub : 248235 * r = 252600 * r - 4365 * r :=
      (Nat.sub_eq_of_eq_add heq.symm).symm
    have hle : 252600 * r - 4365 * r ≤ 252600 * r - 252600 :=
      Nat.sub_le_sub_left hdiff _
    have hrw : 252600 * r - 252600 = 252600 * (r - 1) := by
      simpa using (Nat.mul_sub_left_distrib 252600 r 1).symm
    calc
      248235 * r = 252600 * r - 4365 * r := hsub
      _ ≤ 252600 * r - 252600 := hle
      _ = 252600 * (r - 1) := hrw
  rw [hL, hR]
  exact hmain

lemma five_sigma_lt_six_usigma_seven_sq_twenty_nine_sq_large {r k : ℕ}
    (hr : r.Prime) (hr59 : 59 ≤ r) (hk : 0 < k) :
    5 * σ 1 (7 ^ 2) * σ 1 (29 ^ 2) * σ 1 (r ^ k) <
      6 * usigma (7 ^ 2) * usigma (29 ^ 2) * usigma (r ^ k) := by
  have hp7 : Nat.Prime 7 := by decide
  have hσ7 : σ 1 (7 ^ 2) = 57 := by
    rw [sigma_prime_pow_two hp7]
    decide
  have hu7 : usigma (7 ^ 2) = 50 := by
    simpa using usigma_prime_pow hp7 (by decide : 0 < 2)
  rw [hσ7, hu7, sigma_twenty_nine_pow_two, usigma_twenty_nine_pow_two]
  have hcp := sigma_lt_cap_usigma hr hk
  have hthis := six_five_of_cap_times_const (A := r - 1) (B := r)
    (X := σ 1 (r ^ k)) (Y := usigma (r ^ k)) (S := 50 * 842) (T := 57 * 871)
    hcp (by
      have hL : 5 * r * (57 * 871) = 5 * r * 57 * 871 := by ring
      have hR : 6 * (r - 1) * (50 * 842) = 6 * (r - 1) * 50 * 842 := by ring
      rw [hL, hR]
      exact five_mul_forty_nine_twenty_nine_sq_cap hr59)
    (by decide : 0 < 57 * 871)
  convert hthis using 1 <;> ring

lemma five_mul_forty_nine_twenty_nine_cap {r : ℕ} (hr : 67 ≤ r) :
    5 * 29 * r * 57 ≤ 6 * 28 * (r - 1) * 50 := by
  have hdiff : 8400 ≤ 135 * r := by
    have hmul : 135 * 67 ≤ 135 * r := Nat.mul_le_mul_left 135 hr
    have hnum : 135 * 67 = 9045 := by decide
    omega
  have hL : 5 * 29 * r * 57 = 8265 * r := by ring
  have hR : 6 * 28 * (r - 1) * 50 = 8400 * (r - 1) := by ring
  have hmain : 8265 * r ≤ 8400 * (r - 1) := by
    have heq : 8265 * r + 135 * r = 8400 * r := by ring
    have hsub : 8265 * r = 8400 * r - 135 * r :=
      (Nat.sub_eq_of_eq_add heq.symm).symm
    have hle : 8400 * r - 135 * r ≤ 8400 * r - 8400 :=
      Nat.sub_le_sub_left hdiff _
    have hrw : 8400 * r - 8400 = 8400 * (r - 1) := by
      simpa using (Nat.mul_sub_left_distrib 8400 r 1).symm
    calc
      8265 * r = 8400 * r - 135 * r := hsub
      _ ≤ 8400 * r - 8400 := hle
      _ = 8400 * (r - 1) := hrw
  rw [hL, hR]
  exact hmain

lemma five_sigma_lt_six_usigma_seven_sq_twenty_nine_large {r b c : ℕ}
    (hr : r.Prime) (hr67 : 67 ≤ r) (hb : 0 < b) (hc : 0 < c) :
    5 * σ 1 (7 ^ 2) * σ 1 (29 ^ b) * σ 1 (r ^ c) <
      6 * usigma (7 ^ 2) * usigma (29 ^ b) * usigma (r ^ c) := by
  have hp7 : Nat.Prime 7 := by decide
  have hσ7 : σ 1 (7 ^ 2) = 57 := by
    rw [sigma_prime_pow_two hp7]
    decide
  have hu7 : usigma (7 ^ 2) = 50 := by
    simpa using usigma_prime_pow hp7 (by decide : 0 < 2)
  rw [hσ7, hu7]
  have h29 := sigma_lt_cap_usigma (by decide : Nat.Prime 29) hb
  have hrcap := sigma_lt_cap_usigma hr hc
  have hu29 : 0 < usigma (29 ^ b) := by
    rw [usigma_prime_pow (by decide : Nat.Prime 29) hb]
    exact Nat.add_pos_left (by decide : 0 < 1) _
  have hthis := six_five_of_two_caps_times_const (A := 28) (B := 29)
    (X := σ 1 (29 ^ b)) (Y := usigma (29 ^ b)) (C := r - 1) (D := r)
    (P := σ 1 (r ^ c)) (Q := usigma (r ^ c)) (S := 50) (T := 57)
    h29 hrcap (five_mul_forty_nine_twenty_nine_cap hr67)
    (by decide : 0 < 29) hu29 (by decide : 0 < 57)
  convert hthis using 1 <;> ring

/-- Leftover `6/5` cannot be three squareful primes `7,29,r` with
`r ≥ 31` times a squarefree coprime factor. -/
lemma not_five_sigma_of_three_sq_primes_seven_twenty_nine {m r : ℕ}
    (hm : m ≠ 0) (hr : r.Prime) (hr31 : 31 ≤ r)
    (h : 5 * σ 1 m = 6 * usigma m)
    (hk7 : 2 ≤ padicValNat 7 m) (hk29 : 2 ≤ padicValNat 29 m)
    (hkr : 2 ≤ padicValNat r m)
    (hs : Squarefree (ordCompl[r] (ordCompl[29] (ordCompl[7] m)))) : False := by
  have hp7 : Nat.Prime 7 := by decide
  have hp29 : Nat.Prime 29 := by decide
  have hpq_ne : (7 : ℕ) ≠ 29 := by decide
  have hpr_ne : (7 : ℕ) ≠ r :=
    Nat.ne_of_lt (lt_of_lt_of_le (by decide : 7 < 31) hr31)
  have hqr_ne : (29 : ℕ) ≠ r :=
    Nat.ne_of_lt (lt_of_lt_of_le (by decide : 29 < 31) hr31)
  have heq := five_sigma_eq_six_of_three_squareful hm hp7 hp29 hr hpq_ne hpr_ne
    hqr_ne h hs
  have hproj_p : ordProj[7] m = 7 ^ padicValNat 7 m := by
    simp [Nat.factorization_def m hp7]
  have hproj_q : ordProj[29] (ordCompl[7] m) =
      29 ^ padicValNat 29 (ordCompl[7] m) := by
    simp [Nat.factorization_def (ordCompl[7] m) hp29]
  have hproj_r : ordProj[r] (ordCompl[29] (ordCompl[7] m)) =
      r ^ padicValNat r (ordCompl[29] (ordCompl[7] m)) := by
    simp [Nat.factorization_def (ordCompl[29] (ordCompl[7] m)) hr]
  rw [hproj_r, padicValNat_ordCompl_of_ne hr hqr_ne,
    padicValNat_ordCompl_of_ne hr hpr_ne, hproj_q,
    padicValNat_ordCompl_of_ne hp29 hpq_ne, hproj_p] at heq
  rcases eq_or_lt_of_le hk7 with h7eq | h73
  · rw [← h7eq] at heq
    rcases eq_or_lt_of_le hk29 with h29eq | h293
    · rw [← h29eq] at heq
      rcases le_or_gt r 53 with h53 | h54
      · have hover := seven_twenty_nine_r_sq_pow_ge_two_overshoot_six_five
          hr hr31 h53 (le_refl _) (le_refl _) hkr
        rw [← heq] at hover
        exact lt_irrefl _ hover
      · have hr59 : 59 ≤ r :=
          prime_ge_fifty_four_ge_fifty_nine hr (Nat.succ_le_of_lt h54)
        exact (five_sigma_lt_six_usigma_seven_sq_twenty_nine_sq_large hr hr59
          (by omega)).ne heq
    · rcases le_or_gt r 61 with h61 | h62
      · have hover := seven_sq_twenty_nine_cube_r_pow_ge_two_overshoot_six_five
          hr hr31 h61 (le_refl _) (Nat.succ_le_of_lt h293) hkr
        rw [← heq] at hover
        exact lt_irrefl _ hover
      · have hr67 : 67 ≤ r :=
          prime_ge_sixty_two_ge_sixty_seven hr (Nat.succ_le_of_lt h62)
        exact (five_sigma_lt_six_usigma_seven_sq_twenty_nine_large hr hr67
          (by omega) (by omega)).ne heq
  · have hover := seven_cube_twenty_nine_r_overshoot_six_five (c := padicValNat r m)
      hr (Nat.succ_le_of_lt h73) hk29
      (lt_of_lt_of_le (by decide : (0 : ℕ) < 2) hkr)
    rw [← heq] at hover
    exact lt_irrefl _ hover

lemma prime_ge_forty_eight_ge_fifty_three {p : ℕ} (hp : p.Prime)
    (h : 48 ≤ p) : 53 ≤ p := by
  have hmem : p = 48 ∨ p = 49 ∨ p = 50 ∨ p = 51 ∨ p = 52 ∨ 53 ≤ p := by omega
  rcases hmem with rfl | rfl | rfl | rfl | rfl | h53
  · exact False.elim ((by decide : ¬ Nat.Prime 48) hp)
  · exact False.elim ((by decide : ¬ Nat.Prime 49) hp)
  · exact False.elim ((by decide : ¬ Nat.Prime 50) hp)
  · exact False.elim ((by decide : ¬ Nat.Prime 51) hp)
  · exact False.elim ((by decide : ¬ Nat.Prime 52) hp)
  · exact h53

lemma usigma_thirty_one_pow_two : usigma (31 ^ 2) = 962 := by
  rw [usigma_prime_pow (by decide : Nat.Prime 31) (by decide : 0 < 2)]
  decide

lemma sigma_thirty_one_pow_two : σ 1 (31 ^ 2) = 993 := by
  rw [sigma_prime_pow_two (by decide : Nat.Prime 31)]
  decide

lemma usigma_thirty_one_pow_three : usigma (31 ^ 3) = 29792 := by
  rw [usigma_prime_pow (by decide : Nat.Prime 31) (by decide : 0 < 3)]
  decide

lemma sigma_thirty_one_pow_three : σ 1 (31 ^ 3) = 30784 := by
  rw [sigma_prime_pow_div (by decide : Nat.Prime 31)]
  norm_num

lemma forty_nine_thirty_one_sq_r_sq_overshoot_six_five {r : ℕ}
    (hr : r.Prime) (h37 : 37 ≤ r) (h47 : r ≤ 47) :
    6 * usigma (7 ^ 2) * usigma (31 ^ 2) * usigma (r ^ 2) <
      5 * σ 1 (7 ^ 2) * σ 1 (31 ^ 2) * σ 1 (r ^ 2) := by
  have hp7 : Nat.Prime 7 := by decide
  have hσ7 : σ 1 (7 ^ 2) = 57 := by
    rw [sigma_prime_pow_two hp7]
    decide
  have hu7 : usigma (7 ^ 2) = 50 := by
    simpa using usigma_prime_pow hp7 (by decide : 0 < 2)
  rw [hσ7, hu7, sigma_thirty_one_pow_two, usigma_thirty_one_pow_two,
    sigma_prime_pow_two hr, usigma_prime_pow hr (by decide : 0 < 2)]
  have hsq : r ^ 2 ≤ 47 * r := by
    rw [pow_two]
    exact Nat.mul_le_mul_right r h47
  have hleft : 5595 * (1 + r ^ 2) < 283005 * r := by
    have h1 : 5595 * (1 + r ^ 2) ≤ 5595 * (1 + 47 * r) :=
      Nat.mul_le_mul_left 5595 (Nat.add_le_add_left hsq 1)
    have h2 : 5595 * (1 + 47 * r) = 5595 + 262965 * r := by
      have : 5595 * 47 = 262965 := by decide
      ring
    have h3 : 5595 + 262965 * r < 283005 * r := by
      have : 5595 < 20040 * r :=
        lt_of_lt_of_le (by decide : 5595 < 741480)
          (Nat.mul_le_mul_left 20040 h37)
      omega
    calc
      5595 * (1 + r ^ 2) ≤ 5595 * (1 + 47 * r) := h1
      _ = 5595 + 262965 * r := h2
      _ < 283005 * r := h3
  have hL : 6 * 50 * 962 * (1 + r ^ 2) = 288600 * (1 + r ^ 2) := by ring
  have hR : 5 * 57 * 993 * (1 + r + r ^ 2) = 283005 * (1 + r + r ^ 2) := by ring
  have hmain : 288600 * (1 + r ^ 2) < 283005 * (1 + r + r ^ 2) := by
    have h1 : 288600 * (1 + r ^ 2) =
        283005 * (1 + r ^ 2) + 5595 * (1 + r ^ 2) := by ring
    have h2 : 283005 * (1 + r + r ^ 2) =
        283005 * (1 + r ^ 2) + 283005 * r := by ring
    rw [h1, h2]
    exact Nat.add_lt_add_left hleft _
  rw [hL, hR]
  exact hmain

lemma seven_thirty_one_r_sq_pow_ge_two_overshoot_six_five {r a b c : ℕ}
    (hr : r.Prime) (h37 : 37 ≤ r) (h47 : r ≤ 47)
    (ha : 2 ≤ a) (hb : 2 ≤ b) (hc : 2 ≤ c) :
    6 * usigma (7 ^ a) * usigma (31 ^ b) * usigma (r ^ c) <
      5 * σ 1 (7 ^ a) * σ 1 (31 ^ b) * σ 1 (r ^ c) :=
  six_five_overshoot_mono_three (by decide : Nat.Prime 7)
    (by decide : Nat.Prime 31) hr
    (by decide : 0 < 2) (by decide : 0 < 2) (by decide : 0 < 2)
    ha hb hc (forty_nine_thirty_one_sq_r_sq_overshoot_six_five hr h37 h47)

lemma forty_nine_thirty_one_cube_r_sq_overshoot_six_five {r : ℕ}
    (hr : r.Prime) (h37 : 37 ≤ r) (h53 : r ≤ 53) :
    6 * usigma (7 ^ 2) * usigma (31 ^ 3) * usigma (r ^ 2) <
      5 * σ 1 (7 ^ 2) * σ 1 (31 ^ 3) * σ 1 (r ^ 2) := by
  have hp7 : Nat.Prime 7 := by decide
  have hσ7 : σ 1 (7 ^ 2) = 57 := by
    rw [sigma_prime_pow_two hp7]
    decide
  have hu7 : usigma (7 ^ 2) = 50 := by
    simpa using usigma_prime_pow hp7 (by decide : 0 < 2)
  rw [hσ7, hu7, sigma_thirty_one_pow_three, usigma_thirty_one_pow_three,
    sigma_prime_pow_two hr, usigma_prime_pow hr (by decide : 0 < 2)]
  have hsq : r ^ 2 ≤ 53 * r := by
    rw [pow_two]
    exact Nat.mul_le_mul_right r h53
  have hleft : 164160 * (1 + r ^ 2) < 8773440 * r := by
    have h1 : 164160 * (1 + r ^ 2) ≤ 164160 * (1 + 53 * r) :=
      Nat.mul_le_mul_left 164160 (Nat.add_le_add_left hsq 1)
    have h2 : 164160 * (1 + 53 * r) = 164160 + 8700480 * r := by
      have : 164160 * 53 = 8700480 := by decide
      ring
    have h3 : 164160 + 8700480 * r < 8773440 * r := by
      have : 164160 < 72960 * r :=
        lt_of_lt_of_le (by decide : 164160 < 2699520)
          (Nat.mul_le_mul_left 72960 h37)
      omega
    calc
      164160 * (1 + r ^ 2) ≤ 164160 * (1 + 53 * r) := h1
      _ = 164160 + 8700480 * r := h2
      _ < 8773440 * r := h3
  have hL : 6 * 50 * 29792 * (1 + r ^ 2) = 8937600 * (1 + r ^ 2) := by ring
  have hR : 5 * 57 * 30784 * (1 + r + r ^ 2) = 8773440 * (1 + r + r ^ 2) :=
    by ring
  have hmain : 8937600 * (1 + r ^ 2) < 8773440 * (1 + r + r ^ 2) := by
    have h1 : 8937600 * (1 + r ^ 2) =
        8773440 * (1 + r ^ 2) + 164160 * (1 + r ^ 2) := by ring
    have h2 : 8773440 * (1 + r + r ^ 2) =
        8773440 * (1 + r ^ 2) + 8773440 * r := by ring
    rw [h1, h2]
    exact Nat.add_lt_add_left hleft _
  rw [hL, hR]
  exact hmain

lemma seven_sq_thirty_one_cube_r_pow_ge_two_overshoot_six_five
    {r a b c : ℕ} (hr : r.Prime) (h37 : 37 ≤ r) (h53 : r ≤ 53)
    (ha : 2 ≤ a) (hb : 3 ≤ b) (hc : 2 ≤ c) :
    6 * usigma (7 ^ a) * usigma (31 ^ b) * usigma (r ^ c) <
      5 * σ 1 (7 ^ a) * σ 1 (31 ^ b) * σ 1 (r ^ c) :=
  six_five_overshoot_mono_three (by decide : Nat.Prime 7)
    (by decide : Nat.Prime 31) hr
    (by decide : 0 < 2) (by decide : 0 < 3) (by decide : 0 < 2)
    ha hb hc (forty_nine_thirty_one_cube_r_sq_overshoot_six_five hr h37 h53)

lemma seven_cube_thirty_one_r_overshoot_six_five {r a b c : ℕ}
    (hr : r.Prime) (ha : 3 ≤ a) (hb : 2 ≤ b) (_hc : 0 < c) :
    6 * usigma (7 ^ a) * usigma (31 ^ b) * usigma (r ^ c) <
      5 * σ 1 (7 ^ a) * σ 1 (31 ^ b) * σ 1 (r ^ c) := by
  have hover := seven_cube_q_pow_ge_two_overshoot_six_five
    (by decide : Nat.Prime 31) (by decide : 11 ≤ 31) (by decide : 31 ≤ 31)
    ha hb
  have h := six_five_overshoot_mul (s := usigma (7 ^ a) * usigma (31 ^ b))
      (t := σ 1 (7 ^ a) * σ 1 (31 ^ b)) (n := r ^ c)
      (Nat.pow_pos hr.pos).ne' (by simpa [mul_assoc] using hover)
  simpa [mul_assoc] using h

lemma five_mul_forty_nine_thirty_one_sq_cap {r : ℕ} (hr : 53 ≤ r) :
    5 * r * 57 * 993 ≤ 6 * (r - 1) * 50 * 962 := by
  have hdiff : 288600 ≤ 5595 * r := by
    have hmul : 5595 * 53 ≤ 5595 * r := Nat.mul_le_mul_left 5595 hr
    have hnum : 5595 * 53 = 296535 := by decide
    omega
  have hL : 5 * r * 57 * 993 = 283005 * r := by ring
  have hR : 6 * (r - 1) * 50 * 962 = 288600 * (r - 1) := by ring
  have hmain : 283005 * r ≤ 288600 * (r - 1) := by
    have heq : 283005 * r + 5595 * r = 288600 * r := by ring
    have hsub : 283005 * r = 288600 * r - 5595 * r :=
      (Nat.sub_eq_of_eq_add heq.symm).symm
    have hle : 288600 * r - 5595 * r ≤ 288600 * r - 288600 :=
      Nat.sub_le_sub_left hdiff _
    have hrw : 288600 * r - 288600 = 288600 * (r - 1) := by
      simpa using (Nat.mul_sub_left_distrib 288600 r 1).symm
    calc
      283005 * r = 288600 * r - 5595 * r := hsub
      _ ≤ 288600 * r - 288600 := hle
      _ = 288600 * (r - 1) := hrw
  rw [hL, hR]
  exact hmain

lemma five_sigma_lt_six_usigma_seven_sq_thirty_one_sq_large {r k : ℕ}
    (hr : r.Prime) (hr53 : 53 ≤ r) (hk : 0 < k) :
    5 * σ 1 (7 ^ 2) * σ 1 (31 ^ 2) * σ 1 (r ^ k) <
      6 * usigma (7 ^ 2) * usigma (31 ^ 2) * usigma (r ^ k) := by
  have hp7 : Nat.Prime 7 := by decide
  have hσ7 : σ 1 (7 ^ 2) = 57 := by
    rw [sigma_prime_pow_two hp7]
    decide
  have hu7 : usigma (7 ^ 2) = 50 := by
    simpa using usigma_prime_pow hp7 (by decide : 0 < 2)
  rw [hσ7, hu7, sigma_thirty_one_pow_two, usigma_thirty_one_pow_two]
  have hcp := sigma_lt_cap_usigma hr hk
  have hthis := six_five_of_cap_times_const (A := r - 1) (B := r)
    (X := σ 1 (r ^ k)) (Y := usigma (r ^ k)) (S := 50 * 962) (T := 57 * 993)
    hcp (by
      have hL : 5 * r * (57 * 993) = 5 * r * 57 * 993 := by ring
      have hR : 6 * (r - 1) * (50 * 962) = 6 * (r - 1) * 50 * 962 := by ring
      rw [hL, hR]
      exact five_mul_forty_nine_thirty_one_sq_cap hr53)
    (by decide : 0 < 57 * 993)
  convert hthis using 1 <;> ring

lemma five_mul_forty_nine_thirty_one_cap {r : ℕ} (hr : 59 ≤ r) :
    5 * 31 * r * 57 ≤ 6 * 30 * (r - 1) * 50 := by
  have hdiff : 9000 ≤ 165 * r := by
    have hmul : 165 * 59 ≤ 165 * r := Nat.mul_le_mul_left 165 hr
    have hnum : 165 * 59 = 9735 := by decide
    omega
  have hL : 5 * 31 * r * 57 = 8835 * r := by ring
  have hR : 6 * 30 * (r - 1) * 50 = 9000 * (r - 1) := by ring
  have hmain : 8835 * r ≤ 9000 * (r - 1) := by
    have heq : 8835 * r + 165 * r = 9000 * r := by ring
    have hsub : 8835 * r = 9000 * r - 165 * r :=
      (Nat.sub_eq_of_eq_add heq.symm).symm
    have hle : 9000 * r - 165 * r ≤ 9000 * r - 9000 :=
      Nat.sub_le_sub_left hdiff _
    have hrw : 9000 * r - 9000 = 9000 * (r - 1) := by
      simpa using (Nat.mul_sub_left_distrib 9000 r 1).symm
    calc
      8835 * r = 9000 * r - 165 * r := hsub
      _ ≤ 9000 * r - 9000 := hle
      _ = 9000 * (r - 1) := hrw
  rw [hL, hR]
  exact hmain

lemma five_sigma_lt_six_usigma_seven_sq_thirty_one_large {r b c : ℕ}
    (hr : r.Prime) (hr59 : 59 ≤ r) (hb : 0 < b) (hc : 0 < c) :
    5 * σ 1 (7 ^ 2) * σ 1 (31 ^ b) * σ 1 (r ^ c) <
      6 * usigma (7 ^ 2) * usigma (31 ^ b) * usigma (r ^ c) := by
  have hp7 : Nat.Prime 7 := by decide
  have hσ7 : σ 1 (7 ^ 2) = 57 := by
    rw [sigma_prime_pow_two hp7]
    decide
  have hu7 : usigma (7 ^ 2) = 50 := by
    simpa using usigma_prime_pow hp7 (by decide : 0 < 2)
  rw [hσ7, hu7]
  have h31 := sigma_lt_cap_usigma (by decide : Nat.Prime 31) hb
  have hrcap := sigma_lt_cap_usigma hr hc
  have hu31 : 0 < usigma (31 ^ b) := by
    rw [usigma_prime_pow (by decide : Nat.Prime 31) hb]
    exact Nat.add_pos_left (by decide : 0 < 1) _
  have hthis := six_five_of_two_caps_times_const (A := 30) (B := 31)
    (X := σ 1 (31 ^ b)) (Y := usigma (31 ^ b)) (C := r - 1) (D := r)
    (P := σ 1 (r ^ c)) (Q := usigma (r ^ c)) (S := 50) (T := 57)
    h31 hrcap (five_mul_forty_nine_thirty_one_cap hr59)
    (by decide : 0 < 31) hu31 (by decide : 0 < 57)
  convert hthis using 1 <;> ring

/-- Leftover `6/5` cannot be three squareful primes `7,31,r` with
`r ≥ 37` times a squarefree coprime factor. -/
lemma not_five_sigma_of_three_sq_primes_seven_thirty_one {m r : ℕ}
    (hm : m ≠ 0) (hr : r.Prime) (hr37 : 37 ≤ r)
    (h : 5 * σ 1 m = 6 * usigma m)
    (hk7 : 2 ≤ padicValNat 7 m) (hk31 : 2 ≤ padicValNat 31 m)
    (hkr : 2 ≤ padicValNat r m)
    (hs : Squarefree (ordCompl[r] (ordCompl[31] (ordCompl[7] m)))) : False := by
  have hp7 : Nat.Prime 7 := by decide
  have hp31 : Nat.Prime 31 := by decide
  have hpq_ne : (7 : ℕ) ≠ 31 := by decide
  have hpr_ne : (7 : ℕ) ≠ r :=
    Nat.ne_of_lt (lt_of_lt_of_le (by decide : 7 < 37) hr37)
  have hqr_ne : (31 : ℕ) ≠ r :=
    Nat.ne_of_lt (lt_of_lt_of_le (by decide : 31 < 37) hr37)
  have heq := five_sigma_eq_six_of_three_squareful hm hp7 hp31 hr hpq_ne hpr_ne
    hqr_ne h hs
  have hproj_p : ordProj[7] m = 7 ^ padicValNat 7 m := by
    simp [Nat.factorization_def m hp7]
  have hproj_q : ordProj[31] (ordCompl[7] m) =
      31 ^ padicValNat 31 (ordCompl[7] m) := by
    simp [Nat.factorization_def (ordCompl[7] m) hp31]
  have hproj_r : ordProj[r] (ordCompl[31] (ordCompl[7] m)) =
      r ^ padicValNat r (ordCompl[31] (ordCompl[7] m)) := by
    simp [Nat.factorization_def (ordCompl[31] (ordCompl[7] m)) hr]
  rw [hproj_r, padicValNat_ordCompl_of_ne hr hqr_ne,
    padicValNat_ordCompl_of_ne hr hpr_ne, hproj_q,
    padicValNat_ordCompl_of_ne hp31 hpq_ne, hproj_p] at heq
  rcases eq_or_lt_of_le hk7 with h7eq | h73
  · rw [← h7eq] at heq
    rcases eq_or_lt_of_le hk31 with h31eq | h313
    · rw [← h31eq] at heq
      rcases le_or_gt r 47 with h47 | h48
      · have hover := seven_thirty_one_r_sq_pow_ge_two_overshoot_six_five
          hr hr37 h47 (le_refl _) (le_refl _) hkr
        rw [← heq] at hover
        exact lt_irrefl _ hover
      · have hr53 : 53 ≤ r :=
          prime_ge_forty_eight_ge_fifty_three hr (Nat.succ_le_of_lt h48)
        exact (five_sigma_lt_six_usigma_seven_sq_thirty_one_sq_large hr hr53
          (by omega)).ne heq
    · rcases le_or_gt r 53 with h53 | h54
      · have hover := seven_sq_thirty_one_cube_r_pow_ge_two_overshoot_six_five
          hr hr37 h53 (le_refl _) (Nat.succ_le_of_lt h313) hkr
        rw [← heq] at hover
        exact lt_irrefl _ hover
      · have hr59 : 59 ≤ r :=
          prime_ge_fifty_four_ge_fifty_nine hr (Nat.succ_le_of_lt h54)
        exact (five_sigma_lt_six_usigma_seven_sq_thirty_one_large hr hr59
          (by omega) (by omega)).ne heq
  · have hover := seven_cube_thirty_one_r_overshoot_six_five (c := padicValNat r m)
      hr (Nat.succ_le_of_lt h73) hk31
      (lt_of_lt_of_le (by decide : (0 : ℕ) < 2) hkr)
    rw [← heq] at hover
    exact lt_irrefl _ hover

lemma prime_ge_forty_two_ge_forty_three {p : ℕ} (hp : p.Prime)
    (h : 42 ≤ p) : 43 ≤ p := by
  have hmem : p = 42 ∨ 43 ≤ p := by omega
  rcases hmem with rfl | h43
  · exact False.elim ((by decide : ¬ Nat.Prime 42) hp)
  · exact h43

lemma prime_ge_two_hundred_six_ge_two_hundred_eleven {p : ℕ} (hp : p.Prime)
    (h : 206 ≤ p) : 211 ≤ p := by
  have hmem : p = 206 ∨ p = 207 ∨ p = 208 ∨ p = 209 ∨ p = 210 ∨ 211 ≤ p :=
    by omega
  rcases hmem with rfl | rfl | rfl | rfl | rfl | h211
  · exact False.elim (not_prime_of_eq_mul (rfl : 206 = 2 * 103)
      (by decide : (2 : ℕ) ≠ 1) (by decide : (103 : ℕ) ≠ 1) hp)
  · exact False.elim (not_prime_of_eq_mul (rfl : 207 = 9 * 23)
      (by decide : (9 : ℕ) ≠ 1) (by decide : (23 : ℕ) ≠ 1) hp)
  · exact False.elim (not_prime_of_eq_mul (rfl : 208 = 2 * 104)
      (by decide : (2 : ℕ) ≠ 1) (by decide : (104 : ℕ) ≠ 1) hp)
  · exact False.elim (not_prime_of_eq_mul (rfl : 209 = 11 * 19)
      (by decide : (11 : ℕ) ≠ 1) (by decide : (19 : ℕ) ≠ 1) hp)
  · exact False.elim (not_prime_of_eq_mul (rfl : 210 = 2 * 105)
      (by decide : (2 : ℕ) ≠ 1) (by decide : (105 : ℕ) ≠ 1) hp)
  · exact h211

lemma prime_ge_two_hundred_forty_three_ge_two_hundred_fifty_one {p : ℕ}
    (hp : p.Prime) (h : 243 ≤ p) : 251 ≤ p := by
  have hmem : p = 243 ∨ p = 244 ∨ p = 245 ∨ p = 246 ∨ p = 247 ∨ p = 248 ∨
      p = 249 ∨ p = 250 ∨ 251 ≤ p := by omega
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | h251
  · exact False.elim (not_prime_of_eq_mul (rfl : 243 = 9 * 27)
      (by decide : (9 : ℕ) ≠ 1) (by decide : (27 : ℕ) ≠ 1) hp)
  · exact False.elim (not_prime_of_eq_mul (rfl : 244 = 2 * 122)
      (by decide : (2 : ℕ) ≠ 1) (by decide : (122 : ℕ) ≠ 1) hp)
  · exact False.elim (not_prime_of_eq_mul (rfl : 245 = 5 * 49)
      (by decide : (5 : ℕ) ≠ 1) (by decide : (49 : ℕ) ≠ 1) hp)
  · exact False.elim (not_prime_of_eq_mul (rfl : 246 = 2 * 123)
      (by decide : (2 : ℕ) ≠ 1) (by decide : (123 : ℕ) ≠ 1) hp)
  · exact False.elim (not_prime_of_eq_mul (rfl : 247 = 13 * 19)
      (by decide : (13 : ℕ) ≠ 1) (by decide : (19 : ℕ) ≠ 1) hp)
  · exact False.elim (not_prime_of_eq_mul (rfl : 248 = 2 * 124)
      (by decide : (2 : ℕ) ≠ 1) (by decide : (124 : ℕ) ≠ 1) hp)
  · exact False.elim (not_prime_of_eq_mul (rfl : 249 = 3 * 83)
      (by decide : (3 : ℕ) ≠ 1) (by decide : (83 : ℕ) ≠ 1) hp)
  · exact False.elim (not_prime_of_eq_mul (rfl : 250 = 2 * 125)
      (by decide : (2 : ℕ) ≠ 1) (by decide : (125 : ℕ) ≠ 1) hp)
  · exact h251

lemma usigma_forty_one_pow_two : usigma (41 ^ 2) = 1682 := by
  rw [usigma_prime_pow (by decide : Nat.Prime 41) (by decide : 0 < 2)]
  decide

lemma sigma_forty_one_pow_two : σ 1 (41 ^ 2) = 1723 := by
  rw [sigma_prime_pow_two (by decide : Nat.Prime 41)]
  decide

lemma usigma_forty_one_pow_three : usigma (41 ^ 3) = 68922 := by
  rw [usigma_prime_pow (by decide : Nat.Prime 41) (by decide : 0 < 3)]
  decide

lemma sigma_forty_one_pow_three : σ 1 (41 ^ 3) = 70644 := by
  rw [sigma_prime_pow_div (by decide : Nat.Prime 41)]
  norm_num

lemma seven_cube_thirty_seven_sq_r_sq_overshoot_six_five {r : ℕ}
    (hr : r.Prime) (h41 : 41 ≤ r) (h205 : r ≤ 205) :
    6 * usigma (7 ^ 3) * usigma (37 ^ 2) * usigma (r ^ 2) <
      5 * σ 1 (7 ^ 3) * σ 1 (37 ^ 2) * σ 1 (r ^ 2) := by
  rw [usigma_seven_pow_three, sigma_seven_pow_three,
    sigma_thirty_seven_pow_two, usigma_thirty_seven_pow_two,
    sigma_prime_pow_two hr, usigma_prime_pow hr (by decide : 0 < 2)]
  have hsq : r ^ 2 ≤ 205 * r := by
    rw [pow_two]
    exact Nat.mul_le_mul_right r h205
  have hleft : 13680 * (1 + r ^ 2) < 2814000 * r := by
    have h1 : 13680 * (1 + r ^ 2) ≤ 13680 * (1 + 205 * r) :=
      Nat.mul_le_mul_left 13680 (Nat.add_le_add_left hsq 1)
    have h2 : 13680 * (1 + 205 * r) = 13680 + 2804400 * r := by
      have : 13680 * 205 = 2804400 := by decide
      ring
    have h3 : 13680 + 2804400 * r < 2814000 * r := by
      have : 13680 < 9600 * r :=
        lt_of_lt_of_le (by decide : 13680 < 393600)
          (Nat.mul_le_mul_left 9600 h41)
      omega
    calc
      13680 * (1 + r ^ 2) ≤ 13680 * (1 + 205 * r) := h1
      _ = 13680 + 2804400 * r := h2
      _ < 2814000 * r := h3
  have hL : 6 * 344 * 1370 * (1 + r ^ 2) = 2827680 * (1 + r ^ 2) := by ring
  have hR : 5 * 400 * 1407 * (1 + r + r ^ 2) = 2814000 * (1 + r + r ^ 2) :=
    by ring
  have hmain : 2827680 * (1 + r ^ 2) < 2814000 * (1 + r + r ^ 2) := by
    have h1 : 2827680 * (1 + r ^ 2) =
        2814000 * (1 + r ^ 2) + 13680 * (1 + r ^ 2) := by ring
    have h2 : 2814000 * (1 + r + r ^ 2) =
        2814000 * (1 + r ^ 2) + 2814000 * r := by ring
    rw [h1, h2]
    exact Nat.add_lt_add_left hleft _
  rw [hL, hR]
  exact hmain

lemma seven_cube_thirty_seven_r_sq_pow_ge_two_overshoot_six_five
    {r a b c : ℕ} (hr : r.Prime) (h41 : 41 ≤ r) (h205 : r ≤ 205)
    (ha : 3 ≤ a) (hb : 2 ≤ b) (hc : 2 ≤ c) :
    6 * usigma (7 ^ a) * usigma (37 ^ b) * usigma (r ^ c) <
      5 * σ 1 (7 ^ a) * σ 1 (37 ^ b) * σ 1 (r ^ c) :=
  six_five_overshoot_mono_three (by decide : Nat.Prime 7)
    (by decide : Nat.Prime 37) hr
    (by decide : 0 < 3) (by decide : 0 < 2) (by decide : 0 < 2)
    ha hb hc (seven_cube_thirty_seven_sq_r_sq_overshoot_six_five hr h41 h205)

lemma five_mul_forty_nine_thirty_seven_cap {r : ℕ} (hr : 43 ≤ r) :
    5 * 37 * r * 57 ≤ 6 * 36 * (r - 1) * 50 := by
  have hdiff : 10800 ≤ 255 * r := by
    have hmul : 255 * 43 ≤ 255 * r := Nat.mul_le_mul_left 255 hr
    have hnum : 255 * 43 = 10965 := by decide
    omega
  have hL : 5 * 37 * r * 57 = 10545 * r := by ring
  have hR : 6 * 36 * (r - 1) * 50 = 10800 * (r - 1) := by ring
  have hmain : 10545 * r ≤ 10800 * (r - 1) := by
    have heq : 10545 * r + 255 * r = 10800 * r := by ring
    have hsub : 10545 * r = 10800 * r - 255 * r :=
      (Nat.sub_eq_of_eq_add heq.symm).symm
    have hle : 10800 * r - 255 * r ≤ 10800 * r - 10800 :=
      Nat.sub_le_sub_left hdiff _
    have hrw : 10800 * r - 10800 = 10800 * (r - 1) := by
      simpa using (Nat.mul_sub_left_distrib 10800 r 1).symm
    calc
      10545 * r = 10800 * r - 255 * r := hsub
      _ ≤ 10800 * r - 10800 := hle
      _ = 10800 * (r - 1) := hrw
  rw [hL, hR]
  exact hmain

lemma five_sigma_lt_six_usigma_seven_sq_thirty_seven_large {r b c : ℕ}
    (hr : r.Prime) (hr43 : 43 ≤ r) (hb : 0 < b) (hc : 0 < c) :
    5 * σ 1 (7 ^ 2) * σ 1 (37 ^ b) * σ 1 (r ^ c) <
      6 * usigma (7 ^ 2) * usigma (37 ^ b) * usigma (r ^ c) := by
  have hp7 : Nat.Prime 7 := by decide
  have hσ7 : σ 1 (7 ^ 2) = 57 := by
    rw [sigma_prime_pow_two hp7]
    decide
  have hu7 : usigma (7 ^ 2) = 50 := by
    simpa using usigma_prime_pow hp7 (by decide : 0 < 2)
  rw [hσ7, hu7]
  have h37 := sigma_lt_cap_usigma (by decide : Nat.Prime 37) hb
  have hrcap := sigma_lt_cap_usigma hr hc
  have hu37 : 0 < usigma (37 ^ b) := by
    rw [usigma_prime_pow (by decide : Nat.Prime 37) hb]
    exact Nat.add_pos_left (by decide : 0 < 1) _
  have hthis := six_five_of_two_caps_times_const (A := 36) (B := 37)
    (X := σ 1 (37 ^ b)) (Y := usigma (37 ^ b)) (C := r - 1) (D := r)
    (P := σ 1 (r ^ c)) (Q := usigma (r ^ c)) (S := 50) (T := 57)
    h37 hrcap (five_mul_forty_nine_thirty_seven_cap hr43)
    (by decide : 0 < 37) hu37 (by decide : 0 < 57)
  convert hthis using 1 <;> ring

lemma forty_nine_thirty_seven_sq_forty_one_sq_under :
    5 * σ 1 (7 ^ 2) * σ 1 (37 ^ 2) * σ 1 (41 ^ 2) <
      6 * usigma (7 ^ 2) * usigma (37 ^ 2) * usigma (41 ^ 2) := by
  have hp7 : Nat.Prime 7 := by decide
  have hσ7 : σ 1 (7 ^ 2) = 57 := by
    rw [sigma_prime_pow_two hp7]
    decide
  have hu7 : usigma (7 ^ 2) = 50 := by
    simpa using usigma_prime_pow hp7 (by decide : 0 < 2)
  rw [hσ7, hu7, sigma_thirty_seven_pow_two, usigma_thirty_seven_pow_two,
    sigma_forty_one_pow_two, usigma_forty_one_pow_two]
  decide

lemma forty_nine_thirty_seven_sq_forty_one_cube_overshoot :
    6 * usigma (7 ^ 2) * usigma (37 ^ 2) * usigma (41 ^ 3) <
      5 * σ 1 (7 ^ 2) * σ 1 (37 ^ 2) * σ 1 (41 ^ 3) := by
  have hp7 : Nat.Prime 7 := by decide
  have hσ7 : σ 1 (7 ^ 2) = 57 := by
    rw [sigma_prime_pow_two hp7]
    decide
  have hu7 : usigma (7 ^ 2) = 50 := by
    simpa using usigma_prime_pow hp7 (by decide : 0 < 2)
  rw [hu7, hσ7, usigma_thirty_seven_pow_two, sigma_thirty_seven_pow_two,
    usigma_forty_one_pow_three, sigma_forty_one_pow_three]
  norm_num

lemma forty_nine_thirty_seven_cube_forty_one_sq_overshoot :
    6 * usigma (7 ^ 2) * usigma (37 ^ 3) * usigma (41 ^ 2) <
      5 * σ 1 (7 ^ 2) * σ 1 (37 ^ 3) * σ 1 (41 ^ 2) := by
  have hp7 : Nat.Prime 7 := by decide
  have hσ7 : σ 1 (7 ^ 2) = 57 := by
    rw [sigma_prime_pow_two hp7]
    decide
  have hu7 : usigma (7 ^ 2) = 50 := by
    simpa using usigma_prime_pow hp7 (by decide : 0 < 2)
  rw [hu7, hσ7, usigma_thirty_seven_pow_three, sigma_thirty_seven_pow_three,
    usigma_forty_one_pow_two, sigma_forty_one_pow_two]
  norm_num

lemma five_mul_seven_cube_thirty_seven_sq_cap {r : ℕ} (hr : 211 ≤ r) :
    5 * r * 400 * 1407 ≤ 6 * (r - 1) * 344 * 1370 := by
  have hdiff : 2827680 ≤ 13680 * r := by
    have hmul : 13680 * 211 ≤ 13680 * r := Nat.mul_le_mul_left 13680 hr
    have hnum : 13680 * 211 = 2886480 := by decide
    omega
  have hL : 5 * r * 400 * 1407 = 2814000 * r := by ring
  have hR : 6 * (r - 1) * 344 * 1370 = 2827680 * (r - 1) := by ring
  have hmain : 2814000 * r ≤ 2827680 * (r - 1) := by
    have heq : 2814000 * r + 13680 * r = 2827680 * r := by ring
    have hsub : 2814000 * r = 2827680 * r - 13680 * r :=
      (Nat.sub_eq_of_eq_add heq.symm).symm
    have hle : 2827680 * r - 13680 * r ≤ 2827680 * r - 2827680 :=
      Nat.sub_le_sub_left hdiff _
    have hrw : 2827680 * r - 2827680 = 2827680 * (r - 1) := by
      simpa using (Nat.mul_sub_left_distrib 2827680 r 1).symm
    calc
      2814000 * r = 2827680 * r - 13680 * r := hsub
      _ ≤ 2827680 * r - 2827680 := hle
      _ = 2827680 * (r - 1) := hrw
  rw [hL, hR]
  exact hmain

lemma five_sigma_lt_six_usigma_seven_cube_thirty_seven_sq_large {r k : ℕ}
    (hr : r.Prime) (hr211 : 211 ≤ r) (hk : 0 < k) :
    5 * σ 1 (7 ^ 3) * σ 1 (37 ^ 2) * σ 1 (r ^ k) <
      6 * usigma (7 ^ 3) * usigma (37 ^ 2) * usigma (r ^ k) := by
  rw [sigma_seven_pow_three, usigma_seven_pow_three,
    sigma_thirty_seven_pow_two, usigma_thirty_seven_pow_two]
  have hcp := sigma_lt_cap_usigma hr hk
  have hthis := six_five_of_cap_times_const (A := r - 1) (B := r)
    (X := σ 1 (r ^ k)) (Y := usigma (r ^ k)) (S := 344 * 1370)
    (T := 400 * 1407) hcp (by
      have hL : 5 * r * (400 * 1407) = 5 * r * 400 * 1407 := by ring
      have hR : 6 * (r - 1) * (344 * 1370) = 6 * (r - 1) * 344 * 1370 :=
        by ring
      rw [hL, hR]
      exact five_mul_seven_cube_thirty_seven_sq_cap hr211)
    (by decide : 0 < 400 * 1407)
  convert hthis using 1 <;> ring

lemma seven_cube_thirty_seven_cube_r_sq_overshoot_six_five {r : ℕ}
    (hr : r.Prime) (h41 : 41 ≤ r) (h242 : r ≤ 242) :
    6 * usigma (7 ^ 3) * usigma (37 ^ 3) * usigma (r ^ 2) <
      5 * σ 1 (7 ^ 3) * σ 1 (37 ^ 3) * σ 1 (r ^ 2) := by
  rw [usigma_seven_pow_three, sigma_seven_pow_three,
    sigma_thirty_seven_pow_three, usigma_thirty_seven_pow_three,
    sigma_prime_pow_two hr, usigma_prime_pow hr (by decide : 0 < 2)]
  have hsq : r ^ 2 ≤ 242 * r := by
    rw [pow_two]
    exact Nat.mul_le_mul_right r h242
  have hleft : 429856 * (1 + r ^ 2) < 104120000 * r := by
    have h1 : 429856 * (1 + r ^ 2) ≤ 429856 * (1 + 242 * r) :=
      Nat.mul_le_mul_left 429856 (Nat.add_le_add_left hsq 1)
    have h2 : 429856 * (1 + 242 * r) = 429856 + 104025152 * r := by
      have : 429856 * 242 = 104025152 := by decide
      ring
    have h3 : 429856 + 104025152 * r < 104120000 * r := by
      have : 429856 < 94848 * r :=
        lt_of_lt_of_le (by decide : 429856 < 3888768)
          (Nat.mul_le_mul_left 94848 h41)
      omega
    calc
      429856 * (1 + r ^ 2) ≤ 429856 * (1 + 242 * r) := h1
      _ = 429856 + 104025152 * r := h2
      _ < 104120000 * r := h3
  have hL : 6 * 344 * 50654 * (1 + r ^ 2) = 104549856 * (1 + r ^ 2) :=
    by ring
  have hR : 5 * 400 * 52060 * (1 + r + r ^ 2) = 104120000 * (1 + r + r ^ 2) :=
    by ring
  have hmain : 104549856 * (1 + r ^ 2) < 104120000 * (1 + r + r ^ 2) := by
    have h1 : 104549856 * (1 + r ^ 2) =
        104120000 * (1 + r ^ 2) + 429856 * (1 + r ^ 2) := by ring
    have h2 : 104120000 * (1 + r + r ^ 2) =
        104120000 * (1 + r ^ 2) + 104120000 * r := by ring
    rw [h1, h2]
    exact Nat.add_lt_add_left hleft _
  rw [hL, hR]
  exact hmain

lemma seven_cube_thirty_seven_cube_r_pow_ge_two_overshoot_six_five
    {r a b c : ℕ} (hr : r.Prime) (h41 : 41 ≤ r) (h242 : r ≤ 242)
    (ha : 3 ≤ a) (hb : 3 ≤ b) (hc : 2 ≤ c) :
    6 * usigma (7 ^ a) * usigma (37 ^ b) * usigma (r ^ c) <
      5 * σ 1 (7 ^ a) * σ 1 (37 ^ b) * σ 1 (r ^ c) :=
  six_five_overshoot_mono_three (by decide : Nat.Prime 7)
    (by decide : Nat.Prime 37) hr
    (by decide : 0 < 3) (by decide : 0 < 3) (by decide : 0 < 2)
    ha hb hc (seven_cube_thirty_seven_cube_r_sq_overshoot_six_five hr h41 h242)

lemma five_mul_seven_cube_thirty_seven_euler_cap {r : ℕ} (hr : 251 ≤ r) :
    5 * 37 * r * 400 ≤ 6 * 36 * (r - 1) * 344 := by
  have hdiff : 74304 ≤ 304 * r := by
    have hmul : 304 * 251 ≤ 304 * r := Nat.mul_le_mul_left 304 hr
    have hnum : 304 * 251 = 76304 := by decide
    omega
  have hL : 5 * 37 * r * 400 = 74000 * r := by ring
  have hR : 6 * 36 * (r - 1) * 344 = 74304 * (r - 1) := by ring
  have hmain : 74000 * r ≤ 74304 * (r - 1) := by
    have heq : 74000 * r + 304 * r = 74304 * r := by ring
    have hsub : 74000 * r = 74304 * r - 304 * r :=
      (Nat.sub_eq_of_eq_add heq.symm).symm
    have hle : 74304 * r - 304 * r ≤ 74304 * r - 74304 :=
      Nat.sub_le_sub_left hdiff _
    have hrw : 74304 * r - 74304 = 74304 * (r - 1) := by
      simpa using (Nat.mul_sub_left_distrib 74304 r 1).symm
    calc
      74000 * r = 74304 * r - 304 * r := hsub
      _ ≤ 74304 * r - 74304 := hle
      _ = 74304 * (r - 1) := hrw
  rw [hL, hR]
  exact hmain

lemma five_sigma_lt_six_usigma_seven_cube_thirty_seven_large {r b c : ℕ}
    (hr : r.Prime) (hr251 : 251 ≤ r) (hb : 0 < b) (hc : 0 < c) :
    5 * σ 1 (7 ^ 3) * σ 1 (37 ^ b) * σ 1 (r ^ c) <
      6 * usigma (7 ^ 3) * usigma (37 ^ b) * usigma (r ^ c) := by
  rw [sigma_seven_pow_three, usigma_seven_pow_three]
  have h37 := sigma_lt_cap_usigma (by decide : Nat.Prime 37) hb
  have hrcap := sigma_lt_cap_usigma hr hc
  have hu37 : 0 < usigma (37 ^ b) := by
    rw [usigma_prime_pow (by decide : Nat.Prime 37) hb]
    exact Nat.add_pos_left (by decide : 0 < 1) _
  have hthis := six_five_of_two_caps_times_const (A := 36) (B := 37)
    (X := σ 1 (37 ^ b)) (Y := usigma (37 ^ b)) (C := r - 1) (D := r)
    (P := σ 1 (r ^ c)) (Q := usigma (r ^ c)) (S := 344) (T := 400)
    h37 hrcap (five_mul_seven_cube_thirty_seven_euler_cap hr251)
    (by decide : 0 < 37) hu37 (by decide : 0 < 400)
  convert hthis using 1 <;> ring

/-- Leftover `6/5` cannot be three squareful primes `7,37,41` times a
squarefree coprime factor. -/
lemma not_five_sigma_of_three_sq_primes_seven_thirty_seven_forty_one {m : ℕ}
    (hm : m ≠ 0) (h : 5 * σ 1 m = 6 * usigma m)
    (hk7 : 2 ≤ padicValNat 7 m) (hk37 : 2 ≤ padicValNat 37 m)
    (hk41 : 2 ≤ padicValNat 41 m)
    (hs : Squarefree (ordCompl[41] (ordCompl[37] (ordCompl[7] m)))) :
    False := by
  have hp7 : Nat.Prime 7 := by decide
  have hp37 : Nat.Prime 37 := by decide
  have hp41 : Nat.Prime 41 := by decide
  have hpq_ne : (7 : ℕ) ≠ 37 := by decide
  have hpr_ne : (7 : ℕ) ≠ 41 := by decide
  have hqr_ne : (37 : ℕ) ≠ 41 := by decide
  have heq := five_sigma_eq_six_of_three_squareful hm hp7 hp37 hp41 hpq_ne
    hpr_ne hqr_ne h hs
  have hproj_p : ordProj[7] m = 7 ^ padicValNat 7 m := by
    simp [Nat.factorization_def m hp7]
  have hproj_q : ordProj[37] (ordCompl[7] m) =
      37 ^ padicValNat 37 (ordCompl[7] m) := by
    simp [Nat.factorization_def (ordCompl[7] m) hp37]
  have hproj_r : ordProj[41] (ordCompl[37] (ordCompl[7] m)) =
      41 ^ padicValNat 41 (ordCompl[37] (ordCompl[7] m)) := by
    simp [Nat.factorization_def (ordCompl[37] (ordCompl[7] m)) hp41]
  rw [hproj_r, padicValNat_ordCompl_of_ne hp41 hqr_ne,
    padicValNat_ordCompl_of_ne hp41 hpr_ne, hproj_q,
    padicValNat_ordCompl_of_ne hp37 hpq_ne, hproj_p] at heq
  rcases eq_or_lt_of_le hk7 with h7eq | h73
  · rw [← h7eq] at heq
    rcases eq_or_lt_of_le hk37 with h37eq | h373
    · rw [← h37eq] at heq
      rcases eq_or_lt_of_le hk41 with h41eq | h41k
      · rw [← h41eq] at heq
        exact forty_nine_thirty_seven_sq_forty_one_sq_under.ne heq
      · have hover := six_five_overshoot_mono_three hp7 hp37 hp41
          (by decide : 0 < 2) (by decide : 0 < 2) (by decide : 0 < 3)
          (le_refl _) (le_refl _) (Nat.succ_le_of_lt h41k)
          forty_nine_thirty_seven_sq_forty_one_cube_overshoot
        rw [← heq] at hover
        exact lt_irrefl _ hover
    · have hover := six_five_overshoot_mono_three hp7 hp37 hp41
        (by decide : 0 < 2) (by decide : 0 < 3) (by decide : 0 < 2)
        (le_refl _) (Nat.succ_le_of_lt h373) hk41
        forty_nine_thirty_seven_cube_forty_one_sq_overshoot
      rw [← heq] at hover
      exact lt_irrefl _ hover
  · have hover := seven_cube_thirty_seven_r_sq_pow_ge_two_overshoot_six_five
      hp41 (by decide : 41 ≤ 41) (by decide : 41 ≤ 205)
      (Nat.succ_le_of_lt h73) hk37 hk41
    rw [← heq] at hover
    exact lt_irrefl _ hover

/-- Leftover `6/5` cannot be three squareful primes `7,37,r` with `r ≥ 43`
and `v₇ = 2` times a squarefree coprime factor. -/
lemma not_five_sigma_of_three_sq_primes_seven_thirty_seven_of_val_seven_eq_two
    {m r : ℕ} (hm : m ≠ 0) (hr : r.Prime) (hr43 : 43 ≤ r)
    (h : 5 * σ 1 m = 6 * usigma m)
    (hk7 : padicValNat 7 m = 2) (hk37 : 2 ≤ padicValNat 37 m)
    (hkr : 2 ≤ padicValNat r m)
    (hs : Squarefree (ordCompl[r] (ordCompl[37] (ordCompl[7] m)))) :
    False := by
  have hp7 : Nat.Prime 7 := by decide
  have hp37 : Nat.Prime 37 := by decide
  have hpq_ne : (7 : ℕ) ≠ 37 := by decide
  have hpr_ne : (7 : ℕ) ≠ r :=
    Nat.ne_of_lt (lt_of_lt_of_le (by decide : 7 < 43) hr43)
  have hqr_ne : (37 : ℕ) ≠ r :=
    Nat.ne_of_lt (lt_of_lt_of_le (by decide : 37 < 43) hr43)
  have heq := five_sigma_eq_six_of_three_squareful hm hp7 hp37 hr hpq_ne hpr_ne
    hqr_ne h hs
  have hproj_p : ordProj[7] m = 7 ^ padicValNat 7 m := by
    simp [Nat.factorization_def m hp7]
  have hproj_q : ordProj[37] (ordCompl[7] m) =
      37 ^ padicValNat 37 (ordCompl[7] m) := by
    simp [Nat.factorization_def (ordCompl[7] m) hp37]
  have hproj_r : ordProj[r] (ordCompl[37] (ordCompl[7] m)) =
      r ^ padicValNat r (ordCompl[37] (ordCompl[7] m)) := by
    simp [Nat.factorization_def (ordCompl[37] (ordCompl[7] m)) hr]
  rw [hproj_r, padicValNat_ordCompl_of_ne hr hqr_ne,
    padicValNat_ordCompl_of_ne hr hpr_ne, hproj_q,
    padicValNat_ordCompl_of_ne hp37 hpq_ne, hproj_p, hk7] at heq
  exact (five_sigma_lt_six_usigma_seven_sq_thirty_seven_large hr hr43
    (lt_of_lt_of_le (by decide : (0 : ℕ) < 2) hk37)
    (lt_of_lt_of_le (by decide : (0 : ℕ) < 2) hkr)).ne heq

/-- Leftover `6/5` cannot be three squareful primes `7,37,r` with
`41 ≤ r ≤ 205` times a squarefree coprime factor. -/
lemma not_five_sigma_of_three_sq_primes_seven_thirty_seven_of_r_le_two_hundred_five
    {m r : ℕ} (hm : m ≠ 0) (hr : r.Prime) (hr41 : 41 ≤ r) (hr205 : r ≤ 205)
    (h : 5 * σ 1 m = 6 * usigma m)
    (hk7 : 2 ≤ padicValNat 7 m) (hk37 : 2 ≤ padicValNat 37 m)
    (hkr : 2 ≤ padicValNat r m)
    (hs : Squarefree (ordCompl[r] (ordCompl[37] (ordCompl[7] m)))) :
    False := by
  rcases le_or_gt r 41 with hle | hgt
  · have hr41eq : r = 41 := le_antisymm hle hr41
    subst r
    exact not_five_sigma_of_three_sq_primes_seven_thirty_seven_forty_one
      hm h hk7 hk37 hkr hs
  · have hr43 : 43 ≤ r :=
      prime_ge_forty_two_ge_forty_three hr (Nat.succ_le_of_lt hgt)
    rcases eq_or_lt_of_le hk7 with h7eq | h73
    · exact not_five_sigma_of_three_sq_primes_seven_thirty_seven_of_val_seven_eq_two
        hm hr hr43 h h7eq.symm hk37 hkr hs
    · have hp7 : Nat.Prime 7 := by decide
      have hp37 : Nat.Prime 37 := by decide
      have hpq_ne : (7 : ℕ) ≠ 37 := by decide
      have hpr_ne : (7 : ℕ) ≠ r :=
        Nat.ne_of_lt (lt_of_lt_of_le (by decide : 7 < 41) hr41)
      have hqr_ne : (37 : ℕ) ≠ r :=
        Nat.ne_of_lt (lt_of_lt_of_le (by decide : 37 < 41) hr41)
      have heq := five_sigma_eq_six_of_three_squareful hm hp7 hp37 hr hpq_ne
        hpr_ne hqr_ne h hs
      have hproj_p : ordProj[7] m = 7 ^ padicValNat 7 m := by
        simp [Nat.factorization_def m hp7]
      have hproj_q : ordProj[37] (ordCompl[7] m) =
          37 ^ padicValNat 37 (ordCompl[7] m) := by
        simp [Nat.factorization_def (ordCompl[7] m) hp37]
      have hproj_r : ordProj[r] (ordCompl[37] (ordCompl[7] m)) =
          r ^ padicValNat r (ordCompl[37] (ordCompl[7] m)) := by
        simp [Nat.factorization_def (ordCompl[37] (ordCompl[7] m)) hr]
      rw [hproj_r, padicValNat_ordCompl_of_ne hr hqr_ne,
        padicValNat_ordCompl_of_ne hr hpr_ne, hproj_q,
        padicValNat_ordCompl_of_ne hp37 hpq_ne, hproj_p] at heq
      have hover := seven_cube_thirty_seven_r_sq_pow_ge_two_overshoot_six_five
        hr hr41 hr205 (Nat.succ_le_of_lt h73) hk37 hkr
      rw [← heq] at hover
      exact lt_irrefl _ hover

/-- Leftover `6/5` cannot be three squareful primes `7,37,r` with `r ≥ 211`
and `v₇ = 3` times a squarefree coprime factor. -/
lemma not_five_sigma_of_three_sq_primes_seven_thirty_seven_of_val_seven_eq_three
    {m r : ℕ} (hm : m ≠ 0) (hr : r.Prime) (hr211 : 211 ≤ r)
    (h : 5 * σ 1 m = 6 * usigma m)
    (hk7 : padicValNat 7 m = 3) (hk37 : 2 ≤ padicValNat 37 m)
    (hkr : 2 ≤ padicValNat r m)
    (hs : Squarefree (ordCompl[r] (ordCompl[37] (ordCompl[7] m)))) :
    False := by
  have hp7 : Nat.Prime 7 := by decide
  have hp37 : Nat.Prime 37 := by decide
  have hpq_ne : (7 : ℕ) ≠ 37 := by decide
  have hpr_ne : (7 : ℕ) ≠ r :=
    Nat.ne_of_lt (lt_of_lt_of_le (by decide : 7 < 211) hr211)
  have hqr_ne : (37 : ℕ) ≠ r :=
    Nat.ne_of_lt (lt_of_lt_of_le (by decide : 37 < 211) hr211)
  have heq := five_sigma_eq_six_of_three_squareful hm hp7 hp37 hr hpq_ne hpr_ne
    hqr_ne h hs
  have hproj_p : ordProj[7] m = 7 ^ padicValNat 7 m := by
    simp [Nat.factorization_def m hp7]
  have hproj_q : ordProj[37] (ordCompl[7] m) =
      37 ^ padicValNat 37 (ordCompl[7] m) := by
    simp [Nat.factorization_def (ordCompl[7] m) hp37]
  have hproj_r : ordProj[r] (ordCompl[37] (ordCompl[7] m)) =
      r ^ padicValNat r (ordCompl[37] (ordCompl[7] m)) := by
    simp [Nat.factorization_def (ordCompl[37] (ordCompl[7] m)) hr]
  rw [hproj_r, padicValNat_ordCompl_of_ne hr hqr_ne,
    padicValNat_ordCompl_of_ne hr hpr_ne, hproj_q,
    padicValNat_ordCompl_of_ne hp37 hpq_ne, hproj_p, hk7] at heq
  rcases eq_or_lt_of_le hk37 with h37eq | h373
  · rw [← h37eq] at heq
    exact (five_sigma_lt_six_usigma_seven_cube_thirty_seven_sq_large hr hr211
      (lt_of_lt_of_le (by decide : (0 : ℕ) < 2) hkr)).ne heq
  · rcases le_or_gt r 242 with h242 | h243
    · have hover := seven_cube_thirty_seven_cube_r_pow_ge_two_overshoot_six_five
        hr (lt_of_lt_of_le (by decide : (41 : ℕ) < 211) hr211).le h242
        (le_refl _) (Nat.succ_le_of_lt h373) hkr
      rw [← heq] at hover
      exact lt_irrefl _ hover
    · have hr251 : 251 ≤ r :=
        prime_ge_two_hundred_forty_three_ge_two_hundred_fifty_one hr
          (Nat.succ_le_of_lt h243)
      exact (five_sigma_lt_six_usigma_seven_cube_thirty_seven_large hr hr251
        (lt_of_lt_of_le (by decide : (0 : ℕ) < 2) hk37)
        ((Nat.zero_lt_succ 1).trans_le hkr)).ne heq

lemma prime_ge_five_hundred_one_ge_five_hundred_three {p : ℕ} (hp : p.Prime)
    (h : 501 ≤ p) : 503 ≤ p := by
  have hmem : p = 501 ∨ p = 502 ∨ 503 ≤ p := by omega
  rcases hmem with rfl | rfl | h503
  · exact False.elim (not_prime_of_eq_mul (rfl : 501 = 3 * 167)
      (by decide : (3 : ℕ) ≠ 1) (by decide : (167 : ℕ) ≠ 1) hp)
  · exact False.elim (not_prime_of_eq_mul (rfl : 502 = 2 * 251)
      (by decide : (2 : ℕ) ≠ 1) (by decide : (251 : ℕ) ≠ 1) hp)
  · exact h503

lemma prime_ge_seven_hundred_eighty_nine_ge_seven_ninety_seven {p : ℕ}
    (hp : p.Prime) (h : 789 ≤ p) : 797 ≤ p := by
  have hmem : p = 789 ∨ p = 790 ∨ p = 791 ∨ p = 792 ∨ p = 793 ∨ p = 794 ∨
      p = 795 ∨ p = 796 ∨ 797 ≤ p := by omega
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | h797
  · exact False.elim (not_prime_of_eq_mul (rfl : 789 = 3 * 263)
      (by decide : (3 : ℕ) ≠ 1) (by decide : (263 : ℕ) ≠ 1) hp)
  · exact False.elim (not_prime_of_eq_mul (rfl : 790 = 2 * 395)
      (by decide : (2 : ℕ) ≠ 1) (by decide : (395 : ℕ) ≠ 1) hp)
  · exact False.elim (not_prime_of_eq_mul (rfl : 791 = 7 * 113)
      (by decide : (7 : ℕ) ≠ 1) (by decide : (113 : ℕ) ≠ 1) hp)
  · exact False.elim (not_prime_of_eq_mul (rfl : 792 = 2 * 396)
      (by decide : (2 : ℕ) ≠ 1) (by decide : (396 : ℕ) ≠ 1) hp)
  · exact False.elim (not_prime_of_eq_mul (rfl : 793 = 13 * 61)
      (by decide : (13 : ℕ) ≠ 1) (by decide : (61 : ℕ) ≠ 1) hp)
  · exact False.elim (not_prime_of_eq_mul (rfl : 794 = 2 * 397)
      (by decide : (2 : ℕ) ≠ 1) (by decide : (397 : ℕ) ≠ 1) hp)
  · exact False.elim (not_prime_of_eq_mul (rfl : 795 = 3 * 265)
      (by decide : (3 : ℕ) ≠ 1) (by decide : (265 : ℕ) ≠ 1) hp)
  · exact False.elim (not_prime_of_eq_mul (rfl : 796 = 2 * 398)
      (by decide : (2 : ℕ) ≠ 1) (by decide : (398 : ℕ) ≠ 1) hp)
  · exact h797

lemma prime_ge_seven_hundred_ninety_eight_ge_eight_hundred_nine {p : ℕ}
    (hp : p.Prime) (h : 798 ≤ p) : 809 ≤ p := by
  have hmem : p = 798 ∨ p = 799 ∨ p = 800 ∨ p = 801 ∨ p = 802 ∨ p = 803 ∨
      p = 804 ∨ p = 805 ∨ p = 806 ∨ p = 807 ∨ p = 808 ∨ 809 ≤ p := by omega
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | h809
  · exact False.elim (not_prime_of_eq_mul (rfl : 798 = 2 * 399)
      (by decide : (2 : ℕ) ≠ 1) (by decide : (399 : ℕ) ≠ 1) hp)
  · exact False.elim (not_prime_of_eq_mul (rfl : 799 = 17 * 47)
      (by decide : (17 : ℕ) ≠ 1) (by decide : (47 : ℕ) ≠ 1) hp)
  · exact False.elim (not_prime_of_eq_mul (rfl : 800 = 2 * 400)
      (by decide : (2 : ℕ) ≠ 1) (by decide : (400 : ℕ) ≠ 1) hp)
  · exact False.elim (not_prime_of_eq_mul (rfl : 801 = 3 * 267)
      (by decide : (3 : ℕ) ≠ 1) (by decide : (267 : ℕ) ≠ 1) hp)
  · exact False.elim (not_prime_of_eq_mul (rfl : 802 = 2 * 401)
      (by decide : (2 : ℕ) ≠ 1) (by decide : (401 : ℕ) ≠ 1) hp)
  · exact False.elim (not_prime_of_eq_mul (rfl : 803 = 11 * 73)
      (by decide : (11 : ℕ) ≠ 1) (by decide : (73 : ℕ) ≠ 1) hp)
  · exact False.elim (not_prime_of_eq_mul (rfl : 804 = 2 * 402)
      (by decide : (2 : ℕ) ≠ 1) (by decide : (402 : ℕ) ≠ 1) hp)
  · exact False.elim (not_prime_of_eq_mul (rfl : 805 = 5 * 161)
      (by decide : (5 : ℕ) ≠ 1) (by decide : (161 : ℕ) ≠ 1) hp)
  · exact False.elim (not_prime_of_eq_mul (rfl : 806 = 2 * 403)
      (by decide : (2 : ℕ) ≠ 1) (by decide : (403 : ℕ) ≠ 1) hp)
  · exact False.elim (not_prime_of_eq_mul (rfl : 807 = 3 * 269)
      (by decide : (3 : ℕ) ≠ 1) (by decide : (269 : ℕ) ≠ 1) hp)
  · exact False.elim (not_prime_of_eq_mul (rfl : 808 = 2 * 404)
      (by decide : (2 : ℕ) ≠ 1) (by decide : (404 : ℕ) ≠ 1) hp)
  · exact h809

lemma prime_seven_ninety_seven : Nat.Prime 797 := by norm_num

lemma usigma_thirty_seven_pow_four : usigma (37 ^ 4) = 1874162 := by
  rw [usigma_prime_pow (by decide : Nat.Prime 37) (by decide : 0 < 4)]
  decide

lemma sigma_thirty_seven_pow_four : σ 1 (37 ^ 4) = 1926221 := by
  rw [sigma_prime_pow_div (by decide : Nat.Prime 37)]
  norm_num

lemma seven_fourth_thirty_seven_sq_r_sq_overshoot_six_five {r : ℕ}
    (hr : r.Prime) (h211 : 211 ≤ r) (h500 : r ≤ 500) :
    6 * usigma (7 ^ 4) * usigma (37 ^ 2) * usigma (r ^ 2) <
      5 * σ 1 (7 ^ 4) * σ 1 (37 ^ 2) * σ 1 (r ^ 2) := by
  rw [usigma_seven_pow_four, sigma_seven_pow_four,
    sigma_thirty_seven_pow_two, usigma_thirty_seven_pow_two,
    sigma_prime_pow_two hr, usigma_prime_pow hr (by decide : 0 < 2)]
  have hsq : r ^ 2 ≤ 500 * r := by
    rw [pow_two]
    exact Nat.mul_le_mul_right r h500
  have hleft : 39405 * (1 + r ^ 2) < 19705035 * r := by
    have h1 : 39405 * (1 + r ^ 2) ≤ 39405 * (1 + 500 * r) :=
      Nat.mul_le_mul_left 39405 (Nat.add_le_add_left hsq 1)
    have h2 : 39405 * (1 + 500 * r) = 39405 + 19702500 * r := by
      have : 39405 * 500 = 19702500 := by decide
      ring
    have h3 : 39405 + 19702500 * r < 19705035 * r := by
      have : 39405 < 2535 * r :=
        lt_of_lt_of_le (by decide : 39405 < 534885)
          (Nat.mul_le_mul_left 2535 h211)
      omega
    calc
      39405 * (1 + r ^ 2) ≤ 39405 * (1 + 500 * r) := h1
      _ = 39405 + 19702500 * r := h2
      _ < 19705035 * r := h3
  have hL : 6 * 2402 * 1370 * (1 + r ^ 2) = 19744440 * (1 + r ^ 2) := by ring
  have hR : 5 * 2801 * 1407 * (1 + r + r ^ 2) = 19705035 * (1 + r + r ^ 2) :=
    by ring
  have hmain : 19744440 * (1 + r ^ 2) < 19705035 * (1 + r + r ^ 2) := by
    have h1 : 19744440 * (1 + r ^ 2) =
        19705035 * (1 + r ^ 2) + 39405 * (1 + r ^ 2) := by ring
    have h2 : 19705035 * (1 + r + r ^ 2) =
        19705035 * (1 + r ^ 2) + 19705035 * r := by ring
    rw [h1, h2]
    exact Nat.add_lt_add_left hleft _
  rw [hL, hR]
  exact hmain

lemma seven_fourth_thirty_seven_r_sq_pow_ge_two_overshoot_six_five
    {r a b c : ℕ} (hr : r.Prime) (h211 : 211 ≤ r) (h500 : r ≤ 500)
    (ha : 4 ≤ a) (hb : 2 ≤ b) (hc : 2 ≤ c) :
    6 * usigma (7 ^ a) * usigma (37 ^ b) * usigma (r ^ c) <
      5 * σ 1 (7 ^ a) * σ 1 (37 ^ b) * σ 1 (r ^ c) :=
  six_five_overshoot_mono_three (by decide : Nat.Prime 7)
    (by decide : Nat.Prime 37) hr
    (by decide : 0 < 4) (by decide : 0 < 2) (by decide : 0 < 2)
    ha hb hc (seven_fourth_thirty_seven_sq_r_sq_overshoot_six_five hr h211 h500)

lemma five_mul_seven_fourth_thirty_seven_sq_cap {r : ℕ} (hr : 503 ≤ r) :
    5 * r * 2801 * 1407 ≤ 6 * (r - 1) * 2402 * 1370 := by
  have hdiff : 19744440 ≤ 39405 * r := by
    have hmul : 39405 * 503 ≤ 39405 * r := Nat.mul_le_mul_left 39405 hr
    have hnum : 39405 * 503 = 19820715 := by decide
    omega
  have hL : 5 * r * 2801 * 1407 = 19705035 * r := by ring
  have hR : 6 * (r - 1) * 2402 * 1370 = 19744440 * (r - 1) := by ring
  have hmain : 19705035 * r ≤ 19744440 * (r - 1) := by
    have heq : 19705035 * r + 39405 * r = 19744440 * r := by ring
    have hsub : 19705035 * r = 19744440 * r - 39405 * r :=
      (Nat.sub_eq_of_eq_add heq.symm).symm
    have hle : 19744440 * r - 39405 * r ≤ 19744440 * r - 19744440 :=
      Nat.sub_le_sub_left hdiff _
    have hrw : 19744440 * r - 19744440 = 19744440 * (r - 1) := by
      simpa using (Nat.mul_sub_left_distrib 19744440 r 1).symm
    calc
      19705035 * r = 19744440 * r - 39405 * r := hsub
      _ ≤ 19744440 * r - 19744440 := hle
      _ = 19744440 * (r - 1) := hrw
  rw [hL, hR]
  exact hmain

lemma five_sigma_lt_six_usigma_seven_fourth_thirty_seven_sq_large {r k : ℕ}
    (hr : r.Prime) (hr503 : 503 ≤ r) (hk : 0 < k) :
    5 * σ 1 (7 ^ 4) * σ 1 (37 ^ 2) * σ 1 (r ^ k) <
      6 * usigma (7 ^ 4) * usigma (37 ^ 2) * usigma (r ^ k) := by
  rw [sigma_seven_pow_four, usigma_seven_pow_four,
    sigma_thirty_seven_pow_two, usigma_thirty_seven_pow_two]
  have hcp := sigma_lt_cap_usigma hr hk
  have hthis := six_five_of_cap_times_const (A := r - 1) (B := r)
    (X := σ 1 (r ^ k)) (Y := usigma (r ^ k)) (S := 2402 * 1370)
    (T := 2801 * 1407) hcp (by
      have hL : 5 * r * (2801 * 1407) = 5 * r * 2801 * 1407 := by ring
      have hR : 6 * (r - 1) * (2402 * 1370) = 6 * (r - 1) * 2402 * 1370 :=
        by ring
      rw [hL, hR]
      exact five_mul_seven_fourth_thirty_seven_sq_cap hr503)
    (by decide : 0 < 2801 * 1407)
  convert hthis using 1 <;> ring

lemma seven_fourth_thirty_seven_cube_r_sq_overshoot_six_five {r : ℕ}
    (hr : r.Prime) (h211 : 211 ≤ r) (h788 : r ≤ 788) :
    6 * usigma (7 ^ 4) * usigma (37 ^ 3) * usigma (r ^ 2) <
      5 * σ 1 (7 ^ 4) * σ 1 (37 ^ 3) * σ 1 (r ^ 2) := by
  rw [usigma_seven_pow_four, sigma_seven_pow_four,
    sigma_thirty_seven_pow_three, usigma_thirty_seven_pow_three,
    sigma_prime_pow_two hr, usigma_prime_pow hr (by decide : 0 < 2)]
  have hsq : r ^ 2 ≤ 788 * r := by
    rw [pow_two]
    exact Nat.mul_le_mul_right r h788
  have hleft : 925148 * (1 + r ^ 2) < 729100300 * r := by
    have h1 : 925148 * (1 + r ^ 2) ≤ 925148 * (1 + 788 * r) :=
      Nat.mul_le_mul_left 925148 (Nat.add_le_add_left hsq 1)
    have h2 : 925148 * (1 + 788 * r) = 925148 + 729016624 * r := by
      have : 925148 * 788 = 729016624 := by decide
      ring
    have h3 : 925148 + 729016624 * r < 729100300 * r := by
      have : 925148 < 83676 * r :=
        lt_of_lt_of_le (by decide : 925148 < 17655636)
          (Nat.mul_le_mul_left 83676 h211)
      omega
    calc
      925148 * (1 + r ^ 2) ≤ 925148 * (1 + 788 * r) := h1
      _ = 925148 + 729016624 * r := h2
      _ < 729100300 * r := h3
  have hL : 6 * 2402 * 50654 * (1 + r ^ 2) = 730025448 * (1 + r ^ 2) :=
    by ring
  have hR : 5 * 2801 * 52060 * (1 + r + r ^ 2) = 729100300 * (1 + r + r ^ 2) :=
    by ring
  have hmain : 730025448 * (1 + r ^ 2) < 729100300 * (1 + r + r ^ 2) := by
    have h1 : 730025448 * (1 + r ^ 2) =
        729100300 * (1 + r ^ 2) + 925148 * (1 + r ^ 2) := by ring
    have h2 : 729100300 * (1 + r + r ^ 2) =
        729100300 * (1 + r ^ 2) + 729100300 * r := by ring
    rw [h1, h2]
    exact Nat.add_lt_add_left hleft _
  rw [hL, hR]
  exact hmain

lemma seven_fourth_thirty_seven_cube_r_pow_ge_two_overshoot_six_five
    {r a b c : ℕ} (hr : r.Prime) (h211 : 211 ≤ r) (h788 : r ≤ 788)
    (ha : 4 ≤ a) (hb : 3 ≤ b) (hc : 2 ≤ c) :
    6 * usigma (7 ^ a) * usigma (37 ^ b) * usigma (r ^ c) <
      5 * σ 1 (7 ^ a) * σ 1 (37 ^ b) * σ 1 (r ^ c) :=
  six_five_overshoot_mono_three (by decide : Nat.Prime 7)
    (by decide : Nat.Prime 37) hr
    (by decide : 0 < 4) (by decide : 0 < 3) (by decide : 0 < 2)
    ha hb hc (seven_fourth_thirty_seven_cube_r_sq_overshoot_six_five hr h211 h788)

lemma five_mul_seven_fourth_thirty_seven_cube_cap {r : ℕ} (hr : 797 ≤ r) :
    5 * r * 2801 * 52060 ≤ 6 * (r - 1) * 2402 * 50654 := by
  have hdiff : 730025448 ≤ 925148 * r := by
    have hmul : 925148 * 797 ≤ 925148 * r := Nat.mul_le_mul_left 925148 hr
    have hnum : 925148 * 797 = 737342956 := by decide
    omega
  have hL : 5 * r * 2801 * 52060 = 729100300 * r := by ring
  have hR : 6 * (r - 1) * 2402 * 50654 = 730025448 * (r - 1) := by ring
  have hmain : 729100300 * r ≤ 730025448 * (r - 1) := by
    have heq : 729100300 * r + 925148 * r = 730025448 * r := by ring
    have hsub : 729100300 * r = 730025448 * r - 925148 * r :=
      (Nat.sub_eq_of_eq_add heq.symm).symm
    have hle : 730025448 * r - 925148 * r ≤ 730025448 * r - 730025448 :=
      Nat.sub_le_sub_left hdiff _
    have hrw : 730025448 * r - 730025448 = 730025448 * (r - 1) := by
      simpa using (Nat.mul_sub_left_distrib 730025448 r 1).symm
    calc
      729100300 * r = 730025448 * r - 925148 * r := hsub
      _ ≤ 730025448 * r - 730025448 := hle
      _ = 730025448 * (r - 1) := hrw
  rw [hL, hR]
  exact hmain

lemma five_sigma_lt_six_usigma_seven_fourth_thirty_seven_cube_large {r k : ℕ}
    (hr : r.Prime) (hr797 : 797 ≤ r) (hk : 0 < k) :
    5 * σ 1 (7 ^ 4) * σ 1 (37 ^ 3) * σ 1 (r ^ k) <
      6 * usigma (7 ^ 4) * usigma (37 ^ 3) * usigma (r ^ k) := by
  rw [sigma_seven_pow_four, usigma_seven_pow_four,
    sigma_thirty_seven_pow_three, usigma_thirty_seven_pow_three]
  have hcp := sigma_lt_cap_usigma hr hk
  have hT : 0 < 2801 * 52060 :=
    Nat.mul_pos (by decide : 0 < 2801) (by decide : 0 < 52060)
  have hthis := six_five_of_cap_times_const (A := r - 1) (B := r)
    (X := σ 1 (r ^ k)) (Y := usigma (r ^ k)) (S := 2402 * 50654)
    (T := 2801 * 52060) hcp (by
      have hL : 5 * r * (2801 * 52060) = 5 * r * 2801 * 52060 := by ring
      have hR : 6 * (r - 1) * (2402 * 50654) = 6 * (r - 1) * 2402 * 50654 :=
        by ring
      rw [hL, hR]
      exact five_mul_seven_fourth_thirty_seven_cube_cap hr797)
    hT
  convert hthis using 1 <;> ring

lemma five_mul_seven_fourth_thirty_seven_euler_cap {r : ℕ} (hr : 809 ≤ r) :
    5 * 37 * r * 2801 ≤ 6 * 36 * (r - 1) * 2402 := by
  have hdiff : 518832 ≤ 647 * r := by
    have hmul : 647 * 809 ≤ 647 * r := Nat.mul_le_mul_left 647 hr
    have hnum : 647 * 809 = 523423 := by decide
    omega
  have hL : 5 * 37 * r * 2801 = 518185 * r := by ring
  have hR : 6 * 36 * (r - 1) * 2402 = 518832 * (r - 1) := by ring
  have hmain : 518185 * r ≤ 518832 * (r - 1) := by
    have heq : 518185 * r + 647 * r = 518832 * r := by ring
    have hsub : 518185 * r = 518832 * r - 647 * r :=
      (Nat.sub_eq_of_eq_add heq.symm).symm
    have hle : 518832 * r - 647 * r ≤ 518832 * r - 518832 :=
      Nat.sub_le_sub_left hdiff _
    have hrw : 518832 * r - 518832 = 518832 * (r - 1) := by
      simpa using (Nat.mul_sub_left_distrib 518832 r 1).symm
    calc
      518185 * r = 518832 * r - 647 * r := hsub
      _ ≤ 518832 * r - 518832 := hle
      _ = 518832 * (r - 1) := hrw
  rw [hL, hR]
  exact hmain

lemma five_sigma_lt_six_usigma_seven_fourth_thirty_seven_large {r b c : ℕ}
    (hr : r.Prime) (hr809 : 809 ≤ r) (hb : 0 < b) (hc : 0 < c) :
    5 * σ 1 (7 ^ 4) * σ 1 (37 ^ b) * σ 1 (r ^ c) <
      6 * usigma (7 ^ 4) * usigma (37 ^ b) * usigma (r ^ c) := by
  rw [sigma_seven_pow_four, usigma_seven_pow_four]
  have h37 := sigma_lt_cap_usigma (by decide : Nat.Prime 37) hb
  have hrcap := sigma_lt_cap_usigma hr hc
  have hu37 : 0 < usigma (37 ^ b) := by
    rw [usigma_prime_pow (by decide : Nat.Prime 37) hb]
    exact Nat.add_pos_left (by decide : 0 < 1) _
  have hthis := six_five_of_two_caps_times_const (A := 36) (B := 37)
    (X := σ 1 (37 ^ b)) (Y := usigma (37 ^ b)) (C := r - 1) (D := r)
    (P := σ 1 (r ^ c)) (Q := usigma (r ^ c)) (S := 2402) (T := 2801)
    h37 hrcap (five_mul_seven_fourth_thirty_seven_euler_cap hr809)
    (by decide : 0 < 37) hu37 (by decide : 0 < 2801)
  convert hthis using 1 <;> ring

lemma seven_fourth_thirty_seven_fourth_seven_ninety_seven_sq_overshoot :
    6 * usigma (7 ^ 4) * usigma (37 ^ 4) * usigma (797 ^ 2) <
      5 * σ 1 (7 ^ 4) * σ 1 (37 ^ 4) * σ 1 (797 ^ 2) := by
  rw [usigma_seven_pow_four, sigma_seven_pow_four,
    usigma_thirty_seven_pow_four, sigma_thirty_seven_pow_four,
    usigma_prime_pow prime_seven_ninety_seven (by decide : 0 < 2),
    sigma_prime_pow_two prime_seven_ninety_seven]
  norm_num

/-- Leftover `6/5` cannot be three squareful primes `7,37,r` with `r ≥ 211`
and `v₇ = 4` times a squarefree coprime factor. -/
lemma not_five_sigma_of_three_sq_primes_seven_thirty_seven_of_val_seven_eq_four
    {m r : ℕ} (hm : m ≠ 0) (hr : r.Prime) (hr211 : 211 ≤ r)
    (h : 5 * σ 1 m = 6 * usigma m)
    (hk7 : padicValNat 7 m = 4) (hk37 : 2 ≤ padicValNat 37 m)
    (hkr : 2 ≤ padicValNat r m)
    (hs : Squarefree (ordCompl[r] (ordCompl[37] (ordCompl[7] m)))) :
    False := by
  have hp7 : Nat.Prime 7 := by decide
  have hp37 : Nat.Prime 37 := by decide
  have hpq_ne : (7 : ℕ) ≠ 37 := by decide
  have hpr_ne : (7 : ℕ) ≠ r :=
    Nat.ne_of_lt (lt_of_lt_of_le (by decide : 7 < 211) hr211)
  have hqr_ne : (37 : ℕ) ≠ r :=
    Nat.ne_of_lt (lt_of_lt_of_le (by decide : 37 < 211) hr211)
  have heq := five_sigma_eq_six_of_three_squareful hm hp7 hp37 hr hpq_ne hpr_ne
    hqr_ne h hs
  have hproj_p : ordProj[7] m = 7 ^ padicValNat 7 m := by
    simp [Nat.factorization_def m hp7]
  have hproj_q : ordProj[37] (ordCompl[7] m) =
      37 ^ padicValNat 37 (ordCompl[7] m) := by
    simp [Nat.factorization_def (ordCompl[7] m) hp37]
  have hproj_r : ordProj[r] (ordCompl[37] (ordCompl[7] m)) =
      r ^ padicValNat r (ordCompl[37] (ordCompl[7] m)) := by
    simp [Nat.factorization_def (ordCompl[37] (ordCompl[7] m)) hr]
  rw [hproj_r, padicValNat_ordCompl_of_ne hr hqr_ne,
    padicValNat_ordCompl_of_ne hr hpr_ne, hproj_q,
    padicValNat_ordCompl_of_ne hp37 hpq_ne, hproj_p, hk7] at heq
  rcases le_or_gt r 500 with h500 | h501
  · have hover := seven_fourth_thirty_seven_r_sq_pow_ge_two_overshoot_six_five
      hr hr211 h500 (le_refl _) hk37 hkr
    rw [← heq] at hover
    exact lt_irrefl _ hover
  · have hr503 : 503 ≤ r :=
      prime_ge_five_hundred_one_ge_five_hundred_three hr (Nat.succ_le_of_lt h501)
    rcases eq_or_lt_of_le hk37 with h37eq | h373
    · rw [← h37eq] at heq
      exact (five_sigma_lt_six_usigma_seven_fourth_thirty_seven_sq_large hr
        hr503 ((Nat.zero_lt_succ 1).trans_le hkr)).ne heq
    · rcases le_or_gt r 788 with h788 | h789
      · have hover := seven_fourth_thirty_seven_cube_r_pow_ge_two_overshoot_six_five
          hr hr211 h788 (le_refl _) (Nat.succ_le_of_lt h373) hkr
        rw [← heq] at hover
        exact lt_irrefl _ hover
      · have hr797 : 797 ≤ r :=
          prime_ge_seven_hundred_eighty_nine_ge_seven_ninety_seven hr
            (Nat.succ_le_of_lt h789)
        rcases le_or_gt r 797 with h797 | h798
        · have hr797eq : r = 797 := le_antisymm h797 hr797
          subst r
          rcases eq_or_lt_of_le (Nat.succ_le_of_lt h373) with h37eq3 | h374
          · have h37eq : padicValNat 37 m = 3 := h37eq3.symm
            rw [h37eq] at heq
            have hlt :=
              five_sigma_lt_six_usigma_seven_fourth_thirty_seven_cube_large
                prime_seven_ninety_seven (le_refl _)
                ((Nat.zero_lt_succ 1).trans_le hkr)
            exact hlt.ne heq
          · have hover := six_five_overshoot_mono_three hp7 hp37
              prime_seven_ninety_seven
              (by decide : 0 < 4) (by decide : 0 < 4) (by decide : 0 < 2)
              (le_refl _) (Nat.succ_le_of_lt h374) hkr
              seven_fourth_thirty_seven_fourth_seven_ninety_seven_sq_overshoot
            rw [← heq] at hover
            exact lt_irrefl _ hover
        · have hr809 : 809 ≤ r :=
            prime_ge_seven_hundred_ninety_eight_ge_eight_hundred_nine hr
              (Nat.succ_le_of_lt h798)
          exact (five_sigma_lt_six_usigma_seven_fourth_thirty_seven_large hr
            hr809 (lt_of_lt_of_le (by decide : (0 : ℕ) < 2) hk37)
            ((Nat.zero_lt_succ 1).trans_le hkr)).ne heq

lemma prime_ge_six_hundred_twenty_ge_six_hundred_thirty_one {p : ℕ} (hp : p.Prime)
    (h : 620 ≤ p) : 631 ≤ p := by
  have hmem : p = 620 ∨ p = 621 ∨ p = 622 ∨ p = 623 ∨ p = 624 ∨ p = 625 ∨
      p = 626 ∨ p = 627 ∨ p = 628 ∨ p = 629 ∨ p = 630 ∨ 631 ≤ p := by omega
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | h631
  · exact False.elim (not_prime_of_eq_mul (rfl : 620 = 2 * 310)
      (by decide : (2 : ℕ) ≠ 1) (by decide : (310 : ℕ) ≠ 1) hp)
  · exact False.elim (not_prime_of_eq_mul (rfl : 621 = 3 * 207)
      (by decide : (3 : ℕ) ≠ 1) (by decide : (207 : ℕ) ≠ 1) hp)
  · exact False.elim (not_prime_of_eq_mul (rfl : 622 = 2 * 311)
      (by decide : (2 : ℕ) ≠ 1) (by decide : (311 : ℕ) ≠ 1) hp)
  · exact False.elim (not_prime_of_eq_mul (rfl : 623 = 7 * 89)
      (by decide : (7 : ℕ) ≠ 1) (by decide : (89 : ℕ) ≠ 1) hp)
  · exact False.elim (not_prime_of_eq_mul (rfl : 624 = 2 * 312)
      (by decide : (2 : ℕ) ≠ 1) (by decide : (312 : ℕ) ≠ 1) hp)
  · exact False.elim (not_prime_of_eq_mul (rfl : 625 = 5 * 125)
      (by decide : (5 : ℕ) ≠ 1) (by decide : (125 : ℕ) ≠ 1) hp)
  · exact False.elim (not_prime_of_eq_mul (rfl : 626 = 2 * 313)
      (by decide : (2 : ℕ) ≠ 1) (by decide : (313 : ℕ) ≠ 1) hp)
  · exact False.elim (not_prime_of_eq_mul (rfl : 627 = 3 * 209)
      (by decide : (3 : ℕ) ≠ 1) (by decide : (209 : ℕ) ≠ 1) hp)
  · exact False.elim (not_prime_of_eq_mul (rfl : 628 = 2 * 314)
      (by decide : (2 : ℕ) ≠ 1) (by decide : (314 : ℕ) ≠ 1) hp)
  · exact False.elim (not_prime_of_eq_mul (rfl : 629 = 17 * 37)
      (by decide : (17 : ℕ) ≠ 1) (by decide : (37 : ℕ) ≠ 1) hp)
  · exact False.elim (not_prime_of_eq_mul (rfl : 630 = 2 * 315)
      (by decide : (2 : ℕ) ≠ 1) (by decide : (315 : ℕ) ≠ 1) hp)
  · exact h631

lemma prime_ge_one_one_five_four_ge_one_one_six_three {p : ℕ} (hp : p.Prime)
    (h : 1154 ≤ p) : 1163 ≤ p := by
  have hmem : p = 1154 ∨ p = 1155 ∨ p = 1156 ∨ p = 1157 ∨ p = 1158 ∨
      p = 1159 ∨ p = 1160 ∨ p = 1161 ∨ p = 1162 ∨ 1163 ≤ p := by omega
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | h1163
  · exact False.elim (not_prime_of_eq_mul (rfl : 1154 = 2 * 577)
      (by decide : (2 : ℕ) ≠ 1) (by decide : (577 : ℕ) ≠ 1) hp)
  · exact False.elim (not_prime_of_eq_mul (rfl : 1155 = 3 * 385)
      (by decide : (3 : ℕ) ≠ 1) (by decide : (385 : ℕ) ≠ 1) hp)
  · exact False.elim (not_prime_of_eq_mul (rfl : 1156 = 2 * 578)
      (by decide : (2 : ℕ) ≠ 1) (by decide : (578 : ℕ) ≠ 1) hp)
  · exact False.elim (not_prime_of_eq_mul (rfl : 1157 = 13 * 89)
      (by decide : (13 : ℕ) ≠ 1) (by decide : (89 : ℕ) ≠ 1) hp)
  · exact False.elim (not_prime_of_eq_mul (rfl : 1158 = 2 * 579)
      (by decide : (2 : ℕ) ≠ 1) (by decide : (579 : ℕ) ≠ 1) hp)
  · exact False.elim (not_prime_of_eq_mul (rfl : 1159 = 19 * 61)
      (by decide : (19 : ℕ) ≠ 1) (by decide : (61 : ℕ) ≠ 1) hp)
  · exact False.elim (not_prime_of_eq_mul (rfl : 1160 = 2 * 580)
      (by decide : (2 : ℕ) ≠ 1) (by decide : (580 : ℕ) ≠ 1) hp)
  · exact False.elim (not_prime_of_eq_mul (rfl : 1161 = 3 * 387)
      (by decide : (3 : ℕ) ≠ 1) (by decide : (387 : ℕ) ≠ 1) hp)
  · exact False.elim (not_prime_of_eq_mul (rfl : 1162 = 2 * 581)
      (by decide : (2 : ℕ) ≠ 1) (by decide : (581 : ℕ) ≠ 1) hp)
  · exact h1163

lemma prime_ge_one_one_six_four_ge_one_one_seven_one {p : ℕ} (hp : p.Prime)
    (h : 1164 ≤ p) : 1171 ≤ p := by
  have hmem : p = 1164 ∨ p = 1165 ∨ p = 1166 ∨ p = 1167 ∨ p = 1168 ∨
      p = 1169 ∨ p = 1170 ∨ 1171 ≤ p := by omega
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl | rfl | h1171
  · exact False.elim (not_prime_of_eq_mul (rfl : 1164 = 2 * 582)
      (by decide : (2 : ℕ) ≠ 1) (by decide : (582 : ℕ) ≠ 1) hp)
  · exact False.elim (not_prime_of_eq_mul (rfl : 1165 = 5 * 233)
      (by decide : (5 : ℕ) ≠ 1) (by decide : (233 : ℕ) ≠ 1) hp)
  · exact False.elim (not_prime_of_eq_mul (rfl : 1166 = 2 * 583)
      (by decide : (2 : ℕ) ≠ 1) (by decide : (583 : ℕ) ≠ 1) hp)
  · exact False.elim (not_prime_of_eq_mul (rfl : 1167 = 3 * 389)
      (by decide : (3 : ℕ) ≠ 1) (by decide : (389 : ℕ) ≠ 1) hp)
  · exact False.elim (not_prime_of_eq_mul (rfl : 1168 = 2 * 584)
      (by decide : (2 : ℕ) ≠ 1) (by decide : (584 : ℕ) ≠ 1) hp)
  · exact False.elim (not_prime_of_eq_mul (rfl : 1169 = 7 * 167)
      (by decide : (7 : ℕ) ≠ 1) (by decide : (167 : ℕ) ≠ 1) hp)
  · exact False.elim (not_prime_of_eq_mul (rfl : 1170 = 2 * 585)
      (by decide : (2 : ℕ) ≠ 1) (by decide : (585 : ℕ) ≠ 1) hp)
  · exact h1171

lemma prime_ge_one_one_eight_eight_ge_one_one_nine_three {p : ℕ} (hp : p.Prime)
    (h : 1188 ≤ p) : 1193 ≤ p := by
  have hmem : p = 1188 ∨ p = 1189 ∨ p = 1190 ∨ p = 1191 ∨ p = 1192 ∨
      1193 ≤ p := by omega
  rcases hmem with rfl | rfl | rfl | rfl | rfl | h1193
  · exact False.elim (not_prime_of_eq_mul (rfl : 1188 = 2 * 594)
      (by decide : (2 : ℕ) ≠ 1) (by decide : (594 : ℕ) ≠ 1) hp)
  · exact False.elim (not_prime_of_eq_mul (rfl : 1189 = 29 * 41)
      (by decide : (29 : ℕ) ≠ 1) (by decide : (41 : ℕ) ≠ 1) hp)
  · exact False.elim (not_prime_of_eq_mul (rfl : 1190 = 2 * 595)
      (by decide : (2 : ℕ) ≠ 1) (by decide : (595 : ℕ) ≠ 1) hp)
  · exact False.elim (not_prime_of_eq_mul (rfl : 1191 = 3 * 397)
      (by decide : (3 : ℕ) ≠ 1) (by decide : (397 : ℕ) ≠ 1) hp)
  · exact False.elim (not_prime_of_eq_mul (rfl : 1192 = 2 * 596)
      (by decide : (2 : ℕ) ≠ 1) (by decide : (596 : ℕ) ≠ 1) hp)
  · exact h1193

lemma prime_one_one_six_three : Nat.Prime 1163 := by norm_num

lemma seven_pow_five_thirty_seven_sq_r_sq_overshoot_six_five {r : ℕ}
    (hr : r.Prime) (h211 : 211 ≤ r) (h619 : r ≤ 619) :
    6 * usigma (7 ^ 5) * usigma (37 ^ 2) * usigma (r ^ 2) <
      5 * σ 1 (7 ^ 5) * σ 1 (37 ^ 2) * σ 1 (r ^ 2) := by
  rw [usigma_seven_pow_five, sigma_seven_pow_five,
    sigma_thirty_seven_pow_two, usigma_thirty_seven_pow_two,
    sigma_prime_pow_two hr, usigma_prime_pow hr (by decide : 0 < 2)]
  have hsq : r ^ 2 ≤ 619 * r := by
    rw [pow_two]
    exact Nat.mul_le_mul_right r h619
  have hleft : 219480 * (1 + r ^ 2) < 137942280 * r := by
    have h1 : 219480 * (1 + r ^ 2) ≤ 219480 * (1 + 619 * r) :=
      Nat.mul_le_mul_left 219480 (Nat.add_le_add_left hsq 1)
    have h2 : 219480 * (1 + 619 * r) = 219480 + 135858120 * r := by
      have : 219480 * 619 = 135858120 := by norm_num
      ring
    have h3 : 219480 + 135858120 * r < 137942280 * r := by
      have : 219480 < 2084160 * r :=
        lt_of_lt_of_le (by decide : 219480 < 439757760)
          (Nat.mul_le_mul_left 2084160 h211)
      omega
    calc
      219480 * (1 + r ^ 2) ≤ 219480 * (1 + 619 * r) := h1
      _ = 219480 + 135858120 * r := h2
      _ < 137942280 * r := h3
  have hL : 6 * 16808 * 1370 * (1 + r ^ 2) = 138161760 * (1 + r ^ 2) := by ring
  have hR : 5 * 19608 * 1407 * (1 + r + r ^ 2) = 137942280 * (1 + r + r ^ 2) :=
    by ring
  have hmain : 138161760 * (1 + r ^ 2) < 137942280 * (1 + r + r ^ 2) := by
    have h1 : 138161760 * (1 + r ^ 2) =
        137942280 * (1 + r ^ 2) + 219480 * (1 + r ^ 2) := by ring
    have h2 : 137942280 * (1 + r + r ^ 2) =
        137942280 * (1 + r ^ 2) + 137942280 * r := by ring
    rw [h1, h2]
    exact Nat.add_lt_add_left hleft _
  rw [hL, hR]
  exact hmain

lemma seven_pow_five_thirty_seven_r_sq_pow_ge_two_overshoot_six_five
    {r a b c : ℕ} (hr : r.Prime) (h211 : 211 ≤ r) (h619 : r ≤ 619)
    (ha : 5 ≤ a) (hb : 2 ≤ b) (hc : 2 ≤ c) :
    6 * usigma (7 ^ a) * usigma (37 ^ b) * usigma (r ^ c) <
      5 * σ 1 (7 ^ a) * σ 1 (37 ^ b) * σ 1 (r ^ c) :=
  six_five_overshoot_mono_three (by decide : Nat.Prime 7)
    (by decide : Nat.Prime 37) hr
    (by decide : 0 < 5) (by decide : 0 < 2) (by decide : 0 < 2)
    ha hb hc (seven_pow_five_thirty_seven_sq_r_sq_overshoot_six_five hr h211 h619)

lemma five_mul_seven_pow_five_thirty_seven_sq_cap {r : ℕ} (hr : 631 ≤ r) :
    5 * r * 19608 * 1407 ≤ 6 * (r - 1) * 16808 * 1370 := by
  have hdiff : 138161760 ≤ 219480 * r := by
    have hmul : 219480 * 631 ≤ 219480 * r := Nat.mul_le_mul_left 219480 hr
    have hnum : 219480 * 631 = 138491880 := by norm_num
    omega
  have hL : 5 * r * 19608 * 1407 = 137942280 * r := by ring
  have hR : 6 * (r - 1) * 16808 * 1370 = 138161760 * (r - 1) := by ring
  have hmain : 137942280 * r ≤ 138161760 * (r - 1) := by
    have heq : 137942280 * r + 219480 * r = 138161760 * r := by ring
    have hsub : 137942280 * r = 138161760 * r - 219480 * r :=
      (Nat.sub_eq_of_eq_add heq.symm).symm
    have hle : 138161760 * r - 219480 * r ≤ 138161760 * r - 138161760 :=
      Nat.sub_le_sub_left hdiff _
    have hrw : 138161760 * r - 138161760 = 138161760 * (r - 1) := by
      simpa using (Nat.mul_sub_left_distrib 138161760 r 1).symm
    calc
      137942280 * r = 138161760 * r - 219480 * r := hsub
      _ ≤ 138161760 * r - 138161760 := hle
      _ = 138161760 * (r - 1) := hrw
  rw [hL, hR]
  exact hmain

lemma five_sigma_lt_six_usigma_seven_pow_five_thirty_seven_sq_large {r k : ℕ}
    (hr : r.Prime) (hr631 : 631 ≤ r) (hk : 0 < k) :
    5 * σ 1 (7 ^ 5) * σ 1 (37 ^ 2) * σ 1 (r ^ k) <
      6 * usigma (7 ^ 5) * usigma (37 ^ 2) * usigma (r ^ k) := by
  rw [sigma_seven_pow_five, usigma_seven_pow_five,
    sigma_thirty_seven_pow_two, usigma_thirty_seven_pow_two]
  have hcp := sigma_lt_cap_usigma hr hk
  have hT : 0 < 19608 * 1407 :=
    Nat.mul_pos (by decide : 0 < 19608) (by decide : 0 < 1407)
  have hthis := six_five_of_cap_times_const (A := r - 1) (B := r)
    (X := σ 1 (r ^ k)) (Y := usigma (r ^ k)) (S := 16808 * 1370)
    (T := 19608 * 1407) hcp (by
      have hL : 5 * r * (19608 * 1407) = 5 * r * 19608 * 1407 := by ring
      have hR : 6 * (r - 1) * (16808 * 1370) = 6 * (r - 1) * 16808 * 1370 :=
        by ring
      rw [hL, hR]
      exact five_mul_seven_pow_five_thirty_seven_sq_cap hr631)
    hT
  convert hthis using 1 <;> ring

lemma seven_pow_five_thirty_seven_cube_r_sq_overshoot_six_five {r : ℕ}
    (hr : r.Prime) (h211 : 211 ≤ r) (h1153 : r ≤ 1153) :
    6 * usigma (7 ^ 5) * usigma (37 ^ 3) * usigma (r ^ 2) <
      5 * σ 1 (7 ^ 5) * σ 1 (37 ^ 3) * σ 1 (r ^ 2) := by
  rw [usigma_seven_pow_five, sigma_seven_pow_five,
    sigma_thirty_seven_pow_three, usigma_thirty_seven_pow_three,
    sigma_prime_pow_two hr, usigma_prime_pow hr (by decide : 0 < 2)]
  have hsq : r ^ 2 ≤ 1153 * r := by
    rw [pow_two]
    exact Nat.mul_le_mul_right r h1153
  have hleft : 4392192 * (1 + r ^ 2) < 5103962400 * r := by
    have h1 : 4392192 * (1 + r ^ 2) ≤ 4392192 * (1 + 1153 * r) :=
      Nat.mul_le_mul_left 4392192 (Nat.add_le_add_left hsq 1)
    have h2 : 4392192 * (1 + 1153 * r) = 4392192 + 5064197376 * r := by
      have : 4392192 * 1153 = 5064197376 := by norm_num
      ring
    have h3 : 4392192 + 5064197376 * r < 5103962400 * r := by
      have : 4392192 < 39765024 * r :=
        lt_of_lt_of_le (by norm_num : 4392192 < 8390420064)
          (Nat.mul_le_mul_left 39765024 h211)
      omega
    calc
      4392192 * (1 + r ^ 2) ≤ 4392192 * (1 + 1153 * r) := h1
      _ = 4392192 + 5064197376 * r := h2
      _ < 5103962400 * r := h3
  have hL : 6 * 16808 * 50654 * (1 + r ^ 2) = 5108354592 * (1 + r ^ 2) :=
    by ring
  have hR : 5 * 19608 * 52060 * (1 + r + r ^ 2) = 5103962400 * (1 + r + r ^ 2) :=
    by ring
  have hmain : 5108354592 * (1 + r ^ 2) < 5103962400 * (1 + r + r ^ 2) := by
    have h1 : 5108354592 * (1 + r ^ 2) =
        5103962400 * (1 + r ^ 2) + 4392192 * (1 + r ^ 2) := by ring
    have h2 : 5103962400 * (1 + r + r ^ 2) =
        5103962400 * (1 + r ^ 2) + 5103962400 * r := by ring
    rw [h1, h2]
    exact Nat.add_lt_add_left hleft _
  rw [hL, hR]
  exact hmain

lemma seven_pow_five_thirty_seven_cube_r_pow_ge_two_overshoot_six_five
    {r a b c : ℕ} (hr : r.Prime) (h211 : 211 ≤ r) (h1153 : r ≤ 1153)
    (ha : 5 ≤ a) (hb : 3 ≤ b) (hc : 2 ≤ c) :
    6 * usigma (7 ^ a) * usigma (37 ^ b) * usigma (r ^ c) <
      5 * σ 1 (7 ^ a) * σ 1 (37 ^ b) * σ 1 (r ^ c) :=
  six_five_overshoot_mono_three (by decide : Nat.Prime 7)
    (by decide : Nat.Prime 37) hr
    (by decide : 0 < 5) (by decide : 0 < 3) (by decide : 0 < 2)
    ha hb hc
    (seven_pow_five_thirty_seven_cube_r_sq_overshoot_six_five hr h211 h1153)

lemma five_mul_seven_pow_five_thirty_seven_cube_cap {r : ℕ} (hr : 1171 ≤ r) :
    5 * r * 19608 * 52060 ≤ 6 * (r - 1) * 16808 * 50654 := by
  have hdiff : 5108354592 ≤ 4392192 * r := by
    have hmul : 4392192 * 1171 ≤ 4392192 * r := Nat.mul_le_mul_left 4392192 hr
    have hnum : 4392192 * 1171 = 5143256832 := by norm_num
    omega
  have hL : 5 * r * 19608 * 52060 = 5103962400 * r := by ring
  have hR : 6 * (r - 1) * 16808 * 50654 = 5108354592 * (r - 1) := by ring
  have hmain : 5103962400 * r ≤ 5108354592 * (r - 1) := by
    have heq : 5103962400 * r + 4392192 * r = 5108354592 * r := by ring
    have hsub : 5103962400 * r = 5108354592 * r - 4392192 * r :=
      (Nat.sub_eq_of_eq_add heq.symm).symm
    have hle : 5108354592 * r - 4392192 * r ≤ 5108354592 * r - 5108354592 :=
      Nat.sub_le_sub_left hdiff _
    have hrw : 5108354592 * r - 5108354592 = 5108354592 * (r - 1) := by
      simpa using (Nat.mul_sub_left_distrib 5108354592 r 1).symm
    calc
      5103962400 * r = 5108354592 * r - 4392192 * r := hsub
      _ ≤ 5108354592 * r - 5108354592 := hle
      _ = 5108354592 * (r - 1) := hrw
  rw [hL, hR]
  exact hmain

lemma five_sigma_lt_six_usigma_seven_pow_five_thirty_seven_cube_large {r k : ℕ}
    (hr : r.Prime) (hr1171 : 1171 ≤ r) (hk : 0 < k) :
    5 * σ 1 (7 ^ 5) * σ 1 (37 ^ 3) * σ 1 (r ^ k) <
      6 * usigma (7 ^ 5) * usigma (37 ^ 3) * usigma (r ^ k) := by
  rw [sigma_seven_pow_five, usigma_seven_pow_five,
    sigma_thirty_seven_pow_three, usigma_thirty_seven_pow_three]
  have hcp := sigma_lt_cap_usigma hr hk
  have hT : 0 < 19608 * 52060 :=
    Nat.mul_pos (by decide : 0 < 19608) (by decide : 0 < 52060)
  have hthis := six_five_of_cap_times_const (A := r - 1) (B := r)
    (X := σ 1 (r ^ k)) (Y := usigma (r ^ k)) (S := 16808 * 50654)
    (T := 19608 * 52060) hcp (by
      have hL : 5 * r * (19608 * 52060) = 5 * r * 19608 * 52060 := by ring
      have hR : 6 * (r - 1) * (16808 * 50654) = 6 * (r - 1) * 16808 * 50654 :=
        by ring
      rw [hL, hR]
      exact five_mul_seven_pow_five_thirty_seven_cube_cap hr1171)
    hT
  convert hthis using 1 <;> ring

lemma seven_pow_five_thirty_seven_fourth_r_sq_overshoot_six_five {r : ℕ}
    (hr : r.Prime) (h211 : 211 ≤ r) (h1187 : r ≤ 1187) :
    6 * usigma (7 ^ 5) * usigma (37 ^ 4) * usigma (r ^ 2) <
      5 * σ 1 (7 ^ 5) * σ 1 (37 ^ 4) * σ 1 (r ^ 2) := by
  rw [usigma_seven_pow_five, sigma_seven_pow_five,
    sigma_thirty_seven_pow_four, usigma_thirty_seven_pow_four,
    sigma_prime_pow_two hr, usigma_prime_pow hr (by decide : 0 < 2)]
  have hsq : r ^ 2 ≤ 1187 * r := by
    rw [pow_two]
    exact Nat.mul_le_mul_right r h1187
  have hleft : 158782536 * (1 + r ^ 2) < 188846706840 * r := by
    have h1 : 158782536 * (1 + r ^ 2) ≤ 158782536 * (1 + 1187 * r) :=
      Nat.mul_le_mul_left 158782536 (Nat.add_le_add_left hsq 1)
    have h2 : 158782536 * (1 + 1187 * r) = 158782536 + 188474870232 * r := by
      have : 158782536 * 1187 = 188474870232 := by norm_num
      ring
    have h3 : 158782536 + 188474870232 * r < 188846706840 * r := by
      have : 158782536 < 371836608 * r :=
        lt_of_lt_of_le (by norm_num : 158782536 < 78457524288)
          (Nat.mul_le_mul_left 371836608 h211)
      omega
    calc
      158782536 * (1 + r ^ 2) ≤ 158782536 * (1 + 1187 * r) := h1
      _ = 158782536 + 188474870232 * r := h2
      _ < 188846706840 * r := h3
  have hL : 6 * 16808 * 1874162 * (1 + r ^ 2) =
      189005489376 * (1 + r ^ 2) := by ring
  have hR : 5 * 19608 * 1926221 * (1 + r + r ^ 2) =
      188846706840 * (1 + r + r ^ 2) := by ring
  have hmain : 189005489376 * (1 + r ^ 2) < 188846706840 * (1 + r + r ^ 2) := by
    have h1 : 189005489376 * (1 + r ^ 2) =
        188846706840 * (1 + r ^ 2) + 158782536 * (1 + r ^ 2) := by ring
    have h2 : 188846706840 * (1 + r + r ^ 2) =
        188846706840 * (1 + r ^ 2) + 188846706840 * r := by ring
    rw [h1, h2]
    exact Nat.add_lt_add_left hleft _
  rw [hL, hR]
  exact hmain

lemma seven_pow_five_thirty_seven_fourth_r_pow_ge_two_overshoot_six_five
    {r a b c : ℕ} (hr : r.Prime) (h211 : 211 ≤ r) (h1187 : r ≤ 1187)
    (ha : 5 ≤ a) (hb : 4 ≤ b) (hc : 2 ≤ c) :
    6 * usigma (7 ^ a) * usigma (37 ^ b) * usigma (r ^ c) <
      5 * σ 1 (7 ^ a) * σ 1 (37 ^ b) * σ 1 (r ^ c) :=
  six_five_overshoot_mono_three (by decide : Nat.Prime 7)
    (by decide : Nat.Prime 37) hr
    (by decide : 0 < 5) (by decide : 0 < 4) (by decide : 0 < 2)
    ha hb hc
    (seven_pow_five_thirty_seven_fourth_r_sq_overshoot_six_five hr h211 h1187)

lemma five_mul_seven_pow_five_thirty_seven_euler_cap {r : ℕ} (hr : 1193 ≤ r) :
    5 * 37 * r * 19608 ≤ 6 * 36 * (r - 1) * 16808 := by
  have hdiff : 3630528 ≤ 3048 * r := by
    have hmul : 3048 * 1193 ≤ 3048 * r := Nat.mul_le_mul_left 3048 hr
    have hnum : 3048 * 1193 = 3636264 := by decide
    omega
  have hL : 5 * 37 * r * 19608 = 3627480 * r := by ring
  have hR : 6 * 36 * (r - 1) * 16808 = 3630528 * (r - 1) := by ring
  have hmain : 3627480 * r ≤ 3630528 * (r - 1) := by
    have heq : 3627480 * r + 3048 * r = 3630528 * r := by ring
    have hsub : 3627480 * r = 3630528 * r - 3048 * r :=
      (Nat.sub_eq_of_eq_add heq.symm).symm
    have hle : 3630528 * r - 3048 * r ≤ 3630528 * r - 3630528 :=
      Nat.sub_le_sub_left hdiff _
    have hrw : 3630528 * r - 3630528 = 3630528 * (r - 1) := by
      simpa using (Nat.mul_sub_left_distrib 3630528 r 1).symm
    calc
      3627480 * r = 3630528 * r - 3048 * r := hsub
      _ ≤ 3630528 * r - 3630528 := hle
      _ = 3630528 * (r - 1) := hrw
  rw [hL, hR]
  exact hmain

lemma five_sigma_lt_six_usigma_seven_pow_five_thirty_seven_large {r b c : ℕ}
    (hr : r.Prime) (hr1193 : 1193 ≤ r) (hb : 0 < b) (hc : 0 < c) :
    5 * σ 1 (7 ^ 5) * σ 1 (37 ^ b) * σ 1 (r ^ c) <
      6 * usigma (7 ^ 5) * usigma (37 ^ b) * usigma (r ^ c) := by
  rw [sigma_seven_pow_five, usigma_seven_pow_five]
  have h37 := sigma_lt_cap_usigma (by decide : Nat.Prime 37) hb
  have hrcap := sigma_lt_cap_usigma hr hc
  have hu37 : 0 < usigma (37 ^ b) := by
    rw [usigma_prime_pow (by decide : Nat.Prime 37) hb]
    exact Nat.add_pos_left (by decide : 0 < 1) _
  have hthis := six_five_of_two_caps_times_const (A := 36) (B := 37)
    (X := σ 1 (37 ^ b)) (Y := usigma (37 ^ b)) (C := r - 1) (D := r)
    (P := σ 1 (r ^ c)) (Q := usigma (r ^ c)) (S := 16808) (T := 19608)
    h37 hrcap (five_mul_seven_pow_five_thirty_seven_euler_cap hr1193)
    (by decide : 0 < 37) hu37 (by decide : 0 < 19608)
  convert hthis using 1 <;> ring

lemma five_sigma_lt_six_usigma_seven_pow_five_thirty_seven_cube_one_one_six_three_sq :
    5 * σ 1 (7 ^ 5) * σ 1 (37 ^ 3) * σ 1 (1163 ^ 2) <
      6 * usigma (7 ^ 5) * usigma (37 ^ 3) * usigma (1163 ^ 2) := by
  rw [sigma_seven_pow_five, usigma_seven_pow_five,
    sigma_thirty_seven_pow_three, usigma_thirty_seven_pow_three,
    sigma_prime_pow_two prime_one_one_six_three,
    usigma_prime_pow prime_one_one_six_three (by decide : 0 < 2)]
  norm_num

lemma seven_pow_five_thirty_seven_cube_one_one_six_three_cube_overshoot :
    6 * usigma (7 ^ 5) * usigma (37 ^ 3) * usigma (1163 ^ 3) <
      5 * σ 1 (7 ^ 5) * σ 1 (37 ^ 3) * σ 1 (1163 ^ 3) := by
  rw [usigma_seven_pow_five, sigma_seven_pow_five,
    usigma_thirty_seven_pow_three, sigma_thirty_seven_pow_three,
    usigma_prime_pow prime_one_one_six_three (by decide : 0 < 3),
    sigma_prime_pow_div prime_one_one_six_three]
  norm_num

/-- Leftover `6/5` cannot be three squareful primes `7,37,1163` with
`v₇ = 5` times a squarefree coprime factor. -/
lemma not_five_sigma_of_three_sq_primes_seven_thirty_seven_one_one_six_three
    {m : ℕ} (hm : m ≠ 0) (h : 5 * σ 1 m = 6 * usigma m)
    (hk7 : padicValNat 7 m = 5) (hk37 : 2 ≤ padicValNat 37 m)
    (hkr : 2 ≤ padicValNat 1163 m)
    (hs : Squarefree (ordCompl[1163] (ordCompl[37] (ordCompl[7] m)))) :
    False := by
  have hp7 : Nat.Prime 7 := by decide
  have hp37 : Nat.Prime 37 := by decide
  have hp1163 : Nat.Prime 1163 := prime_one_one_six_three
  have hpq_ne : (7 : ℕ) ≠ 37 := by decide
  have hpr_ne : (7 : ℕ) ≠ 1163 := by decide
  have hqr_ne : (37 : ℕ) ≠ 1163 := by decide
  have heq := five_sigma_eq_six_of_three_squareful hm hp7 hp37 hp1163 hpq_ne
    hpr_ne hqr_ne h hs
  have hproj_p : ordProj[7] m = 7 ^ padicValNat 7 m := by
    simp [Nat.factorization_def m hp7]
  have hproj_q : ordProj[37] (ordCompl[7] m) =
      37 ^ padicValNat 37 (ordCompl[7] m) := by
    simp [Nat.factorization_def (ordCompl[7] m) hp37]
  have hproj_r : ordProj[1163] (ordCompl[37] (ordCompl[7] m)) =
      1163 ^ padicValNat 1163 (ordCompl[37] (ordCompl[7] m)) := by
    simp [Nat.factorization_def (ordCompl[37] (ordCompl[7] m)) hp1163]
  rw [hproj_r, padicValNat_ordCompl_of_ne hp1163 hqr_ne,
    padicValNat_ordCompl_of_ne hp1163 hpr_ne, hproj_q,
    padicValNat_ordCompl_of_ne hp37 hpq_ne, hproj_p, hk7] at heq
  rcases eq_or_lt_of_le hk37 with h37eq | h373
  · rw [← h37eq] at heq
    exact (five_sigma_lt_six_usigma_seven_pow_five_thirty_seven_sq_large
      hp1163 (by decide : 631 ≤ 1163)
      ((Nat.zero_lt_succ 1).trans_le hkr)).ne heq
  · have h3le : 3 ≤ padicValNat 37 m := Nat.succ_le_of_lt h373
    rcases eq_or_lt_of_le h3le with h37eq3 | h374
    · have h37eq : padicValNat 37 m = 3 := h37eq3.symm
      rw [h37eq] at heq
      rcases eq_or_lt_of_le hkr with hreq | hr3
      · rw [← hreq] at heq
        exact
          five_sigma_lt_six_usigma_seven_pow_five_thirty_seven_cube_one_one_six_three_sq.ne
            heq
      · have hover := six_five_overshoot_mono_three hp7 hp37 hp1163
          (by decide : 0 < 5) (by decide : 0 < 3) (by decide : 0 < 3)
          (le_refl _) (le_refl _) (Nat.succ_le_of_lt hr3)
          seven_pow_five_thirty_seven_cube_one_one_six_three_cube_overshoot
        rw [← heq] at hover
        exact lt_irrefl _ hover
    · have hover :=
        seven_pow_five_thirty_seven_fourth_r_pow_ge_two_overshoot_six_five
          hp1163 (by decide : 211 ≤ 1163) (by decide : 1163 ≤ 1187)
          (le_refl _) (Nat.succ_le_of_lt h374) hkr
      rw [← heq] at hover
      exact lt_irrefl _ hover

/-- Leftover `6/5` cannot be three squareful primes `7,37,r` with `r ≥ 211`
and `v₇ = 5` times a squarefree coprime factor. -/
lemma not_five_sigma_of_three_sq_primes_seven_thirty_seven_of_val_seven_eq_five
    {m r : ℕ} (hm : m ≠ 0) (hr : r.Prime) (hr211 : 211 ≤ r)
    (h : 5 * σ 1 m = 6 * usigma m)
    (hk7 : padicValNat 7 m = 5) (hk37 : 2 ≤ padicValNat 37 m)
    (hkr : 2 ≤ padicValNat r m)
    (hs : Squarefree (ordCompl[r] (ordCompl[37] (ordCompl[7] m)))) :
    False := by
  have hp7 : Nat.Prime 7 := by decide
  have hp37 : Nat.Prime 37 := by decide
  have hpq_ne : (7 : ℕ) ≠ 37 := by decide
  have hpr_ne : (7 : ℕ) ≠ r :=
    Nat.ne_of_lt (lt_of_lt_of_le (by decide : 7 < 211) hr211)
  have hqr_ne : (37 : ℕ) ≠ r :=
    Nat.ne_of_lt (lt_of_lt_of_le (by decide : 37 < 211) hr211)
  have heq := five_sigma_eq_six_of_three_squareful hm hp7 hp37 hr hpq_ne hpr_ne
    hqr_ne h hs
  have hproj_p : ordProj[7] m = 7 ^ padicValNat 7 m := by
    simp [Nat.factorization_def m hp7]
  have hproj_q : ordProj[37] (ordCompl[7] m) =
      37 ^ padicValNat 37 (ordCompl[7] m) := by
    simp [Nat.factorization_def (ordCompl[7] m) hp37]
  have hproj_r : ordProj[r] (ordCompl[37] (ordCompl[7] m)) =
      r ^ padicValNat r (ordCompl[37] (ordCompl[7] m)) := by
    simp [Nat.factorization_def (ordCompl[37] (ordCompl[7] m)) hr]
  rw [hproj_r, padicValNat_ordCompl_of_ne hr hqr_ne,
    padicValNat_ordCompl_of_ne hr hpr_ne, hproj_q,
    padicValNat_ordCompl_of_ne hp37 hpq_ne, hproj_p, hk7] at heq
  rcases eq_or_lt_of_le hk37 with h37eq | h373
  · rw [← h37eq] at heq
    rcases le_or_gt r 619 with h619 | h620
    · have hover := seven_pow_five_thirty_seven_r_sq_pow_ge_two_overshoot_six_five
        hr hr211 h619 (le_refl _) (le_refl _) hkr
      rw [← heq] at hover
      exact lt_irrefl _ hover
    · have hr631 : 631 ≤ r :=
        prime_ge_six_hundred_twenty_ge_six_hundred_thirty_one hr
          (Nat.succ_le_of_lt h620)
      exact (five_sigma_lt_six_usigma_seven_pow_five_thirty_seven_sq_large hr
        hr631 ((Nat.zero_lt_succ 1).trans_le hkr)).ne heq
  · rcases le_or_gt r 1153 with h1153 | h1154
    · have hover := seven_pow_five_thirty_seven_cube_r_pow_ge_two_overshoot_six_five
        hr hr211 h1153 (le_refl _) (Nat.succ_le_of_lt h373) hkr
      rw [← heq] at hover
      exact lt_irrefl _ hover
    · have hr1163 : 1163 ≤ r :=
        prime_ge_one_one_five_four_ge_one_one_six_three hr
          (Nat.succ_le_of_lt h1154)
      rcases le_or_gt r 1163 with h1163 | h1164
      · have hr1163eq : r = 1163 := le_antisymm h1163 hr1163
        subst r
        exact not_five_sigma_of_three_sq_primes_seven_thirty_seven_one_one_six_three
          hm h hk7 hk37 hkr hs
      · have hr1171 : 1171 ≤ r :=
          prime_ge_one_one_six_four_ge_one_one_seven_one hr
            (Nat.succ_le_of_lt h1164)
        rcases eq_or_lt_of_le (Nat.succ_le_of_lt h373) with h37eq3 | h374
        · have h37eq : padicValNat 37 m = 3 := h37eq3.symm
          rw [h37eq] at heq
          exact (five_sigma_lt_six_usigma_seven_pow_five_thirty_seven_cube_large
            hr hr1171 ((Nat.zero_lt_succ 1).trans_le hkr)).ne heq
        · rcases le_or_gt r 1187 with h1187 | h1188
          · have hover :=
              seven_pow_five_thirty_seven_fourth_r_pow_ge_two_overshoot_six_five
                hr hr211 h1187 (le_refl _) (Nat.succ_le_of_lt h374) hkr
            rw [← heq] at hover
            exact lt_irrefl _ hover
          · have hr1193 : 1193 ≤ r :=
              prime_ge_one_one_eight_eight_ge_one_one_nine_three hr
                (Nat.succ_le_of_lt h1188)
            exact (five_sigma_lt_six_usigma_seven_pow_five_thirty_seven_large hr
              hr1193 (lt_of_lt_of_le (by decide : (0 : ℕ) < 2) hk37)
              ((Nat.zero_lt_succ 1).trans_le hkr)).ne heq

lemma prime_ge_six_hundred_forty_eight_ge_six_hundred_fifty_three {p : ℕ}
    (hp : p.Prime) (h : 648 ≤ p) : 653 ≤ p := by
  have hmem : p = 648 ∨ p = 649 ∨ p = 650 ∨ p = 651 ∨ p = 652 ∨
      653 ≤ p := by omega
  rcases hmem with rfl | rfl | rfl | rfl | rfl | h653
  · exact False.elim (not_prime_of_eq_mul (rfl : 648 = 2 * 324)
      (by decide : (2 : ℕ) ≠ 1) (by decide : (324 : ℕ) ≠ 1) hp)
  · exact False.elim (not_prime_of_eq_mul (rfl : 649 = 11 * 59)
      (by decide : (11 : ℕ) ≠ 1) (by decide : (59 : ℕ) ≠ 1) hp)
  · exact False.elim (not_prime_of_eq_mul (rfl : 650 = 2 * 325)
      (by decide : (2 : ℕ) ≠ 1) (by decide : (325 : ℕ) ≠ 1) hp)
  · exact False.elim (not_prime_of_eq_mul (rfl : 651 = 3 * 217)
      (by decide : (3 : ℕ) ≠ 1) (by decide : (217 : ℕ) ≠ 1) hp)
  · exact False.elim (not_prime_of_eq_mul (rfl : 652 = 2 * 326)
      (by decide : (2 : ℕ) ≠ 1) (by decide : (326 : ℕ) ≠ 1) hp)
  · exact h653

lemma prime_ge_six_hundred_fifty_four_ge_six_hundred_fifty_nine {p : ℕ}
    (hp : p.Prime) (h : 654 ≤ p) : 659 ≤ p := by
  have hmem : p = 654 ∨ p = 655 ∨ p = 656 ∨ p = 657 ∨ p = 658 ∨
      659 ≤ p := by omega
  rcases hmem with rfl | rfl | rfl | rfl | rfl | h659
  · exact False.elim (not_prime_of_eq_mul (rfl : 654 = 2 * 327)
      (by decide : (2 : ℕ) ≠ 1) (by decide : (327 : ℕ) ≠ 1) hp)
  · exact False.elim (not_prime_of_eq_mul (rfl : 655 = 5 * 131)
      (by decide : (5 : ℕ) ≠ 1) (by decide : (131 : ℕ) ≠ 1) hp)
  · exact False.elim (not_prime_of_eq_mul (rfl : 656 = 2 * 328)
      (by decide : (2 : ℕ) ≠ 1) (by decide : (328 : ℕ) ≠ 1) hp)
  · exact False.elim (not_prime_of_eq_mul (rfl : 657 = 3 * 219)
      (by decide : (3 : ℕ) ≠ 1) (by decide : (219 : ℕ) ≠ 1) hp)
  · exact False.elim (not_prime_of_eq_mul (rfl : 658 = 2 * 329)
      (by decide : (2 : ℕ) ≠ 1) (by decide : (329 : ℕ) ≠ 1) hp)
  · exact h659

lemma prime_ge_one_two_three_eight_ge_one_two_four_nine {p : ℕ} (hp : p.Prime)
    (h : 1238 ≤ p) : 1249 ≤ p := by
  have hmem : p = 1238 ∨ p = 1239 ∨ p = 1240 ∨ p = 1241 ∨ p = 1242 ∨
      p = 1243 ∨ p = 1244 ∨ p = 1245 ∨ p = 1246 ∨ p = 1247 ∨ p = 1248 ∨
      1249 ≤ p := by omega
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | h1249
  · exact False.elim (not_prime_of_eq_mul (rfl : 1238 = 2 * 619)
      (by decide : (2 : ℕ) ≠ 1) (by decide : (619 : ℕ) ≠ 1) hp)
  · exact False.elim (not_prime_of_eq_mul (rfl : 1239 = 3 * 413)
      (by decide : (3 : ℕ) ≠ 1) (by decide : (413 : ℕ) ≠ 1) hp)
  · exact False.elim (not_prime_of_eq_mul (rfl : 1240 = 2 * 620)
      (by decide : (2 : ℕ) ≠ 1) (by decide : (620 : ℕ) ≠ 1) hp)
  · exact False.elim (not_prime_of_eq_mul (rfl : 1241 = 17 * 73)
      (by decide : (17 : ℕ) ≠ 1) (by decide : (73 : ℕ) ≠ 1) hp)
  · exact False.elim (not_prime_of_eq_mul (rfl : 1242 = 2 * 621)
      (by decide : (2 : ℕ) ≠ 1) (by decide : (621 : ℕ) ≠ 1) hp)
  · exact False.elim (not_prime_of_eq_mul (rfl : 1243 = 11 * 113)
      (by decide : (11 : ℕ) ≠ 1) (by decide : (113 : ℕ) ≠ 1) hp)
  · exact False.elim (not_prime_of_eq_mul (rfl : 1244 = 2 * 622)
      (by decide : (2 : ℕ) ≠ 1) (by decide : (622 : ℕ) ≠ 1) hp)
  · exact False.elim (not_prime_of_eq_mul (rfl : 1245 = 3 * 415)
      (by decide : (3 : ℕ) ≠ 1) (by decide : (415 : ℕ) ≠ 1) hp)
  · exact False.elim (not_prime_of_eq_mul (rfl : 1246 = 2 * 623)
      (by decide : (2 : ℕ) ≠ 1) (by decide : (623 : ℕ) ≠ 1) hp)
  · exact False.elim (not_prime_of_eq_mul (rfl : 1247 = 29 * 43)
      (by decide : (29 : ℕ) ≠ 1) (by decide : (43 : ℕ) ≠ 1) hp)
  · exact False.elim (not_prime_of_eq_mul (rfl : 1248 = 2 * 624)
      (by decide : (2 : ℕ) ≠ 1) (by decide : (624 : ℕ) ≠ 1) hp)
  · exact h1249

lemma prime_ge_one_two_seven_eight_ge_one_two_seven_nine {p : ℕ} (hp : p.Prime)
    (h : 1278 ≤ p) : 1279 ≤ p := by
  have hmem : p = 1278 ∨ 1279 ≤ p := by omega
  rcases hmem with rfl | h1279
  · exact False.elim (not_prime_of_eq_mul (rfl : 1278 = 2 * 639)
      (by decide : (2 : ℕ) ≠ 1) (by decide : (639 : ℕ) ≠ 1) hp)
  · exact h1279

lemma prime_ge_one_two_eight_zero_ge_one_two_eight_three {p : ℕ} (hp : p.Prime)
    (h : 1280 ≤ p) : 1283 ≤ p := by
  have hmem : p = 1280 ∨ p = 1281 ∨ p = 1282 ∨ 1283 ≤ p := by omega
  rcases hmem with rfl | rfl | rfl | h1283
  · exact False.elim (not_prime_of_eq_mul (rfl : 1280 = 2 * 640)
      (by decide : (2 : ℕ) ≠ 1) (by decide : (640 : ℕ) ≠ 1) hp)
  · exact False.elim (not_prime_of_eq_mul (rfl : 1281 = 3 * 427)
      (by decide : (3 : ℕ) ≠ 1) (by decide : (427 : ℕ) ≠ 1) hp)
  · exact False.elim (not_prime_of_eq_mul (rfl : 1282 = 2 * 641)
      (by decide : (2 : ℕ) ≠ 1) (by decide : (641 : ℕ) ≠ 1) hp)
  · exact h1283

lemma prime_six_fifty_three : Nat.Prime 653 := by norm_num

lemma prime_one_two_seven_nine : Nat.Prime 1279 := by norm_num

lemma seven_pow_six_thirty_seven_sq_r_sq_overshoot_six_five {r : ℕ}
    (hr : r.Prime) (h211 : 211 ≤ r) (h647 : r ≤ 647) :
    6 * usigma (7 ^ 6) * usigma (37 ^ 2) * usigma (r ^ 2) <
      5 * σ 1 (7 ^ 6) * σ 1 (37 ^ 2) * σ 1 (r ^ 2) := by
  rw [usigma_seven_pow_six, sigma_seven_pow_six,
    sigma_thirty_seven_pow_two, usigma_thirty_seven_pow_two,
    sigma_prime_pow_two hr, usigma_prime_pow hr (by decide : 0 < 2)]
  have hsq : r ^ 2 ≤ 647 * r := by
    rw [pow_two]
    exact Nat.mul_le_mul_right r h647
  have hleft : 1480005 * (1 + r ^ 2) < 965602995 * r := by
    have h1 : 1480005 * (1 + r ^ 2) ≤ 1480005 * (1 + 647 * r) :=
      Nat.mul_le_mul_left 1480005 (Nat.add_le_add_left hsq 1)
    have h2 : 1480005 * (1 + 647 * r) = 1480005 + 957563235 * r := by
      have : 1480005 * 647 = 957563235 := by norm_num
      ring
    have h3 : 1480005 + 957563235 * r < 965602995 * r := by
      have : 1480005 < 8039760 * r :=
        lt_of_lt_of_le (by norm_num : 1480005 < 1696389360)
          (Nat.mul_le_mul_left 8039760 h211)
      omega
    calc
      1480005 * (1 + r ^ 2) ≤ 1480005 * (1 + 647 * r) := h1
      _ = 1480005 + 957563235 * r := h2
      _ < 965602995 * r := h3
  have hL : 6 * 117650 * 1370 * (1 + r ^ 2) = 967083000 * (1 + r ^ 2) :=
    by ring
  have hR : 5 * 137257 * 1407 * (1 + r + r ^ 2) =
      965602995 * (1 + r + r ^ 2) := by ring
  have hmain : 967083000 * (1 + r ^ 2) < 965602995 * (1 + r + r ^ 2) := by
    have h1 : 967083000 * (1 + r ^ 2) =
        965602995 * (1 + r ^ 2) + 1480005 * (1 + r ^ 2) := by ring
    have h2 : 965602995 * (1 + r + r ^ 2) =
        965602995 * (1 + r ^ 2) + 965602995 * r := by ring
    rw [h1, h2]
    exact Nat.add_lt_add_left hleft _
  rw [hL, hR]
  exact hmain

lemma seven_pow_six_thirty_seven_r_sq_pow_ge_two_overshoot_six_five
    {r a b c : ℕ} (hr : r.Prime) (h211 : 211 ≤ r) (h647 : r ≤ 647)
    (ha : 6 ≤ a) (hb : 2 ≤ b) (hc : 2 ≤ c) :
    6 * usigma (7 ^ a) * usigma (37 ^ b) * usigma (r ^ c) <
      5 * σ 1 (7 ^ a) * σ 1 (37 ^ b) * σ 1 (r ^ c) :=
  six_five_overshoot_mono_three (by decide : Nat.Prime 7)
    (by decide : Nat.Prime 37) hr
    (by decide : 0 < 6) (by decide : 0 < 2) (by decide : 0 < 2)
    ha hb hc (seven_pow_six_thirty_seven_sq_r_sq_overshoot_six_five hr h211 h647)

lemma five_mul_seven_pow_six_thirty_seven_sq_cap {r : ℕ} (hr : 659 ≤ r) :
    5 * r * 137257 * 1407 ≤ 6 * (r - 1) * 117650 * 1370 := by
  have hdiff : 967083000 ≤ 1480005 * r := by
    have hmul : 1480005 * 659 ≤ 1480005 * r := Nat.mul_le_mul_left 1480005 hr
    have hnum : 1480005 * 659 = 975323295 := by norm_num
    omega
  have hL : 5 * r * 137257 * 1407 = 965602995 * r := by ring
  have hR : 6 * (r - 1) * 117650 * 1370 = 967083000 * (r - 1) := by ring
  have hmain : 965602995 * r ≤ 967083000 * (r - 1) := by
    have heq : 965602995 * r + 1480005 * r = 967083000 * r := by ring
    have hsub : 965602995 * r = 967083000 * r - 1480005 * r :=
      (Nat.sub_eq_of_eq_add heq.symm).symm
    have hle : 967083000 * r - 1480005 * r ≤ 967083000 * r - 967083000 :=
      Nat.sub_le_sub_left hdiff _
    have hrw : 967083000 * r - 967083000 = 967083000 * (r - 1) := by
      simpa using (Nat.mul_sub_left_distrib 967083000 r 1).symm
    calc
      965602995 * r = 967083000 * r - 1480005 * r := hsub
      _ ≤ 967083000 * r - 967083000 := hle
      _ = 967083000 * (r - 1) := hrw
  rw [hL, hR]
  exact hmain

lemma five_sigma_lt_six_usigma_seven_pow_six_thirty_seven_sq_large {r k : ℕ}
    (hr : r.Prime) (hr659 : 659 ≤ r) (hk : 0 < k) :
    5 * σ 1 (7 ^ 6) * σ 1 (37 ^ 2) * σ 1 (r ^ k) <
      6 * usigma (7 ^ 6) * usigma (37 ^ 2) * usigma (r ^ k) := by
  rw [sigma_seven_pow_six, usigma_seven_pow_six,
    sigma_thirty_seven_pow_two, usigma_thirty_seven_pow_two]
  have hcp := sigma_lt_cap_usigma hr hk
  have hT : 0 < 137257 * 1407 :=
    Nat.mul_pos (by decide : 0 < 137257) (by decide : 0 < 1407)
  have hthis := six_five_of_cap_times_const (A := r - 1) (B := r)
    (X := σ 1 (r ^ k)) (Y := usigma (r ^ k)) (S := 117650 * 1370)
    (T := 137257 * 1407) hcp (by
      have hL : 5 * r * (137257 * 1407) = 5 * r * 137257 * 1407 := by ring
      have hR : 6 * (r - 1) * (117650 * 1370) = 6 * (r - 1) * 117650 * 1370 :=
        by ring
      rw [hL, hR]
      exact five_mul_seven_pow_six_thirty_seven_sq_cap hr659)
    hT
  convert hthis using 1 <;> ring

lemma seven_pow_six_thirty_seven_cube_r_sq_overshoot_six_five {r : ℕ}
    (hr : r.Prime) (h211 : 211 ≤ r) (h1237 : r ≤ 1237) :
    6 * usigma (7 ^ 6) * usigma (37 ^ 3) * usigma (r ^ 2) <
      5 * σ 1 (7 ^ 6) * σ 1 (37 ^ 3) * σ 1 (r ^ 2) := by
  rw [usigma_seven_pow_six, sigma_seven_pow_six,
    sigma_thirty_seven_pow_three, usigma_thirty_seven_pow_three,
    sigma_prime_pow_two hr, usigma_prime_pow hr (by decide : 0 < 2)]
  have hsq : r ^ 2 ≤ 1237 * r := by
    rw [pow_two]
    exact Nat.mul_le_mul_right r h1237
  have hleft : 28661500 * (1 + r ^ 2) < 35727997100 * r := by
    have h1 : 28661500 * (1 + r ^ 2) ≤ 28661500 * (1 + 1237 * r) :=
      Nat.mul_le_mul_left 28661500 (Nat.add_le_add_left hsq 1)
    have h2 : 28661500 * (1 + 1237 * r) = 28661500 + 35454275500 * r := by
      have : 28661500 * 1237 = 35454275500 := by norm_num
      ring
    have h3 : 28661500 + 35454275500 * r < 35727997100 * r := by
      have : 28661500 < 273721600 * r :=
        lt_of_lt_of_le (by norm_num : 28661500 < 57755257600)
          (Nat.mul_le_mul_left 273721600 h211)
      omega
    calc
      28661500 * (1 + r ^ 2) ≤ 28661500 * (1 + 1237 * r) := h1
      _ = 28661500 + 35454275500 * r := h2
      _ < 35727997100 * r := h3
  have hL : 6 * 117650 * 50654 * (1 + r ^ 2) = 35756658600 * (1 + r ^ 2) :=
    by ring
  have hR : 5 * 137257 * 52060 * (1 + r + r ^ 2) =
      35727997100 * (1 + r + r ^ 2) := by ring
  have hmain : 35756658600 * (1 + r ^ 2) < 35727997100 * (1 + r + r ^ 2) := by
    have h1 : 35756658600 * (1 + r ^ 2) =
        35727997100 * (1 + r ^ 2) + 28661500 * (1 + r ^ 2) := by ring
    have h2 : 35727997100 * (1 + r + r ^ 2) =
        35727997100 * (1 + r ^ 2) + 35727997100 * r := by ring
    rw [h1, h2]
    exact Nat.add_lt_add_left hleft _
  rw [hL, hR]
  exact hmain

lemma seven_pow_six_thirty_seven_cube_r_pow_ge_two_overshoot_six_five
    {r a b c : ℕ} (hr : r.Prime) (h211 : 211 ≤ r) (h1237 : r ≤ 1237)
    (ha : 6 ≤ a) (hb : 3 ≤ b) (hc : 2 ≤ c) :
    6 * usigma (7 ^ a) * usigma (37 ^ b) * usigma (r ^ c) <
      5 * σ 1 (7 ^ a) * σ 1 (37 ^ b) * σ 1 (r ^ c) :=
  six_five_overshoot_mono_three (by decide : Nat.Prime 7)
    (by decide : Nat.Prime 37) hr
    (by decide : 0 < 6) (by decide : 0 < 3) (by decide : 0 < 2)
    ha hb hc
    (seven_pow_six_thirty_seven_cube_r_sq_overshoot_six_five hr h211 h1237)

lemma five_mul_seven_pow_six_thirty_seven_cube_cap {r : ℕ} (hr : 1249 ≤ r) :
    5 * r * 137257 * 52060 ≤ 6 * (r - 1) * 117650 * 50654 := by
  have hdiff : 35756658600 ≤ 28661500 * r := by
    have hmul : 28661500 * 1249 ≤ 28661500 * r :=
      Nat.mul_le_mul_left 28661500 hr
    have hnum : 28661500 * 1249 = 35798213500 := by norm_num
    omega
  have hL : 5 * r * 137257 * 52060 = 35727997100 * r := by ring
  have hR : 6 * (r - 1) * 117650 * 50654 = 35756658600 * (r - 1) := by ring
  have hmain : 35727997100 * r ≤ 35756658600 * (r - 1) := by
    have heq : 35727997100 * r + 28661500 * r = 35756658600 * r := by ring
    have hsub : 35727997100 * r = 35756658600 * r - 28661500 * r :=
      (Nat.sub_eq_of_eq_add heq.symm).symm
    have hle : 35756658600 * r - 28661500 * r ≤ 35756658600 * r - 35756658600 :=
      Nat.sub_le_sub_left hdiff _
    have hrw : 35756658600 * r - 35756658600 = 35756658600 * (r - 1) := by
      simpa using (Nat.mul_sub_left_distrib 35756658600 r 1).symm
    calc
      35727997100 * r = 35756658600 * r - 28661500 * r := hsub
      _ ≤ 35756658600 * r - 35756658600 := hle
      _ = 35756658600 * (r - 1) := hrw
  rw [hL, hR]
  exact hmain

lemma five_sigma_lt_six_usigma_seven_pow_six_thirty_seven_cube_large {r k : ℕ}
    (hr : r.Prime) (hr1249 : 1249 ≤ r) (hk : 0 < k) :
    5 * σ 1 (7 ^ 6) * σ 1 (37 ^ 3) * σ 1 (r ^ k) <
      6 * usigma (7 ^ 6) * usigma (37 ^ 3) * usigma (r ^ k) := by
  rw [sigma_seven_pow_six, usigma_seven_pow_six,
    sigma_thirty_seven_pow_three, usigma_thirty_seven_pow_three]
  have hcp := sigma_lt_cap_usigma hr hk
  have hT : 0 < 137257 * 52060 :=
    Nat.mul_pos (by decide : 0 < 137257) (by decide : 0 < 52060)
  have hthis := six_five_of_cap_times_const (A := r - 1) (B := r)
    (X := σ 1 (r ^ k)) (Y := usigma (r ^ k)) (S := 117650 * 50654)
    (T := 137257 * 52060) hcp (by
      have hL : 5 * r * (137257 * 52060) = 5 * r * 137257 * 52060 := by ring
      have hR : 6 * (r - 1) * (117650 * 50654) =
          6 * (r - 1) * 117650 * 50654 := by ring
      rw [hL, hR]
      exact five_mul_seven_pow_six_thirty_seven_cube_cap hr1249)
    hT
  convert hthis using 1 <;> ring

lemma seven_pow_six_thirty_seven_fourth_r_sq_overshoot_six_five {r : ℕ}
    (hr : r.Prime) (h211 : 211 ≤ r) (h1277 : r ≤ 1277) :
    6 * usigma (7 ^ 6) * usigma (37 ^ 4) * usigma (r ^ 2) <
      5 * σ 1 (7 ^ 6) * σ 1 (37 ^ 4) * σ 1 (r ^ 2) := by
  rw [usigma_seven_pow_six, sigma_seven_pow_six,
    sigma_thirty_seven_pow_four, usigma_thirty_seven_pow_four,
    sigma_prime_pow_two hr, usigma_prime_pow hr (by decide : 0 < 2)]
  have hsq : r ^ 2 ≤ 1277 * r := by
    rw [pow_two]
    exact Nat.mul_le_mul_right r h1277
  have hleft : 1034376815 * (1 + r ^ 2) < 1321936578985 * r := by
    have h1 : 1034376815 * (1 + r ^ 2) ≤ 1034376815 * (1 + 1277 * r) :=
      Nat.mul_le_mul_left 1034376815 (Nat.add_le_add_left hsq 1)
    have h2 : 1034376815 * (1 + 1277 * r) =
        1034376815 + 1320899192755 * r := by
      have : 1034376815 * 1277 = 1320899192755 := by norm_num
      ring
    have h3 : 1034376815 + 1320899192755 * r < 1321936578985 * r := by
      have : 1034376815 < 1037386230 * r :=
        lt_of_lt_of_le (by norm_num : 1034376815 < 218888494530)
          (Nat.mul_le_mul_left 1037386230 h211)
      omega
    calc
      1034376815 * (1 + r ^ 2) ≤ 1034376815 * (1 + 1277 * r) := h1
      _ = 1034376815 + 1320899192755 * r := h2
      _ < 1321936578985 * r := h3
  have hL : 6 * 117650 * 1874162 * (1 + r ^ 2) =
      1322970955800 * (1 + r ^ 2) := by ring
  have hR : 5 * 137257 * 1926221 * (1 + r + r ^ 2) =
      1321936578985 * (1 + r + r ^ 2) := by ring
  have hmain : 1322970955800 * (1 + r ^ 2) <
      1321936578985 * (1 + r + r ^ 2) := by
    have h1 : 1322970955800 * (1 + r ^ 2) =
        1321936578985 * (1 + r ^ 2) + 1034376815 * (1 + r ^ 2) := by ring
    have h2 : 1321936578985 * (1 + r + r ^ 2) =
        1321936578985 * (1 + r ^ 2) + 1321936578985 * r := by ring
    rw [h1, h2]
    exact Nat.add_lt_add_left hleft _
  rw [hL, hR]
  exact hmain

lemma seven_pow_six_thirty_seven_fourth_r_pow_ge_two_overshoot_six_five
    {r a b c : ℕ} (hr : r.Prime) (h211 : 211 ≤ r) (h1277 : r ≤ 1277)
    (ha : 6 ≤ a) (hb : 4 ≤ b) (hc : 2 ≤ c) :
    6 * usigma (7 ^ a) * usigma (37 ^ b) * usigma (r ^ c) <
      5 * σ 1 (7 ^ a) * σ 1 (37 ^ b) * σ 1 (r ^ c) :=
  six_five_overshoot_mono_three (by decide : Nat.Prime 7)
    (by decide : Nat.Prime 37) hr
    (by decide : 0 < 6) (by decide : 0 < 4) (by decide : 0 < 2)
    ha hb hc
    (seven_pow_six_thirty_seven_fourth_r_sq_overshoot_six_five hr h211 h1277)

lemma five_mul_seven_pow_six_thirty_seven_euler_cap {r : ℕ} (hr : 1283 ≤ r) :
    5 * 37 * r * 137257 ≤ 6 * 36 * (r - 1) * 117650 := by
  have hdiff : 25412400 ≤ 19855 * r := by
    have hmul : 19855 * 1283 ≤ 19855 * r := Nat.mul_le_mul_left 19855 hr
    have hnum : 19855 * 1283 = 25473965 := by norm_num
    omega
  have hL : 5 * 37 * r * 137257 = 25392545 * r := by ring
  have hR : 6 * 36 * (r - 1) * 117650 = 25412400 * (r - 1) := by ring
  have hmain : 25392545 * r ≤ 25412400 * (r - 1) := by
    have heq : 25392545 * r + 19855 * r = 25412400 * r := by ring
    have hsub : 25392545 * r = 25412400 * r - 19855 * r :=
      (Nat.sub_eq_of_eq_add heq.symm).symm
    have hle : 25412400 * r - 19855 * r ≤ 25412400 * r - 25412400 :=
      Nat.sub_le_sub_left hdiff _
    have hrw : 25412400 * r - 25412400 = 25412400 * (r - 1) := by
      simpa using (Nat.mul_sub_left_distrib 25412400 r 1).symm
    calc
      25392545 * r = 25412400 * r - 19855 * r := hsub
      _ ≤ 25412400 * r - 25412400 := hle
      _ = 25412400 * (r - 1) := hrw
  rw [hL, hR]
  exact hmain

lemma five_sigma_lt_six_usigma_seven_pow_six_thirty_seven_large {r b c : ℕ}
    (hr : r.Prime) (hr1283 : 1283 ≤ r) (hb : 0 < b) (hc : 0 < c) :
    5 * σ 1 (7 ^ 6) * σ 1 (37 ^ b) * σ 1 (r ^ c) <
      6 * usigma (7 ^ 6) * usigma (37 ^ b) * usigma (r ^ c) := by
  rw [sigma_seven_pow_six, usigma_seven_pow_six]
  have h37 := sigma_lt_cap_usigma (by decide : Nat.Prime 37) hb
  have hrcap := sigma_lt_cap_usigma hr hc
  have hu37 : 0 < usigma (37 ^ b) := by
    rw [usigma_prime_pow (by decide : Nat.Prime 37) hb]
    exact Nat.add_pos_left (by decide : 0 < 1) _
  have hthis := six_five_of_two_caps_times_const (A := 36) (B := 37)
    (X := σ 1 (37 ^ b)) (Y := usigma (37 ^ b)) (C := r - 1) (D := r)
    (P := σ 1 (r ^ c)) (Q := usigma (r ^ c)) (S := 117650) (T := 137257)
    h37 hrcap (five_mul_seven_pow_six_thirty_seven_euler_cap hr1283)
    (by decide : 0 < 37) hu37 (by decide : 0 < 137257)
  convert hthis using 1 <;> ring

lemma five_sigma_lt_six_usigma_seven_pow_six_thirty_seven_sq_six_fifty_three_sq :
    5 * σ 1 (7 ^ 6) * σ 1 (37 ^ 2) * σ 1 (653 ^ 2) <
      6 * usigma (7 ^ 6) * usigma (37 ^ 2) * usigma (653 ^ 2) := by
  rw [sigma_seven_pow_six, usigma_seven_pow_six,
    sigma_thirty_seven_pow_two, usigma_thirty_seven_pow_two,
    sigma_prime_pow_two prime_six_fifty_three,
    usigma_prime_pow prime_six_fifty_three (by decide : 0 < 2)]
  norm_num

lemma seven_pow_six_thirty_seven_sq_six_fifty_three_cube_overshoot :
    6 * usigma (7 ^ 6) * usigma (37 ^ 2) * usigma (653 ^ 3) <
      5 * σ 1 (7 ^ 6) * σ 1 (37 ^ 2) * σ 1 (653 ^ 3) := by
  rw [usigma_seven_pow_six, sigma_seven_pow_six,
    usigma_thirty_seven_pow_two, sigma_thirty_seven_pow_two,
    usigma_prime_pow prime_six_fifty_three (by decide : 0 < 3),
    sigma_prime_pow_div prime_six_fifty_three]
  norm_num

lemma five_sigma_lt_six_usigma_seven_pow_six_thirty_seven_cap_one_two_seven_nine_sq
    {b : ℕ} (hb : 0 < b) :
    5 * σ 1 (7 ^ 6) * σ 1 (37 ^ b) * σ 1 (1279 ^ 2) <
      6 * usigma (7 ^ 6) * usigma (37 ^ b) * usigma (1279 ^ 2) := by
  rw [sigma_seven_pow_six, usigma_seven_pow_six,
    sigma_prime_pow_two prime_one_two_seven_nine,
    usigma_prime_pow prime_one_two_seven_nine (by decide : 0 < 2)]
  have h37 := sigma_lt_cap_usigma (by decide : Nat.Prime 37) hb
  have hu37 : 0 < usigma (37 ^ b) := by
    rw [usigma_prime_pow (by decide : Nat.Prime 37) hb]
    exact Nat.add_pos_left (by decide : 0 < 1) _
  have hcap : 5 * 37 * (137257 * 1637121) ≤ 6 * 36 * (117650 * 1635842) := by
    norm_num
  have hT : 0 < 137257 * 1637121 :=
    Nat.mul_pos (by decide : 0 < 137257) (by decide : 0 < 1637121)
  have hthis := six_five_of_cap_times_const (A := 36) (B := 37)
    (X := σ 1 (37 ^ b)) (Y := usigma (37 ^ b)) (S := 117650 * 1635842)
    (T := 137257 * 1637121) h37 hcap hT
  convert hthis using 1 <;> ring

lemma seven_pow_six_thirty_seven_fourth_one_two_seven_nine_cube_overshoot :
    6 * usigma (7 ^ 6) * usigma (37 ^ 4) * usigma (1279 ^ 3) <
      5 * σ 1 (7 ^ 6) * σ 1 (37 ^ 4) * σ 1 (1279 ^ 3) := by
  rw [usigma_seven_pow_six, sigma_seven_pow_six,
    usigma_thirty_seven_pow_four, sigma_thirty_seven_pow_four,
    usigma_prime_pow prime_one_two_seven_nine (by decide : 0 < 3),
    sigma_prime_pow_div prime_one_two_seven_nine]
  norm_num

/-- Leftover `6/5` cannot be three squareful primes `7,37,653` with
`v₇ = 6` times a squarefree coprime factor. -/
lemma not_five_sigma_of_three_sq_primes_seven_thirty_seven_six_fifty_three
    {m : ℕ} (hm : m ≠ 0) (h : 5 * σ 1 m = 6 * usigma m)
    (hk7 : padicValNat 7 m = 6) (hk37 : 2 ≤ padicValNat 37 m)
    (hkr : 2 ≤ padicValNat 653 m)
    (hs : Squarefree (ordCompl[653] (ordCompl[37] (ordCompl[7] m)))) :
    False := by
  have hp7 : Nat.Prime 7 := by decide
  have hp37 : Nat.Prime 37 := by decide
  have hp653 : Nat.Prime 653 := prime_six_fifty_three
  have hpq_ne : (7 : ℕ) ≠ 37 := by decide
  have hpr_ne : (7 : ℕ) ≠ 653 := by decide
  have hqr_ne : (37 : ℕ) ≠ 653 := by decide
  have heq := five_sigma_eq_six_of_three_squareful hm hp7 hp37 hp653 hpq_ne
    hpr_ne hqr_ne h hs
  have hproj_p : ordProj[7] m = 7 ^ padicValNat 7 m := by
    simp [Nat.factorization_def m hp7]
  have hproj_q : ordProj[37] (ordCompl[7] m) =
      37 ^ padicValNat 37 (ordCompl[7] m) := by
    simp [Nat.factorization_def (ordCompl[7] m) hp37]
  have hproj_r : ordProj[653] (ordCompl[37] (ordCompl[7] m)) =
      653 ^ padicValNat 653 (ordCompl[37] (ordCompl[7] m)) := by
    simp [Nat.factorization_def (ordCompl[37] (ordCompl[7] m)) hp653]
  rw [hproj_r, padicValNat_ordCompl_of_ne hp653 hqr_ne,
    padicValNat_ordCompl_of_ne hp653 hpr_ne, hproj_q,
    padicValNat_ordCompl_of_ne hp37 hpq_ne, hproj_p, hk7] at heq
  rcases eq_or_lt_of_le hk37 with h37eq | h373
  · rw [← h37eq] at heq
    rcases eq_or_lt_of_le hkr with hreq | hr3
    · rw [← hreq] at heq
      exact five_sigma_lt_six_usigma_seven_pow_six_thirty_seven_sq_six_fifty_three_sq.ne
        heq
    · have hover := six_five_overshoot_mono_three hp7 hp37 hp653
        (by decide : 0 < 6) (by decide : 0 < 2) (by decide : 0 < 3)
        (le_refl _) (le_refl _) (Nat.succ_le_of_lt hr3)
        seven_pow_six_thirty_seven_sq_six_fifty_three_cube_overshoot
      rw [← heq] at hover
      exact lt_irrefl _ hover
  · have hover := seven_pow_six_thirty_seven_cube_r_pow_ge_two_overshoot_six_five
      hp653 (by decide : 211 ≤ 653) (by decide : 653 ≤ 1237)
      (le_refl _) (Nat.succ_le_of_lt h373) hkr
    rw [← heq] at hover
    exact lt_irrefl _ hover

/-- Leftover `6/5` cannot be three squareful primes `7,37,1279` with
`v₇ = 6` times a squarefree coprime factor. -/
lemma not_five_sigma_of_three_sq_primes_seven_thirty_seven_one_two_seven_nine
    {m : ℕ} (hm : m ≠ 0) (h : 5 * σ 1 m = 6 * usigma m)
    (hk7 : padicValNat 7 m = 6) (hk37 : 2 ≤ padicValNat 37 m)
    (hkr : 2 ≤ padicValNat 1279 m)
    (hs : Squarefree (ordCompl[1279] (ordCompl[37] (ordCompl[7] m)))) :
    False := by
  have hp7 : Nat.Prime 7 := by decide
  have hp37 : Nat.Prime 37 := by decide
  have hp1279 : Nat.Prime 1279 := prime_one_two_seven_nine
  have hpq_ne : (7 : ℕ) ≠ 37 := by decide
  have hpr_ne : (7 : ℕ) ≠ 1279 := by decide
  have hqr_ne : (37 : ℕ) ≠ 1279 := by decide
  have heq := five_sigma_eq_six_of_three_squareful hm hp7 hp37 hp1279 hpq_ne
    hpr_ne hqr_ne h hs
  have hproj_p : ordProj[7] m = 7 ^ padicValNat 7 m := by
    simp [Nat.factorization_def m hp7]
  have hproj_q : ordProj[37] (ordCompl[7] m) =
      37 ^ padicValNat 37 (ordCompl[7] m) := by
    simp [Nat.factorization_def (ordCompl[7] m) hp37]
  have hproj_r : ordProj[1279] (ordCompl[37] (ordCompl[7] m)) =
      1279 ^ padicValNat 1279 (ordCompl[37] (ordCompl[7] m)) := by
    simp [Nat.factorization_def (ordCompl[37] (ordCompl[7] m)) hp1279]
  rw [hproj_r, padicValNat_ordCompl_of_ne hp1279 hqr_ne,
    padicValNat_ordCompl_of_ne hp1279 hpr_ne, hproj_q,
    padicValNat_ordCompl_of_ne hp37 hpq_ne, hproj_p, hk7] at heq
  rcases eq_or_lt_of_le hk37 with h37eq | h373
  · rw [← h37eq] at heq
    exact (five_sigma_lt_six_usigma_seven_pow_six_thirty_seven_sq_large
      hp1279 (by decide : 659 ≤ 1279)
      ((Nat.zero_lt_succ 1).trans_le hkr)).ne heq
  · have h3le : 3 ≤ padicValNat 37 m := Nat.succ_le_of_lt h373
    rcases eq_or_lt_of_le h3le with h37eq3 | h374
    · have h37eq : padicValNat 37 m = 3 := h37eq3.symm
      rw [h37eq] at heq
      exact (five_sigma_lt_six_usigma_seven_pow_six_thirty_seven_cube_large
        hp1279 (by decide : 1249 ≤ 1279)
        ((Nat.zero_lt_succ 1).trans_le hkr)).ne heq
    · rcases eq_or_lt_of_le hkr with hreq | hr3
      · rw [← hreq] at heq
        exact (five_sigma_lt_six_usigma_seven_pow_six_thirty_seven_cap_one_two_seven_nine_sq
          (lt_of_lt_of_le (by decide : (0 : ℕ) < 2) hk37)).ne heq
      · have hover := six_five_overshoot_mono_three hp7 hp37 hp1279
          (by decide : 0 < 6) (by decide : 0 < 4) (by decide : 0 < 3)
          (le_refl _) (Nat.succ_le_of_lt h374) (Nat.succ_le_of_lt hr3)
          seven_pow_six_thirty_seven_fourth_one_two_seven_nine_cube_overshoot
        rw [← heq] at hover
        exact lt_irrefl _ hover

/-- Leftover `6/5` cannot be three squareful primes `7,37,r` with `r ≥ 211`
and `v₇ = 6` times a squarefree coprime factor. -/
lemma not_five_sigma_of_three_sq_primes_seven_thirty_seven_of_val_seven_eq_six
    {m r : ℕ} (hm : m ≠ 0) (hr : r.Prime) (hr211 : 211 ≤ r)
    (h : 5 * σ 1 m = 6 * usigma m)
    (hk7 : padicValNat 7 m = 6) (hk37 : 2 ≤ padicValNat 37 m)
    (hkr : 2 ≤ padicValNat r m)
    (hs : Squarefree (ordCompl[r] (ordCompl[37] (ordCompl[7] m)))) :
    False := by
  have hp7 : Nat.Prime 7 := by decide
  have hp37 : Nat.Prime 37 := by decide
  have hpq_ne : (7 : ℕ) ≠ 37 := by decide
  have hpr_ne : (7 : ℕ) ≠ r :=
    Nat.ne_of_lt (lt_of_lt_of_le (by decide : 7 < 211) hr211)
  have hqr_ne : (37 : ℕ) ≠ r :=
    Nat.ne_of_lt (lt_of_lt_of_le (by decide : 37 < 211) hr211)
  have heq := five_sigma_eq_six_of_three_squareful hm hp7 hp37 hr hpq_ne hpr_ne
    hqr_ne h hs
  have hproj_p : ordProj[7] m = 7 ^ padicValNat 7 m := by
    simp [Nat.factorization_def m hp7]
  have hproj_q : ordProj[37] (ordCompl[7] m) =
      37 ^ padicValNat 37 (ordCompl[7] m) := by
    simp [Nat.factorization_def (ordCompl[7] m) hp37]
  have hproj_r : ordProj[r] (ordCompl[37] (ordCompl[7] m)) =
      r ^ padicValNat r (ordCompl[37] (ordCompl[7] m)) := by
    simp [Nat.factorization_def (ordCompl[37] (ordCompl[7] m)) hr]
  rw [hproj_r, padicValNat_ordCompl_of_ne hr hqr_ne,
    padicValNat_ordCompl_of_ne hr hpr_ne, hproj_q,
    padicValNat_ordCompl_of_ne hp37 hpq_ne, hproj_p, hk7] at heq
  rcases eq_or_lt_of_le hk37 with h37eq | h373
  · rw [← h37eq] at heq
    rcases le_or_gt r 647 with h647 | h648
    · have hover := seven_pow_six_thirty_seven_r_sq_pow_ge_two_overshoot_six_five
        hr hr211 h647 (le_refl _) (le_refl _) hkr
      rw [← heq] at hover
      exact lt_irrefl _ hover
    · have hr653 : 653 ≤ r :=
        prime_ge_six_hundred_forty_eight_ge_six_hundred_fifty_three hr
          (Nat.succ_le_of_lt h648)
      rcases le_or_gt r 653 with h653 | h654
      · have hr653eq : r = 653 := le_antisymm h653 hr653
        subst r
        exact not_five_sigma_of_three_sq_primes_seven_thirty_seven_six_fifty_three
          hm h hk7 hk37 hkr hs
      · have hr659 : 659 ≤ r :=
          prime_ge_six_hundred_fifty_four_ge_six_hundred_fifty_nine hr
            (Nat.succ_le_of_lt h654)
        exact (five_sigma_lt_six_usigma_seven_pow_six_thirty_seven_sq_large hr
          hr659 ((Nat.zero_lt_succ 1).trans_le hkr)).ne heq
  · rcases le_or_gt r 1237 with h1237 | h1238
    · have hover := seven_pow_six_thirty_seven_cube_r_pow_ge_two_overshoot_six_five
        hr hr211 h1237 (le_refl _) (Nat.succ_le_of_lt h373) hkr
      rw [← heq] at hover
      exact lt_irrefl _ hover
    · have hr1249 : 1249 ≤ r :=
        prime_ge_one_two_three_eight_ge_one_two_four_nine hr
          (Nat.succ_le_of_lt h1238)
      rcases eq_or_lt_of_le (Nat.succ_le_of_lt h373) with h37eq3 | h374
      · have h37eq : padicValNat 37 m = 3 := h37eq3.symm
        rw [h37eq] at heq
        exact (five_sigma_lt_six_usigma_seven_pow_six_thirty_seven_cube_large hr
          hr1249 ((Nat.zero_lt_succ 1).trans_le hkr)).ne heq
      · rcases le_or_gt r 1277 with h1277 | h1278
        · have hover :=
            seven_pow_six_thirty_seven_fourth_r_pow_ge_two_overshoot_six_five
              hr hr211 h1277 (le_refl _) (Nat.succ_le_of_lt h374) hkr
          rw [← heq] at hover
          exact lt_irrefl _ hover
        · have hr1279 : 1279 ≤ r :=
            prime_ge_one_two_seven_eight_ge_one_two_seven_nine hr
              (Nat.succ_le_of_lt h1278)
          rcases le_or_gt r 1279 with h1279 | h1280
          · have hr1279eq : r = 1279 := le_antisymm h1279 hr1279
            subst r
            exact
              not_five_sigma_of_three_sq_primes_seven_thirty_seven_one_two_seven_nine
                hm h hk7 hk37 hkr hs
          · have hr1283 : 1283 ≤ r :=
              prime_ge_one_two_eight_zero_ge_one_two_eight_three hr
                (Nat.succ_le_of_lt h1280)
            exact (five_sigma_lt_six_usigma_seven_pow_six_thirty_seven_large hr
              hr1283 (lt_of_lt_of_le (by decide : (0 : ℕ) < 2) hk37)
              ((Nat.zero_lt_succ 1).trans_le hkr)).ne heq

lemma seven_pow_seven_thirty_seven_sq_r_sq_overshoot_six_five {r : ℕ}
    (hr : r.Prime) (h211 : 211 ≤ r) (h653 : r ≤ 653) :
    6 * usigma (7 ^ 7) * usigma (37 ^ 2) * usigma (r ^ 2) <
      5 * σ 1 (7 ^ 7) * σ 1 (37 ^ 2) * σ 1 (r ^ 2) := by
  rw [usigma_seven_pow_seven, sigma_seven_pow_seven,
    sigma_thirty_seven_pow_two, usigma_thirty_seven_pow_two,
    sigma_prime_pow_two hr, usigma_prime_pow hr (by decide : 0 < 2)]
  have hsq : r ^ 2 ≤ 653 * r := by
    rw [pow_two]
    exact Nat.mul_le_mul_right r h653
  have hleft : 10303680 * (1 + r ^ 2) < 6759228000 * r := by
    have h1 : 10303680 * (1 + r ^ 2) ≤ 10303680 * (1 + 653 * r) :=
      Nat.mul_le_mul_left 10303680 (Nat.add_le_add_left hsq 1)
    have h2 : 10303680 * (1 + 653 * r) = 10303680 + 6728303040 * r := by
      have : 10303680 * 653 = 6728303040 := by norm_num
      ring
    have h3 : 10303680 + 6728303040 * r < 6759228000 * r := by
      have : 10303680 < 30924960 * r :=
        lt_of_lt_of_le (by norm_num : 10303680 < 6525166560)
          (Nat.mul_le_mul_left 30924960 h211)
      omega
    calc
      10303680 * (1 + r ^ 2) ≤ 10303680 * (1 + 653 * r) := h1
      _ = 10303680 + 6728303040 * r := h2
      _ < 6759228000 * r := h3
  have hL : 6 * 823544 * 1370 * (1 + r ^ 2) = 6769531680 * (1 + r ^ 2) :=
    by ring
  have hR : 5 * 960800 * 1407 * (1 + r + r ^ 2) =
      6759228000 * (1 + r + r ^ 2) := by ring
  have hmain : 6769531680 * (1 + r ^ 2) < 6759228000 * (1 + r + r ^ 2) := by
    have h1 : 6769531680 * (1 + r ^ 2) =
        6759228000 * (1 + r ^ 2) + 10303680 * (1 + r ^ 2) := by ring
    have h2 : 6759228000 * (1 + r + r ^ 2) =
        6759228000 * (1 + r ^ 2) + 6759228000 * r := by ring
    rw [h1, h2]
    exact Nat.add_lt_add_left hleft _
  rw [hL, hR]
  exact hmain

lemma seven_pow_seven_thirty_seven_r_sq_pow_ge_two_overshoot_six_five
    {r a b c : ℕ} (hr : r.Prime) (h211 : 211 ≤ r) (h653 : r ≤ 653)
    (ha : 7 ≤ a) (hb : 2 ≤ b) (hc : 2 ≤ c) :
    6 * usigma (7 ^ a) * usigma (37 ^ b) * usigma (r ^ c) <
      5 * σ 1 (7 ^ a) * σ 1 (37 ^ b) * σ 1 (r ^ c) :=
  six_five_overshoot_mono_three (by decide : Nat.Prime 7)
    (by decide : Nat.Prime 37) hr
    (by decide : 0 < 7) (by decide : 0 < 2) (by decide : 0 < 2)
    ha hb hc
    (seven_pow_seven_thirty_seven_sq_r_sq_overshoot_six_five hr h211 h653)

lemma five_mul_seven_cap_thirty_seven_sq {r : ℕ} (hr : 659 ≤ r) :
    5 * 7 * r * 1407 ≤ 6 * 6 * (r - 1) * 1370 := by
  have hdiff : 49320 ≤ 75 * r := by
    have hmul : 75 * 659 ≤ 75 * r := Nat.mul_le_mul_left 75 hr
    have hnum : 75 * 659 = 49425 := by decide
    omega
  have hL : 5 * 7 * r * 1407 = 49245 * r := by ring
  have hR : 6 * 6 * (r - 1) * 1370 = 49320 * (r - 1) := by ring
  have hmain : 49245 * r ≤ 49320 * (r - 1) := by
    have heq : 49245 * r + 75 * r = 49320 * r := by ring
    have hsub : 49245 * r = 49320 * r - 75 * r :=
      (Nat.sub_eq_of_eq_add heq.symm).symm
    have hle : 49320 * r - 75 * r ≤ 49320 * r - 49320 :=
      Nat.sub_le_sub_left hdiff _
    have hrw : 49320 * r - 49320 = 49320 * (r - 1) := by
      simpa using (Nat.mul_sub_left_distrib 49320 r 1).symm
    calc
      49245 * r = 49320 * r - 75 * r := hsub
      _ ≤ 49320 * r - 49320 := hle
      _ = 49320 * (r - 1) := hrw
  rw [hL, hR]
  exact hmain

lemma five_sigma_lt_six_usigma_seven_cap_thirty_seven_sq_large {r a k : ℕ}
    (hr : r.Prime) (hr659 : 659 ≤ r) (ha : 0 < a) (hk : 0 < k) :
    5 * σ 1 (7 ^ a) * σ 1 (37 ^ 2) * σ 1 (r ^ k) <
      6 * usigma (7 ^ a) * usigma (37 ^ 2) * usigma (r ^ k) := by
  rw [sigma_thirty_seven_pow_two, usigma_thirty_seven_pow_two]
  have h7 := sigma_lt_cap_usigma (by decide : Nat.Prime 7) ha
  have hrcap := sigma_lt_cap_usigma hr hk
  have hu7 : 0 < usigma (7 ^ a) := by
    rw [usigma_prime_pow (by decide : Nat.Prime 7) ha]
    exact Nat.add_pos_left (by decide : 0 < 1) _
  have hthis := six_five_of_two_caps_times_const (A := 6) (B := 7)
    (X := σ 1 (7 ^ a)) (Y := usigma (7 ^ a)) (C := r - 1) (D := r)
    (P := σ 1 (r ^ k)) (Q := usigma (r ^ k)) (S := 1370) (T := 1407)
    h7 hrcap (five_mul_seven_cap_thirty_seven_sq hr659)
    (by decide : 0 < 7) hu7 (by decide : 0 < 1407)
  convert hthis using 1 <;> ring

/-- Leftover `6/5` cannot be three squareful primes `7,37,r` with `r ≥ 211`,
`v₇ ≥ 7` and `v₃₇ = 2`, times a squarefree coprime factor. -/
lemma not_five_sigma_of_three_sq_primes_seven_thirty_seven_of_val_seven_ge_seven_of_val_thirty_seven_eq_two
    {m r : ℕ} (hm : m ≠ 0) (hr : r.Prime) (hr211 : 211 ≤ r)
    (h : 5 * σ 1 m = 6 * usigma m)
    (hk7 : 7 ≤ padicValNat 7 m) (hk37 : padicValNat 37 m = 2)
    (hkr : 2 ≤ padicValNat r m)
    (hs : Squarefree (ordCompl[r] (ordCompl[37] (ordCompl[7] m)))) :
    False := by
  have hp7 : Nat.Prime 7 := by decide
  have hp37 : Nat.Prime 37 := by decide
  have hpq_ne : (7 : ℕ) ≠ 37 := by decide
  have hpr_ne : (7 : ℕ) ≠ r :=
    Nat.ne_of_lt (lt_of_lt_of_le (by decide : 7 < 211) hr211)
  have hqr_ne : (37 : ℕ) ≠ r :=
    Nat.ne_of_lt (lt_of_lt_of_le (by decide : 37 < 211) hr211)
  have heq := five_sigma_eq_six_of_three_squareful hm hp7 hp37 hr hpq_ne hpr_ne
    hqr_ne h hs
  have hproj_p : ordProj[7] m = 7 ^ padicValNat 7 m := by
    simp [Nat.factorization_def m hp7]
  have hproj_q : ordProj[37] (ordCompl[7] m) =
      37 ^ padicValNat 37 (ordCompl[7] m) := by
    simp [Nat.factorization_def (ordCompl[7] m) hp37]
  have hproj_r : ordProj[r] (ordCompl[37] (ordCompl[7] m)) =
      r ^ padicValNat r (ordCompl[37] (ordCompl[7] m)) := by
    simp [Nat.factorization_def (ordCompl[37] (ordCompl[7] m)) hr]
  rw [hproj_r, padicValNat_ordCompl_of_ne hr hqr_ne,
    padicValNat_ordCompl_of_ne hr hpr_ne, hproj_q,
    padicValNat_ordCompl_of_ne hp37 hpq_ne, hproj_p, hk37] at heq
  rcases le_or_gt r 653 with h653 | h654
  · have hover := seven_pow_seven_thirty_seven_r_sq_pow_ge_two_overshoot_six_five
      hr hr211 h653 hk7 (le_refl _) hkr
    rw [← heq] at hover
    exact lt_irrefl _ hover
  · have hr659 : 659 ≤ r :=
      prime_ge_six_hundred_fifty_four_ge_six_hundred_fifty_nine hr
        (Nat.succ_le_of_lt h654)
    exact (five_sigma_lt_six_usigma_seven_cap_thirty_seven_sq_large hr hr659
      (lt_of_lt_of_le (by decide : (0 : ℕ) < 7) hk7)
      ((Nat.zero_lt_succ 1).trans_le hkr)).ne heq

lemma prime_ge_one_two_six_zero_ge_one_two_seven_seven {p : ℕ} (hp : p.Prime)
    (h : 1260 ≤ p) : 1277 ≤ p := by
  have hmem : p = 1260 ∨ p = 1261 ∨ p = 1262 ∨ p = 1263 ∨ p = 1264 ∨
      p = 1265 ∨ p = 1266 ∨ p = 1267 ∨ p = 1268 ∨ p = 1269 ∨ p = 1270 ∨
      p = 1271 ∨ p = 1272 ∨ p = 1273 ∨ p = 1274 ∨ p = 1275 ∨ p = 1276 ∨
      1277 ≤ p := by omega
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | h1277
  · exact False.elim (not_prime_of_eq_mul (rfl : 1260 = 2 * 630)
      (by decide : (2 : ℕ) ≠ 1) (by decide : (630 : ℕ) ≠ 1) hp)
  · exact False.elim (not_prime_of_eq_mul (rfl : 1261 = 13 * 97)
      (by decide : (13 : ℕ) ≠ 1) (by decide : (97 : ℕ) ≠ 1) hp)
  · exact False.elim (not_prime_of_eq_mul (rfl : 1262 = 2 * 631)
      (by decide : (2 : ℕ) ≠ 1) (by decide : (631 : ℕ) ≠ 1) hp)
  · exact False.elim (not_prime_of_eq_mul (rfl : 1263 = 3 * 421)
      (by decide : (3 : ℕ) ≠ 1) (by decide : (421 : ℕ) ≠ 1) hp)
  · exact False.elim (not_prime_of_eq_mul (rfl : 1264 = 2 * 632)
      (by decide : (2 : ℕ) ≠ 1) (by decide : (632 : ℕ) ≠ 1) hp)
  · exact False.elim (not_prime_of_eq_mul (rfl : 1265 = 5 * 253)
      (by decide : (5 : ℕ) ≠ 1) (by decide : (253 : ℕ) ≠ 1) hp)
  · exact False.elim (not_prime_of_eq_mul (rfl : 1266 = 2 * 633)
      (by decide : (2 : ℕ) ≠ 1) (by decide : (633 : ℕ) ≠ 1) hp)
  · exact False.elim (not_prime_of_eq_mul (rfl : 1267 = 7 * 181)
      (by decide : (7 : ℕ) ≠ 1) (by decide : (181 : ℕ) ≠ 1) hp)
  · exact False.elim (not_prime_of_eq_mul (rfl : 1268 = 2 * 634)
      (by decide : (2 : ℕ) ≠ 1) (by decide : (634 : ℕ) ≠ 1) hp)
  · exact False.elim (not_prime_of_eq_mul (rfl : 1269 = 3 * 423)
      (by decide : (3 : ℕ) ≠ 1) (by decide : (423 : ℕ) ≠ 1) hp)
  · exact False.elim (not_prime_of_eq_mul (rfl : 1270 = 2 * 635)
      (by decide : (2 : ℕ) ≠ 1) (by decide : (635 : ℕ) ≠ 1) hp)
  · exact False.elim (not_prime_of_eq_mul (rfl : 1271 = 31 * 41)
      (by decide : (31 : ℕ) ≠ 1) (by decide : (41 : ℕ) ≠ 1) hp)
  · exact False.elim (not_prime_of_eq_mul (rfl : 1272 = 2 * 636)
      (by decide : (2 : ℕ) ≠ 1) (by decide : (636 : ℕ) ≠ 1) hp)
  · exact False.elim (not_prime_of_eq_mul (rfl : 1273 = 19 * 67)
      (by decide : (19 : ℕ) ≠ 1) (by decide : (67 : ℕ) ≠ 1) hp)
  · exact False.elim (not_prime_of_eq_mul (rfl : 1274 = 2 * 637)
      (by decide : (2 : ℕ) ≠ 1) (by decide : (637 : ℕ) ≠ 1) hp)
  · exact False.elim (not_prime_of_eq_mul (rfl : 1275 = 3 * 425)
      (by decide : (3 : ℕ) ≠ 1) (by decide : (425 : ℕ) ≠ 1) hp)
  · exact False.elim (not_prime_of_eq_mul (rfl : 1276 = 2 * 638)
      (by decide : (2 : ℕ) ≠ 1) (by decide : (638 : ℕ) ≠ 1) hp)
  · exact h1277

lemma prime_le_one_two_nine_six_le_one_two_nine_one {p : ℕ} (hp : p.Prime)
    (h : p ≤ 1296) : p ≤ 1291 := by
  have hmem : p ≤ 1291 ∨ p = 1292 ∨ p = 1293 ∨ p = 1294 ∨ p = 1295 ∨
      p = 1296 := by omega
  rcases hmem with h1291 | rfl | rfl | rfl | rfl | rfl
  · exact h1291
  · exact False.elim (not_prime_of_eq_mul (rfl : 1292 = 2 * 646)
      (by decide : (2 : ℕ) ≠ 1) (by decide : (646 : ℕ) ≠ 1) hp)
  · exact False.elim (not_prime_of_eq_mul (rfl : 1293 = 3 * 431)
      (by decide : (3 : ℕ) ≠ 1) (by decide : (431 : ℕ) ≠ 1) hp)
  · exact False.elim (not_prime_of_eq_mul (rfl : 1294 = 2 * 647)
      (by decide : (2 : ℕ) ≠ 1) (by decide : (647 : ℕ) ≠ 1) hp)
  · exact False.elim (not_prime_of_eq_mul (rfl : 1295 = 5 * 259)
      (by decide : (5 : ℕ) ≠ 1) (by decide : (259 : ℕ) ≠ 1) hp)
  · exact False.elim (not_prime_of_eq_mul (rfl : 1296 = 2 * 648)
      (by decide : (2 : ℕ) ≠ 1) (by decide : (648 : ℕ) ≠ 1) hp)

lemma seven_pow_seven_thirty_seven_cube_r_sq_overshoot_six_five {r : ℕ}
    (hr : r.Prime) (h211 : 211 ≤ r) (h1259 : r ≤ 1259) :
    6 * usigma (7 ^ 7) * usigma (37 ^ 3) * usigma (r ^ 2) <
      5 * σ 1 (7 ^ 7) * σ 1 (37 ^ 3) * σ 1 (r ^ 2) := by
  rw [usigma_seven_pow_seven, sigma_seven_pow_seven,
    sigma_thirty_seven_pow_three, usigma_thirty_seven_pow_three,
    sigma_prime_pow_two hr, usigma_prime_pow hr (by decide : 0 < 2)]
  have hsq : r ^ 2 ≤ 1259 * r := by
    rw [pow_two]
    exact Nat.mul_le_mul_right r h1259
  have hleft : 198546656 * (1 + r ^ 2) < 250096240000 * r := by
    have h1 : 198546656 * (1 + r ^ 2) ≤ 198546656 * (1 + 1259 * r) :=
      Nat.mul_le_mul_left 198546656 (Nat.add_le_add_left hsq 1)
    have h2 : 198546656 * (1 + 1259 * r) = 198546656 + 249970239904 * r := by
      have : 198546656 * 1259 = 249970239904 := by norm_num
      ring
    have h3 : 198546656 + 249970239904 * r < 250096240000 * r := by
      have : 198546656 < 126000096 * r :=
        lt_of_lt_of_le (by norm_num : 198546656 < 26586020256)
          (Nat.mul_le_mul_left 126000096 h211)
      omega
    calc
      198546656 * (1 + r ^ 2) ≤ 198546656 * (1 + 1259 * r) := h1
      _ = 198546656 + 249970239904 * r := h2
      _ < 250096240000 * r := h3
  have hL : 6 * 823544 * 50654 * (1 + r ^ 2) =
      250294786656 * (1 + r ^ 2) := by ring
  have hR : 5 * 960800 * 52060 * (1 + r + r ^ 2) =
      250096240000 * (1 + r + r ^ 2) := by ring
  have hmain : 250294786656 * (1 + r ^ 2) <
      250096240000 * (1 + r + r ^ 2) := by
    have h1 : 250294786656 * (1 + r ^ 2) =
        250096240000 * (1 + r ^ 2) + 198546656 * (1 + r ^ 2) := by ring
    have h2 : 250096240000 * (1 + r + r ^ 2) =
        250096240000 * (1 + r ^ 2) + 250096240000 * r := by ring
    rw [h1, h2]
    exact Nat.add_lt_add_left hleft _
  rw [hL, hR]
  exact hmain

lemma seven_pow_seven_thirty_seven_cube_r_pow_ge_two_overshoot_six_five
    {r a b c : ℕ} (hr : r.Prime) (h211 : 211 ≤ r) (h1259 : r ≤ 1259)
    (ha : 7 ≤ a) (hb : 3 ≤ b) (hc : 2 ≤ c) :
    6 * usigma (7 ^ a) * usigma (37 ^ b) * usigma (r ^ c) <
      5 * σ 1 (7 ^ a) * σ 1 (37 ^ b) * σ 1 (r ^ c) :=
  six_five_overshoot_mono_three (by decide : Nat.Prime 7)
    (by decide : Nat.Prime 37) hr
    (by decide : 0 < 7) (by decide : 0 < 3) (by decide : 0 < 2)
    ha hb hc
    (seven_pow_seven_thirty_seven_cube_r_sq_overshoot_six_five hr h211 h1259)

lemma five_mul_seven_cap_thirty_seven_cube {r : ℕ} (hr : 1277 ≤ r) :
    5 * 7 * r * 52060 ≤ 6 * 6 * (r - 1) * 50654 := by
  have hdiff : 1823544 ≤ 1444 * r := by
    have hmul : 1444 * 1277 ≤ 1444 * r := Nat.mul_le_mul_left 1444 hr
    have hnum : 1444 * 1277 = 1843988 := by norm_num
    omega
  have hL : 5 * 7 * r * 52060 = 1822100 * r := by ring
  have hR : 6 * 6 * (r - 1) * 50654 = 1823544 * (r - 1) := by ring
  have hmain : 1822100 * r ≤ 1823544 * (r - 1) := by
    have heq : 1822100 * r + 1444 * r = 1823544 * r := by ring
    have hsub : 1822100 * r = 1823544 * r - 1444 * r :=
      (Nat.sub_eq_of_eq_add heq.symm).symm
    have hle : 1823544 * r - 1444 * r ≤ 1823544 * r - 1823544 :=
      Nat.sub_le_sub_left hdiff _
    have hrw : 1823544 * r - 1823544 = 1823544 * (r - 1) := by
      simpa using (Nat.mul_sub_left_distrib 1823544 r 1).symm
    calc
      1822100 * r = 1823544 * r - 1444 * r := hsub
      _ ≤ 1823544 * r - 1823544 := hle
      _ = 1823544 * (r - 1) := hrw
  rw [hL, hR]
  exact hmain

lemma five_sigma_lt_six_usigma_seven_cap_thirty_seven_cube_large {r a k : ℕ}
    (hr : r.Prime) (hr1277 : 1277 ≤ r) (ha : 0 < a) (hk : 0 < k) :
    5 * σ 1 (7 ^ a) * σ 1 (37 ^ 3) * σ 1 (r ^ k) <
      6 * usigma (7 ^ a) * usigma (37 ^ 3) * usigma (r ^ k) := by
  rw [sigma_thirty_seven_pow_three, usigma_thirty_seven_pow_three]
  have h7 := sigma_lt_cap_usigma (by decide : Nat.Prime 7) ha
  have hrcap := sigma_lt_cap_usigma hr hk
  have hu7 : 0 < usigma (7 ^ a) := by
    rw [usigma_prime_pow (by decide : Nat.Prime 7) ha]
    exact Nat.add_pos_left (by decide : 0 < 1) _
  have hthis := six_five_of_two_caps_times_const (A := 6) (B := 7)
    (X := σ 1 (7 ^ a)) (Y := usigma (7 ^ a)) (C := r - 1) (D := r)
    (P := σ 1 (r ^ k)) (Q := usigma (r ^ k)) (S := 50654) (T := 52060)
    h7 hrcap (five_mul_seven_cap_thirty_seven_cube hr1277)
    (by decide : 0 < 7) hu7 (by decide : 0 < 52060)
  convert hthis using 1 <;> ring

lemma seven_pow_seven_thirty_seven_fourth_r_sq_overshoot_six_five {r : ℕ}
    (hr : r.Prime) (h211 : 211 ≤ r) (h1291 : r ≤ 1291) :
    6 * usigma (7 ^ 7) * usigma (37 ^ 4) * usigma (r ^ 2) <
      5 * σ 1 (7 ^ 7) * σ 1 (37 ^ 4) * σ 1 (r ^ 2) := by
  rw [usigma_seven_pow_seven, sigma_seven_pow_seven,
    sigma_thirty_seven_pow_four, usigma_thirty_seven_pow_four,
    sigma_prime_pow_two hr, usigma_prime_pow hr (by decide : 0 < 2)]
  have hsq : r ^ 2 ≤ 1291 * r := by
    rw [pow_two]
    exact Nat.mul_le_mul_right r h1291
  have hleft : 7163536768 * (1 + r ^ 2) < 9253565684000 * r := by
    have h1 : 7163536768 * (1 + r ^ 2) ≤ 7163536768 * (1 + 1291 * r) :=
      Nat.mul_le_mul_left 7163536768 (Nat.add_le_add_left hsq 1)
    have h2 : 7163536768 * (1 + 1291 * r) =
        7163536768 + 9248125967488 * r := by
      have : 7163536768 * 1291 = 9248125967488 := by norm_num
      ring
    have h3 : 7163536768 + 9248125967488 * r < 9253565684000 * r := by
      have : 7163536768 < 5439716512 * r :=
        lt_of_lt_of_le (by norm_num : 7163536768 < 1147780184032)
          (Nat.mul_le_mul_left 5439716512 h211)
      omega
    calc
      7163536768 * (1 + r ^ 2) ≤ 7163536768 * (1 + 1291 * r) := h1
      _ = 7163536768 + 9248125967488 * r := h2
      _ < 9253565684000 * r := h3
  have hL : 6 * 823544 * 1874162 * (1 + r ^ 2) =
      9260729220768 * (1 + r ^ 2) := by ring
  have hR : 5 * 960800 * 1926221 * (1 + r + r ^ 2) =
      9253565684000 * (1 + r + r ^ 2) := by ring
  have hmain : 9260729220768 * (1 + r ^ 2) <
      9253565684000 * (1 + r + r ^ 2) := by
    have h1 : 9260729220768 * (1 + r ^ 2) =
        9253565684000 * (1 + r ^ 2) + 7163536768 * (1 + r ^ 2) := by ring
    have h2 : 9253565684000 * (1 + r + r ^ 2) =
        9253565684000 * (1 + r ^ 2) + 9253565684000 * r := by ring
    rw [h1, h2]
    exact Nat.add_lt_add_left hleft _
  rw [hL, hR]
  exact hmain

lemma seven_pow_seven_thirty_seven_fourth_r_pow_ge_two_overshoot_six_five
    {r a b c : ℕ} (hr : r.Prime) (h211 : 211 ≤ r) (h1291 : r ≤ 1291)
    (ha : 7 ≤ a) (hb : 4 ≤ b) (hc : 2 ≤ c) :
    6 * usigma (7 ^ a) * usigma (37 ^ b) * usigma (r ^ c) <
      5 * σ 1 (7 ^ a) * σ 1 (37 ^ b) * σ 1 (r ^ c) :=
  six_five_overshoot_mono_three (by decide : Nat.Prime 7)
    (by decide : Nat.Prime 37) hr
    (by decide : 0 < 7) (by decide : 0 < 4) (by decide : 0 < 2)
    ha hb hc
    (seven_pow_seven_thirty_seven_fourth_r_sq_overshoot_six_five hr h211 h1291)

/-- Leftover `6/5` cannot be three squareful primes `7,37,r` with `r ≥ 211`,
`v₇ ≥ 7` and `v₃₇ = 3`, times a squarefree coprime factor. -/
lemma not_five_sigma_of_three_sq_primes_seven_thirty_seven_of_val_seven_ge_seven_of_val_thirty_seven_eq_three
    {m r : ℕ} (hm : m ≠ 0) (hr : r.Prime) (hr211 : 211 ≤ r)
    (h : 5 * σ 1 m = 6 * usigma m)
    (hk7 : 7 ≤ padicValNat 7 m) (hk37 : padicValNat 37 m = 3)
    (hkr : 2 ≤ padicValNat r m)
    (hs : Squarefree (ordCompl[r] (ordCompl[37] (ordCompl[7] m)))) :
    False := by
  have hp7 : Nat.Prime 7 := by decide
  have hp37 : Nat.Prime 37 := by decide
  have hpq_ne : (7 : ℕ) ≠ 37 := by decide
  have hpr_ne : (7 : ℕ) ≠ r :=
    Nat.ne_of_lt (lt_of_lt_of_le (by decide : 7 < 211) hr211)
  have hqr_ne : (37 : ℕ) ≠ r :=
    Nat.ne_of_lt (lt_of_lt_of_le (by decide : 37 < 211) hr211)
  have heq := five_sigma_eq_six_of_three_squareful hm hp7 hp37 hr hpq_ne hpr_ne
    hqr_ne h hs
  have hproj_p : ordProj[7] m = 7 ^ padicValNat 7 m := by
    simp [Nat.factorization_def m hp7]
  have hproj_q : ordProj[37] (ordCompl[7] m) =
      37 ^ padicValNat 37 (ordCompl[7] m) := by
    simp [Nat.factorization_def (ordCompl[7] m) hp37]
  have hproj_r : ordProj[r] (ordCompl[37] (ordCompl[7] m)) =
      r ^ padicValNat r (ordCompl[37] (ordCompl[7] m)) := by
    simp [Nat.factorization_def (ordCompl[37] (ordCompl[7] m)) hr]
  rw [hproj_r, padicValNat_ordCompl_of_ne hr hqr_ne,
    padicValNat_ordCompl_of_ne hr hpr_ne, hproj_q,
    padicValNat_ordCompl_of_ne hp37 hpq_ne, hproj_p, hk37] at heq
  rcases le_or_gt r 1259 with h1259 | h1260
  · have hover := seven_pow_seven_thirty_seven_cube_r_pow_ge_two_overshoot_six_five
      hr hr211 h1259 hk7 (le_refl _) hkr
    rw [← heq] at hover
    exact lt_irrefl _ hover
  · have hr1277 : 1277 ≤ r :=
      prime_ge_one_two_six_zero_ge_one_two_seven_seven hr
        (Nat.succ_le_of_lt h1260)
    exact (five_sigma_lt_six_usigma_seven_cap_thirty_seven_cube_large hr hr1277
      (lt_of_lt_of_le (by decide : (0 : ℕ) < 7) hk7)
      ((Nat.zero_lt_succ 1).trans_le hkr)).ne heq

/-- Leftover `6/5` cannot be three squareful primes `7,37,r` with
`211 ≤ r ≤ 1296`, `v₇ ≥ 7` and `v₃₇ ≥ 4`, times a squarefree coprime factor. -/
lemma not_five_sigma_of_three_sq_primes_seven_thirty_seven_of_val_seven_ge_seven_of_val_thirty_seven_ge_four
    {m r : ℕ} (hm : m ≠ 0) (hr : r.Prime) (hr211 : 211 ≤ r) (hr1296 : r ≤ 1296)
    (h : 5 * σ 1 m = 6 * usigma m)
    (hk7 : 7 ≤ padicValNat 7 m) (hk37 : 4 ≤ padicValNat 37 m)
    (hkr : 2 ≤ padicValNat r m)
    (hs : Squarefree (ordCompl[r] (ordCompl[37] (ordCompl[7] m)))) :
    False := by
  have hp7 : Nat.Prime 7 := by decide
  have hp37 : Nat.Prime 37 := by decide
  have hpq_ne : (7 : ℕ) ≠ 37 := by decide
  have hpr_ne : (7 : ℕ) ≠ r :=
    Nat.ne_of_lt (lt_of_lt_of_le (by decide : 7 < 211) hr211)
  have hqr_ne : (37 : ℕ) ≠ r :=
    Nat.ne_of_lt (lt_of_lt_of_le (by decide : 37 < 211) hr211)
  have heq := five_sigma_eq_six_of_three_squareful hm hp7 hp37 hr hpq_ne hpr_ne
    hqr_ne h hs
  have hproj_p : ordProj[7] m = 7 ^ padicValNat 7 m := by
    simp [Nat.factorization_def m hp7]
  have hproj_q : ordProj[37] (ordCompl[7] m) =
      37 ^ padicValNat 37 (ordCompl[7] m) := by
    simp [Nat.factorization_def (ordCompl[7] m) hp37]
  have hproj_r : ordProj[r] (ordCompl[37] (ordCompl[7] m)) =
      r ^ padicValNat r (ordCompl[37] (ordCompl[7] m)) := by
    simp [Nat.factorization_def (ordCompl[37] (ordCompl[7] m)) hr]
  rw [hproj_r, padicValNat_ordCompl_of_ne hr hqr_ne,
    padicValNat_ordCompl_of_ne hr hpr_ne, hproj_q,
    padicValNat_ordCompl_of_ne hp37 hpq_ne, hproj_p] at heq
  have hr1291 : r ≤ 1291 :=
    prime_le_one_two_nine_six_le_one_two_nine_one hr hr1296
  have hover := seven_pow_seven_thirty_seven_fourth_r_pow_ge_two_overshoot_six_five
    hr hr211 hr1291 hk7 hk37 hkr
  rw [← heq] at hover
  exact lt_irrefl _ hover

lemma prime_ge_one_two_nine_six_ge_one_two_nine_seven {p : ℕ} (hp : p.Prime)
    (h : 1296 ≤ p) : 1297 ≤ p := by
  have hmem : p = 1296 ∨ 1297 ≤ p := by omega
  rcases hmem with rfl | h1297
  · exact False.elim (not_prime_of_eq_mul (rfl : 1296 = 2 * 648)
      (by decide : (2 : ℕ) ≠ 1) (by decide : (648 : ℕ) ≠ 1) hp)
  · exact h1297

lemma five_seven_thirty_seven_r_euler_cap {r : ℕ} (hr : 1297 ≤ r) :
    5 * 7 * 37 * r ≤ 6 * 6 * 36 * (r - 1) := by
  have hdiff : 1296 ≤ r :=
    le_trans (by decide : (1296 : ℕ) ≤ 1297) hr
  have hL : 5 * 7 * 37 * r = 1295 * r := by ring
  have hR : 6 * 6 * 36 * (r - 1) = 1296 * (r - 1) := by ring
  have hmain : 1295 * r ≤ 1296 * (r - 1) := by
    have heq : 1295 * r + r = 1296 * r := by ring
    have hsub : 1295 * r = 1296 * r - r :=
      (Nat.sub_eq_of_eq_add heq.symm).symm
    have hle : 1296 * r - r ≤ 1296 * r - 1296 :=
      Nat.sub_le_sub_left hdiff _
    have hrw : 1296 * r - 1296 = 1296 * (r - 1) := by
      simpa using (Nat.mul_sub_left_distrib 1296 r 1).symm
    calc
      1295 * r = 1296 * r - r := hsub
      _ ≤ 1296 * r - 1296 := hle
      _ = 1296 * (r - 1) := hrw
  rw [hL, hR]
  exact hmain

lemma five_sigma_lt_six_usigma_seven_thirty_seven_euler_large {r a b c : ℕ}
    (hr : r.Prime) (hr1297 : 1297 ≤ r) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    5 * σ 1 (7 ^ a) * σ 1 (37 ^ b) * σ 1 (r ^ c) <
      6 * usigma (7 ^ a) * usigma (37 ^ b) * usigma (r ^ c) := by
  have hp7 : Nat.Prime 7 := by decide
  have hp37 : Nat.Prime 37 := by decide
  have h7 := sigma_lt_cap_usigma hp7 ha
  have h37 := sigma_lt_cap_usigma hp37 hb
  have hrcap := sigma_lt_cap_usigma hr hc
  have hu7 : 0 < usigma (7 ^ a) := by
    rw [usigma_prime_pow hp7 ha]
    exact Nat.add_pos_left (by decide : 0 < 1) _
  have hu37 : 0 < usigma (37 ^ b) := by
    rw [usigma_prime_pow hp37 hb]
    exact Nat.add_pos_left (by decide : 0 < 1) _
  have hthis := six_five_of_three_caps (A := 6) (B := 7) (X := σ 1 (7 ^ a))
    (Y := usigma (7 ^ a)) (C := 36) (D := 37) (P := σ 1 (37 ^ b))
    (Q := usigma (37 ^ b)) (E := r - 1) (F := r) (R := σ 1 (r ^ c))
    (S := usigma (r ^ c)) h7 h37 hrcap (five_seven_thirty_seven_r_euler_cap hr1297)
    (by decide : 0 < 7) hu7 (by decide : 0 < 37) hu37
  simpa [mul_assoc, mul_left_comm, mul_comm] using hthis

/-- Leftover `6/5` cannot be three squareful primes `7,37,r` with
`r ≥ 1297` times a squarefree coprime factor. -/
lemma not_five_sigma_of_three_sq_primes_seven_thirty_seven_of_r_ge_one_two_nine_seven
    {m r : ℕ} (hm : m ≠ 0) (hr : r.Prime) (hr1297 : 1297 ≤ r)
    (h : 5 * σ 1 m = 6 * usigma m)
    (hk7 : 2 ≤ padicValNat 7 m) (hk37 : 2 ≤ padicValNat 37 m)
    (hkr : 2 ≤ padicValNat r m)
    (hs : Squarefree (ordCompl[r] (ordCompl[37] (ordCompl[7] m)))) :
    False := by
  have hp7 : Nat.Prime 7 := by decide
  have hp37 : Nat.Prime 37 := by decide
  have hpq_ne : (7 : ℕ) ≠ 37 := by decide
  have hpr_ne : (7 : ℕ) ≠ r :=
    Nat.ne_of_lt (lt_of_lt_of_le (by decide : 7 < 1297) hr1297)
  have hqr_ne : (37 : ℕ) ≠ r :=
    Nat.ne_of_lt (lt_of_lt_of_le (by decide : 37 < 1297) hr1297)
  have heq := five_sigma_eq_six_of_three_squareful hm hp7 hp37 hr hpq_ne hpr_ne
    hqr_ne h hs
  have hproj_p : ordProj[7] m = 7 ^ padicValNat 7 m := by
    simp [Nat.factorization_def m hp7]
  have hproj_q : ordProj[37] (ordCompl[7] m) =
      37 ^ padicValNat 37 (ordCompl[7] m) := by
    simp [Nat.factorization_def (ordCompl[7] m) hp37]
  have hproj_r : ordProj[r] (ordCompl[37] (ordCompl[7] m)) =
      r ^ padicValNat r (ordCompl[37] (ordCompl[7] m)) := by
    simp [Nat.factorization_def (ordCompl[37] (ordCompl[7] m)) hr]
  rw [hproj_r, padicValNat_ordCompl_of_ne hr hqr_ne,
    padicValNat_ordCompl_of_ne hr hpr_ne, hproj_q,
    padicValNat_ordCompl_of_ne hp37 hpq_ne, hproj_p] at heq
  exact (five_sigma_lt_six_usigma_seven_thirty_seven_euler_large hr hr1297
    (lt_of_lt_of_le (by decide : (0 : ℕ) < 2) hk7)
    (lt_of_lt_of_le (by decide : (0 : ℕ) < 2) hk37)
    ((Nat.zero_lt_succ 1).trans_le hkr)).ne heq

/-- Leftover `6/5` cannot be three squareful primes `7,37,r` with `r ≥ 41`
times a squarefree coprime factor. -/
lemma not_five_sigma_of_three_sq_primes_seven_thirty_seven {m r : ℕ}
    (hm : m ≠ 0) (hr : r.Prime) (hr41 : 41 ≤ r)
    (h : 5 * σ 1 m = 6 * usigma m)
    (hk7 : 2 ≤ padicValNat 7 m) (hk37 : 2 ≤ padicValNat 37 m)
    (hkr : 2 ≤ padicValNat r m)
    (hs : Squarefree (ordCompl[r] (ordCompl[37] (ordCompl[7] m)))) :
    False := by
  rcases le_or_gt r 205 with h205 | h206
  · exact not_five_sigma_of_three_sq_primes_seven_thirty_seven_of_r_le_two_hundred_five
      hm hr hr41 h205 h hk7 hk37 hkr hs
  · have hr211 : 211 ≤ r :=
      prime_ge_two_hundred_six_ge_two_hundred_eleven hr (Nat.succ_le_of_lt h206)
    rcases le_or_gt r 1296 with h1296 | h1297gt
    · rcases le_or_gt (padicValNat 7 m) 6 with hk7le | hk7gt
      · rcases eq_or_lt_of_le hk7 with h7eq | h73
        · exact not_five_sigma_of_three_sq_primes_seven_thirty_seven_of_val_seven_eq_two
            hm hr (lt_of_lt_of_le (by decide : (43 : ℕ) < 211) hr211).le h h7eq.symm
            hk37 hkr hs
        · have h3le : 3 ≤ padicValNat 7 m := Nat.succ_le_of_lt h73
          rcases eq_or_lt_of_le h3le with h7eq3 | h74
          · exact not_five_sigma_of_three_sq_primes_seven_thirty_seven_of_val_seven_eq_three
              hm hr hr211 h h7eq3.symm hk37 hkr hs
          · have h4le : 4 ≤ padicValNat 7 m := Nat.succ_le_of_lt h74
            rcases eq_or_lt_of_le h4le with h7eq4 | h75
            · exact not_five_sigma_of_three_sq_primes_seven_thirty_seven_of_val_seven_eq_four
                hm hr hr211 h h7eq4.symm hk37 hkr hs
            · have h5le : 5 ≤ padicValNat 7 m := Nat.succ_le_of_lt h75
              rcases eq_or_lt_of_le h5le with h7eq5 | h76
              · exact
                  not_five_sigma_of_three_sq_primes_seven_thirty_seven_of_val_seven_eq_five
                    hm hr hr211 h h7eq5.symm hk37 hkr hs
              · have h7eq6 : padicValNat 7 m = 6 :=
                  le_antisymm hk7le (Nat.succ_le_of_lt h76)
                exact
                  not_five_sigma_of_three_sq_primes_seven_thirty_seven_of_val_seven_eq_six
                    hm hr hr211 h h7eq6 hk37 hkr hs
      · have h7ge : 7 ≤ padicValNat 7 m := Nat.succ_le_of_lt hk7gt
        rcases eq_or_lt_of_le hk37 with h37eq | h373
        · exact
            not_five_sigma_of_three_sq_primes_seven_thirty_seven_of_val_seven_ge_seven_of_val_thirty_seven_eq_two
              hm hr hr211 h h7ge h37eq.symm hkr hs
        · have h3le : 3 ≤ padicValNat 37 m := Nat.succ_le_of_lt h373
          rcases eq_or_lt_of_le h3le with h37eq3 | h374
          · exact
              not_five_sigma_of_three_sq_primes_seven_thirty_seven_of_val_seven_ge_seven_of_val_thirty_seven_eq_three
                hm hr hr211 h h7ge h37eq3.symm hkr hs
          · exact
              not_five_sigma_of_three_sq_primes_seven_thirty_seven_of_val_seven_ge_seven_of_val_thirty_seven_ge_four
                hm hr hr211 h1296 h h7ge (Nat.succ_le_of_lt h374) hkr hs
    · have hr1297 : 1297 ≤ r := Nat.succ_le_of_lt h1297gt
      exact not_five_sigma_of_three_sq_primes_seven_thirty_seven_of_r_ge_one_two_nine_seven
        hm hr hr1297 h hk7 hk37 hkr hs

lemma five_mul_forty_nine_forty_one_cap {r : ℕ} (hr : 43 ≤ r) :
    5 * 41 * r * 57 ≤ 6 * 40 * (r - 1) * 50 := by
  have hdiff : 12000 ≤ 315 * r := by
    have hmul : 315 * 43 ≤ 315 * r := Nat.mul_le_mul_left 315 hr
    have hnum : 315 * 43 = 13545 := by decide
    omega
  have hL : 5 * 41 * r * 57 = 11685 * r := by ring
  have hR : 6 * 40 * (r - 1) * 50 = 12000 * (r - 1) := by ring
  have hmain : 11685 * r ≤ 12000 * (r - 1) := by
    have heq : 11685 * r + 315 * r = 12000 * r := by ring
    have hsub : 11685 * r = 12000 * r - 315 * r :=
      (Nat.sub_eq_of_eq_add heq.symm).symm
    have hle : 12000 * r - 315 * r ≤ 12000 * r - 12000 :=
      Nat.sub_le_sub_left hdiff _
    have hrw : 12000 * r - 12000 = 12000 * (r - 1) := by
      simpa using (Nat.mul_sub_left_distrib 12000 r 1).symm
    calc
      11685 * r = 12000 * r - 315 * r := hsub
      _ ≤ 12000 * r - 12000 := hle
      _ = 12000 * (r - 1) := hrw
  rw [hL, hR]
  exact hmain

lemma five_sigma_lt_six_usigma_seven_sq_forty_one_large {r b c : ℕ}
    (hr : r.Prime) (hr43 : 43 ≤ r) (hb : 0 < b) (hc : 0 < c) :
    5 * σ 1 (7 ^ 2) * σ 1 (41 ^ b) * σ 1 (r ^ c) <
      6 * usigma (7 ^ 2) * usigma (41 ^ b) * usigma (r ^ c) := by
  have hp7 : Nat.Prime 7 := by decide
  have hσ7 : σ 1 (7 ^ 2) = 57 := by
    rw [sigma_prime_pow_two hp7]
    decide
  have hu7 : usigma (7 ^ 2) = 50 := by
    simpa using usigma_prime_pow hp7 (by decide : 0 < 2)
  rw [hσ7, hu7]
  have h41 := sigma_lt_cap_usigma (by decide : Nat.Prime 41) hb
  have hrcap := sigma_lt_cap_usigma hr hc
  have hu41 : 0 < usigma (41 ^ b) := by
    rw [usigma_prime_pow (by decide : Nat.Prime 41) hb]
    exact Nat.add_pos_left (by decide : 0 < 1) _
  have hthis := six_five_of_two_caps_times_const (A := 40) (B := 41)
    (X := σ 1 (41 ^ b)) (Y := usigma (41 ^ b)) (C := r - 1) (D := r)
    (P := σ 1 (r ^ c)) (Q := usigma (r ^ c)) (S := 50) (T := 57)
    h41 hrcap (five_mul_forty_nine_forty_one_cap hr43)
    (by decide : 0 < 41) hu41 (by decide : 0 < 57)
  convert hthis using 1 <;> ring

lemma prime_ge_two_hundred_eighty_eight_ge_two_hundred_ninety_three {p : ℕ}
    (hp : p.Prime) (h : 288 ≤ p) : 293 ≤ p := by
  have hmem : p = 288 ∨ p = 289 ∨ p = 290 ∨ p = 291 ∨ p = 292 ∨
      293 ≤ p := by omega
  rcases hmem with rfl | rfl | rfl | rfl | rfl | h293
  · exact False.elim (not_prime_of_eq_mul (rfl : 288 = 2 * 144)
      (by decide : (2 : ℕ) ≠ 1) (by decide : (144 : ℕ) ≠ 1) hp)
  · exact False.elim (not_prime_of_eq_mul (rfl : 289 = 17 * 17)
      (by decide : (17 : ℕ) ≠ 1) (by decide : (17 : ℕ) ≠ 1) hp)
  · exact False.elim (not_prime_of_eq_mul (rfl : 290 = 2 * 145)
      (by decide : (2 : ℕ) ≠ 1) (by decide : (145 : ℕ) ≠ 1) hp)
  · exact False.elim (not_prime_of_eq_mul (rfl : 291 = 3 * 97)
      (by decide : (3 : ℕ) ≠ 1) (by decide : (97 : ℕ) ≠ 1) hp)
  · exact False.elim (not_prime_of_eq_mul (rfl : 292 = 2 * 146)
      (by decide : (2 : ℕ) ≠ 1) (by decide : (146 : ℕ) ≠ 1) hp)
  · exact h293

lemma five_seven_forty_one_r_euler_cap {r : ℕ} (hr : 293 ≤ r) :
    5 * 7 * 41 * r ≤ 6 * 6 * 40 * (r - 1) := by
  have hdiff : 1440 ≤ 5 * r := by
    have hmul : 5 * 293 ≤ 5 * r := Nat.mul_le_mul_left 5 hr
    have hnum : 5 * 293 = 1465 := by decide
    omega
  have hL : 5 * 7 * 41 * r = 1435 * r := by ring
  have hR : 6 * 6 * 40 * (r - 1) = 1440 * (r - 1) := by ring
  have hmain : 1435 * r ≤ 1440 * (r - 1) := by
    have heq : 1435 * r + 5 * r = 1440 * r := by ring
    have hsub : 1435 * r = 1440 * r - 5 * r :=
      (Nat.sub_eq_of_eq_add heq.symm).symm
    have hle : 1440 * r - 5 * r ≤ 1440 * r - 1440 :=
      Nat.sub_le_sub_left hdiff _
    have hrw : 1440 * r - 1440 = 1440 * (r - 1) := by
      simpa using (Nat.mul_sub_left_distrib 1440 r 1).symm
    calc
      1435 * r = 1440 * r - 5 * r := hsub
      _ ≤ 1440 * r - 1440 := hle
      _ = 1440 * (r - 1) := hrw
  rw [hL, hR]
  exact hmain

lemma five_sigma_lt_six_usigma_seven_forty_one_euler_large {r a b c : ℕ}
    (hr : r.Prime) (hr293 : 293 ≤ r) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    5 * σ 1 (7 ^ a) * σ 1 (41 ^ b) * σ 1 (r ^ c) <
      6 * usigma (7 ^ a) * usigma (41 ^ b) * usigma (r ^ c) := by
  have hp7 : Nat.Prime 7 := by decide
  have hp41 : Nat.Prime 41 := by decide
  have h7 := sigma_lt_cap_usigma hp7 ha
  have h41 := sigma_lt_cap_usigma hp41 hb
  have hrcap := sigma_lt_cap_usigma hr hc
  have hu7 : 0 < usigma (7 ^ a) := by
    rw [usigma_prime_pow hp7 ha]
    exact Nat.add_pos_left (by decide : 0 < 1) _
  have hu41 : 0 < usigma (41 ^ b) := by
    rw [usigma_prime_pow hp41 hb]
    exact Nat.add_pos_left (by decide : 0 < 1) _
  have hthis := six_five_of_three_caps (A := 6) (B := 7) (X := σ 1 (7 ^ a))
    (Y := usigma (7 ^ a)) (C := 40) (D := 41) (P := σ 1 (41 ^ b))
    (Q := usigma (41 ^ b)) (E := r - 1) (F := r) (R := σ 1 (r ^ c))
    (S := usigma (r ^ c)) h7 h41 hrcap (five_seven_forty_one_r_euler_cap hr293)
    (by decide : 0 < 7) hu7 (by decide : 0 < 41) hu41
  simpa [mul_assoc, mul_left_comm, mul_comm] using hthis

/-- Leftover `6/5` cannot be three squareful primes `7,41,r` with `r ≥ 43`
and `v₇ = 2` times a squarefree coprime factor. -/
lemma not_five_sigma_of_three_sq_primes_seven_forty_one_of_val_seven_eq_two
    {m r : ℕ} (hm : m ≠ 0) (hr : r.Prime) (hr43 : 43 ≤ r)
    (h : 5 * σ 1 m = 6 * usigma m)
    (hk7 : padicValNat 7 m = 2) (hk41 : 2 ≤ padicValNat 41 m)
    (hkr : 2 ≤ padicValNat r m)
    (hs : Squarefree (ordCompl[r] (ordCompl[41] (ordCompl[7] m)))) :
    False := by
  have hp7 : Nat.Prime 7 := by decide
  have hp41 : Nat.Prime 41 := by decide
  have hpq_ne : (7 : ℕ) ≠ 41 := by decide
  have hpr_ne : (7 : ℕ) ≠ r :=
    Nat.ne_of_lt (lt_of_lt_of_le (by decide : 7 < 43) hr43)
  have hqr_ne : (41 : ℕ) ≠ r :=
    Nat.ne_of_lt (lt_of_lt_of_le (by decide : 41 < 43) hr43)
  have heq := five_sigma_eq_six_of_three_squareful hm hp7 hp41 hr hpq_ne hpr_ne
    hqr_ne h hs
  have hproj_p : ordProj[7] m = 7 ^ padicValNat 7 m := by
    simp [Nat.factorization_def m hp7]
  have hproj_q : ordProj[41] (ordCompl[7] m) =
      41 ^ padicValNat 41 (ordCompl[7] m) := by
    simp [Nat.factorization_def (ordCompl[7] m) hp41]
  have hproj_r : ordProj[r] (ordCompl[41] (ordCompl[7] m)) =
      r ^ padicValNat r (ordCompl[41] (ordCompl[7] m)) := by
    simp [Nat.factorization_def (ordCompl[41] (ordCompl[7] m)) hr]
  rw [hproj_r, padicValNat_ordCompl_of_ne hr hqr_ne,
    padicValNat_ordCompl_of_ne hr hpr_ne, hproj_q,
    padicValNat_ordCompl_of_ne hp41 hpq_ne, hproj_p, hk7] at heq
  exact (five_sigma_lt_six_usigma_seven_sq_forty_one_large hr hr43
    (lt_of_lt_of_le (by decide : (0 : ℕ) < 2) hk41)
    (lt_of_lt_of_le (by decide : (0 : ℕ) < 2) hkr)).ne heq

/-- Leftover `6/5` cannot be three squareful primes `7,41,r` with
`r ≥ 293` times a squarefree coprime factor. -/
lemma not_five_sigma_of_three_sq_primes_seven_forty_one_of_r_ge_two_hundred_ninety_three
    {m r : ℕ} (hm : m ≠ 0) (hr : r.Prime) (hr293 : 293 ≤ r)
    (h : 5 * σ 1 m = 6 * usigma m)
    (hk7 : 2 ≤ padicValNat 7 m) (hk41 : 2 ≤ padicValNat 41 m)
    (hkr : 2 ≤ padicValNat r m)
    (hs : Squarefree (ordCompl[r] (ordCompl[41] (ordCompl[7] m)))) :
    False := by
  have hp7 : Nat.Prime 7 := by decide
  have hp41 : Nat.Prime 41 := by decide
  have hpq_ne : (7 : ℕ) ≠ 41 := by decide
  have hpr_ne : (7 : ℕ) ≠ r :=
    Nat.ne_of_lt (lt_of_lt_of_le (by decide : 7 < 293) hr293)
  have hqr_ne : (41 : ℕ) ≠ r :=
    Nat.ne_of_lt (lt_of_lt_of_le (by decide : 41 < 293) hr293)
  have heq := five_sigma_eq_six_of_three_squareful hm hp7 hp41 hr hpq_ne hpr_ne
    hqr_ne h hs
  have hproj_p : ordProj[7] m = 7 ^ padicValNat 7 m := by
    simp [Nat.factorization_def m hp7]
  have hproj_q : ordProj[41] (ordCompl[7] m) =
      41 ^ padicValNat 41 (ordCompl[7] m) := by
    simp [Nat.factorization_def (ordCompl[7] m) hp41]
  have hproj_r : ordProj[r] (ordCompl[41] (ordCompl[7] m)) =
      r ^ padicValNat r (ordCompl[41] (ordCompl[7] m)) := by
    simp [Nat.factorization_def (ordCompl[41] (ordCompl[7] m)) hr]
  rw [hproj_r, padicValNat_ordCompl_of_ne hr hqr_ne,
    padicValNat_ordCompl_of_ne hr hpr_ne, hproj_q,
    padicValNat_ordCompl_of_ne hp41 hpq_ne, hproj_p] at heq
  exact (five_sigma_lt_six_usigma_seven_forty_one_euler_large hr hr293
    (lt_of_lt_of_le (by decide : (0 : ℕ) < 2) hk7)
    (lt_of_lt_of_le (by decide : (0 : ℕ) < 2) hk41)
    ((Nat.zero_lt_succ 1).trans_le hkr)).ne heq

lemma seven_cube_forty_one_sq_r_sq_overshoot_six_five {r : ℕ}
    (hr : r.Prime) (h43 : 43 ≤ r) (h131 : r ≤ 131) :
    6 * usigma (7 ^ 3) * usigma (41 ^ 2) * usigma (r ^ 2) <
      5 * σ 1 (7 ^ 3) * σ 1 (41 ^ 2) * σ 1 (r ^ 2) := by
  rw [usigma_seven_pow_three, sigma_seven_pow_three,
    sigma_forty_one_pow_two, usigma_forty_one_pow_two,
    sigma_prime_pow_two hr, usigma_prime_pow hr (by decide : 0 < 2)]
  have hsq : r ^ 2 ≤ 131 * r := by
    rw [pow_two]
    exact Nat.mul_le_mul_right r h131
  have hleft : 25648 * (1 + r ^ 2) < 3446000 * r := by
    have h1 : 25648 * (1 + r ^ 2) ≤ 25648 * (1 + 131 * r) :=
      Nat.mul_le_mul_left 25648 (Nat.add_le_add_left hsq 1)
    have h2 : 25648 * (1 + 131 * r) = 25648 + 3359888 * r := by
      have : 25648 * 131 = 3359888 := by decide
      ring
    have h3 : 25648 + 3359888 * r < 3446000 * r := by
      have : 25648 < 86112 * r :=
        lt_of_lt_of_le (by decide : 25648 < 3702816)
          (Nat.mul_le_mul_left 86112 h43)
      omega
    calc
      25648 * (1 + r ^ 2) ≤ 25648 * (1 + 131 * r) := h1
      _ = 25648 + 3359888 * r := h2
      _ < 3446000 * r := h3
  have hL : 6 * 344 * 1682 * (1 + r ^ 2) = 3471648 * (1 + r ^ 2) := by ring
  have hR : 5 * 400 * 1723 * (1 + r + r ^ 2) = 3446000 * (1 + r + r ^ 2) :=
    by ring
  have hmain : 3471648 * (1 + r ^ 2) < 3446000 * (1 + r + r ^ 2) := by
    have h1 : 3471648 * (1 + r ^ 2) =
        3446000 * (1 + r ^ 2) + 25648 * (1 + r ^ 2) := by ring
    have h2 : 3446000 * (1 + r + r ^ 2) =
        3446000 * (1 + r ^ 2) + 3446000 * r := by ring
    rw [h1, h2]
    exact Nat.add_lt_add_left hleft _
  rw [hL, hR]
  exact hmain

lemma seven_cube_forty_one_r_sq_pow_ge_two_overshoot_six_five
    {r a b c : ℕ} (hr : r.Prime) (h43 : 43 ≤ r) (h131 : r ≤ 131)
    (ha : 3 ≤ a) (hb : 2 ≤ b) (hc : 2 ≤ c) :
    6 * usigma (7 ^ a) * usigma (41 ^ b) * usigma (r ^ c) <
      5 * σ 1 (7 ^ a) * σ 1 (41 ^ b) * σ 1 (r ^ c) :=
  six_five_overshoot_mono_three (by decide : Nat.Prime 7)
    (by decide : Nat.Prime 41) hr
    (by decide : 0 < 3) (by decide : 0 < 2) (by decide : 0 < 2)
    ha hb hc (seven_cube_forty_one_sq_r_sq_overshoot_six_five hr h43 h131)

lemma prime_ge_one_three_two_ge_one_three_seven {p : ℕ} (hp : p.Prime)
    (h : 132 ≤ p) : 137 ≤ p := by
  have hmem : p = 132 ∨ p = 133 ∨ p = 134 ∨ p = 135 ∨ p = 136 ∨
      137 ≤ p := by omega
  rcases hmem with rfl | rfl | rfl | rfl | rfl | h137
  · exact False.elim (not_prime_of_eq_mul (rfl : 132 = 2 * 66)
      (by decide : (2 : ℕ) ≠ 1) (by decide : (66 : ℕ) ≠ 1) hp)
  · exact False.elim (not_prime_of_eq_mul (rfl : 133 = 7 * 19)
      (by decide : (7 : ℕ) ≠ 1) (by decide : (19 : ℕ) ≠ 1) hp)
  · exact False.elim (not_prime_of_eq_mul (rfl : 134 = 2 * 67)
      (by decide : (2 : ℕ) ≠ 1) (by decide : (67 : ℕ) ≠ 1) hp)
  · exact False.elim (not_prime_of_eq_mul (rfl : 135 = 5 * 27)
      (by decide : (5 : ℕ) ≠ 1) (by decide : (27 : ℕ) ≠ 1) hp)
  · exact False.elim (not_prime_of_eq_mul (rfl : 136 = 2 * 68)
      (by decide : (2 : ℕ) ≠ 1) (by decide : (68 : ℕ) ≠ 1) hp)
  · exact h137

lemma five_mul_seven_cube_forty_one_sq_cap {r : ℕ} (hr : 137 ≤ r) :
    5 * r * 400 * 1723 ≤ 6 * (r - 1) * 344 * 1682 := by
  have hdiff : 3471648 ≤ 25648 * r := by
    have hmul : 25648 * 137 ≤ 25648 * r := Nat.mul_le_mul_left 25648 hr
    have hnum : 25648 * 137 = 3513776 := by decide
    omega
  have hL : 5 * r * 400 * 1723 = 3446000 * r := by ring
  have hR : 6 * (r - 1) * 344 * 1682 = 3471648 * (r - 1) := by ring
  have hmain : 3446000 * r ≤ 3471648 * (r - 1) := by
    have heq : 3446000 * r + 25648 * r = 3471648 * r := by ring
    have hsub : 3446000 * r = 3471648 * r - 25648 * r :=
      (Nat.sub_eq_of_eq_add heq.symm).symm
    have hle : 3471648 * r - 25648 * r ≤ 3471648 * r - 3471648 :=
      Nat.sub_le_sub_left hdiff _
    have hrw : 3471648 * r - 3471648 = 3471648 * (r - 1) := by
      simpa using (Nat.mul_sub_left_distrib 3471648 r 1).symm
    calc
      3446000 * r = 3471648 * r - 25648 * r := hsub
      _ ≤ 3471648 * r - 3471648 := hle
      _ = 3471648 * (r - 1) := hrw
  rw [hL, hR]
  exact hmain

lemma five_sigma_lt_six_usigma_seven_cube_forty_one_sq_large {r k : ℕ}
    (hr : r.Prime) (hr137 : 137 ≤ r) (hk : 0 < k) :
    5 * σ 1 (7 ^ 3) * σ 1 (41 ^ 2) * σ 1 (r ^ k) <
      6 * usigma (7 ^ 3) * usigma (41 ^ 2) * usigma (r ^ k) := by
  rw [sigma_seven_pow_three, usigma_seven_pow_three,
    sigma_forty_one_pow_two, usigma_forty_one_pow_two]
  have hcp := sigma_lt_cap_usigma hr hk
  have hthis := six_five_of_cap_times_const (A := r - 1) (B := r)
    (X := σ 1 (r ^ k)) (Y := usigma (r ^ k)) (S := 344 * 1682)
    (T := 400 * 1723) hcp (by
      have hL : 5 * r * (400 * 1723) = 5 * r * 400 * 1723 := by ring
      have hR : 6 * (r - 1) * (344 * 1682) = 6 * (r - 1) * 344 * 1682 :=
        by ring
      rw [hL, hR]
      exact five_mul_seven_cube_forty_one_sq_cap hr137)
    (by decide : 0 < 400 * 1723)
  convert hthis using 1 <;> ring

lemma seven_cube_forty_one_cube_r_sq_overshoot_six_five {r : ℕ}
    (hr : r.Prime) (h137 : 137 ≤ r) (h139 : r ≤ 139) :
    6 * usigma (7 ^ 3) * usigma (41 ^ 3) * usigma (r ^ 2) <
      5 * σ 1 (7 ^ 3) * σ 1 (41 ^ 3) * σ 1 (r ^ 2) := by
  rw [usigma_seven_pow_three, sigma_seven_pow_three,
    sigma_forty_one_pow_three, usigma_forty_one_pow_three,
    sigma_prime_pow_two hr, usigma_prime_pow hr (by decide : 0 < 2)]
  have hsq : r ^ 2 ≤ 139 * r := by
    rw [pow_two]
    exact Nat.mul_le_mul_right r h139
  have hleft : 967008 * (1 + r ^ 2) < 141288000 * r := by
    have h1 : 967008 * (1 + r ^ 2) ≤ 967008 * (1 + 139 * r) :=
      Nat.mul_le_mul_left 967008 (Nat.add_le_add_left hsq 1)
    have h2 : 967008 * (1 + 139 * r) = 967008 + 134414112 * r := by
      have : 967008 * 139 = 134414112 := by decide
      ring
    have h3 : 967008 + 134414112 * r < 141288000 * r := by
      have : 967008 < 6873888 * r :=
        lt_of_lt_of_le (by decide : 967008 < 941722656)
          (Nat.mul_le_mul_left 6873888 h137)
      omega
    calc
      967008 * (1 + r ^ 2) ≤ 967008 * (1 + 139 * r) := h1
      _ = 967008 + 134414112 * r := h2
      _ < 141288000 * r := h3
  have hL : 6 * 344 * 68922 * (1 + r ^ 2) = 142255008 * (1 + r ^ 2) :=
    by ring
  have hR : 5 * 400 * 70644 * (1 + r + r ^ 2) = 141288000 * (1 + r + r ^ 2) :=
    by ring
  have hmain : 142255008 * (1 + r ^ 2) < 141288000 * (1 + r + r ^ 2) := by
    have h1 : 142255008 * (1 + r ^ 2) =
        141288000 * (1 + r ^ 2) + 967008 * (1 + r ^ 2) := by ring
    have h2 : 141288000 * (1 + r + r ^ 2) =
        141288000 * (1 + r ^ 2) + 141288000 * r := by ring
    rw [h1, h2]
    exact Nat.add_lt_add_left hleft _
  rw [hL, hR]
  exact hmain

lemma seven_cube_forty_one_cube_r_pow_ge_two_overshoot_six_five
    {r a b c : ℕ} (hr : r.Prime) (h137 : 137 ≤ r) (h139 : r ≤ 139)
    (ha : 3 ≤ a) (hb : 3 ≤ b) (hc : 2 ≤ c) :
    6 * usigma (7 ^ a) * usigma (41 ^ b) * usigma (r ^ c) <
      5 * σ 1 (7 ^ a) * σ 1 (41 ^ b) * σ 1 (r ^ c) :=
  six_five_overshoot_mono_three (by decide : Nat.Prime 7)
    (by decide : Nat.Prime 41) hr
    (by decide : 0 < 3) (by decide : 0 < 3) (by decide : 0 < 2)
    ha hb hc (seven_cube_forty_one_cube_r_sq_overshoot_six_five hr h137 h139)

lemma prime_ge_one_four_zero_ge_one_four_nine {p : ℕ} (hp : p.Prime)
    (h : 140 ≤ p) : 149 ≤ p := by
  have hmem : p = 140 ∨ p = 141 ∨ p = 142 ∨ p = 143 ∨ p = 144 ∨ p = 145 ∨
      p = 146 ∨ p = 147 ∨ p = 148 ∨ 149 ≤ p := by omega
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | h149
  · exact False.elim (not_prime_of_eq_mul (rfl : 140 = 2 * 70)
      (by decide : (2 : ℕ) ≠ 1) (by decide : (70 : ℕ) ≠ 1) hp)
  · exact False.elim (not_prime_of_eq_mul (rfl : 141 = 3 * 47)
      (by decide : (3 : ℕ) ≠ 1) (by decide : (47 : ℕ) ≠ 1) hp)
  · exact False.elim (not_prime_of_eq_mul (rfl : 142 = 2 * 71)
      (by decide : (2 : ℕ) ≠ 1) (by decide : (71 : ℕ) ≠ 1) hp)
  · exact False.elim (not_prime_of_eq_mul (rfl : 143 = 11 * 13)
      (by decide : (11 : ℕ) ≠ 1) (by decide : (13 : ℕ) ≠ 1) hp)
  · exact False.elim (not_prime_of_eq_mul (rfl : 144 = 2 * 72)
      (by decide : (2 : ℕ) ≠ 1) (by decide : (72 : ℕ) ≠ 1) hp)
  · exact False.elim (not_prime_of_eq_mul (rfl : 145 = 5 * 29)
      (by decide : (5 : ℕ) ≠ 1) (by decide : (29 : ℕ) ≠ 1) hp)
  · exact False.elim (not_prime_of_eq_mul (rfl : 146 = 2 * 73)
      (by decide : (2 : ℕ) ≠ 1) (by decide : (73 : ℕ) ≠ 1) hp)
  · exact False.elim (not_prime_of_eq_mul (rfl : 147 = 3 * 49)
      (by decide : (3 : ℕ) ≠ 1) (by decide : (49 : ℕ) ≠ 1) hp)
  · exact False.elim (not_prime_of_eq_mul (rfl : 148 = 2 * 74)
      (by decide : (2 : ℕ) ≠ 1) (by decide : (74 : ℕ) ≠ 1) hp)
  · exact h149

lemma five_mul_seven_cube_forty_one_euler_cap {r : ℕ} (hr : 149 ≤ r) :
    5 * 41 * r * 400 ≤ 6 * 40 * (r - 1) * 344 := by
  have hdiff : 82560 ≤ 560 * r := by
    have hmul : 560 * 149 ≤ 560 * r := Nat.mul_le_mul_left 560 hr
    have hnum : 560 * 149 = 83440 := by decide
    omega
  have hL : 5 * 41 * r * 400 = 82000 * r := by ring
  have hR : 6 * 40 * (r - 1) * 344 = 82560 * (r - 1) := by ring
  have hmain : 82000 * r ≤ 82560 * (r - 1) := by
    have heq : 82000 * r + 560 * r = 82560 * r := by ring
    have hsub : 82000 * r = 82560 * r - 560 * r :=
      (Nat.sub_eq_of_eq_add heq.symm).symm
    have hle : 82560 * r - 560 * r ≤ 82560 * r - 82560 :=
      Nat.sub_le_sub_left hdiff _
    have hrw : 82560 * r - 82560 = 82560 * (r - 1) := by
      simpa using (Nat.mul_sub_left_distrib 82560 r 1).symm
    calc
      82000 * r = 82560 * r - 560 * r := hsub
      _ ≤ 82560 * r - 82560 := hle
      _ = 82560 * (r - 1) := hrw
  rw [hL, hR]
  exact hmain

lemma five_sigma_lt_six_usigma_seven_cube_forty_one_large {r b c : ℕ}
    (hr : r.Prime) (hr149 : 149 ≤ r) (hb : 0 < b) (hc : 0 < c) :
    5 * σ 1 (7 ^ 3) * σ 1 (41 ^ b) * σ 1 (r ^ c) <
      6 * usigma (7 ^ 3) * usigma (41 ^ b) * usigma (r ^ c) := by
  rw [sigma_seven_pow_three, usigma_seven_pow_three]
  have h41 := sigma_lt_cap_usigma (by decide : Nat.Prime 41) hb
  have hrcap := sigma_lt_cap_usigma hr hc
  have hu41 : 0 < usigma (41 ^ b) := by
    rw [usigma_prime_pow (by decide : Nat.Prime 41) hb]
    exact Nat.add_pos_left (by decide : 0 < 1) _
  have hthis := six_five_of_two_caps_times_const (A := 40) (B := 41)
    (X := σ 1 (41 ^ b)) (Y := usigma (41 ^ b)) (C := r - 1) (D := r)
    (P := σ 1 (r ^ c)) (Q := usigma (r ^ c)) (S := 344) (T := 400)
    h41 hrcap (five_mul_seven_cube_forty_one_euler_cap hr149)
    (by decide : 0 < 41) hu41 (by decide : 0 < 400)
  convert hthis using 1 <;> ring

/-- Leftover `6/5` cannot be three squareful primes `7,41,r` with `r ≥ 43`
and `v₇ = 3` times a squarefree coprime factor. -/
lemma not_five_sigma_of_three_sq_primes_seven_forty_one_of_val_seven_eq_three
    {m r : ℕ} (hm : m ≠ 0) (hr : r.Prime) (hr43 : 43 ≤ r)
    (h : 5 * σ 1 m = 6 * usigma m)
    (hk7 : padicValNat 7 m = 3) (hk41 : 2 ≤ padicValNat 41 m)
    (hkr : 2 ≤ padicValNat r m)
    (hs : Squarefree (ordCompl[r] (ordCompl[41] (ordCompl[7] m)))) :
    False := by
  have hp7 : Nat.Prime 7 := by decide
  have hp41 : Nat.Prime 41 := by decide
  have hpq_ne : (7 : ℕ) ≠ 41 := by decide
  have hpr_ne : (7 : ℕ) ≠ r :=
    Nat.ne_of_lt (lt_of_lt_of_le (by decide : 7 < 43) hr43)
  have hqr_ne : (41 : ℕ) ≠ r :=
    Nat.ne_of_lt (lt_of_lt_of_le (by decide : 41 < 43) hr43)
  have heq := five_sigma_eq_six_of_three_squareful hm hp7 hp41 hr hpq_ne hpr_ne
    hqr_ne h hs
  have hproj_p : ordProj[7] m = 7 ^ padicValNat 7 m := by
    simp [Nat.factorization_def m hp7]
  have hproj_q : ordProj[41] (ordCompl[7] m) =
      41 ^ padicValNat 41 (ordCompl[7] m) := by
    simp [Nat.factorization_def (ordCompl[7] m) hp41]
  have hproj_r : ordProj[r] (ordCompl[41] (ordCompl[7] m)) =
      r ^ padicValNat r (ordCompl[41] (ordCompl[7] m)) := by
    simp [Nat.factorization_def (ordCompl[41] (ordCompl[7] m)) hr]
  rw [hproj_r, padicValNat_ordCompl_of_ne hr hqr_ne,
    padicValNat_ordCompl_of_ne hr hpr_ne, hproj_q,
    padicValNat_ordCompl_of_ne hp41 hpq_ne, hproj_p, hk7] at heq
  rcases le_or_gt r 131 with h131 | h132gt
  · have hover := seven_cube_forty_one_r_sq_pow_ge_two_overshoot_six_five
      hr hr43 h131 (le_refl _) hk41 hkr
    rw [← heq] at hover
    exact lt_irrefl _ hover
  · have hr137 : 137 ≤ r :=
      prime_ge_one_three_two_ge_one_three_seven hr (Nat.succ_le_of_lt h132gt)
    rcases eq_or_lt_of_le hk41 with h41eq | h413
    · rw [← h41eq] at heq
      exact (five_sigma_lt_six_usigma_seven_cube_forty_one_sq_large hr hr137
        ((Nat.zero_lt_succ 1).trans_le hkr)).ne heq
    · rcases le_or_gt r 139 with h139 | h140gt
      · have hover := seven_cube_forty_one_cube_r_pow_ge_two_overshoot_six_five
          hr hr137 h139 (le_refl _) (Nat.succ_le_of_lt h413) hkr
        rw [← heq] at hover
        exact lt_irrefl _ hover
      · have hr149 : 149 ≤ r :=
          prime_ge_one_four_zero_ge_one_four_nine hr (Nat.succ_le_of_lt h140gt)
        exact (five_sigma_lt_six_usigma_seven_cube_forty_one_large hr hr149
          (lt_of_lt_of_le (by decide : (0 : ℕ) < 2) hk41)
          ((Nat.zero_lt_succ 1).trans_le hkr)).ne heq

lemma seven_fourth_forty_one_sq_r_sq_overshoot_six_five {r : ℕ}
    (hr : r.Prime) (h43 : 43 ≤ r) (h211 : r ≤ 211) :
    6 * usigma (7 ^ 4) * usigma (41 ^ 2) * usigma (r ^ 2) <
      5 * σ 1 (7 ^ 4) * σ 1 (41 ^ 2) * σ 1 (r ^ 2) := by
  rw [usigma_seven_pow_four, sigma_seven_pow_four,
    sigma_forty_one_pow_two, usigma_forty_one_pow_two,
    sigma_prime_pow_two hr, usigma_prime_pow hr (by decide : 0 < 2)]
  have hsq : r ^ 2 ≤ 211 * r := by
    rw [pow_two]
    exact Nat.mul_le_mul_right r h211
  have hleft : 110369 * (1 + r ^ 2) < 24130615 * r := by
    have h1 : 110369 * (1 + r ^ 2) ≤ 110369 * (1 + 211 * r) :=
      Nat.mul_le_mul_left 110369 (Nat.add_le_add_left hsq 1)
    have h2 : 110369 * (1 + 211 * r) = 110369 + 23287859 * r := by
      have : 110369 * 211 = 23287859 := by decide
      ring
    have h3 : 110369 + 23287859 * r < 24130615 * r := by
      have : 110369 < 842756 * r :=
        lt_of_lt_of_le (by decide : 110369 < 36238508)
          (Nat.mul_le_mul_left 842756 h43)
      omega
    calc
      110369 * (1 + r ^ 2) ≤ 110369 * (1 + 211 * r) := h1
      _ = 110369 + 23287859 * r := h2
      _ < 24130615 * r := h3
  have hL : 6 * 2402 * 1682 * (1 + r ^ 2) = 24240984 * (1 + r ^ 2) := by ring
  have hR : 5 * 2801 * 1723 * (1 + r + r ^ 2) = 24130615 * (1 + r + r ^ 2) :=
    by ring
  have hmain : 24240984 * (1 + r ^ 2) < 24130615 * (1 + r + r ^ 2) := by
    have h1 : 24240984 * (1 + r ^ 2) =
        24130615 * (1 + r ^ 2) + 110369 * (1 + r ^ 2) := by ring
    have h2 : 24130615 * (1 + r + r ^ 2) =
        24130615 * (1 + r ^ 2) + 24130615 * r := by ring
    rw [h1, h2]
    exact Nat.add_lt_add_left hleft _
  rw [hL, hR]
  exact hmain

lemma seven_fourth_forty_one_r_sq_pow_ge_two_overshoot_six_five
    {r a b c : ℕ} (hr : r.Prime) (h43 : 43 ≤ r) (h211 : r ≤ 211)
    (ha : 4 ≤ a) (hb : 2 ≤ b) (hc : 2 ≤ c) :
    6 * usigma (7 ^ a) * usigma (41 ^ b) * usigma (r ^ c) <
      5 * σ 1 (7 ^ a) * σ 1 (41 ^ b) * σ 1 (r ^ c) :=
  six_five_overshoot_mono_three (by decide : Nat.Prime 7)
    (by decide : Nat.Prime 41) hr
    (by decide : 0 < 4) (by decide : 0 < 2) (by decide : 0 < 2)
    ha hb hc (seven_fourth_forty_one_sq_r_sq_overshoot_six_five hr h43 h211)

lemma prime_ge_two_hundred_twelve_ge_two_hundred_twenty_three {p : ℕ}
    (hp : p.Prime) (h : 212 ≤ p) : 223 ≤ p := by
  have hmem : p = 212 ∨ p = 213 ∨ p = 214 ∨ p = 215 ∨ p = 216 ∨ p = 217 ∨
      p = 218 ∨ p = 219 ∨ p = 220 ∨ p = 221 ∨ p = 222 ∨ 223 ≤ p := by omega
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | h223
  · exact False.elim (not_prime_of_eq_mul (rfl : 212 = 2 * 106)
      (by decide : (2 : ℕ) ≠ 1) (by decide : (106 : ℕ) ≠ 1) hp)
  · exact False.elim (not_prime_of_eq_mul (rfl : 213 = 3 * 71)
      (by decide : (3 : ℕ) ≠ 1) (by decide : (71 : ℕ) ≠ 1) hp)
  · exact False.elim (not_prime_of_eq_mul (rfl : 214 = 2 * 107)
      (by decide : (2 : ℕ) ≠ 1) (by decide : (107 : ℕ) ≠ 1) hp)
  · exact False.elim (not_prime_of_eq_mul (rfl : 215 = 5 * 43)
      (by decide : (5 : ℕ) ≠ 1) (by decide : (43 : ℕ) ≠ 1) hp)
  · exact False.elim (not_prime_of_eq_mul (rfl : 216 = 2 * 108)
      (by decide : (2 : ℕ) ≠ 1) (by decide : (108 : ℕ) ≠ 1) hp)
  · exact False.elim (not_prime_of_eq_mul (rfl : 217 = 7 * 31)
      (by decide : (7 : ℕ) ≠ 1) (by decide : (31 : ℕ) ≠ 1) hp)
  · exact False.elim (not_prime_of_eq_mul (rfl : 218 = 2 * 109)
      (by decide : (2 : ℕ) ≠ 1) (by decide : (109 : ℕ) ≠ 1) hp)
  · exact False.elim (not_prime_of_eq_mul (rfl : 219 = 3 * 73)
      (by decide : (3 : ℕ) ≠ 1) (by decide : (73 : ℕ) ≠ 1) hp)
  · exact False.elim (not_prime_of_eq_mul (rfl : 220 = 2 * 110)
      (by decide : (2 : ℕ) ≠ 1) (by decide : (110 : ℕ) ≠ 1) hp)
  · exact False.elim (not_prime_of_eq_mul (rfl : 221 = 13 * 17)
      (by decide : (13 : ℕ) ≠ 1) (by decide : (17 : ℕ) ≠ 1) hp)
  · exact False.elim (not_prime_of_eq_mul (rfl : 222 = 2 * 111)
      (by decide : (2 : ℕ) ≠ 1) (by decide : (111 : ℕ) ≠ 1) hp)
  · exact h223

lemma five_mul_seven_fourth_forty_one_sq_cap {r : ℕ} (hr : 223 ≤ r) :
    5 * r * 2801 * 1723 ≤ 6 * (r - 1) * 2402 * 1682 := by
  have hdiff : 24240984 ≤ 110369 * r := by
    have hmul : 110369 * 223 ≤ 110369 * r := Nat.mul_le_mul_left 110369 hr
    have hnum : 110369 * 223 = 24612287 := by decide
    omega
  have hL : 5 * r * 2801 * 1723 = 24130615 * r := by ring
  have hR : 6 * (r - 1) * 2402 * 1682 = 24240984 * (r - 1) := by ring
  have hmain : 24130615 * r ≤ 24240984 * (r - 1) := by
    have heq : 24130615 * r + 110369 * r = 24240984 * r := by ring
    have hsub : 24130615 * r = 24240984 * r - 110369 * r :=
      (Nat.sub_eq_of_eq_add heq.symm).symm
    have hle : 24240984 * r - 110369 * r ≤ 24240984 * r - 24240984 :=
      Nat.sub_le_sub_left hdiff _
    have hrw : 24240984 * r - 24240984 = 24240984 * (r - 1) := by
      simpa using (Nat.mul_sub_left_distrib 24240984 r 1).symm
    calc
      24130615 * r = 24240984 * r - 110369 * r := hsub
      _ ≤ 24240984 * r - 24240984 := hle
      _ = 24240984 * (r - 1) := hrw
  rw [hL, hR]
  exact hmain

lemma five_sigma_lt_six_usigma_seven_fourth_forty_one_sq_large {r k : ℕ}
    (hr : r.Prime) (hr223 : 223 ≤ r) (hk : 0 < k) :
    5 * σ 1 (7 ^ 4) * σ 1 (41 ^ 2) * σ 1 (r ^ k) <
      6 * usigma (7 ^ 4) * usigma (41 ^ 2) * usigma (r ^ k) := by
  rw [sigma_seven_pow_four, usigma_seven_pow_four,
    sigma_forty_one_pow_two, usigma_forty_one_pow_two]
  have hcp := sigma_lt_cap_usigma hr hk
  have hT : 0 < 2801 * 1723 :=
    Nat.mul_pos (by decide : 0 < 2801) (by decide : 0 < 1723)
  have hthis := six_five_of_cap_times_const (A := r - 1) (B := r)
    (X := σ 1 (r ^ k)) (Y := usigma (r ^ k)) (S := 2402 * 1682)
    (T := 2801 * 1723) hcp (by
      have hL : 5 * r * (2801 * 1723) = 5 * r * 2801 * 1723 := by ring
      have hR : 6 * (r - 1) * (2402 * 1682) = 6 * (r - 1) * 2402 * 1682 :=
        by ring
      rw [hL, hR]
      exact five_mul_seven_fourth_forty_one_sq_cap hr223)
    hT
  convert hthis using 1 <;> ring

lemma seven_fourth_forty_one_cube_r_sq_overshoot_six_five {r : ℕ}
    (hr : r.Prime) (h223 : 223 ≤ r) (h251 : r ≤ 251) :
    6 * usigma (7 ^ 4) * usigma (41 ^ 3) * usigma (r ^ 2) <
      5 * σ 1 (7 ^ 4) * σ 1 (41 ^ 3) * σ 1 (r ^ 2) := by
  rw [usigma_seven_pow_four, sigma_seven_pow_four,
    sigma_forty_one_pow_three, usigma_forty_one_pow_three,
    sigma_prime_pow_two hr, usigma_prime_pow hr (by decide : 0 < 2)]
  have hsq : r ^ 2 ≤ 251 * r := by
    rw [pow_two]
    exact Nat.mul_le_mul_right r h251
  have hleft : 3934644 * (1 + r ^ 2) < 989369220 * r := by
    have h1 : 3934644 * (1 + r ^ 2) ≤ 3934644 * (1 + 251 * r) :=
      Nat.mul_le_mul_left 3934644 (Nat.add_le_add_left hsq 1)
    have h2 : 3934644 * (1 + 251 * r) = 3934644 + 987595644 * r := by
      have : 3934644 * 251 = 987595644 := by decide
      ring
    have h3 : 3934644 + 987595644 * r < 989369220 * r := by
      have : 3934644 < 1773576 * r :=
        lt_of_lt_of_le (by decide : 3934644 < 395507448)
          (Nat.mul_le_mul_left 1773576 h223)
      omega
    calc
      3934644 * (1 + r ^ 2) ≤ 3934644 * (1 + 251 * r) := h1
      _ = 3934644 + 987595644 * r := h2
      _ < 989369220 * r := h3
  have hL : 6 * 2402 * 68922 * (1 + r ^ 2) = 993303864 * (1 + r ^ 2) :=
    by ring
  have hR : 5 * 2801 * 70644 * (1 + r + r ^ 2) = 989369220 * (1 + r + r ^ 2) :=
    by ring
  have hmain : 993303864 * (1 + r ^ 2) < 989369220 * (1 + r + r ^ 2) := by
    have h1 : 993303864 * (1 + r ^ 2) =
        989369220 * (1 + r ^ 2) + 3934644 * (1 + r ^ 2) := by ring
    have h2 : 989369220 * (1 + r + r ^ 2) =
        989369220 * (1 + r ^ 2) + 989369220 * r := by ring
    rw [h1, h2]
    exact Nat.add_lt_add_left hleft _
  rw [hL, hR]
  exact hmain

lemma seven_fourth_forty_one_cube_r_pow_ge_two_overshoot_six_five
    {r a b c : ℕ} (hr : r.Prime) (h223 : 223 ≤ r) (h251 : r ≤ 251)
    (ha : 4 ≤ a) (hb : 3 ≤ b) (hc : 2 ≤ c) :
    6 * usigma (7 ^ a) * usigma (41 ^ b) * usigma (r ^ c) <
      5 * σ 1 (7 ^ a) * σ 1 (41 ^ b) * σ 1 (r ^ c) :=
  six_five_overshoot_mono_three (by decide : Nat.Prime 7)
    (by decide : Nat.Prime 41) hr
    (by decide : 0 < 4) (by decide : 0 < 3) (by decide : 0 < 2)
    ha hb hc (seven_fourth_forty_one_cube_r_sq_overshoot_six_five hr h223 h251)

lemma prime_ge_two_hundred_fifty_two_ge_two_hundred_fifty_seven {p : ℕ}
    (hp : p.Prime) (h : 252 ≤ p) : 257 ≤ p := by
  have hmem : p = 252 ∨ p = 253 ∨ p = 254 ∨ p = 255 ∨ p = 256 ∨
      257 ≤ p := by omega
  rcases hmem with rfl | rfl | rfl | rfl | rfl | h257
  · exact False.elim (not_prime_of_eq_mul (rfl : 252 = 2 * 126)
      (by decide : (2 : ℕ) ≠ 1) (by decide : (126 : ℕ) ≠ 1) hp)
  · exact False.elim (not_prime_of_eq_mul (rfl : 253 = 11 * 23)
      (by decide : (11 : ℕ) ≠ 1) (by decide : (23 : ℕ) ≠ 1) hp)
  · exact False.elim (not_prime_of_eq_mul (rfl : 254 = 2 * 127)
      (by decide : (2 : ℕ) ≠ 1) (by decide : (127 : ℕ) ≠ 1) hp)
  · exact False.elim (not_prime_of_eq_mul (rfl : 255 = 3 * 85)
      (by decide : (3 : ℕ) ≠ 1) (by decide : (85 : ℕ) ≠ 1) hp)
  · exact False.elim (not_prime_of_eq_mul (rfl : 256 = 2 * 128)
      (by decide : (2 : ℕ) ≠ 1) (by decide : (128 : ℕ) ≠ 1) hp)
  · exact h257

lemma five_mul_seven_fourth_forty_one_euler_cap {r : ℕ} (hr : 257 ≤ r) :
    5 * 41 * r * 2801 ≤ 6 * 40 * (r - 1) * 2402 := by
  have hdiff : 576480 ≤ 2275 * r := by
    have hmul : 2275 * 257 ≤ 2275 * r := Nat.mul_le_mul_left 2275 hr
    have hnum : 2275 * 257 = 584675 := by decide
    omega
  have hL : 5 * 41 * r * 2801 = 574205 * r := by ring
  have hR : 6 * 40 * (r - 1) * 2402 = 576480 * (r - 1) := by ring
  have hmain : 574205 * r ≤ 576480 * (r - 1) := by
    have heq : 574205 * r + 2275 * r = 576480 * r := by ring
    have hsub : 574205 * r = 576480 * r - 2275 * r :=
      (Nat.sub_eq_of_eq_add heq.symm).symm
    have hle : 576480 * r - 2275 * r ≤ 576480 * r - 576480 :=
      Nat.sub_le_sub_left hdiff _
    have hrw : 576480 * r - 576480 = 576480 * (r - 1) := by
      simpa using (Nat.mul_sub_left_distrib 576480 r 1).symm
    calc
      574205 * r = 576480 * r - 2275 * r := hsub
      _ ≤ 576480 * r - 576480 := hle
      _ = 576480 * (r - 1) := hrw
  rw [hL, hR]
  exact hmain

lemma five_sigma_lt_six_usigma_seven_fourth_forty_one_large {r b c : ℕ}
    (hr : r.Prime) (hr257 : 257 ≤ r) (hb : 0 < b) (hc : 0 < c) :
    5 * σ 1 (7 ^ 4) * σ 1 (41 ^ b) * σ 1 (r ^ c) <
      6 * usigma (7 ^ 4) * usigma (41 ^ b) * usigma (r ^ c) := by
  rw [sigma_seven_pow_four, usigma_seven_pow_four]
  have h41 := sigma_lt_cap_usigma (by decide : Nat.Prime 41) hb
  have hrcap := sigma_lt_cap_usigma hr hc
  have hu41 : 0 < usigma (41 ^ b) := by
    rw [usigma_prime_pow (by decide : Nat.Prime 41) hb]
    exact Nat.add_pos_left (by decide : 0 < 1) _
  have hthis := six_five_of_two_caps_times_const (A := 40) (B := 41)
    (X := σ 1 (41 ^ b)) (Y := usigma (41 ^ b)) (C := r - 1) (D := r)
    (P := σ 1 (r ^ c)) (Q := usigma (r ^ c)) (S := 2402) (T := 2801)
    h41 hrcap (five_mul_seven_fourth_forty_one_euler_cap hr257)
    (by decide : 0 < 41) hu41 (by decide : 0 < 2801)
  convert hthis using 1 <;> ring

/-- Leftover `6/5` cannot be three squareful primes `7,41,r` with `r ≥ 43`
and `v₇ = 4` times a squarefree coprime factor. -/
lemma not_five_sigma_of_three_sq_primes_seven_forty_one_of_val_seven_eq_four
    {m r : ℕ} (hm : m ≠ 0) (hr : r.Prime) (hr43 : 43 ≤ r)
    (h : 5 * σ 1 m = 6 * usigma m)
    (hk7 : padicValNat 7 m = 4) (hk41 : 2 ≤ padicValNat 41 m)
    (hkr : 2 ≤ padicValNat r m)
    (hs : Squarefree (ordCompl[r] (ordCompl[41] (ordCompl[7] m)))) :
    False := by
  have hp7 : Nat.Prime 7 := by decide
  have hp41 : Nat.Prime 41 := by decide
  have hpq_ne : (7 : ℕ) ≠ 41 := by decide
  have hpr_ne : (7 : ℕ) ≠ r :=
    Nat.ne_of_lt (lt_of_lt_of_le (by decide : 7 < 43) hr43)
  have hqr_ne : (41 : ℕ) ≠ r :=
    Nat.ne_of_lt (lt_of_lt_of_le (by decide : 41 < 43) hr43)
  have heq := five_sigma_eq_six_of_three_squareful hm hp7 hp41 hr hpq_ne hpr_ne
    hqr_ne h hs
  have hproj_p : ordProj[7] m = 7 ^ padicValNat 7 m := by
    simp [Nat.factorization_def m hp7]
  have hproj_q : ordProj[41] (ordCompl[7] m) =
      41 ^ padicValNat 41 (ordCompl[7] m) := by
    simp [Nat.factorization_def (ordCompl[7] m) hp41]
  have hproj_r : ordProj[r] (ordCompl[41] (ordCompl[7] m)) =
      r ^ padicValNat r (ordCompl[41] (ordCompl[7] m)) := by
    simp [Nat.factorization_def (ordCompl[41] (ordCompl[7] m)) hr]
  rw [hproj_r, padicValNat_ordCompl_of_ne hr hqr_ne,
    padicValNat_ordCompl_of_ne hr hpr_ne, hproj_q,
    padicValNat_ordCompl_of_ne hp41 hpq_ne, hproj_p, hk7] at heq
  rcases le_or_gt r 211 with h211 | h212gt
  · have hover := seven_fourth_forty_one_r_sq_pow_ge_two_overshoot_six_five
      hr hr43 h211 (le_refl _) hk41 hkr
    rw [← heq] at hover
    exact lt_irrefl _ hover
  · have hr223 : 223 ≤ r :=
      prime_ge_two_hundred_twelve_ge_two_hundred_twenty_three hr
        (Nat.succ_le_of_lt h212gt)
    rcases eq_or_lt_of_le hk41 with h41eq | h413
    · rw [← h41eq] at heq
      exact (five_sigma_lt_six_usigma_seven_fourth_forty_one_sq_large hr hr223
        ((Nat.zero_lt_succ 1).trans_le hkr)).ne heq
    · rcases le_or_gt r 251 with h251 | h252gt
      · have hover := seven_fourth_forty_one_cube_r_pow_ge_two_overshoot_six_five
          hr hr223 h251 (le_refl _) (Nat.succ_le_of_lt h413) hkr
        rw [← heq] at hover
        exact lt_irrefl _ hover
      · have hr257 : 257 ≤ r :=
          prime_ge_two_hundred_fifty_two_ge_two_hundred_fifty_seven hr
            (Nat.succ_le_of_lt h252gt)
        exact (five_sigma_lt_six_usigma_seven_fourth_forty_one_large hr hr257
          (lt_of_lt_of_le (by decide : (0 : ℕ) < 2) hk41)
          ((Nat.zero_lt_succ 1).trans_le hkr)).ne heq

lemma seven_pow_seven_forty_one_sq_r_sq_overshoot_six_five {r : ℕ}
    (hr : r.Prime) (h43 : 43 ≤ r) (h241 : r ≤ 241) :
    6 * usigma (7 ^ 7) * usigma (41 ^ 2) * usigma (r ^ 2) <
      5 * σ 1 (7 ^ 7) * σ 1 (41 ^ 2) * σ 1 (r ^ 2) := by
  rw [usigma_seven_pow_seven, sigma_seven_pow_seven,
    sigma_forty_one_pow_two, usigma_forty_one_pow_two,
    sigma_prime_pow_two hr, usigma_prime_pow hr (by decide : 0 < 2)]
  have hsq : r ^ 2 ≤ 241 * r := by
    rw [pow_two]
    exact Nat.mul_le_mul_right r h241
  have hleft : 33914048 * (1 + r ^ 2) < 8277292000 * r := by
    have h1 : 33914048 * (1 + r ^ 2) ≤ 33914048 * (1 + 241 * r) :=
      Nat.mul_le_mul_left 33914048 (Nat.add_le_add_left hsq 1)
    have h2 : 33914048 * (1 + 241 * r) = 33914048 + 8173285568 * r := by
      have : 33914048 * 241 = 8173285568 := by norm_num
      ring
    have h3 : 33914048 + 8173285568 * r < 8277292000 * r := by
      have : 33914048 < 104006432 * r :=
        lt_of_lt_of_le (by norm_num : 33914048 < 4472276576)
          (Nat.mul_le_mul_left 104006432 h43)
      omega
    calc
      33914048 * (1 + r ^ 2) ≤ 33914048 * (1 + 241 * r) := h1
      _ = 33914048 + 8173285568 * r := h2
      _ < 8277292000 * r := h3
  have hL : 6 * 823544 * 1682 * (1 + r ^ 2) = 8311206048 * (1 + r ^ 2) :=
    by ring
  have hR : 5 * 960800 * 1723 * (1 + r + r ^ 2) =
      8277292000 * (1 + r + r ^ 2) := by ring
  have hmain : 8311206048 * (1 + r ^ 2) < 8277292000 * (1 + r + r ^ 2) := by
    have h1 : 8311206048 * (1 + r ^ 2) =
        8277292000 * (1 + r ^ 2) + 33914048 * (1 + r ^ 2) := by ring
    have h2 : 8277292000 * (1 + r + r ^ 2) =
        8277292000 * (1 + r ^ 2) + 8277292000 * r := by ring
    rw [h1, h2]
    exact Nat.add_lt_add_left hleft _
  rw [hL, hR]
  exact hmain

lemma seven_pow_seven_forty_one_r_sq_pow_ge_two_overshoot_six_five
    {r a b c : ℕ} (hr : r.Prime) (h43 : 43 ≤ r) (h241 : r ≤ 241)
    (ha : 7 ≤ a) (hb : 2 ≤ b) (hc : 2 ≤ c) :
    6 * usigma (7 ^ a) * usigma (41 ^ b) * usigma (r ^ c) <
      5 * σ 1 (7 ^ a) * σ 1 (41 ^ b) * σ 1 (r ^ c) :=
  six_five_overshoot_mono_three (by decide : Nat.Prime 7)
    (by decide : Nat.Prime 41) hr
    (by decide : 0 < 7) (by decide : 0 < 2) (by decide : 0 < 2)
    ha hb hc (seven_pow_seven_forty_one_sq_r_sq_overshoot_six_five hr h43 h241)

lemma prime_ge_two_hundred_forty_two_ge_two_hundred_fifty_one {p : ℕ}
    (hp : p.Prime) (h : 242 ≤ p) : 251 ≤ p := by
  have hmem : p = 242 ∨ p = 243 ∨ p = 244 ∨ p = 245 ∨ p = 246 ∨ p = 247 ∨
      p = 248 ∨ p = 249 ∨ p = 250 ∨ 251 ≤ p := by omega
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | h251
  · exact False.elim (not_prime_of_eq_mul (rfl : 242 = 2 * 121)
      (by decide : (2 : ℕ) ≠ 1) (by decide : (121 : ℕ) ≠ 1) hp)
  · exact False.elim (not_prime_of_eq_mul (rfl : 243 = 3 * 81)
      (by decide : (3 : ℕ) ≠ 1) (by decide : (81 : ℕ) ≠ 1) hp)
  · exact False.elim (not_prime_of_eq_mul (rfl : 244 = 2 * 122)
      (by decide : (2 : ℕ) ≠ 1) (by decide : (122 : ℕ) ≠ 1) hp)
  · exact False.elim (not_prime_of_eq_mul (rfl : 245 = 5 * 49)
      (by decide : (5 : ℕ) ≠ 1) (by decide : (49 : ℕ) ≠ 1) hp)
  · exact False.elim (not_prime_of_eq_mul (rfl : 246 = 2 * 123)
      (by decide : (2 : ℕ) ≠ 1) (by decide : (123 : ℕ) ≠ 1) hp)
  · exact False.elim (not_prime_of_eq_mul (rfl : 247 = 13 * 19)
      (by decide : (13 : ℕ) ≠ 1) (by decide : (19 : ℕ) ≠ 1) hp)
  · exact False.elim (not_prime_of_eq_mul (rfl : 248 = 2 * 124)
      (by decide : (2 : ℕ) ≠ 1) (by decide : (124 : ℕ) ≠ 1) hp)
  · exact False.elim (not_prime_of_eq_mul (rfl : 249 = 3 * 83)
      (by decide : (3 : ℕ) ≠ 1) (by decide : (83 : ℕ) ≠ 1) hp)
  · exact False.elim (not_prime_of_eq_mul (rfl : 250 = 2 * 125)
      (by decide : (2 : ℕ) ≠ 1) (by decide : (125 : ℕ) ≠ 1) hp)
  · exact h251

lemma five_mul_seven_cap_forty_one_sq {r : ℕ} (hr : 251 ≤ r) :
    5 * 7 * r * 1723 ≤ 6 * 6 * (r - 1) * 1682 := by
  have hdiff : 60552 ≤ 247 * r := by
    have hmul : 247 * 251 ≤ 247 * r := Nat.mul_le_mul_left 247 hr
    have hnum : 247 * 251 = 61997 := by decide
    omega
  have hL : 5 * 7 * r * 1723 = 60305 * r := by ring
  have hR : 6 * 6 * (r - 1) * 1682 = 60552 * (r - 1) := by ring
  have hmain : 60305 * r ≤ 60552 * (r - 1) := by
    have heq : 60305 * r + 247 * r = 60552 * r := by ring
    have hsub : 60305 * r = 60552 * r - 247 * r :=
      (Nat.sub_eq_of_eq_add heq.symm).symm
    have hle : 60552 * r - 247 * r ≤ 60552 * r - 60552 :=
      Nat.sub_le_sub_left hdiff _
    have hrw : 60552 * r - 60552 = 60552 * (r - 1) := by
      simpa using (Nat.mul_sub_left_distrib 60552 r 1).symm
    calc
      60305 * r = 60552 * r - 247 * r := hsub
      _ ≤ 60552 * r - 60552 := hle
      _ = 60552 * (r - 1) := hrw
  rw [hL, hR]
  exact hmain

lemma five_sigma_lt_six_usigma_seven_cap_forty_one_sq_large {r a k : ℕ}
    (hr : r.Prime) (hr251 : 251 ≤ r) (ha : 0 < a) (hk : 0 < k) :
    5 * σ 1 (7 ^ a) * σ 1 (41 ^ 2) * σ 1 (r ^ k) <
      6 * usigma (7 ^ a) * usigma (41 ^ 2) * usigma (r ^ k) := by
  rw [sigma_forty_one_pow_two, usigma_forty_one_pow_two]
  have h7 := sigma_lt_cap_usigma (by decide : Nat.Prime 7) ha
  have hrcap := sigma_lt_cap_usigma hr hk
  have hu7 : 0 < usigma (7 ^ a) := by
    rw [usigma_prime_pow (by decide : Nat.Prime 7) ha]
    exact Nat.add_pos_left (by decide : 0 < 1) _
  have hthis := six_five_of_two_caps_times_const (A := 6) (B := 7)
    (X := σ 1 (7 ^ a)) (Y := usigma (7 ^ a)) (C := r - 1) (D := r)
    (P := σ 1 (r ^ k)) (Q := usigma (r ^ k)) (S := 1682) (T := 1723)
    h7 hrcap (five_mul_seven_cap_forty_one_sq hr251)
    (by decide : 0 < 7) hu7 (by decide : 0 < 1723)
  convert hthis using 1 <;> ring

lemma seven_pow_seven_forty_one_cube_r_sq_overshoot_six_five {r : ℕ}
    (hr : r.Prime) (h251 : 251 ≤ r) (h283 : r ≤ 283) :
    6 * usigma (7 ^ 7) * usigma (41 ^ 3) * usigma (r ^ 2) <
      5 * σ 1 (7 ^ 7) * σ 1 (41 ^ 3) * σ 1 (r ^ 2) := by
  rw [usigma_seven_pow_seven, sigma_seven_pow_seven,
    sigma_forty_one_pow_three, usigma_forty_one_pow_three,
    sigma_prime_pow_two hr, usigma_prime_pow hr (by decide : 0 < 2)]
  have hsq : r ^ 2 ≤ 283 * r := by
    rw [pow_two]
    exact Nat.mul_le_mul_right r h283
  have hleft : 1188021408 * (1 + r ^ 2) < 339373776000 * r := by
    have h1 : 1188021408 * (1 + r ^ 2) ≤ 1188021408 * (1 + 283 * r) :=
      Nat.mul_le_mul_left 1188021408 (Nat.add_le_add_left hsq 1)
    have h2 : 1188021408 * (1 + 283 * r) = 1188021408 + 336210058464 * r := by
      have : 1188021408 * 283 = 336210058464 := by norm_num
      ring
    have h3 : 1188021408 + 336210058464 * r < 339373776000 * r := by
      have : 1188021408 < 3163717536 * r :=
        lt_of_lt_of_le (by norm_num : 1188021408 < 794093101536)
          (Nat.mul_le_mul_left 3163717536 h251)
      omega
    calc
      1188021408 * (1 + r ^ 2) ≤ 1188021408 * (1 + 283 * r) := h1
      _ = 1188021408 + 336210058464 * r := h2
      _ < 339373776000 * r := h3
  have hL : 6 * 823544 * 68922 * (1 + r ^ 2) = 340561797408 * (1 + r ^ 2) :=
    by ring
  have hR : 5 * 960800 * 70644 * (1 + r + r ^ 2) =
      339373776000 * (1 + r + r ^ 2) := by ring
  have hmain : 340561797408 * (1 + r ^ 2) < 339373776000 * (1 + r + r ^ 2) :=
    by
    have h1 : 340561797408 * (1 + r ^ 2) =
        339373776000 * (1 + r ^ 2) + 1188021408 * (1 + r ^ 2) := by ring
    have h2 : 339373776000 * (1 + r + r ^ 2) =
        339373776000 * (1 + r ^ 2) + 339373776000 * r := by ring
    rw [h1, h2]
    exact Nat.add_lt_add_left hleft _
  rw [hL, hR]
  exact hmain

lemma seven_pow_seven_forty_one_cube_r_pow_ge_two_overshoot_six_five
    {r a b c : ℕ} (hr : r.Prime) (h251 : 251 ≤ r) (h283 : r ≤ 283)
    (ha : 7 ≤ a) (hb : 3 ≤ b) (hc : 2 ≤ c) :
    6 * usigma (7 ^ a) * usigma (41 ^ b) * usigma (r ^ c) <
      5 * σ 1 (7 ^ a) * σ 1 (41 ^ b) * σ 1 (r ^ c) :=
  six_five_overshoot_mono_three (by decide : Nat.Prime 7)
    (by decide : Nat.Prime 41) hr
    (by decide : 0 < 7) (by decide : 0 < 3) (by decide : 0 < 2)
    ha hb hc
    (seven_pow_seven_forty_one_cube_r_sq_overshoot_six_five hr h251 h283)

lemma prime_ge_two_hundred_eighty_four_ge_two_hundred_ninety_three {p : ℕ}
    (hp : p.Prime) (h : 284 ≤ p) : 293 ≤ p := by
  have hmem : p = 284 ∨ p = 285 ∨ p = 286 ∨ p = 287 ∨ p = 288 ∨ p = 289 ∨
      p = 290 ∨ p = 291 ∨ p = 292 ∨ 293 ≤ p := by omega
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | h293
  · exact False.elim (not_prime_of_eq_mul (rfl : 284 = 2 * 142)
      (by decide : (2 : ℕ) ≠ 1) (by decide : (142 : ℕ) ≠ 1) hp)
  · exact False.elim (not_prime_of_eq_mul (rfl : 285 = 5 * 57)
      (by decide : (5 : ℕ) ≠ 1) (by decide : (57 : ℕ) ≠ 1) hp)
  · exact False.elim (not_prime_of_eq_mul (rfl : 286 = 2 * 143)
      (by decide : (2 : ℕ) ≠ 1) (by decide : (143 : ℕ) ≠ 1) hp)
  · exact False.elim (not_prime_of_eq_mul (rfl : 287 = 7 * 41)
      (by decide : (7 : ℕ) ≠ 1) (by decide : (41 : ℕ) ≠ 1) hp)
  · exact False.elim (not_prime_of_eq_mul (rfl : 288 = 2 * 144)
      (by decide : (2 : ℕ) ≠ 1) (by decide : (144 : ℕ) ≠ 1) hp)
  · exact False.elim (not_prime_of_eq_mul (rfl : 289 = 17 * 17)
      (by decide : (17 : ℕ) ≠ 1) (by decide : (17 : ℕ) ≠ 1) hp)
  · exact False.elim (not_prime_of_eq_mul (rfl : 290 = 2 * 145)
      (by decide : (2 : ℕ) ≠ 1) (by decide : (145 : ℕ) ≠ 1) hp)
  · exact False.elim (not_prime_of_eq_mul (rfl : 291 = 3 * 97)
      (by decide : (3 : ℕ) ≠ 1) (by decide : (97 : ℕ) ≠ 1) hp)
  · exact False.elim (not_prime_of_eq_mul (rfl : 292 = 2 * 146)
      (by decide : (2 : ℕ) ≠ 1) (by decide : (146 : ℕ) ≠ 1) hp)
  · exact h293

/-- Leftover `6/5` cannot be three squareful primes `7,41,r` with `r ≥ 43`
and `v₇ ≥ 7` times a squarefree coprime factor. -/
lemma not_five_sigma_of_three_sq_primes_seven_forty_one_of_val_seven_ge_seven
    {m r : ℕ} (hm : m ≠ 0) (hr : r.Prime) (hr43 : 43 ≤ r)
    (h : 5 * σ 1 m = 6 * usigma m)
    (hk7 : 7 ≤ padicValNat 7 m) (hk41 : 2 ≤ padicValNat 41 m)
    (hkr : 2 ≤ padicValNat r m)
    (hs : Squarefree (ordCompl[r] (ordCompl[41] (ordCompl[7] m)))) :
    False := by
  have hp7 : Nat.Prime 7 := by decide
  have hp41 : Nat.Prime 41 := by decide
  have hpq_ne : (7 : ℕ) ≠ 41 := by decide
  have hpr_ne : (7 : ℕ) ≠ r :=
    Nat.ne_of_lt (lt_of_lt_of_le (by decide : 7 < 43) hr43)
  have hqr_ne : (41 : ℕ) ≠ r :=
    Nat.ne_of_lt (lt_of_lt_of_le (by decide : 41 < 43) hr43)
  have heq := five_sigma_eq_six_of_three_squareful hm hp7 hp41 hr hpq_ne hpr_ne
    hqr_ne h hs
  have hproj_p : ordProj[7] m = 7 ^ padicValNat 7 m := by
    simp [Nat.factorization_def m hp7]
  have hproj_q : ordProj[41] (ordCompl[7] m) =
      41 ^ padicValNat 41 (ordCompl[7] m) := by
    simp [Nat.factorization_def (ordCompl[7] m) hp41]
  have hproj_r : ordProj[r] (ordCompl[41] (ordCompl[7] m)) =
      r ^ padicValNat r (ordCompl[41] (ordCompl[7] m)) := by
    simp [Nat.factorization_def (ordCompl[41] (ordCompl[7] m)) hr]
  rw [hproj_r, padicValNat_ordCompl_of_ne hr hqr_ne,
    padicValNat_ordCompl_of_ne hr hpr_ne, hproj_q,
    padicValNat_ordCompl_of_ne hp41 hpq_ne, hproj_p] at heq
  rcases le_or_gt r 241 with h241 | h242gt
  · have hover := seven_pow_seven_forty_one_r_sq_pow_ge_two_overshoot_six_five
      hr hr43 h241 hk7 hk41 hkr
    rw [← heq] at hover
    exact lt_irrefl _ hover
  · have hr251 : 251 ≤ r :=
      prime_ge_two_hundred_forty_two_ge_two_hundred_fifty_one hr
        (Nat.succ_le_of_lt h242gt)
    rcases le_or_gt r 283 with h283 | h284gt
    · rcases eq_or_lt_of_le hk41 with h41eq | h413
      · rw [← h41eq] at heq
        exact (five_sigma_lt_six_usigma_seven_cap_forty_one_sq_large hr hr251
          (lt_of_lt_of_le (by decide : (0 : ℕ) < 7) hk7)
          ((Nat.zero_lt_succ 1).trans_le hkr)).ne heq
      · have hover :=
          seven_pow_seven_forty_one_cube_r_pow_ge_two_overshoot_six_five
            hr hr251 h283 hk7 (Nat.succ_le_of_lt h413) hkr
        rw [← heq] at hover
        exact lt_irrefl _ hover
    · have hr293 : 293 ≤ r :=
        prime_ge_two_hundred_eighty_four_ge_two_hundred_ninety_three hr
          (Nat.succ_le_of_lt h284gt)
      exact (five_sigma_lt_six_usigma_seven_forty_one_euler_large hr hr293
        (lt_of_lt_of_le (by decide : (0 : ℕ) < 7) hk7)
        (lt_of_lt_of_le (by decide : (0 : ℕ) < 2) hk41)
        ((Nat.zero_lt_succ 1).trans_le hkr)).ne heq

lemma seven_pow_six_forty_one_sq_r_sq_overshoot_six_five {r : ℕ}
    (hr : r.Prime) (h43 : 43 ≤ r) (h241 : r ≤ 241) :
    6 * usigma (7 ^ 6) * usigma (41 ^ 2) * usigma (r ^ 2) <
      5 * σ 1 (7 ^ 6) * σ 1 (41 ^ 2) * σ 1 (r ^ 2) := by
  rw [usigma_seven_pow_six, sigma_seven_pow_six,
    sigma_forty_one_pow_two, usigma_forty_one_pow_two,
    sigma_prime_pow_two hr, usigma_prime_pow hr (by decide : 0 < 2)]
  have hsq : r ^ 2 ≤ 241 * r := by
    rw [pow_two]
    exact Nat.mul_le_mul_right r h241
  have hleft : 4854745 * (1 + r ^ 2) < 1182469055 * r := by
    have h1 : 4854745 * (1 + r ^ 2) ≤ 4854745 * (1 + 241 * r) :=
      Nat.mul_le_mul_left 4854745 (Nat.add_le_add_left hsq 1)
    have h2 : 4854745 * (1 + 241 * r) = 4854745 + 1169993545 * r := by
      have : 4854745 * 241 = 1169993545 := by norm_num
      ring
    have h3 : 4854745 + 1169993545 * r < 1182469055 * r := by
      have : 4854745 < 12475510 * r :=
        lt_of_lt_of_le (by norm_num : 4854745 < 536446930)
          (Nat.mul_le_mul_left 12475510 h43)
      omega
    calc
      4854745 * (1 + r ^ 2) ≤ 4854745 * (1 + 241 * r) := h1
      _ = 4854745 + 1169993545 * r := h2
      _ < 1182469055 * r := h3
  have hL : 6 * 117650 * 1682 * (1 + r ^ 2) = 1187323800 * (1 + r ^ 2) :=
    by ring
  have hR : 5 * 137257 * 1723 * (1 + r + r ^ 2) =
      1182469055 * (1 + r + r ^ 2) := by ring
  have hmain : 1187323800 * (1 + r ^ 2) < 1182469055 * (1 + r + r ^ 2) := by
    have h1 : 1187323800 * (1 + r ^ 2) =
        1182469055 * (1 + r ^ 2) + 4854745 * (1 + r ^ 2) := by ring
    have h2 : 1182469055 * (1 + r + r ^ 2) =
        1182469055 * (1 + r ^ 2) + 1182469055 * r := by ring
    rw [h1, h2]
    exact Nat.add_lt_add_left hleft _
  rw [hL, hR]
  exact hmain

lemma seven_pow_six_forty_one_r_sq_pow_ge_two_overshoot_six_five
    {r a b c : ℕ} (hr : r.Prime) (h43 : 43 ≤ r) (h241 : r ≤ 241)
    (ha : 6 ≤ a) (hb : 2 ≤ b) (hc : 2 ≤ c) :
    6 * usigma (7 ^ a) * usigma (41 ^ b) * usigma (r ^ c) <
      5 * σ 1 (7 ^ a) * σ 1 (41 ^ b) * σ 1 (r ^ c) :=
  six_five_overshoot_mono_three (by decide : Nat.Prime 7)
    (by decide : Nat.Prime 41) hr
    (by decide : 0 < 6) (by decide : 0 < 2) (by decide : 0 < 2)
    ha hb hc (seven_pow_six_forty_one_sq_r_sq_overshoot_six_five hr h43 h241)

lemma five_mul_seven_pow_six_forty_one_sq_cap {r : ℕ} (hr : 251 ≤ r) :
    5 * r * 137257 * 1723 ≤ 6 * (r - 1) * 117650 * 1682 := by
  have hdiff : 1187323800 ≤ 4854745 * r := by
    have hmul : 4854745 * 251 ≤ 4854745 * r := Nat.mul_le_mul_left 4854745 hr
    have hnum : 4854745 * 251 = 1218540995 := by norm_num
    omega
  have hL : 5 * r * 137257 * 1723 = 1182469055 * r := by ring
  have hR : 6 * (r - 1) * 117650 * 1682 = 1187323800 * (r - 1) := by ring
  have hmain : 1182469055 * r ≤ 1187323800 * (r - 1) := by
    have heq : 1182469055 * r + 4854745 * r = 1187323800 * r := by ring
    have hsub : 1182469055 * r = 1187323800 * r - 4854745 * r :=
      (Nat.sub_eq_of_eq_add heq.symm).symm
    have hle : 1187323800 * r - 4854745 * r ≤ 1187323800 * r - 1187323800 :=
      Nat.sub_le_sub_left hdiff _
    have hrw : 1187323800 * r - 1187323800 = 1187323800 * (r - 1) := by
      simpa using (Nat.mul_sub_left_distrib 1187323800 r 1).symm
    calc
      1182469055 * r = 1187323800 * r - 4854745 * r := hsub
      _ ≤ 1187323800 * r - 1187323800 := hle
      _ = 1187323800 * (r - 1) := hrw
  rw [hL, hR]
  exact hmain

lemma five_sigma_lt_six_usigma_seven_pow_six_forty_one_sq_large {r k : ℕ}
    (hr : r.Prime) (hr251 : 251 ≤ r) (hk : 0 < k) :
    5 * σ 1 (7 ^ 6) * σ 1 (41 ^ 2) * σ 1 (r ^ k) <
      6 * usigma (7 ^ 6) * usigma (41 ^ 2) * usigma (r ^ k) := by
  rw [sigma_seven_pow_six, usigma_seven_pow_six,
    sigma_forty_one_pow_two, usigma_forty_one_pow_two]
  have hcp := sigma_lt_cap_usigma hr hk
  have hT : 0 < 137257 * 1723 :=
    Nat.mul_pos (by decide : 0 < 137257) (by decide : 0 < 1723)
  have hthis := six_five_of_cap_times_const (A := r - 1) (B := r)
    (X := σ 1 (r ^ k)) (Y := usigma (r ^ k)) (S := 117650 * 1682)
    (T := 137257 * 1723) hcp (by
      have hL : 5 * r * (137257 * 1723) = 5 * r * 137257 * 1723 := by ring
      have hR : 6 * (r - 1) * (117650 * 1682) = 6 * (r - 1) * 117650 * 1682 :=
        by ring
      rw [hL, hR]
      exact five_mul_seven_pow_six_forty_one_sq_cap hr251)
    hT
  convert hthis using 1 <;> ring

lemma seven_pow_six_forty_one_cube_r_sq_overshoot_six_five {r : ℕ}
    (hr : r.Prime) (h251 : 251 ≤ r) (h283 : r ≤ 283) :
    6 * usigma (7 ^ 6) * usigma (41 ^ 3) * usigma (r ^ 2) <
      5 * σ 1 (7 ^ 6) * σ 1 (41 ^ 3) * σ 1 (r ^ 2) := by
  rw [usigma_seven_pow_six, sigma_seven_pow_six,
    sigma_forty_one_pow_three, usigma_forty_one_pow_three,
    sigma_prime_pow_two hr, usigma_prime_pow hr (by decide : 0 < 2)]
  have hsq : r ^ 2 ≤ 283 * r := by
    rw [pow_two]
    exact Nat.mul_le_mul_right r h283
  have hleft : 170122260 * (1 + r ^ 2) < 48481917540 * r := by
    have h1 : 170122260 * (1 + r ^ 2) ≤ 170122260 * (1 + 283 * r) :=
      Nat.mul_le_mul_left 170122260 (Nat.add_le_add_left hsq 1)
    have h2 : 170122260 * (1 + 283 * r) = 170122260 + 48144599580 * r := by
      have : 170122260 * 283 = 48144599580 := by norm_num
      ring
    have h3 : 170122260 + 48144599580 * r < 48481917540 * r := by
      have : 170122260 < 337317960 * r :=
        lt_of_lt_of_le (by norm_num : 170122260 < 84666807960)
          (Nat.mul_le_mul_left 337317960 h251)
      omega
    calc
      170122260 * (1 + r ^ 2) ≤ 170122260 * (1 + 283 * r) := h1
      _ = 170122260 + 48144599580 * r := h2
      _ < 48481917540 * r := h3
  have hL : 6 * 117650 * 68922 * (1 + r ^ 2) = 48652039800 * (1 + r ^ 2) :=
    by ring
  have hR : 5 * 137257 * 70644 * (1 + r + r ^ 2) =
      48481917540 * (1 + r + r ^ 2) := by ring
  have hmain : 48652039800 * (1 + r ^ 2) < 48481917540 * (1 + r + r ^ 2) :=
    by
    have h1 : 48652039800 * (1 + r ^ 2) =
        48481917540 * (1 + r ^ 2) + 170122260 * (1 + r ^ 2) := by ring
    have h2 : 48481917540 * (1 + r + r ^ 2) =
        48481917540 * (1 + r ^ 2) + 48481917540 * r := by ring
    rw [h1, h2]
    exact Nat.add_lt_add_left hleft _
  rw [hL, hR]
  exact hmain

lemma seven_pow_six_forty_one_cube_r_pow_ge_two_overshoot_six_five
    {r a b c : ℕ} (hr : r.Prime) (h251 : 251 ≤ r) (h283 : r ≤ 283)
    (ha : 6 ≤ a) (hb : 3 ≤ b) (hc : 2 ≤ c) :
    6 * usigma (7 ^ a) * usigma (41 ^ b) * usigma (r ^ c) <
      5 * σ 1 (7 ^ a) * σ 1 (41 ^ b) * σ 1 (r ^ c) :=
  six_five_overshoot_mono_three (by decide : Nat.Prime 7)
    (by decide : Nat.Prime 41) hr
    (by decide : 0 < 6) (by decide : 0 < 3) (by decide : 0 < 2)
    ha hb hc
    (seven_pow_six_forty_one_cube_r_sq_overshoot_six_five hr h251 h283)

/-- Leftover `6/5` cannot be three squareful primes `7,41,r` with `r ≥ 43`
and `v₇ = 6` times a squarefree coprime factor. -/
lemma not_five_sigma_of_three_sq_primes_seven_forty_one_of_val_seven_eq_six
    {m r : ℕ} (hm : m ≠ 0) (hr : r.Prime) (hr43 : 43 ≤ r)
    (h : 5 * σ 1 m = 6 * usigma m)
    (hk7 : padicValNat 7 m = 6) (hk41 : 2 ≤ padicValNat 41 m)
    (hkr : 2 ≤ padicValNat r m)
    (hs : Squarefree (ordCompl[r] (ordCompl[41] (ordCompl[7] m)))) :
    False := by
  have hp7 : Nat.Prime 7 := by decide
  have hp41 : Nat.Prime 41 := by decide
  have hpq_ne : (7 : ℕ) ≠ 41 := by decide
  have hpr_ne : (7 : ℕ) ≠ r :=
    Nat.ne_of_lt (lt_of_lt_of_le (by decide : 7 < 43) hr43)
  have hqr_ne : (41 : ℕ) ≠ r :=
    Nat.ne_of_lt (lt_of_lt_of_le (by decide : 41 < 43) hr43)
  have heq := five_sigma_eq_six_of_three_squareful hm hp7 hp41 hr hpq_ne hpr_ne
    hqr_ne h hs
  have hproj_p : ordProj[7] m = 7 ^ padicValNat 7 m := by
    simp [Nat.factorization_def m hp7]
  have hproj_q : ordProj[41] (ordCompl[7] m) =
      41 ^ padicValNat 41 (ordCompl[7] m) := by
    simp [Nat.factorization_def (ordCompl[7] m) hp41]
  have hproj_r : ordProj[r] (ordCompl[41] (ordCompl[7] m)) =
      r ^ padicValNat r (ordCompl[41] (ordCompl[7] m)) := by
    simp [Nat.factorization_def (ordCompl[41] (ordCompl[7] m)) hr]
  rw [hproj_r, padicValNat_ordCompl_of_ne hr hqr_ne,
    padicValNat_ordCompl_of_ne hr hpr_ne, hproj_q,
    padicValNat_ordCompl_of_ne hp41 hpq_ne, hproj_p, hk7] at heq
  rcases le_or_gt r 241 with h241 | h242gt
  · have hover := seven_pow_six_forty_one_r_sq_pow_ge_two_overshoot_six_five
      hr hr43 h241 (le_refl _) hk41 hkr
    rw [← heq] at hover
    exact lt_irrefl _ hover
  · have hr251 : 251 ≤ r :=
      prime_ge_two_hundred_forty_two_ge_two_hundred_fifty_one hr
        (Nat.succ_le_of_lt h242gt)
    rcases le_or_gt r 283 with h283 | h284gt
    · rcases eq_or_lt_of_le hk41 with h41eq | h413
      · rw [← h41eq] at heq
        exact (five_sigma_lt_six_usigma_seven_pow_six_forty_one_sq_large hr
          hr251 ((Nat.zero_lt_succ 1).trans_le hkr)).ne heq
      · have hover :=
          seven_pow_six_forty_one_cube_r_pow_ge_two_overshoot_six_five
            hr hr251 h283 (le_refl _) (Nat.succ_le_of_lt h413) hkr
        rw [← heq] at hover
        exact lt_irrefl _ hover
    · have hr293 : 293 ≤ r :=
        prime_ge_two_hundred_eighty_four_ge_two_hundred_ninety_three hr
          (Nat.succ_le_of_lt h284gt)
      exact (five_sigma_lt_six_usigma_seven_forty_one_euler_large hr hr293
        (by decide : 0 < 6) (lt_of_lt_of_le (by decide : (0 : ℕ) < 2) hk41)
        ((Nat.zero_lt_succ 1).trans_le hkr)).ne heq

lemma seven_pow_five_forty_one_sq_r_sq_overshoot_six_five {r : ℕ}
    (hr : r.Prime) (h43 : 43 ≤ r) (h239 : r ≤ 239) :
    6 * usigma (7 ^ 5) * usigma (41 ^ 2) * usigma (r ^ 2) <
      5 * σ 1 (7 ^ 5) * σ 1 (41 ^ 2) * σ 1 (r ^ 2) := by
  rw [usigma_seven_pow_five, sigma_seven_pow_five,
    sigma_forty_one_pow_two, usigma_forty_one_pow_two,
    sigma_prime_pow_two hr, usigma_prime_pow hr (by decide : 0 < 2)]
  have hsq : r ^ 2 ≤ 239 * r := by
    rw [pow_two]
    exact Nat.mul_le_mul_right r h239
  have hleft : 703416 * (1 + r ^ 2) < 168922920 * r := by
    have h1 : 703416 * (1 + r ^ 2) ≤ 703416 * (1 + 239 * r) :=
      Nat.mul_le_mul_left 703416 (Nat.add_le_add_left hsq 1)
    have h2 : 703416 * (1 + 239 * r) = 703416 + 168116424 * r := by
      have : 703416 * 239 = 168116424 := by decide
      ring
    have h3 : 703416 + 168116424 * r < 168922920 * r := by
      have : 703416 < 806496 * r :=
        lt_of_lt_of_le (by decide : 703416 < 34679328)
          (Nat.mul_le_mul_left 806496 h43)
      omega
    calc
      703416 * (1 + r ^ 2) ≤ 703416 * (1 + 239 * r) := h1
      _ = 703416 + 168116424 * r := h2
      _ < 168922920 * r := h3
  have hL : 6 * 16808 * 1682 * (1 + r ^ 2) = 169626336 * (1 + r ^ 2) :=
    by ring
  have hR : 5 * 19608 * 1723 * (1 + r + r ^ 2) =
      168922920 * (1 + r + r ^ 2) := by ring
  have hmain : 169626336 * (1 + r ^ 2) < 168922920 * (1 + r + r ^ 2) := by
    have h1 : 169626336 * (1 + r ^ 2) =
        168922920 * (1 + r ^ 2) + 703416 * (1 + r ^ 2) := by ring
    have h2 : 168922920 * (1 + r + r ^ 2) =
        168922920 * (1 + r ^ 2) + 168922920 * r := by ring
    rw [h1, h2]
    exact Nat.add_lt_add_left hleft _
  rw [hL, hR]
  exact hmain

lemma seven_pow_five_forty_one_r_sq_pow_ge_two_overshoot_six_five
    {r a b c : ℕ} (hr : r.Prime) (h43 : 43 ≤ r) (h239 : r ≤ 239)
    (ha : 5 ≤ a) (hb : 2 ≤ b) (hc : 2 ≤ c) :
    6 * usigma (7 ^ a) * usigma (41 ^ b) * usigma (r ^ c) <
      5 * σ 1 (7 ^ a) * σ 1 (41 ^ b) * σ 1 (r ^ c) :=
  six_five_overshoot_mono_three (by decide : Nat.Prime 7)
    (by decide : Nat.Prime 41) hr
    (by decide : 0 < 5) (by decide : 0 < 2) (by decide : 0 < 2)
    ha hb hc (seven_pow_five_forty_one_sq_r_sq_overshoot_six_five hr h43 h239)

lemma prime_ge_two_hundred_forty_ge_two_hundred_forty_one {p : ℕ}
    (hp : p.Prime) (h : 240 ≤ p) : 241 ≤ p := by
  have hmem : p = 240 ∨ 241 ≤ p := by omega
  rcases hmem with rfl | h241
  · exact False.elim (not_prime_of_eq_mul (rfl : 240 = 2 * 120)
      (by decide : (2 : ℕ) ≠ 1) (by decide : (120 : ℕ) ≠ 1) hp)
  · exact h241

lemma prime_two_four_one : Nat.Prime 241 := by norm_num

lemma usigma_two_four_one_pow_two : usigma (241 ^ 2) = 58082 := by
  rw [usigma_prime_pow prime_two_four_one (by decide : 0 < 2)]
  decide

lemma sigma_two_four_one_pow_two : σ 1 (241 ^ 2) = 58323 := by
  rw [sigma_prime_pow_two prime_two_four_one]
  decide

lemma usigma_two_four_one_pow_three : usigma (241 ^ 3) = 13997522 := by
  rw [usigma_prime_pow prime_two_four_one (by decide : 0 < 3)]
  norm_num

lemma sigma_two_four_one_pow_three : σ 1 (241 ^ 3) = 14055844 := by
  rw [sigma_prime_pow_div prime_two_four_one]
  norm_num

lemma seven_pow_five_forty_one_sq_two_four_one_sq_under :
    5 * σ 1 (7 ^ 5) * σ 1 (41 ^ 2) * σ 1 (241 ^ 2) <
      6 * usigma (7 ^ 5) * usigma (41 ^ 2) * usigma (241 ^ 2) := by
  rw [sigma_seven_pow_five, usigma_seven_pow_five,
    sigma_forty_one_pow_two, usigma_forty_one_pow_two,
    sigma_two_four_one_pow_two, usigma_two_four_one_pow_two]
  norm_num

lemma seven_pow_five_forty_one_sq_two_four_one_cube_overshoot :
    6 * usigma (7 ^ 5) * usigma (41 ^ 2) * usigma (241 ^ 3) <
      5 * σ 1 (7 ^ 5) * σ 1 (41 ^ 2) * σ 1 (241 ^ 3) := by
  rw [usigma_seven_pow_five, sigma_seven_pow_five,
    usigma_forty_one_pow_two, sigma_forty_one_pow_two,
    usigma_two_four_one_pow_three, sigma_two_four_one_pow_three]
  norm_num

lemma seven_pow_five_forty_one_cube_two_four_one_sq_overshoot :
    6 * usigma (7 ^ 5) * usigma (41 ^ 3) * usigma (241 ^ 2) <
      5 * σ 1 (7 ^ 5) * σ 1 (41 ^ 3) * σ 1 (241 ^ 2) := by
  rw [usigma_seven_pow_five, sigma_seven_pow_five,
    usigma_forty_one_pow_three, sigma_forty_one_pow_three,
    usigma_two_four_one_pow_two, sigma_two_four_one_pow_two]
  norm_num

lemma five_mul_seven_pow_five_forty_one_sq_cap {r : ℕ} (hr : 251 ≤ r) :
    5 * r * 19608 * 1723 ≤ 6 * (r - 1) * 16808 * 1682 := by
  have hdiff : 169626336 ≤ 703416 * r := by
    have hmul : 703416 * 251 ≤ 703416 * r := Nat.mul_le_mul_left 703416 hr
    have hnum : 703416 * 251 = 176557416 := by norm_num
    omega
  have hL : 5 * r * 19608 * 1723 = 168922920 * r := by ring
  have hR : 6 * (r - 1) * 16808 * 1682 = 169626336 * (r - 1) := by ring
  have hmain : 168922920 * r ≤ 169626336 * (r - 1) := by
    have heq : 168922920 * r + 703416 * r = 169626336 * r := by ring
    have hsub : 168922920 * r = 169626336 * r - 703416 * r :=
      (Nat.sub_eq_of_eq_add heq.symm).symm
    have hle : 169626336 * r - 703416 * r ≤ 169626336 * r - 169626336 :=
      Nat.sub_le_sub_left hdiff _
    have hrw : 169626336 * r - 169626336 = 169626336 * (r - 1) := by
      simpa using (Nat.mul_sub_left_distrib 169626336 r 1).symm
    calc
      168922920 * r = 169626336 * r - 703416 * r := hsub
      _ ≤ 169626336 * r - 169626336 := hle
      _ = 169626336 * (r - 1) := hrw
  rw [hL, hR]
  exact hmain

lemma five_sigma_lt_six_usigma_seven_pow_five_forty_one_sq_large {r k : ℕ}
    (hr : r.Prime) (hr251 : 251 ≤ r) (hk : 0 < k) :
    5 * σ 1 (7 ^ 5) * σ 1 (41 ^ 2) * σ 1 (r ^ k) <
      6 * usigma (7 ^ 5) * usigma (41 ^ 2) * usigma (r ^ k) := by
  rw [sigma_seven_pow_five, usigma_seven_pow_five,
    sigma_forty_one_pow_two, usigma_forty_one_pow_two]
  have hcp := sigma_lt_cap_usigma hr hk
  have hT : 0 < 19608 * 1723 :=
    Nat.mul_pos (by decide : 0 < 19608) (by decide : 0 < 1723)
  have hthis := six_five_of_cap_times_const (A := r - 1) (B := r)
    (X := σ 1 (r ^ k)) (Y := usigma (r ^ k)) (S := 16808 * 1682)
    (T := 19608 * 1723) hcp (by
      have hL : 5 * r * (19608 * 1723) = 5 * r * 19608 * 1723 := by ring
      have hR : 6 * (r - 1) * (16808 * 1682) = 6 * (r - 1) * 16808 * 1682 :=
        by ring
      rw [hL, hR]
      exact five_mul_seven_pow_five_forty_one_sq_cap hr251)
    hT
  convert hthis using 1 <;> ring

lemma seven_pow_five_forty_one_cube_r_sq_overshoot_six_five {r : ℕ}
    (hr : r.Prime) (h251 : 251 ≤ r) (h277 : r ≤ 277) :
    6 * usigma (7 ^ 5) * usigma (41 ^ 3) * usigma (r ^ 2) <
      5 * σ 1 (7 ^ 5) * σ 1 (41 ^ 3) * σ 1 (r ^ 2) := by
  rw [usigma_seven_pow_five, sigma_seven_pow_five,
    sigma_forty_one_pow_three, usigma_forty_one_pow_three,
    sigma_prime_pow_two hr, usigma_prime_pow hr (by decide : 0 < 2)]
  have hsq : r ^ 2 ≤ 277 * r := by
    rw [pow_two]
    exact Nat.mul_le_mul_right r h277
  have hleft : 24708096 * (1 + r ^ 2) < 6925937760 * r := by
    have h1 : 24708096 * (1 + r ^ 2) ≤ 24708096 * (1 + 277 * r) :=
      Nat.mul_le_mul_left 24708096 (Nat.add_le_add_left hsq 1)
    have h2 : 24708096 * (1 + 277 * r) = 24708096 + 6844142592 * r := by
      have : 24708096 * 277 = 6844142592 := by norm_num
      ring
    have h3 : 24708096 + 6844142592 * r < 6925937760 * r := by
      have : 24708096 < 81795168 * r :=
        lt_of_lt_of_le (by norm_num : 24708096 < 20530587168)
          (Nat.mul_le_mul_left 81795168 h251)
      omega
    calc
      24708096 * (1 + r ^ 2) ≤ 24708096 * (1 + 277 * r) := h1
      _ = 24708096 + 6844142592 * r := h2
      _ < 6925937760 * r := h3
  have hL : 6 * 16808 * 68922 * (1 + r ^ 2) = 6950645856 * (1 + r ^ 2) :=
    by ring
  have hR : 5 * 19608 * 70644 * (1 + r + r ^ 2) =
      6925937760 * (1 + r + r ^ 2) := by ring
  have hmain : 6950645856 * (1 + r ^ 2) < 6925937760 * (1 + r + r ^ 2) := by
    have h1 : 6950645856 * (1 + r ^ 2) =
        6925937760 * (1 + r ^ 2) + 24708096 * (1 + r ^ 2) := by ring
    have h2 : 6925937760 * (1 + r + r ^ 2) =
        6925937760 * (1 + r ^ 2) + 6925937760 * r := by ring
    rw [h1, h2]
    exact Nat.add_lt_add_left hleft _
  rw [hL, hR]
  exact hmain

lemma seven_pow_five_forty_one_cube_r_pow_ge_two_overshoot_six_five
    {r a b c : ℕ} (hr : r.Prime) (h251 : 251 ≤ r) (h277 : r ≤ 277)
    (ha : 5 ≤ a) (hb : 3 ≤ b) (hc : 2 ≤ c) :
    6 * usigma (7 ^ a) * usigma (41 ^ b) * usigma (r ^ c) <
      5 * σ 1 (7 ^ a) * σ 1 (41 ^ b) * σ 1 (r ^ c) :=
  six_five_overshoot_mono_three (by decide : Nat.Prime 7)
    (by decide : Nat.Prime 41) hr
    (by decide : 0 < 5) (by decide : 0 < 3) (by decide : 0 < 2)
    ha hb hc
    (seven_pow_five_forty_one_cube_r_sq_overshoot_six_five hr h251 h277)

lemma prime_ge_two_hundred_seventy_eight_ge_two_hundred_eighty_one {p : ℕ}
    (hp : p.Prime) (h : 278 ≤ p) : 281 ≤ p := by
  have hmem : p = 278 ∨ p = 279 ∨ p = 280 ∨ 281 ≤ p := by omega
  rcases hmem with rfl | rfl | rfl | h281
  · exact False.elim (not_prime_of_eq_mul (rfl : 278 = 2 * 139)
      (by decide : (2 : ℕ) ≠ 1) (by decide : (139 : ℕ) ≠ 1) hp)
  · exact False.elim (not_prime_of_eq_mul (rfl : 279 = 3 * 93)
      (by decide : (3 : ℕ) ≠ 1) (by decide : (93 : ℕ) ≠ 1) hp)
  · exact False.elim (not_prime_of_eq_mul (rfl : 280 = 2 * 140)
      (by decide : (2 : ℕ) ≠ 1) (by decide : (140 : ℕ) ≠ 1) hp)
  · exact h281

lemma prime_two_eight_one : Nat.Prime 281 := by norm_num

lemma usigma_two_eight_one_pow_two : usigma (281 ^ 2) = 78962 := by
  rw [usigma_prime_pow prime_two_eight_one (by decide : 0 < 2)]
  decide

lemma sigma_two_eight_one_pow_two : σ 1 (281 ^ 2) = 79243 := by
  rw [sigma_prime_pow_two prime_two_eight_one]
  decide

lemma usigma_two_eight_one_pow_three : usigma (281 ^ 3) = 22188042 := by
  rw [usigma_prime_pow prime_two_eight_one (by decide : 0 < 3)]
  norm_num

lemma sigma_two_eight_one_pow_three : σ 1 (281 ^ 3) = 22267284 := by
  rw [sigma_prime_pow_div prime_two_eight_one]
  norm_num

lemma usigma_forty_one_pow_four : usigma (41 ^ 4) = 2825762 := by
  rw [usigma_prime_pow (by decide : Nat.Prime 41) (by decide : 0 < 4)]
  decide

lemma sigma_forty_one_pow_four : σ 1 (41 ^ 4) = 2896405 := by
  rw [sigma_prime_pow_div (by decide : Nat.Prime 41)]
  norm_num

lemma seven_pow_five_forty_one_cube_two_eight_one_sq_under :
    5 * σ 1 (7 ^ 5) * σ 1 (41 ^ 3) * σ 1 (281 ^ 2) <
      6 * usigma (7 ^ 5) * usigma (41 ^ 3) * usigma (281 ^ 2) := by
  rw [sigma_seven_pow_five, usigma_seven_pow_five,
    sigma_forty_one_pow_three, usigma_forty_one_pow_three,
    sigma_two_eight_one_pow_two, usigma_two_eight_one_pow_two]
  norm_num

lemma seven_pow_five_forty_one_cube_two_eight_one_cube_overshoot :
    6 * usigma (7 ^ 5) * usigma (41 ^ 3) * usigma (281 ^ 3) <
      5 * σ 1 (7 ^ 5) * σ 1 (41 ^ 3) * σ 1 (281 ^ 3) := by
  rw [usigma_seven_pow_five, sigma_seven_pow_five,
    usigma_forty_one_pow_three, sigma_forty_one_pow_three,
    usigma_two_eight_one_pow_three, sigma_two_eight_one_pow_three]
  norm_num

lemma seven_pow_five_forty_one_fourth_two_eight_one_sq_overshoot :
    6 * usigma (7 ^ 5) * usigma (41 ^ 4) * usigma (281 ^ 2) <
      5 * σ 1 (7 ^ 5) * σ 1 (41 ^ 4) * σ 1 (281 ^ 2) := by
  rw [usigma_seven_pow_five, sigma_seven_pow_five,
    usigma_forty_one_pow_four, sigma_forty_one_pow_four,
    usigma_two_eight_one_pow_two, sigma_two_eight_one_pow_two]
  norm_num

lemma five_mul_seven_pow_five_forty_one_euler_cap {r : ℕ} (hr : 283 ≤ r) :
    5 * 41 * r * 19608 ≤ 6 * 40 * (r - 1) * 16808 := by
  have hdiff : 4033920 ≤ 14280 * r := by
    have hmul : 14280 * 283 ≤ 14280 * r := Nat.mul_le_mul_left 14280 hr
    have hnum : 14280 * 283 = 4041240 := by decide
    omega
  have hL : 5 * 41 * r * 19608 = 4019640 * r := by ring
  have hR : 6 * 40 * (r - 1) * 16808 = 4033920 * (r - 1) := by ring
  have hmain : 4019640 * r ≤ 4033920 * (r - 1) := by
    have heq : 4019640 * r + 14280 * r = 4033920 * r := by ring
    have hsub : 4019640 * r = 4033920 * r - 14280 * r :=
      (Nat.sub_eq_of_eq_add heq.symm).symm
    have hle : 4033920 * r - 14280 * r ≤ 4033920 * r - 4033920 :=
      Nat.sub_le_sub_left hdiff _
    have hrw : 4033920 * r - 4033920 = 4033920 * (r - 1) := by
      simpa using (Nat.mul_sub_left_distrib 4033920 r 1).symm
    calc
      4019640 * r = 4033920 * r - 14280 * r := hsub
      _ ≤ 4033920 * r - 4033920 := hle
      _ = 4033920 * (r - 1) := hrw
  rw [hL, hR]
  exact hmain

lemma five_sigma_lt_six_usigma_seven_pow_five_forty_one_large {r b c : ℕ}
    (hr : r.Prime) (hr283 : 283 ≤ r) (hb : 0 < b) (hc : 0 < c) :
    5 * σ 1 (7 ^ 5) * σ 1 (41 ^ b) * σ 1 (r ^ c) <
      6 * usigma (7 ^ 5) * usigma (41 ^ b) * usigma (r ^ c) := by
  rw [sigma_seven_pow_five, usigma_seven_pow_five]
  have h41 := sigma_lt_cap_usigma (by decide : Nat.Prime 41) hb
  have hrcap := sigma_lt_cap_usigma hr hc
  have hu41 : 0 < usigma (41 ^ b) := by
    rw [usigma_prime_pow (by decide : Nat.Prime 41) hb]
    exact Nat.add_pos_left (by decide : 0 < 1) _
  have hthis := six_five_of_two_caps_times_const (A := 40) (B := 41)
    (X := σ 1 (41 ^ b)) (Y := usigma (41 ^ b)) (C := r - 1) (D := r)
    (P := σ 1 (r ^ c)) (Q := usigma (r ^ c)) (S := 16808) (T := 19608)
    h41 hrcap (five_mul_seven_pow_five_forty_one_euler_cap hr283)
    (by decide : 0 < 41) hu41 (by decide : 0 < 19608)
  convert hthis using 1 <;> ring

lemma prime_ge_two_hundred_eighty_two_ge_two_hundred_eighty_three {p : ℕ}
    (hp : p.Prime) (h : 282 ≤ p) : 283 ≤ p := by
  have hmem : p = 282 ∨ 283 ≤ p := by omega
  rcases hmem with rfl | h283
  · exact False.elim (not_prime_of_eq_mul (rfl : 282 = 2 * 141)
      (by decide : (2 : ℕ) ≠ 1) (by decide : (141 : ℕ) ≠ 1) hp)
  · exact h283

/-- Leftover `6/5` cannot be three squareful primes `7,41,241` with
`v₇ = 5` times a squarefree coprime factor. -/
lemma not_five_sigma_of_three_sq_primes_seven_forty_one_two_four_one
    {m : ℕ} (hm : m ≠ 0) (h : 5 * σ 1 m = 6 * usigma m)
    (hk7 : padicValNat 7 m = 5) (hk41 : 2 ≤ padicValNat 41 m)
    (hkr : 2 ≤ padicValNat 241 m)
    (hs : Squarefree (ordCompl[241] (ordCompl[41] (ordCompl[7] m)))) :
    False := by
  have hp7 : Nat.Prime 7 := by decide
  have hp41 : Nat.Prime 41 := by decide
  have hp241 : Nat.Prime 241 := prime_two_four_one
  have hpq_ne : (7 : ℕ) ≠ 41 := by decide
  have hpr_ne : (7 : ℕ) ≠ 241 := by decide
  have hqr_ne : (41 : ℕ) ≠ 241 := by decide
  have heq := five_sigma_eq_six_of_three_squareful hm hp7 hp41 hp241 hpq_ne
    hpr_ne hqr_ne h hs
  have hproj_p : ordProj[7] m = 7 ^ padicValNat 7 m := by
    simp [Nat.factorization_def m hp7]
  have hproj_q : ordProj[41] (ordCompl[7] m) =
      41 ^ padicValNat 41 (ordCompl[7] m) := by
    simp [Nat.factorization_def (ordCompl[7] m) hp41]
  have hproj_r : ordProj[241] (ordCompl[41] (ordCompl[7] m)) =
      241 ^ padicValNat 241 (ordCompl[41] (ordCompl[7] m)) := by
    simp [Nat.factorization_def (ordCompl[41] (ordCompl[7] m)) hp241]
  rw [hproj_r, padicValNat_ordCompl_of_ne hp241 hqr_ne,
    padicValNat_ordCompl_of_ne hp241 hpr_ne, hproj_q,
    padicValNat_ordCompl_of_ne hp41 hpq_ne, hproj_p, hk7] at heq
  rcases eq_or_lt_of_le hk41 with h41eq | h413
  · rw [← h41eq] at heq
    rcases eq_or_lt_of_le hkr with hreq | hr3
    · rw [← hreq] at heq
      exact seven_pow_five_forty_one_sq_two_four_one_sq_under.ne heq
    · have hover := six_five_overshoot_mono_three hp7 hp41 hp241
        (by decide : 0 < 5) (by decide : 0 < 2) (by decide : 0 < 3)
        (le_refl _) (le_refl _) (Nat.succ_le_of_lt hr3)
        seven_pow_five_forty_one_sq_two_four_one_cube_overshoot
      rw [← heq] at hover
      exact lt_irrefl _ hover
  · have hover := six_five_overshoot_mono_three hp7 hp41 hp241
      (by decide : 0 < 5) (by decide : 0 < 3) (by decide : 0 < 2)
      (le_refl _) (Nat.succ_le_of_lt h413) hkr
      seven_pow_five_forty_one_cube_two_four_one_sq_overshoot
    rw [← heq] at hover
    exact lt_irrefl _ hover

/-- Leftover `6/5` cannot be three squareful primes `7,41,281` with
`v₇ = 5` times a squarefree coprime factor. -/
lemma not_five_sigma_of_three_sq_primes_seven_forty_one_two_eight_one
    {m : ℕ} (hm : m ≠ 0) (h : 5 * σ 1 m = 6 * usigma m)
    (hk7 : padicValNat 7 m = 5) (hk41 : 2 ≤ padicValNat 41 m)
    (hkr : 2 ≤ padicValNat 281 m)
    (hs : Squarefree (ordCompl[281] (ordCompl[41] (ordCompl[7] m)))) :
    False := by
  have hp7 : Nat.Prime 7 := by decide
  have hp41 : Nat.Prime 41 := by decide
  have hp281 : Nat.Prime 281 := prime_two_eight_one
  have hpq_ne : (7 : ℕ) ≠ 41 := by decide
  have hpr_ne : (7 : ℕ) ≠ 281 := by decide
  have hqr_ne : (41 : ℕ) ≠ 281 := by decide
  have heq := five_sigma_eq_six_of_three_squareful hm hp7 hp41 hp281 hpq_ne
    hpr_ne hqr_ne h hs
  have hproj_p : ordProj[7] m = 7 ^ padicValNat 7 m := by
    simp [Nat.factorization_def m hp7]
  have hproj_q : ordProj[41] (ordCompl[7] m) =
      41 ^ padicValNat 41 (ordCompl[7] m) := by
    simp [Nat.factorization_def (ordCompl[7] m) hp41]
  have hproj_r : ordProj[281] (ordCompl[41] (ordCompl[7] m)) =
      281 ^ padicValNat 281 (ordCompl[41] (ordCompl[7] m)) := by
    simp [Nat.factorization_def (ordCompl[41] (ordCompl[7] m)) hp281]
  rw [hproj_r, padicValNat_ordCompl_of_ne hp281 hqr_ne,
    padicValNat_ordCompl_of_ne hp281 hpr_ne, hproj_q,
    padicValNat_ordCompl_of_ne hp41 hpq_ne, hproj_p, hk7] at heq
  rcases eq_or_lt_of_le hk41 with h41eq | h413
  · rw [← h41eq] at heq
    exact (five_sigma_lt_six_usigma_seven_pow_five_forty_one_sq_large hp281
      (by decide : 251 ≤ 281) ((Nat.zero_lt_succ 1).trans_le hkr)).ne heq
  · have h3le : 3 ≤ padicValNat 41 m := Nat.succ_le_of_lt h413
    rcases eq_or_lt_of_le h3le with h41eq3 | h414
    · rw [← h41eq3] at heq
      rcases eq_or_lt_of_le hkr with hreq | hr3
      · rw [← hreq] at heq
        exact seven_pow_five_forty_one_cube_two_eight_one_sq_under.ne heq
      · have hover := six_five_overshoot_mono_three hp7 hp41 hp281
          (by decide : 0 < 5) (by decide : 0 < 3) (by decide : 0 < 3)
          (le_refl _) (le_refl _) (Nat.succ_le_of_lt hr3)
          seven_pow_five_forty_one_cube_two_eight_one_cube_overshoot
        rw [← heq] at hover
        exact lt_irrefl _ hover
    · have hover := six_five_overshoot_mono_three hp7 hp41 hp281
        (by decide : 0 < 5) (by decide : 0 < 4) (by decide : 0 < 2)
        (le_refl _) (Nat.succ_le_of_lt h414) hkr
        seven_pow_five_forty_one_fourth_two_eight_one_sq_overshoot
      rw [← heq] at hover
      exact lt_irrefl _ hover

/-- Leftover `6/5` cannot be three squareful primes `7,41,r` with `r ≥ 43`
and `v₇ = 5` times a squarefree coprime factor. -/
lemma not_five_sigma_of_three_sq_primes_seven_forty_one_of_val_seven_eq_five
    {m r : ℕ} (hm : m ≠ 0) (hr : r.Prime) (hr43 : 43 ≤ r)
    (h : 5 * σ 1 m = 6 * usigma m)
    (hk7 : padicValNat 7 m = 5) (hk41 : 2 ≤ padicValNat 41 m)
    (hkr : 2 ≤ padicValNat r m)
    (hs : Squarefree (ordCompl[r] (ordCompl[41] (ordCompl[7] m)))) :
    False := by
  have hp7 : Nat.Prime 7 := by decide
  have hp41 : Nat.Prime 41 := by decide
  have hpq_ne : (7 : ℕ) ≠ 41 := by decide
  have hpr_ne : (7 : ℕ) ≠ r :=
    Nat.ne_of_lt (lt_of_lt_of_le (by decide : 7 < 43) hr43)
  have hqr_ne : (41 : ℕ) ≠ r :=
    Nat.ne_of_lt (lt_of_lt_of_le (by decide : 41 < 43) hr43)
  rcases le_or_gt r 239 with h239 | h240gt
  · have heq := five_sigma_eq_six_of_three_squareful hm hp7 hp41 hr hpq_ne
      hpr_ne hqr_ne h hs
    have hproj_p : ordProj[7] m = 7 ^ padicValNat 7 m := by
      simp [Nat.factorization_def m hp7]
    have hproj_q : ordProj[41] (ordCompl[7] m) =
        41 ^ padicValNat 41 (ordCompl[7] m) := by
      simp [Nat.factorization_def (ordCompl[7] m) hp41]
    have hproj_r : ordProj[r] (ordCompl[41] (ordCompl[7] m)) =
        r ^ padicValNat r (ordCompl[41] (ordCompl[7] m)) := by
      simp [Nat.factorization_def (ordCompl[41] (ordCompl[7] m)) hr]
    rw [hproj_r, padicValNat_ordCompl_of_ne hr hqr_ne,
      padicValNat_ordCompl_of_ne hr hpr_ne, hproj_q,
      padicValNat_ordCompl_of_ne hp41 hpq_ne, hproj_p, hk7] at heq
    have hover := seven_pow_five_forty_one_r_sq_pow_ge_two_overshoot_six_five
      hr hr43 h239 (le_refl _) hk41 hkr
    rw [← heq] at hover
    exact lt_irrefl _ hover
  · have hr241 : 241 ≤ r :=
      prime_ge_two_hundred_forty_ge_two_hundred_forty_one hr
        (Nat.succ_le_of_lt h240gt)
    rcases le_or_gt r 241 with h241le | h242gt
    · have hr241eq : r = 241 := Nat.le_antisymm h241le hr241
      subst hr241eq
      exact not_five_sigma_of_three_sq_primes_seven_forty_one_two_four_one
        hm h hk7 hk41 hkr hs
    · have hr251 : 251 ≤ r :=
        prime_ge_two_hundred_forty_two_ge_two_hundred_fifty_one hr
          (Nat.succ_le_of_lt h242gt)
      rcases le_or_gt r 277 with h277 | h278gt
      · have heq := five_sigma_eq_six_of_three_squareful hm hp7 hp41 hr hpq_ne
          hpr_ne hqr_ne h hs
        have hproj_p : ordProj[7] m = 7 ^ padicValNat 7 m := by
          simp [Nat.factorization_def m hp7]
        have hproj_q : ordProj[41] (ordCompl[7] m) =
            41 ^ padicValNat 41 (ordCompl[7] m) := by
          simp [Nat.factorization_def (ordCompl[7] m) hp41]
        have hproj_r : ordProj[r] (ordCompl[41] (ordCompl[7] m)) =
            r ^ padicValNat r (ordCompl[41] (ordCompl[7] m)) := by
          simp [Nat.factorization_def (ordCompl[41] (ordCompl[7] m)) hr]
        rw [hproj_r, padicValNat_ordCompl_of_ne hr hqr_ne,
          padicValNat_ordCompl_of_ne hr hpr_ne, hproj_q,
          padicValNat_ordCompl_of_ne hp41 hpq_ne, hproj_p, hk7] at heq
        rcases eq_or_lt_of_le hk41 with h41eq | h413
        · rw [← h41eq] at heq
          exact (five_sigma_lt_six_usigma_seven_pow_five_forty_one_sq_large hr
            hr251 ((Nat.zero_lt_succ 1).trans_le hkr)).ne heq
        · have hover :=
            seven_pow_five_forty_one_cube_r_pow_ge_two_overshoot_six_five
              hr hr251 h277 (le_refl _) (Nat.succ_le_of_lt h413) hkr
          rw [← heq] at hover
          exact lt_irrefl _ hover
      · have hr281 : 281 ≤ r :=
          prime_ge_two_hundred_seventy_eight_ge_two_hundred_eighty_one hr
            (Nat.succ_le_of_lt h278gt)
        rcases le_or_gt r 281 with h281le | h282gt
        · have hr281eq : r = 281 := Nat.le_antisymm h281le hr281
          subst hr281eq
          exact not_five_sigma_of_three_sq_primes_seven_forty_one_two_eight_one
            hm h hk7 hk41 hkr hs
        · have hr283 : 283 ≤ r :=
            prime_ge_two_hundred_eighty_two_ge_two_hundred_eighty_three hr
              (Nat.succ_le_of_lt h282gt)
          have heq := five_sigma_eq_six_of_three_squareful hm hp7 hp41 hr
            hpq_ne hpr_ne hqr_ne h hs
          have hproj_p : ordProj[7] m = 7 ^ padicValNat 7 m := by
            simp [Nat.factorization_def m hp7]
          have hproj_q : ordProj[41] (ordCompl[7] m) =
              41 ^ padicValNat 41 (ordCompl[7] m) := by
            simp [Nat.factorization_def (ordCompl[7] m) hp41]
          have hproj_r : ordProj[r] (ordCompl[41] (ordCompl[7] m)) =
              r ^ padicValNat r (ordCompl[41] (ordCompl[7] m)) := by
            simp [Nat.factorization_def (ordCompl[41] (ordCompl[7] m)) hr]
          rw [hproj_r, padicValNat_ordCompl_of_ne hr hqr_ne,
            padicValNat_ordCompl_of_ne hr hpr_ne, hproj_q,
            padicValNat_ordCompl_of_ne hp41 hpq_ne, hproj_p, hk7] at heq
          exact (five_sigma_lt_six_usigma_seven_pow_five_forty_one_large hr
            hr283 (lt_of_lt_of_le (by decide : (0 : ℕ) < 2) hk41)
            ((Nat.zero_lt_succ 1).trans_le hkr)).ne heq

/-- Leftover `6/5` cannot be three squareful primes `7,41,r` with `r ≥ 43`
times a squarefree coprime factor. -/
lemma not_five_sigma_of_three_sq_primes_seven_forty_one {m r : ℕ}
    (hm : m ≠ 0) (hr : r.Prime) (hr43 : 43 ≤ r)
    (h : 5 * σ 1 m = 6 * usigma m)
    (hk7 : 2 ≤ padicValNat 7 m) (hk41 : 2 ≤ padicValNat 41 m)
    (hkr : 2 ≤ padicValNat r m)
    (hs : Squarefree (ordCompl[r] (ordCompl[41] (ordCompl[7] m)))) :
    False := by
  rcases eq_or_lt_of_le hk7 with h7eq | h73
  · exact not_five_sigma_of_three_sq_primes_seven_forty_one_of_val_seven_eq_two
      hm hr hr43 h h7eq.symm hk41 hkr hs
  · have h3le : 3 ≤ padicValNat 7 m := Nat.succ_le_of_lt h73
    rcases eq_or_lt_of_le h3le with h7eq3 | h74
    · exact not_five_sigma_of_three_sq_primes_seven_forty_one_of_val_seven_eq_three
        hm hr hr43 h h7eq3.symm hk41 hkr hs
    · have h4le : 4 ≤ padicValNat 7 m := Nat.succ_le_of_lt h74
      rcases eq_or_lt_of_le h4le with h7eq4 | h75
      · exact not_five_sigma_of_three_sq_primes_seven_forty_one_of_val_seven_eq_four
          hm hr hr43 h h7eq4.symm hk41 hkr hs
      · have h5le : 5 ≤ padicValNat 7 m := Nat.succ_le_of_lt h75
        rcases eq_or_lt_of_le h5le with h7eq5 | h76
        · exact
            not_five_sigma_of_three_sq_primes_seven_forty_one_of_val_seven_eq_five
              hm hr hr43 h h7eq5.symm hk41 hkr hs
        · have h6le : 6 ≤ padicValNat 7 m := Nat.succ_le_of_lt h76
          rcases eq_or_lt_of_le h6le with h7eq6 | h77
          · exact
              not_five_sigma_of_three_sq_primes_seven_forty_one_of_val_seven_eq_six
                hm hr hr43 h h7eq6.symm hk41 hkr hs
          · exact
              not_five_sigma_of_three_sq_primes_seven_forty_one_of_val_seven_ge_seven
                hm hr hr43 h (Nat.succ_le_of_lt h77) hk41 hkr hs

lemma five_mul_forty_nine_q_r_cap {q r : ℕ} (hq : 43 ≤ q) (hqr : q < r) :
    5 * q * r * 57 ≤ 6 * (q - 1) * (r - 1) * 50 := by
  have hq1 : 1 ≤ q := le_trans (by decide : 1 ≤ 43) hq
  have hr44 : 44 ≤ r := Nat.succ_le_of_lt (lt_of_le_of_lt hq hqr)
  have hr1 : 1 ≤ r := le_trans (by decide : 1 ≤ 44) hr44
  have hL : 5 * q * r * 57 = 285 * q * r := by ring
  have hR : 6 * (q - 1) * (r - 1) * 50 = 300 * (q - 1) * (r - 1) := by ring
  rw [hL, hR]
  have hqcast : ((q - 1 : ℕ) : ℤ) = (q : ℤ) - 1 := by
    rw [Nat.cast_sub hq1, Nat.cast_one]
  have hrcast : ((r - 1 : ℕ) : ℤ) = (r : ℤ) - 1 := by
    rw [Nat.cast_sub hr1, Nat.cast_one]
  have hmain : (285 : ℤ) * q * r ≤ 300 * ((q : ℤ) - 1) * ((r : ℤ) - 1) := by
    have hq43 : (43 : ℤ) ≤ q := by exact_mod_cast hq
    have hr44z : (44 : ℤ) ≤ r := by exact_mod_cast hr44
    nlinarith
  have hmain' : (285 : ℤ) * q * r ≤ 300 * (q - 1 : ℕ) * (r - 1) := by
    simpa [hqcast, hrcast] using hmain
  exact_mod_cast hmain'

lemma five_sigma_lt_six_usigma_seven_sq_q_large {q r b c : ℕ}
    (hq : q.Prime) (hr : r.Prime) (hq43 : 43 ≤ q) (hqr : q < r)
    (hb : 0 < b) (hc : 0 < c) :
    5 * σ 1 (7 ^ 2) * σ 1 (q ^ b) * σ 1 (r ^ c) <
      6 * usigma (7 ^ 2) * usigma (q ^ b) * usigma (r ^ c) := by
  have hp7 : Nat.Prime 7 := by decide
  have hσ7 : σ 1 (7 ^ 2) = 57 := by
    rw [sigma_prime_pow_two hp7]
    decide
  have hu7 : usigma (7 ^ 2) = 50 := by
    simpa using usigma_prime_pow hp7 (by decide : 0 < 2)
  rw [hσ7, hu7]
  have hqcap := sigma_lt_cap_usigma hq hb
  have hrcap := sigma_lt_cap_usigma hr hc
  have huq : 0 < usigma (q ^ b) := by
    rw [usigma_prime_pow hq hb]
    exact Nat.add_pos_left (by decide : 0 < 1) _
  have hqpos : 0 < q := lt_of_lt_of_le (by decide : 0 < 43) hq43
  have hthis := six_five_of_two_caps_times_const (A := q - 1) (B := q)
    (X := σ 1 (q ^ b)) (Y := usigma (q ^ b)) (C := r - 1) (D := r)
    (P := σ 1 (r ^ c)) (Q := usigma (r ^ c)) (S := 50) (T := 57)
    hqcap hrcap (five_mul_forty_nine_q_r_cap hq43 hqr)
    hqpos huq (by decide : 0 < 57)
  convert hthis using 1 <;> ring

/-- Leftover `6/5` cannot be three squareful primes `7,q,r` with
`43 ≤ q < r` and `v₇ = 2` times a squarefree coprime factor. -/
lemma not_five_sigma_of_three_sq_primes_seven_q_of_val_seven_eq_two
    {m q r : ℕ} (hm : m ≠ 0) (hq : q.Prime) (hr : r.Prime)
    (hq43 : 43 ≤ q) (hqr : q < r)
    (h : 5 * σ 1 m = 6 * usigma m)
    (hk7 : padicValNat 7 m = 2) (hkq : 2 ≤ padicValNat q m)
    (hkr : 2 ≤ padicValNat r m)
    (hs : Squarefree (ordCompl[r] (ordCompl[q] (ordCompl[7] m)))) :
    False := by
  have hp7 : Nat.Prime 7 := by decide
  have hpq_ne : (7 : ℕ) ≠ q :=
    Nat.ne_of_lt (lt_of_lt_of_le (by decide : 7 < 43) hq43)
  have hpr_ne : (7 : ℕ) ≠ r :=
    Nat.ne_of_lt (lt_of_lt_of_le (lt_of_lt_of_le (by decide : 7 < 43) hq43)
      (Nat.le_of_lt hqr))
  have hqr_ne : q ≠ r := Nat.ne_of_lt hqr
  have heq := five_sigma_eq_six_of_three_squareful hm hp7 hq hr hpq_ne hpr_ne
    hqr_ne h hs
  have hproj_p : ordProj[7] m = 7 ^ padicValNat 7 m := by
    simp [Nat.factorization_def m hp7]
  have hproj_q : ordProj[q] (ordCompl[7] m) =
      q ^ padicValNat q (ordCompl[7] m) := by
    simp [Nat.factorization_def (ordCompl[7] m) hq]
  have hproj_r : ordProj[r] (ordCompl[q] (ordCompl[7] m)) =
      r ^ padicValNat r (ordCompl[q] (ordCompl[7] m)) := by
    simp [Nat.factorization_def (ordCompl[q] (ordCompl[7] m)) hr]
  rw [hproj_r, padicValNat_ordCompl_of_ne hr hqr_ne,
    padicValNat_ordCompl_of_ne hr hpr_ne, hproj_q,
    padicValNat_ordCompl_of_ne hq hpq_ne, hproj_p, hk7] at heq
  exact (five_sigma_lt_six_usigma_seven_sq_q_large hq hr hq43 hqr
    (lt_of_lt_of_le (by decide : (0 : ℕ) < 2) hkq)
    (lt_of_lt_of_le (by decide : (0 : ℕ) < 2) hkr)).ne heq

lemma five_seven_q_r_euler_cap {q r : ℕ} (hq : 43 ≤ q) (hr223 : 223 ≤ r)
    (hqr : q < r) :
    5 * 7 * q * r ≤ 6 * 6 * (q - 1) * (r - 1) := by
  have hq1 : 1 ≤ q := le_trans (by decide : 1 ≤ 43) hq
  have hr1 : 1 ≤ r := le_trans (by decide : 1 ≤ 223) hr223
  have hL : 5 * 7 * q * r = 35 * q * r := by ring
  have hR : 6 * 6 * (q - 1) * (r - 1) = 36 * (q - 1) * (r - 1) := by ring
  rw [hL, hR]
  have hqcast : ((q - 1 : ℕ) : ℤ) = (q : ℤ) - 1 := by
    rw [Nat.cast_sub hq1, Nat.cast_one]
  have hrcast : ((r - 1 : ℕ) : ℤ) = (r : ℤ) - 1 := by
    rw [Nat.cast_sub hr1, Nat.cast_one]
  have hmain : (35 : ℤ) * q * r ≤ 36 * ((q : ℤ) - 1) * ((r : ℤ) - 1) := by
    have hq43 : (43 : ℤ) ≤ q := by exact_mod_cast hq
    have hr223z : (223 : ℤ) ≤ r := by exact_mod_cast hr223
    have hqr' : (q : ℤ) < r := by exact_mod_cast hqr
    nlinarith
  have hmain' : (35 : ℤ) * q * r ≤ 36 * (q - 1 : ℕ) * (r - 1) := by
    simpa [hqcast, hrcast] using hmain
  exact_mod_cast hmain'

lemma five_sigma_lt_six_usigma_seven_q_euler_large {q r a b c : ℕ}
    (hq : q.Prime) (hr : r.Prime) (hq43 : 43 ≤ q) (hr223 : 223 ≤ r)
    (hqr : q < r) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    5 * σ 1 (7 ^ a) * σ 1 (q ^ b) * σ 1 (r ^ c) <
      6 * usigma (7 ^ a) * usigma (q ^ b) * usigma (r ^ c) := by
  have hp7 : Nat.Prime 7 := by decide
  have h7 := sigma_lt_cap_usigma hp7 ha
  have hqcap := sigma_lt_cap_usigma hq hb
  have hrcap := sigma_lt_cap_usigma hr hc
  have hu7 : 0 < usigma (7 ^ a) := by
    rw [usigma_prime_pow hp7 ha]
    exact Nat.add_pos_left (by decide : 0 < 1) _
  have huq : 0 < usigma (q ^ b) := by
    rw [usigma_prime_pow hq hb]
    exact Nat.add_pos_left (by decide : 0 < 1) _
  have hqpos : 0 < q := lt_of_lt_of_le (by decide : 0 < 43) hq43
  have hthis := six_five_of_three_caps (A := 6) (B := 7) (X := σ 1 (7 ^ a))
    (Y := usigma (7 ^ a)) (C := q - 1) (D := q) (P := σ 1 (q ^ b))
    (Q := usigma (q ^ b)) (E := r - 1) (F := r) (R := σ 1 (r ^ c))
    (S := usigma (r ^ c)) h7 hqcap hrcap (five_seven_q_r_euler_cap hq43 hr223 hqr)
    (by decide : 0 < 7) hu7 hqpos huq
  simpa [mul_assoc, mul_left_comm, mul_comm] using hthis

/-- Leftover `6/5` cannot be three squareful primes `7,q,r` with
`43 ≤ q < r` and `r ≥ 223` times a squarefree coprime factor. -/
lemma not_five_sigma_of_three_sq_primes_seven_q_of_r_ge_two_hundred_twenty_three
    {m q r : ℕ} (hm : m ≠ 0) (hq : q.Prime) (hr : r.Prime)
    (hq43 : 43 ≤ q) (hr223 : 223 ≤ r) (hqr : q < r)
    (h : 5 * σ 1 m = 6 * usigma m)
    (hk7 : 2 ≤ padicValNat 7 m) (hkq : 2 ≤ padicValNat q m)
    (hkr : 2 ≤ padicValNat r m)
    (hs : Squarefree (ordCompl[r] (ordCompl[q] (ordCompl[7] m)))) :
    False := by
  have hp7 : Nat.Prime 7 := by decide
  have hpq_ne : (7 : ℕ) ≠ q :=
    Nat.ne_of_lt (lt_of_lt_of_le (by decide : 7 < 43) hq43)
  have hpr_ne : (7 : ℕ) ≠ r :=
    Nat.ne_of_lt (lt_of_lt_of_le (by decide : 7 < 223) hr223)
  have hqr_ne : q ≠ r := Nat.ne_of_lt hqr
  have heq := five_sigma_eq_six_of_three_squareful hm hp7 hq hr hpq_ne hpr_ne
    hqr_ne h hs
  have hproj_p : ordProj[7] m = 7 ^ padicValNat 7 m := by
    simp [Nat.factorization_def m hp7]
  have hproj_q : ordProj[q] (ordCompl[7] m) =
      q ^ padicValNat q (ordCompl[7] m) := by
    simp [Nat.factorization_def (ordCompl[7] m) hq]
  have hproj_r : ordProj[r] (ordCompl[q] (ordCompl[7] m)) =
      r ^ padicValNat r (ordCompl[q] (ordCompl[7] m)) := by
    simp [Nat.factorization_def (ordCompl[q] (ordCompl[7] m)) hr]
  rw [hproj_r, padicValNat_ordCompl_of_ne hr hqr_ne,
    padicValNat_ordCompl_of_ne hr hpr_ne, hproj_q,
    padicValNat_ordCompl_of_ne hq hpq_ne, hproj_p] at heq
  exact (five_sigma_lt_six_usigma_seven_q_euler_large hq hr hq43 hr223 hqr
    (lt_of_lt_of_le (by decide : (0 : ℕ) < 2) hk7)
    (lt_of_lt_of_le (by decide : (0 : ℕ) < 2) hkq)
    ((Nat.zero_lt_succ 1).trans_le hkr)).ne heq

lemma usigma_forty_three_pow_two : usigma (43 ^ 2) = 1850 := by
  rw [usigma_prime_pow (by decide : Nat.Prime 43) (by decide : 0 < 2)]
  decide

lemma sigma_forty_three_pow_two : σ 1 (43 ^ 2) = 1893 := by
  rw [sigma_prime_pow_two (by decide : Nat.Prime 43)]
  decide

lemma usigma_forty_three_pow_three : usigma (43 ^ 3) = 79508 := by
  rw [usigma_prime_pow (by decide : Nat.Prime 43) (by decide : 0 < 3)]
  decide

lemma sigma_forty_three_pow_three : σ 1 (43 ^ 3) = 81400 := by
  rw [sigma_prime_pow_div (by decide : Nat.Prime 43)]
  norm_num

lemma seven_cube_forty_three_sq_r_sq_overshoot_six_five {r : ℕ}
    (hr : r.Prime) (h47 : 47 ≤ r) (h113 : r ≤ 113) :
    6 * usigma (7 ^ 3) * usigma (43 ^ 2) * usigma (r ^ 2) <
      5 * σ 1 (7 ^ 3) * σ 1 (43 ^ 2) * σ 1 (r ^ 2) := by
  rw [usigma_seven_pow_three, sigma_seven_pow_three,
    sigma_forty_three_pow_two, usigma_forty_three_pow_two,
    sigma_prime_pow_two hr, usigma_prime_pow hr (by decide : 0 < 2)]
  have hsq : r ^ 2 ≤ 113 * r := by
    rw [pow_two]
    exact Nat.mul_le_mul_right r h113
  have hleft : 32400 * (1 + r ^ 2) < 3786000 * r := by
    have h1 : 32400 * (1 + r ^ 2) ≤ 32400 * (1 + 113 * r) :=
      Nat.mul_le_mul_left 32400 (Nat.add_le_add_left hsq 1)
    have h2 : 32400 * (1 + 113 * r) = 32400 + 3661200 * r := by
      have : 32400 * 113 = 3661200 := by decide
      ring
    have h3 : 32400 + 3661200 * r < 3786000 * r := by
      have : 32400 < 124800 * r :=
        lt_of_lt_of_le (by decide : 32400 < 5865600)
          (Nat.mul_le_mul_left 124800 h47)
      omega
    calc
      32400 * (1 + r ^ 2) ≤ 32400 * (1 + 113 * r) := h1
      _ = 32400 + 3661200 * r := h2
      _ < 3786000 * r := h3
  have hL : 6 * 344 * 1850 * (1 + r ^ 2) = 3818400 * (1 + r ^ 2) := by ring
  have hR : 5 * 400 * 1893 * (1 + r + r ^ 2) = 3786000 * (1 + r + r ^ 2) :=
    by ring
  have hmain : 3818400 * (1 + r ^ 2) < 3786000 * (1 + r + r ^ 2) := by
    have h1 : 3818400 * (1 + r ^ 2) =
        3786000 * (1 + r ^ 2) + 32400 * (1 + r ^ 2) := by ring
    have h2 : 3786000 * (1 + r + r ^ 2) =
        3786000 * (1 + r ^ 2) + 3786000 * r := by ring
    rw [h1, h2]
    exact Nat.add_lt_add_left hleft _
  rw [hL, hR]
  exact hmain

lemma seven_cube_forty_three_r_sq_pow_ge_two_overshoot_six_five
    {r a b c : ℕ} (hr : r.Prime) (h47 : 47 ≤ r) (h113 : r ≤ 113)
    (ha : 3 ≤ a) (hb : 2 ≤ b) (hc : 2 ≤ c) :
    6 * usigma (7 ^ a) * usigma (43 ^ b) * usigma (r ^ c) <
      5 * σ 1 (7 ^ a) * σ 1 (43 ^ b) * σ 1 (r ^ c) :=
  six_five_overshoot_mono_three (by decide : Nat.Prime 7)
    (by decide : Nat.Prime 43) hr
    (by decide : 0 < 3) (by decide : 0 < 2) (by decide : 0 < 2)
    ha hb hc (seven_cube_forty_three_sq_r_sq_overshoot_six_five hr h47 h113)

lemma prime_ge_one_one_four_ge_one_two_seven {p : ℕ} (hp : p.Prime)
    (h : 114 ≤ p) : 127 ≤ p := by
  have hmem : p = 114 ∨ p = 115 ∨ p = 116 ∨ p = 117 ∨ p = 118 ∨ p = 119 ∨
      p = 120 ∨ p = 121 ∨ p = 122 ∨ p = 123 ∨ p = 124 ∨ p = 125 ∨
      p = 126 ∨ 127 ≤ p := by omega
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | h127
  · exact False.elim (not_prime_of_eq_mul (rfl : 114 = 2 * 57)
      (by decide : (2 : ℕ) ≠ 1) (by decide : (57 : ℕ) ≠ 1) hp)
  · exact False.elim (not_prime_of_eq_mul (rfl : 115 = 5 * 23)
      (by decide : (5 : ℕ) ≠ 1) (by decide : (23 : ℕ) ≠ 1) hp)
  · exact False.elim (not_prime_of_eq_mul (rfl : 116 = 2 * 58)
      (by decide : (2 : ℕ) ≠ 1) (by decide : (58 : ℕ) ≠ 1) hp)
  · exact False.elim (not_prime_of_eq_mul (rfl : 117 = 3 * 39)
      (by decide : (3 : ℕ) ≠ 1) (by decide : (39 : ℕ) ≠ 1) hp)
  · exact False.elim (not_prime_of_eq_mul (rfl : 118 = 2 * 59)
      (by decide : (2 : ℕ) ≠ 1) (by decide : (59 : ℕ) ≠ 1) hp)
  · exact False.elim (not_prime_of_eq_mul (rfl : 119 = 7 * 17)
      (by decide : (7 : ℕ) ≠ 1) (by decide : (17 : ℕ) ≠ 1) hp)
  · exact False.elim (not_prime_of_eq_mul (rfl : 120 = 2 * 60)
      (by decide : (2 : ℕ) ≠ 1) (by decide : (60 : ℕ) ≠ 1) hp)
  · exact False.elim (not_prime_of_eq_mul (rfl : 121 = 11 * 11)
      (by decide : (11 : ℕ) ≠ 1) (by decide : (11 : ℕ) ≠ 1) hp)
  · exact False.elim (not_prime_of_eq_mul (rfl : 122 = 2 * 61)
      (by decide : (2 : ℕ) ≠ 1) (by decide : (61 : ℕ) ≠ 1) hp)
  · exact False.elim (not_prime_of_eq_mul (rfl : 123 = 3 * 41)
      (by decide : (3 : ℕ) ≠ 1) (by decide : (41 : ℕ) ≠ 1) hp)
  · exact False.elim (not_prime_of_eq_mul (rfl : 124 = 2 * 62)
      (by decide : (2 : ℕ) ≠ 1) (by decide : (62 : ℕ) ≠ 1) hp)
  · exact False.elim (not_prime_of_eq_mul (rfl : 125 = 5 * 25)
      (by decide : (5 : ℕ) ≠ 1) (by decide : (25 : ℕ) ≠ 1) hp)
  · exact False.elim (not_prime_of_eq_mul (rfl : 126 = 2 * 63)
      (by decide : (2 : ℕ) ≠ 1) (by decide : (63 : ℕ) ≠ 1) hp)
  · exact h127

lemma five_mul_seven_cube_forty_three_euler_cap {r : ℕ} (hr : 127 ≤ r) :
    5 * 43 * r * 400 ≤ 6 * 42 * (r - 1) * 344 := by
  have hdiff : 86688 ≤ 688 * r := by
    have hmul : 688 * 127 ≤ 688 * r := Nat.mul_le_mul_left 688 hr
    have hnum : 688 * 127 = 87376 := by decide
    omega
  have hL : 5 * 43 * r * 400 = 86000 * r := by ring
  have hR : 6 * 42 * (r - 1) * 344 = 86688 * (r - 1) := by ring
  have hmain : 86000 * r ≤ 86688 * (r - 1) := by
    have heq : 86000 * r + 688 * r = 86688 * r := by ring
    have hsub : 86000 * r = 86688 * r - 688 * r :=
      (Nat.sub_eq_of_eq_add heq.symm).symm
    have hle : 86688 * r - 688 * r ≤ 86688 * r - 86688 :=
      Nat.sub_le_sub_left hdiff _
    have hrw : 86688 * r - 86688 = 86688 * (r - 1) := by
      simpa using (Nat.mul_sub_left_distrib 86688 r 1).symm
    calc
      86000 * r = 86688 * r - 688 * r := hsub
      _ ≤ 86688 * r - 86688 := hle
      _ = 86688 * (r - 1) := hrw
  rw [hL, hR]
  exact hmain

lemma five_sigma_lt_six_usigma_seven_cube_forty_three_large {r b c : ℕ}
    (hr : r.Prime) (hr127 : 127 ≤ r) (hb : 0 < b) (hc : 0 < c) :
    5 * σ 1 (7 ^ 3) * σ 1 (43 ^ b) * σ 1 (r ^ c) <
      6 * usigma (7 ^ 3) * usigma (43 ^ b) * usigma (r ^ c) := by
  rw [sigma_seven_pow_three, usigma_seven_pow_three]
  have h43 := sigma_lt_cap_usigma (by decide : Nat.Prime 43) hb
  have hrcap := sigma_lt_cap_usigma hr hc
  have hu43 : 0 < usigma (43 ^ b) := by
    rw [usigma_prime_pow (by decide : Nat.Prime 43) hb]
    exact Nat.add_pos_left (by decide : 0 < 1) _
  have hthis := six_five_of_two_caps_times_const (A := 42) (B := 43)
    (X := σ 1 (43 ^ b)) (Y := usigma (43 ^ b)) (C := r - 1) (D := r)
    (P := σ 1 (r ^ c)) (Q := usigma (r ^ c)) (S := 344) (T := 400)
    h43 hrcap (five_mul_seven_cube_forty_three_euler_cap hr127)
    (by decide : 0 < 43) hu43 (by decide : 0 < 400)
  convert hthis using 1 <;> ring

/-- Leftover `6/5` cannot be three squareful primes `7,43,r` with `r ≥ 47`
and `v₇ = 3` times a squarefree coprime factor. -/
lemma not_five_sigma_of_three_sq_primes_seven_forty_three_of_val_seven_eq_three
    {m r : ℕ} (hm : m ≠ 0) (hr : r.Prime) (hr47 : 47 ≤ r)
    (h : 5 * σ 1 m = 6 * usigma m)
    (hk7 : padicValNat 7 m = 3) (hk43 : 2 ≤ padicValNat 43 m)
    (hkr : 2 ≤ padicValNat r m)
    (hs : Squarefree (ordCompl[r] (ordCompl[43] (ordCompl[7] m)))) :
    False := by
  have hp7 : Nat.Prime 7 := by decide
  have hp43 : Nat.Prime 43 := by decide
  have hpq_ne : (7 : ℕ) ≠ 43 := by decide
  have hpr_ne : (7 : ℕ) ≠ r :=
    Nat.ne_of_lt (lt_of_lt_of_le (by decide : 7 < 47) hr47)
  have hqr_ne : (43 : ℕ) ≠ r :=
    Nat.ne_of_lt (lt_of_lt_of_le (by decide : 43 < 47) hr47)
  have heq := five_sigma_eq_six_of_three_squareful hm hp7 hp43 hr hpq_ne hpr_ne
    hqr_ne h hs
  have hproj_p : ordProj[7] m = 7 ^ padicValNat 7 m := by
    simp [Nat.factorization_def m hp7]
  have hproj_q : ordProj[43] (ordCompl[7] m) =
      43 ^ padicValNat 43 (ordCompl[7] m) := by
    simp [Nat.factorization_def (ordCompl[7] m) hp43]
  have hproj_r : ordProj[r] (ordCompl[43] (ordCompl[7] m)) =
      r ^ padicValNat r (ordCompl[43] (ordCompl[7] m)) := by
    simp [Nat.factorization_def (ordCompl[43] (ordCompl[7] m)) hr]
  rw [hproj_r, padicValNat_ordCompl_of_ne hr hqr_ne,
    padicValNat_ordCompl_of_ne hr hpr_ne, hproj_q,
    padicValNat_ordCompl_of_ne hp43 hpq_ne, hproj_p, hk7] at heq
  rcases le_or_gt r 113 with h113 | h114gt
  · have hover := seven_cube_forty_three_r_sq_pow_ge_two_overshoot_six_five
      hr hr47 h113 (le_refl _) hk43 hkr
    rw [← heq] at hover
    exact lt_irrefl _ hover
  · have hr127 : 127 ≤ r :=
      prime_ge_one_one_four_ge_one_two_seven hr (Nat.succ_le_of_lt h114gt)
    exact (five_sigma_lt_six_usigma_seven_cube_forty_three_large hr hr127
      (lt_of_lt_of_le (by decide : (0 : ℕ) < 2) hk43)
      ((Nat.zero_lt_succ 1).trans_le hkr)).ne heq

lemma seven_fourth_forty_three_sq_r_sq_overshoot_six_five {r : ℕ}
    (hr : r.Prime) (h47 : 47 ≤ r) (h173 : r ≤ 173) :
    6 * usigma (7 ^ 4) * usigma (43 ^ 2) * usigma (r ^ 2) <
      5 * σ 1 (7 ^ 4) * σ 1 (43 ^ 2) * σ 1 (r ^ 2) := by
  rw [usigma_seven_pow_four, sigma_seven_pow_four,
    sigma_forty_three_pow_two, usigma_forty_three_pow_two,
    sigma_prime_pow_two hr, usigma_prime_pow hr (by decide : 0 < 2)]
  have hsq : r ^ 2 ≤ 173 * r := by
    rw [pow_two]
    exact Nat.mul_le_mul_right r h173
  have hleft : 150735 * (1 + r ^ 2) < 26511465 * r := by
    have h1 : 150735 * (1 + r ^ 2) ≤ 150735 * (1 + 173 * r) :=
      Nat.mul_le_mul_left 150735 (Nat.add_le_add_left hsq 1)
    have h2 : 150735 * (1 + 173 * r) = 150735 + 26077155 * r := by
      have : 150735 * 173 = 26077155 := by decide
      ring
    have h3 : 150735 + 26077155 * r < 26511465 * r := by
      have : 150735 < 434310 * r :=
        lt_of_lt_of_le (by decide : 150735 < 20412570)
          (Nat.mul_le_mul_left 434310 h47)
      omega
    calc
      150735 * (1 + r ^ 2) ≤ 150735 * (1 + 173 * r) := h1
      _ = 150735 + 26077155 * r := h2
      _ < 26511465 * r := h3
  have hL : 6 * 2402 * 1850 * (1 + r ^ 2) = 26662200 * (1 + r ^ 2) := by ring
  have hR : 5 * 2801 * 1893 * (1 + r + r ^ 2) = 26511465 * (1 + r + r ^ 2) :=
    by ring
  have hmain : 26662200 * (1 + r ^ 2) < 26511465 * (1 + r + r ^ 2) := by
    have h1 : 26662200 * (1 + r ^ 2) =
        26511465 * (1 + r ^ 2) + 150735 * (1 + r ^ 2) := by ring
    have h2 : 26511465 * (1 + r + r ^ 2) =
        26511465 * (1 + r ^ 2) + 26511465 * r := by ring
    rw [h1, h2]
    exact Nat.add_lt_add_left hleft _
  rw [hL, hR]
  exact hmain

lemma seven_fourth_forty_three_r_sq_pow_ge_two_overshoot_six_five
    {r a b c : ℕ} (hr : r.Prime) (h47 : 47 ≤ r) (h173 : r ≤ 173)
    (ha : 4 ≤ a) (hb : 2 ≤ b) (hc : 2 ≤ c) :
    6 * usigma (7 ^ a) * usigma (43 ^ b) * usigma (r ^ c) <
      5 * σ 1 (7 ^ a) * σ 1 (43 ^ b) * σ 1 (r ^ c) :=
  six_five_overshoot_mono_three (by decide : Nat.Prime 7)
    (by decide : Nat.Prime 43) hr
    (by decide : 0 < 4) (by decide : 0 < 2) (by decide : 0 < 2)
    ha hb hc (seven_fourth_forty_three_sq_r_sq_overshoot_six_five hr h47 h173)

lemma prime_ge_one_seven_four_ge_one_seven_nine {p : ℕ} (hp : p.Prime)
    (h : 174 ≤ p) : 179 ≤ p := by
  have hmem : p = 174 ∨ p = 175 ∨ p = 176 ∨ p = 177 ∨ p = 178 ∨
      179 ≤ p := by omega
  rcases hmem with rfl | rfl | rfl | rfl | rfl | h179
  · exact False.elim (not_prime_of_eq_mul (rfl : 174 = 2 * 87)
      (by decide : (2 : ℕ) ≠ 1) (by decide : (87 : ℕ) ≠ 1) hp)
  · exact False.elim (not_prime_of_eq_mul (rfl : 175 = 7 * 25)
      (by decide : (7 : ℕ) ≠ 1) (by decide : (25 : ℕ) ≠ 1) hp)
  · exact False.elim (not_prime_of_eq_mul (rfl : 176 = 2 * 88)
      (by decide : (2 : ℕ) ≠ 1) (by decide : (88 : ℕ) ≠ 1) hp)
  · exact False.elim (not_prime_of_eq_mul (rfl : 177 = 3 * 59)
      (by decide : (3 : ℕ) ≠ 1) (by decide : (59 : ℕ) ≠ 1) hp)
  · exact False.elim (not_prime_of_eq_mul (rfl : 178 = 2 * 89)
      (by decide : (2 : ℕ) ≠ 1) (by decide : (89 : ℕ) ≠ 1) hp)
  · exact h179

lemma five_mul_seven_fourth_forty_three_sq_cap {r : ℕ} (hr : 179 ≤ r) :
    5 * r * 2801 * 1893 ≤ 6 * (r - 1) * 2402 * 1850 := by
  have hdiff : 26662200 ≤ 150735 * r := by
    have hmul : 150735 * 179 ≤ 150735 * r := Nat.mul_le_mul_left 150735 hr
    have hnum : 150735 * 179 = 26981565 := by decide
    omega
  have hL : 5 * r * 2801 * 1893 = 26511465 * r := by ring
  have hR : 6 * (r - 1) * 2402 * 1850 = 26662200 * (r - 1) := by ring
  have hmain : 26511465 * r ≤ 26662200 * (r - 1) := by
    have heq : 26511465 * r + 150735 * r = 26662200 * r := by ring
    have hsub : 26511465 * r = 26662200 * r - 150735 * r :=
      (Nat.sub_eq_of_eq_add heq.symm).symm
    have hle : 26662200 * r - 150735 * r ≤ 26662200 * r - 26662200 :=
      Nat.sub_le_sub_left hdiff _
    have hrw : 26662200 * r - 26662200 = 26662200 * (r - 1) := by
      simpa using (Nat.mul_sub_left_distrib 26662200 r 1).symm
    calc
      26511465 * r = 26662200 * r - 150735 * r := hsub
      _ ≤ 26662200 * r - 26662200 := hle
      _ = 26662200 * (r - 1) := hrw
  rw [hL, hR]
  exact hmain

lemma five_sigma_lt_six_usigma_seven_fourth_forty_three_sq_large {r k : ℕ}
    (hr : r.Prime) (hr179 : 179 ≤ r) (hk : 0 < k) :
    5 * σ 1 (7 ^ 4) * σ 1 (43 ^ 2) * σ 1 (r ^ k) <
      6 * usigma (7 ^ 4) * usigma (43 ^ 2) * usigma (r ^ k) := by
  rw [sigma_seven_pow_four, usigma_seven_pow_four,
    sigma_forty_three_pow_two, usigma_forty_three_pow_two]
  have hcp := sigma_lt_cap_usigma hr hk
  have hT : 0 < 2801 * 1893 :=
    Nat.mul_pos (by decide : 0 < 2801) (by decide : 0 < 1893)
  have hthis := six_five_of_cap_times_const (A := r - 1) (B := r)
    (X := σ 1 (r ^ k)) (Y := usigma (r ^ k)) (S := 2402 * 1850)
    (T := 2801 * 1893) hcp (by
      have hL : 5 * r * (2801 * 1893) = 5 * r * 2801 * 1893 := by ring
      have hR : 6 * (r - 1) * (2402 * 1850) = 6 * (r - 1) * 2402 * 1850 :=
        by ring
      rw [hL, hR]
      exact five_mul_seven_fourth_forty_three_sq_cap hr179)
    hT
  convert hthis using 1 <;> ring

lemma seven_fourth_forty_three_cube_r_sq_overshoot_six_five {r : ℕ}
    (hr : r.Prime) (h47 : 47 ≤ r) (h193 : r ≤ 193) :
    6 * usigma (7 ^ 4) * usigma (43 ^ 3) * usigma (r ^ 2) <
      5 * σ 1 (7 ^ 4) * σ 1 (43 ^ 3) * σ 1 (r ^ 2) := by
  rw [usigma_seven_pow_four, sigma_seven_pow_four,
    sigma_forty_three_pow_three, usigma_forty_three_pow_three,
    sigma_prime_pow_two hr, usigma_prime_pow hr (by decide : 0 < 2)]
  have hsq : r ^ 2 ≤ 193 * r := by
    rw [pow_two]
    exact Nat.mul_le_mul_right r h193
  have hleft : 5862296 * (1 + r ^ 2) < 1140007000 * r := by
    have h1 : 5862296 * (1 + r ^ 2) ≤ 5862296 * (1 + 193 * r) :=
      Nat.mul_le_mul_left 5862296 (Nat.add_le_add_left hsq 1)
    have h2 : 5862296 * (1 + 193 * r) = 5862296 + 1131423128 * r := by
      have : 5862296 * 193 = 1131423128 := by norm_num
      ring
    have h3 : 5862296 + 1131423128 * r < 1140007000 * r := by
      have : 5862296 < 8583872 * r :=
        lt_of_lt_of_le (by norm_num : 5862296 < 403441984)
          (Nat.mul_le_mul_left 8583872 h47)
      omega
    calc
      5862296 * (1 + r ^ 2) ≤ 5862296 * (1 + 193 * r) := h1
      _ = 5862296 + 1131423128 * r := h2
      _ < 1140007000 * r := h3
  have hL : 6 * 2402 * 79508 * (1 + r ^ 2) = 1145869296 * (1 + r ^ 2) :=
    by ring
  have hR : 5 * 2801 * 81400 * (1 + r + r ^ 2) =
      1140007000 * (1 + r + r ^ 2) := by ring
  have hmain : 1145869296 * (1 + r ^ 2) < 1140007000 * (1 + r + r ^ 2) := by
    have h1 : 1145869296 * (1 + r ^ 2) =
        1140007000 * (1 + r ^ 2) + 5862296 * (1 + r ^ 2) := by ring
    have h2 : 1140007000 * (1 + r + r ^ 2) =
        1140007000 * (1 + r ^ 2) + 1140007000 * r := by ring
    rw [h1, h2]
    exact Nat.add_lt_add_left hleft _
  rw [hL, hR]
  exact hmain

lemma seven_fourth_forty_three_cube_r_pow_ge_two_overshoot_six_five
    {r a b c : ℕ} (hr : r.Prime) (h47 : 47 ≤ r) (h193 : r ≤ 193)
    (ha : 4 ≤ a) (hb : 3 ≤ b) (hc : 2 ≤ c) :
    6 * usigma (7 ^ a) * usigma (43 ^ b) * usigma (r ^ c) <
      5 * σ 1 (7 ^ a) * σ 1 (43 ^ b) * σ 1 (r ^ c) :=
  six_five_overshoot_mono_three (by decide : Nat.Prime 7)
    (by decide : Nat.Prime 43) hr
    (by decide : 0 < 4) (by decide : 0 < 3) (by decide : 0 < 2)
    ha hb hc (seven_fourth_forty_three_cube_r_sq_overshoot_six_five hr h47 h193)

lemma prime_ge_one_nine_four_ge_one_nine_seven {p : ℕ} (hp : p.Prime)
    (h : 194 ≤ p) : 197 ≤ p := by
  have hmem : p = 194 ∨ p = 195 ∨ p = 196 ∨ 197 ≤ p := by omega
  rcases hmem with rfl | rfl | rfl | h197
  · exact False.elim (not_prime_of_eq_mul (rfl : 194 = 2 * 97)
      (by decide : (2 : ℕ) ≠ 1) (by decide : (97 : ℕ) ≠ 1) hp)
  · exact False.elim (not_prime_of_eq_mul (rfl : 195 = 3 * 65)
      (by decide : (3 : ℕ) ≠ 1) (by decide : (65 : ℕ) ≠ 1) hp)
  · exact False.elim (not_prime_of_eq_mul (rfl : 196 = 2 * 98)
      (by decide : (2 : ℕ) ≠ 1) (by decide : (98 : ℕ) ≠ 1) hp)
  · exact h197

lemma five_mul_seven_fourth_forty_three_euler_cap {r : ℕ} (hr : 197 ≤ r) :
    5 * 43 * r * 2801 ≤ 6 * 42 * (r - 1) * 2402 := by
  have hdiff : 605304 ≤ 3089 * r := by
    have hmul : 3089 * 197 ≤ 3089 * r := Nat.mul_le_mul_left 3089 hr
    have hnum : 3089 * 197 = 608533 := by decide
    omega
  have hL : 5 * 43 * r * 2801 = 602215 * r := by ring
  have hR : 6 * 42 * (r - 1) * 2402 = 605304 * (r - 1) := by ring
  have hmain : 602215 * r ≤ 605304 * (r - 1) := by
    have heq : 602215 * r + 3089 * r = 605304 * r := by ring
    have hsub : 602215 * r = 605304 * r - 3089 * r :=
      (Nat.sub_eq_of_eq_add heq.symm).symm
    have hle : 605304 * r - 3089 * r ≤ 605304 * r - 605304 :=
      Nat.sub_le_sub_left hdiff _
    have hrw : 605304 * r - 605304 = 605304 * (r - 1) := by
      simpa using (Nat.mul_sub_left_distrib 605304 r 1).symm
    calc
      602215 * r = 605304 * r - 3089 * r := hsub
      _ ≤ 605304 * r - 605304 := hle
      _ = 605304 * (r - 1) := hrw
  rw [hL, hR]
  exact hmain

lemma five_sigma_lt_six_usigma_seven_fourth_forty_three_large {r b c : ℕ}
    (hr : r.Prime) (hr197 : 197 ≤ r) (hb : 0 < b) (hc : 0 < c) :
    5 * σ 1 (7 ^ 4) * σ 1 (43 ^ b) * σ 1 (r ^ c) <
      6 * usigma (7 ^ 4) * usigma (43 ^ b) * usigma (r ^ c) := by
  rw [sigma_seven_pow_four, usigma_seven_pow_four]
  have h43 := sigma_lt_cap_usigma (by decide : Nat.Prime 43) hb
  have hrcap := sigma_lt_cap_usigma hr hc
  have hu43 : 0 < usigma (43 ^ b) := by
    rw [usigma_prime_pow (by decide : Nat.Prime 43) hb]
    exact Nat.add_pos_left (by decide : 0 < 1) _
  have hthis := six_five_of_two_caps_times_const (A := 42) (B := 43)
    (X := σ 1 (43 ^ b)) (Y := usigma (43 ^ b)) (C := r - 1) (D := r)
    (P := σ 1 (r ^ c)) (Q := usigma (r ^ c)) (S := 2402) (T := 2801)
    h43 hrcap (five_mul_seven_fourth_forty_three_euler_cap hr197)
    (by decide : 0 < 43) hu43 (by decide : 0 < 2801)
  convert hthis using 1 <;> ring

/-- Leftover `6/5` cannot be three squareful primes `7,43,r` with `r ≥ 47`
and `v₇ = 4` times a squarefree coprime factor. -/
lemma not_five_sigma_of_three_sq_primes_seven_forty_three_of_val_seven_eq_four
    {m r : ℕ} (hm : m ≠ 0) (hr : r.Prime) (hr47 : 47 ≤ r)
    (h : 5 * σ 1 m = 6 * usigma m)
    (hk7 : padicValNat 7 m = 4) (hk43 : 2 ≤ padicValNat 43 m)
    (hkr : 2 ≤ padicValNat r m)
    (hs : Squarefree (ordCompl[r] (ordCompl[43] (ordCompl[7] m)))) :
    False := by
  have hp7 : Nat.Prime 7 := by decide
  have hp43 : Nat.Prime 43 := by decide
  have hpq_ne : (7 : ℕ) ≠ 43 := by decide
  have hpr_ne : (7 : ℕ) ≠ r :=
    Nat.ne_of_lt (lt_of_lt_of_le (by decide : 7 < 47) hr47)
  have hqr_ne : (43 : ℕ) ≠ r :=
    Nat.ne_of_lt (lt_of_lt_of_le (by decide : 43 < 47) hr47)
  have heq := five_sigma_eq_six_of_three_squareful hm hp7 hp43 hr hpq_ne hpr_ne
    hqr_ne h hs
  have hproj_p : ordProj[7] m = 7 ^ padicValNat 7 m := by
    simp [Nat.factorization_def m hp7]
  have hproj_q : ordProj[43] (ordCompl[7] m) =
      43 ^ padicValNat 43 (ordCompl[7] m) := by
    simp [Nat.factorization_def (ordCompl[7] m) hp43]
  have hproj_r : ordProj[r] (ordCompl[43] (ordCompl[7] m)) =
      r ^ padicValNat r (ordCompl[43] (ordCompl[7] m)) := by
    simp [Nat.factorization_def (ordCompl[43] (ordCompl[7] m)) hr]
  rw [hproj_r, padicValNat_ordCompl_of_ne hr hqr_ne,
    padicValNat_ordCompl_of_ne hr hpr_ne, hproj_q,
    padicValNat_ordCompl_of_ne hp43 hpq_ne, hproj_p, hk7] at heq
  rcases le_or_gt r 173 with h173 | h174gt
  · have hover := seven_fourth_forty_three_r_sq_pow_ge_two_overshoot_six_five
      hr hr47 h173 (le_refl _) hk43 hkr
    rw [← heq] at hover
    exact lt_irrefl _ hover
  · have hr179 : 179 ≤ r :=
      prime_ge_one_seven_four_ge_one_seven_nine hr (Nat.succ_le_of_lt h174gt)
    rcases eq_or_lt_of_le hk43 with h43eq | h433
    · rw [← h43eq] at heq
      exact (five_sigma_lt_six_usigma_seven_fourth_forty_three_sq_large hr hr179
        ((Nat.zero_lt_succ 1).trans_le hkr)).ne heq
    · rcases le_or_gt r 193 with h193 | h194gt
      · have hover :=
          seven_fourth_forty_three_cube_r_pow_ge_two_overshoot_six_five
            hr hr47 h193 (le_refl _) (Nat.succ_le_of_lt h433) hkr
        rw [← heq] at hover
        exact lt_irrefl _ hover
      · have hr197 : 197 ≤ r :=
          prime_ge_one_nine_four_ge_one_nine_seven hr
            (Nat.succ_le_of_lt h194gt)
        exact (five_sigma_lt_six_usigma_seven_fourth_forty_three_large hr hr197
          (lt_of_lt_of_le (by decide : (0 : ℕ) < 2) hk43)
          ((Nat.zero_lt_succ 1).trans_le hkr)).ne heq

/-- Leftover `6/5` cannot be three squareful primes `7,43,r` with `r ≥ 47`
when `v₇ ∈ {2, 3, 4}` or the third prime is at least `223`. Remaining `v₇ ≥ 5`
with `47 ≤ r ≤ 211` needs a dedicated sandwich. -/
lemma not_five_sigma_of_three_sq_primes_seven_forty_three
    {m r : ℕ} (hm : m ≠ 0) (hr : r.Prime) (hr47 : 47 ≤ r)
    (h : 5 * σ 1 m = 6 * usigma m)
    (hk7 : 2 ≤ padicValNat 7 m) (hk43 : 2 ≤ padicValNat 43 m)
    (hkr : 2 ≤ padicValNat r m)
    (hcase : padicValNat 7 m = 2 ∨ padicValNat 7 m = 3 ∨
      padicValNat 7 m = 4 ∨ 223 ≤ r)
    (hs : Squarefree (ordCompl[r] (ordCompl[43] (ordCompl[7] m)))) :
    False := by
  rcases hcase with h7eq | h7eq | h7eq | hr223
  · exact not_five_sigma_of_three_sq_primes_seven_q_of_val_seven_eq_two
      hm (by decide : (43 : ℕ).Prime) hr (by decide : (43 : ℕ) ≤ 43)
      (lt_of_lt_of_le (by decide : (43 : ℕ) < 47) hr47) h h7eq hk43 hkr hs
  · exact
      not_five_sigma_of_three_sq_primes_seven_forty_three_of_val_seven_eq_three
        hm hr hr47 h h7eq hk43 hkr hs
  · exact
      not_five_sigma_of_three_sq_primes_seven_forty_three_of_val_seven_eq_four
        hm hr hr47 h h7eq hk43 hkr hs
  · exact
      not_five_sigma_of_three_sq_primes_seven_q_of_r_ge_two_hundred_twenty_three
        hm (by decide : (43 : ℕ).Prime) hr (by decide : (43 : ℕ) ≤ 43) hr223
        (lt_of_lt_of_le (by decide : (43 : ℕ) < 223) hr223) h hk7 hk43 hkr hs

end Unitary

section Congruence

/-- The residue `n ≡ 108 (mod 216)` is the Chinese remainder of `n ≡ 4 (mod 8)`
and `27 ∣ n`. -/
lemma mod_216_eq_108_iff (n : ℕ) :
    n % 216 = 108 ↔ n % 8 = 4 ∧ n % 27 = 0 := by
  omega

lemma mod_8_eq_four_iff_dvd {n : ℕ} :
    n % 8 = 4 ↔ 4 ∣ n ∧ ¬ 8 ∣ n := by omega

lemma padicValNat_two_eq_two_iff {n : ℕ} (hn : n ≠ 0) :
    padicValNat 2 n = 2 ↔ 4 ∣ n ∧ ¬ 8 ∣ n := by
  have h2 : (2 : ℕ) ^ 2 ∣ n ↔ 2 ≤ padicValNat 2 n :=
    pow_dvd_iff_le_padicValNat (by decide : (2 : ℕ) ≠ 1) hn
  have h3 : (2 : ℕ) ^ 3 ∣ n ↔ 3 ≤ padicValNat 2 n :=
    pow_dvd_iff_le_padicValNat (by decide : (2 : ℕ) ≠ 1) hn
  constructor
  · intro h
    constructor
    · exact h2.mpr (by omega)
    · intro hd
      have : 3 ≤ padicValNat 2 n := h3.mp (by simpa using hd)
      omega
  · intro ⟨h4, h8⟩
    have : 2 ≤ padicValNat 2 n := h2.mp (by simpa using h4)
    have : ¬ 3 ≤ padicValNat 2 n := by
      intro h
      exact h8 (by simpa using h3.mpr h)
    omega

lemma padicValNat_three_ge_three_iff {n : ℕ} (hn : n ≠ 0) :
    3 ≤ padicValNat 3 n ↔ 27 ∣ n := by
  simpa using
    (pow_dvd_iff_le_padicValNat (by decide : (3 : ℕ) ≠ 1) hn (k := 3)).symm

lemma mod_216_eq_108_iff_valuations {n : ℕ} (hn : n ≠ 0) :
    n % 216 = 108 ↔ padicValNat 2 n = 2 ∧ 3 ≤ padicValNat 3 n := by
  rw [mod_216_eq_108_iff, ← Nat.dvd_iff_mod_eq_zero,
    mod_8_eq_four_iff_dvd, padicValNat_two_eq_two_iff hn,
    padicValNat_three_ge_three_iff hn]

/-- The frozen congruence, assuming the two local valuations. -/
lemma mod_216_of_A_of_valuations {n : ℕ} (hA : A n)
    (h2 : padicValNat 2 n = 2) (h3 : 3 ≤ padicValNat 3 n) :
    n % 216 = 108 :=
  (mod_216_eq_108_iff_valuations hA.1.ne').mpr ⟨h2, h3⟩

end Congruence

end Cursor05.A063880
