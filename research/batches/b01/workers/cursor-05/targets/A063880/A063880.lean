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
