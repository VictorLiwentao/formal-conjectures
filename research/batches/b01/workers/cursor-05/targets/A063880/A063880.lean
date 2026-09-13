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

end Congruence

end Cursor05.A063880
