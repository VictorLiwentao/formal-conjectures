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

import FormalConjectures.OEIS.«135508»

/-!
Structural lemmas for `OeisA135508.conjecture`.

These results do not import or use the `sorry` placeholder for `conjecture`.
They prove the closed form of `a`, the prime-index dichotomy, the first-entry
criterion, and the conjecture for every prime `p ≥ 7` with `3 ∣ p - 2`
(equivalently `p ≡ 2 (mod 3)`), together with the primes `2` and `3`.
-/

namespace OeisA135508

lemma x_succ {n : ℕ} (hn : 0 < n) :
    x (n + 1) = 2 * x n + Nat.lcm (x n) (n + 1) := by
  cases n with
  | zero => exact (lt_irrefl _ hn).elim
  | succ n => rfl

lemma x_pos : ∀ {n}, 0 < n → 0 < x n
  | 1, _ => by decide
  | n + 2, _ => by
    have hx : 0 < x (n + 1) := x_pos n.succ_pos
    rw [x_succ n.succ_pos]
    exact Nat.add_pos_left (Nat.mul_pos (by decide : 0 < 2) hx) _

lemma lcm_eq_mul_div_gcd (a b : ℕ) (hb : 0 < b) :
    Nat.lcm a b = a * (b / Nat.gcd a b) := by
  have hpos : 0 < Nat.gcd a b := Nat.gcd_pos_of_pos_right a hb
  rw [← Nat.mul_div_cancel_left (Nat.lcm a b) hpos, Nat.gcd_mul_lcm,
    Nat.mul_div_assoc a (Nat.gcd_dvd_right a b)]

lemma x_succ_mul {n : ℕ} (hn : 0 < n) :
    x (n + 1) = x n * (2 + (n + 1) / Nat.gcd (x n) (n + 1)) := by
  rw [x_succ hn, lcm_eq_mul_div_gcd (x n) (n + 1) (Nat.succ_pos n)]
  ring

lemma a_eq {n : ℕ} (hn : 0 < n) : a n = (n + 1) / Nat.gcd (x n) (n + 1) := by
  have hx := x_pos hn
  unfold a
  rw [if_neg hn.ne', x_succ_mul hn, Nat.mul_div_cancel_left _ hx]
  exact Nat.add_sub_cancel_left 2 _

lemma x_succ_a {n : ℕ} (hn : 0 < n) : x (n + 1) = x n * (a n + 2) := by
  rw [x_succ_mul hn, a_eq hn, add_comm]

lemma x_dvd_succ {n : ℕ} (hn : 0 < n) : x n ∣ x (n + 1) := by
  rw [x_succ_a hn]
  exact dvd_mul_right _ _

lemma a_dvd {n : ℕ} (hn : 0 < n) : a n ∣ n + 1 := by
  rw [a_eq hn]
  exact Nat.div_dvd_of_dvd (Nat.gcd_dvd_right _ _)

lemma a_le_succ {n : ℕ} (hn : 0 < n) : a n ≤ n + 1 :=
  Nat.le_of_dvd (Nat.succ_pos n) (a_dvd hn)

lemma a_mul_gcd {n : ℕ} (hn : 0 < n) :
    a n * Nat.gcd (x n) (n + 1) = n + 1 := by
  rw [a_eq hn, Nat.div_mul_cancel (Nat.gcd_dvd_right _ _)]

lemma x_dvd_of_le {m n : ℕ} (hm : 0 < m) (h : m ≤ n) : x m ∣ x n := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le h
  clear h
  induction k with
  | zero => exact dvd_rfl
  | succ k ih =>
    have : m + (k + 1) = m + k + 1 := by omega
    rw [this]
    exact ih.trans (x_dvd_succ (by omega))

lemma a_eq_one_or_self {p : ℕ} (hp : p.Prime) : a (p - 1) = 1 ∨ a (p - 1) = p := by
  have hn : 0 < p - 1 := by have := hp.two_le; omega
  have hdiv := a_dvd hn
  have : p - 1 + 1 = p := by omega
  rw [this] at hdiv
  exact (Nat.dvd_prime hp).1 hdiv

lemma three_dvd_x_four : 3 ∣ x 4 := by
  have h := x_succ_a (n := 3) (by decide)
  rw [a_3] at h
  rw [h]
  exact dvd_mul_left 3 _

lemma three_dvd_x {n : ℕ} (hn : 4 ≤ n) : 3 ∣ x n :=
  three_dvd_x_four.trans (x_dvd_of_le (by decide : 0 < 4) hn)

lemma five_dvd_x_three : 5 ∣ x 3 := by
  have h := x_succ_a (n := 2) (by decide)
  rw [a_2] at h
  rw [h]
  exact dvd_mul_left 5 _

lemma five_dvd_x {n : ℕ} (hn : 3 ≤ n) : 5 ∣ x n :=
  five_dvd_x_three.trans (x_dvd_of_le (by decide : 0 < 3) hn)

lemma exists_least_dvd {p n : ℕ} (hn : 0 < n) (hd : p ∣ x n) :
    ∃ m, 0 < m ∧ m ≤ n ∧ p ∣ x m ∧ ∀ k, 0 < k → k < m → ¬ p ∣ x k := by
  let P : ℕ → Prop := fun m => m ≠ 0 ∧ p ∣ x m
  have hP : ∃ m, P m := ⟨n, hn.ne', hd⟩
  refine ⟨Nat.find hP, ?_, Nat.find_min' hP ⟨hn.ne', hd⟩, (Nat.find_spec hP).2, ?_⟩
  · exact Nat.pos_of_ne_zero (Nat.find_spec hP).1
  · intro k hk hklt hkdvd
    exact Nat.find_min hP hklt ⟨hk.ne', hkdvd⟩

lemma not_prime_dvd_x_one {p : ℕ} (hp : p.Prime) : ¬ p ∣ x 1 := by
  intro h
  have : p ∣ 1 := by simpa [show x 1 = 1 from rfl] using h
  exact hp.ne_one (Nat.dvd_one.mp this)

lemma a_eq_one_iff_dvd {p : ℕ} (hp : p.Prime) :
    a (p - 1) = 1 ↔ p ∣ x (p - 1) := by
  have hn : 0 < p - 1 := by have := hp.two_le; omega
  have hsum : p - 1 + 1 = p := by omega
  rw [a_eq hn, hsum]
  constructor
  · intro h
    have hdiv : Nat.gcd (x (p - 1)) p ∣ p := Nat.gcd_dvd_right _ _
    rcases (Nat.dvd_prime hp).1 hdiv with hg | hg
    · rw [hg, Nat.div_one] at h
      exact (hp.ne_one h).elim
    · have hx := Nat.gcd_dvd_left (x (p - 1)) p
      rwa [hg] at hx
  · intro hd
    have : Nat.gcd (x (p - 1)) p = p := Nat.gcd_eq_right hd
    rw [this, Nat.div_self hp.pos]

lemma dvd_x_pred_of_a {p : ℕ} (_hp : p.Prime) (_hp5 : 5 ≤ p)
    (ha : a (p - 3) = p - 2) : p ∣ x (p - 1) := by
  have h3 : 0 < p - 3 := by omega
  have hstep := x_succ_a h3
  have hidx : p - 3 + 1 = p - 2 := by omega
  rw [hidx, ha] at hstep
  have hsum : p - 2 + 2 = p := by omega
  rw [hsum] at hstep
  have hdiv : p ∣ x (p - 2) := by
    rw [hstep]
    exact dvd_mul_left _ _
  have hpos : 0 < p - 2 := by omega
  have hle : p - 2 ≤ p - 1 := by omega
  exact hdiv.trans (x_dvd_of_le hpos hle)

lemma a_of_dvd_x_pred {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p)
    (hd : p ∣ x (p - 1)) : a (p - 3) = p - 2 := by
  have hn : 0 < p - 1 := by omega
  obtain ⟨m, hmpos, hmle, hdm, hmin⟩ := exists_least_dvd hn hd
  have hmne1 : m ≠ 1 := by
    intro hm1
    subst hm1
    exact not_prime_dvd_x_one hp hdm
  have hmpred : 0 < m - 1 := by omega
  have hnot : ¬ p ∣ x (m - 1) := hmin (m - 1) hmpred (Nat.sub_lt hmpos (by decide))
  have hstep := x_succ_a hmpred
  have hm1 : m - 1 + 1 = m := Nat.sub_add_cancel (by omega)
  rw [hm1] at hstep
  have hmul : p ∣ x (m - 1) * (a (m - 1) + 2) := by
    rwa [← hstep]
  have hfac : p ∣ a (m - 1) + 2 :=
    (hp.dvd_mul.mp hmul).resolve_left hnot
  have hale := a_le_succ hmpred
  have hle : a (m - 1) + 2 ≤ p + 1 := by
    have h1 : a (m - 1) + 2 ≤ m - 1 + 1 + 2 := Nat.add_le_add_right hale 2
    have : m - 1 + 1 + 2 = m + 2 := by omega
    have h2 : m + 2 ≤ p + 1 := by omega
    exact h1.trans (this.le.trans h2)
  have hge : p ≤ a (m - 1) + 2 :=
    Nat.le_of_dvd (Nat.add_pos_right _ (by decide : 0 < 2)) hfac
  have heq : a (m - 1) + 2 = p := by
    have hcases : a (m - 1) + 2 = p ∨ a (m - 1) + 2 = p + 1 := by omega
    rcases hcases with h | h
    · exact h
    · have hfac' : p ∣ p + 1 := by rwa [h] at hfac
      have : (p + 1) % p = 0 := Nat.mod_eq_zero_of_dvd hfac'
      have h1 : (p + 1) % p = 1 := by
        rw [Nat.add_comm p 1, Nat.add_mod_right]
        exact Nat.mod_eq_of_lt (by omega : 1 < p)
      omega
  have haeq : a (m - 1) = p - 2 := by omega
  have hdivn : p - 2 ∣ m := by
    have h := a_dvd hmpred
    rwa [hm1, haeq] at h
  obtain ⟨k, hk⟩ := hdivn
  have hkpos : 0 < k := by
    cases k with
    | zero =>
      rw [Nat.mul_zero] at hk
      exact (hmpos.ne' hk).elim
    | succ k => exact Nat.succ_pos _
  have hk1 : k = 1 := by
    have hcases : k = 1 ∨ 2 ≤ k := by omega
    rcases hcases with h | h
    · exact h
    · have hle2 : 2 * (p - 2) ≤ (p - 2) * k := by
        have := Nat.mul_le_mul_left (p - 2) h
        simpa [mul_comm] using this
      have hle3 : 2 * (p - 2) ≤ m := by
        rwa [hk]
      have hcon : 2 * (p - 2) ≤ p - 1 := hle3.trans hmle
      have hge' : p + 1 ≤ 2 * (p - 2) := by
        calc
          p + 1 = p - 2 + 3 := by omega
          _ ≤ (p - 2) + (p - 2) := by omega
          _ = 2 * (p - 2) := by omega
      have : p + 1 ≤ p - 1 := hge'.trans hcon
      omega
  have hm2 : m = p - 2 := by
    rw [hk, hk1, Nat.mul_one]
  have hidx : m - 1 = p - 3 := by omega
  rw [← hidx, haeq]

lemma dvd_x_pred_iff_a {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) :
    p ∣ x (p - 1) ↔ a (p - 3) = p - 2 :=
  ⟨a_of_dvd_x_pred hp hp5, dvd_x_pred_of_a hp hp5⟩

lemma a_eq_self_of_gcd_gt_one {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p)
    (hg : 1 < Nat.gcd (x (p - 3)) (p - 2)) : a (p - 1) = p := by
  have hn : 0 < p - 3 := by omega
  have hsum : p - 3 + 1 = p - 2 := by omega
  have hne : a (p - 3) ≠ p - 2 := by
    intro h
    have hmul := a_mul_gcd hn
    rw [hsum, h] at hmul
    have hpos : 0 < p - 2 := by omega
    have : Nat.gcd (x (p - 3)) (p - 2) = 1 :=
      Nat.eq_of_mul_eq_mul_left hpos (by simpa using hmul)
    omega
  have hnot : ¬ p ∣ x (p - 1) := fun hd =>
    hne ((dvd_x_pred_iff_a hp hp5).1 hd)
  rcases a_eq_one_or_self hp with h | h
  · exact (hnot ((a_eq_one_iff_dvd hp).1 h)).elim
  · exact h

lemma three_dvd_gcd {p : ℕ} (hp7 : 7 ≤ p) (h3 : 3 ∣ p - 2) :
    1 < Nat.gcd (x (p - 3)) (p - 2) := by
  have hle : 4 ≤ p - 3 := by omega
  have hx : 3 ∣ x (p - 3) := three_dvd_x hle
  have hg : 3 ∣ Nat.gcd (x (p - 3)) (p - 2) := Nat.dvd_gcd hx h3
  have : 3 ≤ Nat.gcd (x (p - 3)) (p - 2) :=
    Nat.le_of_dvd (Nat.gcd_pos_of_pos_right _ (by omega)) hg
  omega

theorem conjecture_of_three_dvd {p : ℕ} (hp : p.Prime) (hp7 : 7 ≤ p)
    (h3 : 3 ∣ p - 2) : a (p - 1) = p :=
  a_eq_self_of_gcd_gt_one hp (by omega) (three_dvd_gcd hp7 h3)

lemma three_dvd_of_mod {p : ℕ} (hp2 : 2 ≤ p) (h : p % 3 = 2) : 3 ∣ p - 2 := by
  have := Nat.div_add_mod p 3
  rw [h] at this
  have hp : p = 3 * (p / 3) + 2 := this.symm
  have : p - 2 = 3 * (p / 3) := by omega
  exact ⟨p / 3, this⟩

theorem conjecture_of_mod_three {p : ℕ} (hp : p.Prime) (hp7 : 7 ≤ p)
    (hmod : p % 3 = 2) : a (p - 1) = p :=
  conjecture_of_three_dvd hp hp7 (three_dvd_of_mod (le_trans (by decide : 2 ≤ 7) hp7) hmod)

theorem conjecture_two (_h : ¬ (2 - 2).Prime) : a (2 - 1) = 2 := a_1

theorem conjecture_three (_h : ¬ (3 - 2).Prime) : a (3 - 1) = 3 := a_2

lemma five_dvd_gcd {p : ℕ} (hp7 : 7 ≤ p) (h5 : 5 ∣ p - 2) :
    1 < Nat.gcd (x (p - 3)) (p - 2) := by
  have hle : 3 ≤ p - 3 := by omega
  have hx : 5 ∣ x (p - 3) := five_dvd_x hle
  have hg : 5 ∣ Nat.gcd (x (p - 3)) (p - 2) := Nat.dvd_gcd hx h5
  have : 5 ≤ Nat.gcd (x (p - 3)) (p - 2) :=
    Nat.le_of_dvd (Nat.gcd_pos_of_pos_right _ (by omega)) hg
  omega

theorem conjecture_of_five_dvd {p : ℕ} (hp : p.Prime) (hp7 : 7 ≤ p)
    (h5 : 5 ∣ p - 2) : a (p - 1) = p :=
  a_eq_self_of_gcd_gt_one hp (by omega) (five_dvd_gcd hp7 h5)

lemma a_46 : a 46 = 47 := by
  have hp : Nat.Prime 47 := by decide
  have := conjecture_of_mod_three hp (by decide) (by decide)
  simpa using this

lemma seven_dvd_x_47 : 7 ∣ x 47 := by
  have h := x_succ_a (n := 46) (by decide)
  rw [a_46] at h
  have hsum : (47 + 2 : ℕ) = 49 := by decide
  rw [h, hsum]
  exact dvd_mul_of_dvd_right (by decide : 7 ∣ 49) _

lemma seven_dvd_x {n : ℕ} (hn : 47 ≤ n) : 7 ∣ x n :=
  seven_dvd_x_47.trans (x_dvd_of_le (by decide : 0 < 47) hn)

theorem conjecture_of_seven_dvd {p : ℕ} (hp : p.Prime) (hp50 : 50 ≤ p)
    (h7 : 7 ∣ p - 2) : a (p - 1) = p := by
  have hn : 47 ≤ p - 3 := by omega
  have hx : 7 ∣ x (p - 3) := seven_dvd_x hn
  have hg : 7 ∣ Nat.gcd (x (p - 3)) (p - 2) := Nat.dvd_gcd hx h7
  have hgt : 1 < Nat.gcd (x (p - 3)) (p - 2) := by
    have : 7 ≤ Nat.gcd (x (p - 3)) (p - 2) :=
      Nat.le_of_dvd (Nat.gcd_pos_of_pos_right _ (by omega)) hg
    omega
  exact a_eq_self_of_gcd_gt_one hp (by omega) hgt

/-- If `a(p-1) = p`, then `p+2` divides `x p` and therefore `a(p+1) = 1`.
This is Cloitre's inhibition lemma, with Lean `a(n) = c_{n+1}`. -/
lemma inhibition {p : ℕ} (hp : 2 ≤ p) (h : a (p - 1) = p) : a (p + 1) = 1 := by
  have hpos : 0 < p - 1 := by omega
  have hxp := x_succ_a hpos
  have hidx : p - 1 + 1 = p := by omega
  rw [hidx, h] at hxp
  have hd : p + 2 ∣ x p := by
    rw [hxp]
    exact dvd_mul_left _ _
  have hd2 : p + 2 ∣ x (p + 1) :=
    hd.trans (x_dvd_of_le (by omega : 0 < p) (by omega))
  have hpos2 : 0 < p + 1 := by omega
  rw [a_eq hpos2]
  have hsum : p + 1 + 1 = p + 2 := by omega
  rw [hsum, Nat.gcd_eq_right hd2, Nat.div_self (by omega : 0 < p + 2)]

/-- Every prime `r ≥ 7` with `r ≡ 2 (mod 3)` contributes the factor `r+2` to `x r`. -/
lemma add_two_dvd_x_of_mod_three {r : ℕ} (hr : r.Prime) (hr7 : 7 ≤ r)
    (hmod : r % 3 = 2) : r + 2 ∣ x r := by
  have h := x_succ_a (n := r - 1) (by omega)
  have hidx : r - 1 + 1 = r := by omega
  have ha := conjecture_of_mod_three hr hr7 hmod
  rw [hidx, ha] at h
  rw [h]
  exact dvd_mul_left _ _

/-- McEachen holds at `p` as soon as some factor of `p-2` already divides `x(p-3)`. -/
theorem conjecture_of_factor_dvd_x {p q : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p)
    (hq : 1 < q) (hqp : q ∣ p - 2) (hx : q ∣ x (p - 3)) : a (p - 1) = p := by
  have hg : q ∣ Nat.gcd (x (p - 3)) (p - 2) := Nat.dvd_gcd hx hqp
  have hgt : 1 < Nat.gcd (x (p - 3)) (p - 2) := by
    have : q ≤ Nat.gcd (x (p - 3)) (p - 2) :=
      Nat.le_of_dvd (Nat.gcd_pos_of_pos_right _ (by omega)) hg
    omega
  exact a_eq_self_of_gcd_gt_one hp hp5 hgt

/-- If a prime `r ≡ 2 (mod 3)` injects a factor of `p-2` by index `r ≤ p-3`, McEachen holds. -/
theorem conjecture_of_injected {p r q : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p)
    (hr : r.Prime) (hr7 : 7 ≤ r) (hmod : r % 3 = 2) (hrle : r ≤ p - 3)
    (hq : 1 < q) (hqr : q ∣ r + 2) (hqp : q ∣ p - 2) : a (p - 1) = p := by
  have hx : q ∣ x r := hqr.trans (add_two_dvd_x_of_mod_three hr hr7 hmod)
  have hx2 : q ∣ x (p - 3) :=
    hx.trans (x_dvd_of_le (by omega : 0 < r) hrle)
  exact conjecture_of_factor_dvd_x hp hp5 hq hqp hx2

lemma not_three_dvd_prime_gt {p : ℕ} (hp : p.Prime) (hp3 : 3 < p) : ¬ 3 ∣ p := by
  intro h
  have := (Nat.prime_dvd_prime_iff_eq (by decide : Nat.Prime 3) hp).1 h
  omega

/-- The smaller member of a twin pair `≥ 11` is `≡ 2 (mod 3)`. -/
lemma smaller_twin_mod_three {p : ℕ} (hp : p.Prime) (hp11 : 11 ≤ p)
    (htwin : (p + 2).Prime) : p % 3 = 2 := by
  have hp3 : 3 < p := by omega
  have hq3 : 3 < p + 2 := by omega
  have hnp : ¬ 3 ∣ p := not_three_dvd_prime_gt hp hp3
  have hnq : ¬ 3 ∣ p + 2 := not_three_dvd_prime_gt htwin hq3
  have hcases : p % 3 = 0 ∨ p % 3 = 1 ∨ p % 3 = 2 := by omega
  rcases hcases with h | h | h
  · exact (hnp (Nat.dvd_of_mod_eq_zero h)).elim
  · have : (p + 2) % 3 = 0 := by omega
    exact (hnq (Nat.dvd_of_mod_eq_zero this)).elim
  · exact h

/-- Unconditional Cloitre 6.3 for twin pairs with smaller member `≥ 11`:
`a(p-1) = p` and `a(p+1) = 1`. No `C₁` hypothesis. -/
theorem twin_pair_inhibition {p : ℕ} (hp : p.Prime) (hp11 : 11 ≤ p)
    (htwin : (p + 2).Prime) : a (p - 1) = p ∧ a (p + 1) = 1 := by
  have hmod := smaller_twin_mod_three hp hp11 htwin
  have ha : a (p - 1) = p :=
    conjecture_of_mod_three hp (le_trans (by decide : 7 ≤ 11) hp11) hmod
  exact ⟨ha, inhibition (le_trans (by decide : 2 ≤ 11) hp11) ha⟩

/-- Larger twin primes `q ≥ 13` satisfy `a(q-1) = 1`. -/
theorem larger_twin_eq_one {q : ℕ} (hq : q.Prime) (h13 : 13 ≤ q)
    (htwin : (q - 2).Prime) : a (q - 1) = 1 := by
  have hp : (q - 2).Prime := htwin
  have hp11 : 11 ≤ q - 2 := by omega
  have ht : ((q - 2) + 2).Prime := by
    have : q - 2 + 2 = q := by omega
    rwa [this]
  have hpair := twin_pair_inhibition hp hp11 ht
  have hidx : (q - 2) + 1 = q - 1 := by omega
  simpa [hidx] using hpair.2

lemma a_10 : a 10 = 11 := by
  simpa using conjecture_of_mod_three (by decide : Nat.Prime 11) (by decide) (by decide)

lemma thirteen_dvd_x_11 : 13 ∣ x 11 := by
  have h := x_succ_a (n := 10) (by decide)
  rw [a_10] at h
  have hsum : (11 + 2 : ℕ) = 13 := by decide
  rw [h, hsum]
  exact dvd_mul_of_dvd_right (by decide : 13 ∣ 13) _

lemma thirteen_dvd_x {n : ℕ} (hn : 11 ≤ n) : 13 ∣ x n :=
  thirteen_dvd_x_11.trans (x_dvd_of_le (by decide : 0 < 11) hn)

theorem conjecture_of_thirteen_dvd {p : ℕ} (hp : p.Prime) (hp14 : 14 ≤ p)
    (h13 : 13 ∣ p - 2) : a (p - 1) = p :=
  conjecture_of_factor_dvd_x hp (by omega) (by decide : 1 < 13) h13
    (thirteen_dvd_x (by omega : 11 ≤ p - 3))

lemma a_52 : a 52 = 53 := by
  simpa using conjecture_of_mod_three (by decide : Nat.Prime 53) (by decide) (by decide)

lemma eleven_dvd_x_53 : 11 ∣ x 53 := by
  have h := x_succ_a (n := 52) (by decide)
  rw [a_52] at h
  have hsum : (53 + 2 : ℕ) = 55 := by decide
  rw [h, hsum]
  exact dvd_mul_of_dvd_right (by decide : 11 ∣ 55) _

lemma eleven_dvd_x {n : ℕ} (hn : 53 ≤ n) : 11 ∣ x n :=
  eleven_dvd_x_53.trans (x_dvd_of_le (by decide : 0 < 53) hn)

theorem conjecture_of_eleven_dvd {p : ℕ} (hp : p.Prime) (hp56 : 56 ≤ p)
    (h11 : 11 ∣ p - 2) : a (p - 1) = p :=
  conjecture_of_factor_dvd_x hp (by omega) (by decide : 1 < 11) h11
    (eleven_dvd_x (by omega : 53 ≤ p - 3))

lemma a_16 : a 16 = 17 := by
  simpa using conjecture_of_mod_three (by decide : Nat.Prime 17) (by decide) (by decide)

lemma nineteen_dvd_x_17 : 19 ∣ x 17 := by
  have h := x_succ_a (n := 16) (by decide)
  rw [a_16] at h
  have hsum : (17 + 2 : ℕ) = 19 := by decide
  rw [h, hsum]
  exact dvd_mul_of_dvd_right (by decide : 19 ∣ 19) _

lemma nineteen_dvd_x {n : ℕ} (hn : 17 ≤ n) : 19 ∣ x n :=
  nineteen_dvd_x_17.trans (x_dvd_of_le (by decide : 0 < 17) hn)

theorem conjecture_of_nineteen_dvd {p : ℕ} (hp : p.Prime) (hp20 : 20 ≤ p)
    (h19 : 19 ∣ p - 2) : a (p - 1) = p :=
  conjecture_of_factor_dvd_x hp (by omega) (by decide : 1 < 19) h19
    (nineteen_dvd_x (by omega : 17 ≤ p - 3))

private instance : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩

lemma a_pos {n : ℕ} (hn : 0 < n) : 0 < a n :=
  Nat.pos_of_dvd_of_pos (a_dvd hn) (Nat.succ_pos n)

lemma v2_gcd {m n : ℕ} (hm : 0 < m) (hn : 0 < n) :
    padicValNat 2 (Nat.gcd m n) = min (padicValNat 2 m) (padicValNat 2 n) := by
  have hg : Nat.gcd m n ≠ 0 := (Nat.gcd_pos_of_pos_left n hm).ne'
  have hm0 : m ≠ 0 := hm.ne'
  have hn0 : n ≠ 0 := hn.ne'
  apply le_antisymm
  · refine le_min ?_ ?_
    · exact (padicValNat_dvd_iff_le hm0).1 <|
        pow_padicValNat_dvd.trans (Nat.gcd_dvd_left m n)
    · exact (padicValNat_dvd_iff_le hn0).1 <|
        pow_padicValNat_dvd.trans (Nat.gcd_dvd_right m n)
  · have hpow : 2 ^ min (padicValNat 2 m) (padicValNat 2 n) ∣ Nat.gcd m n :=
      Nat.dvd_gcd ((padicValNat_dvd_iff_le hm0).2 (min_le_left _ _))
        ((padicValNat_dvd_iff_le hn0).2 (min_le_right _ _))
    exact (padicValNat_dvd_iff_le hg).1 hpow

lemma v2_a {n : ℕ} (hn : 0 < n) :
    padicValNat 2 (a n) =
      padicValNat 2 (n + 1) - min (padicValNat 2 (x n)) (padicValNat 2 (n + 1)) := by
  have hx := x_pos hn
  rw [a_eq hn, padicValNat.div_of_dvd (Nat.gcd_dvd_right _ _), v2_gcd hx (Nat.succ_pos n)]

lemma v2_x_succ {n : ℕ} (hn : 0 < n) :
    padicValNat 2 (x (n + 1)) = padicValNat 2 (x n) + padicValNat 2 (a n + 2) := by
  have hx := x_pos hn
  have ha : a n + 2 ≠ 0 := by omega
  rw [x_succ_a hn, padicValNat.mul hx.ne' ha]

lemma v2_a_eq_zero_of_le {n : ℕ} (hn : 0 < n)
    (h : padicValNat 2 (n + 1) ≤ padicValNat 2 (x n)) : padicValNat 2 (a n) = 0 := by
  rw [v2_a hn, min_eq_right h, Nat.sub_self]

lemma v2_add_two_of_v2_a_zero {n : ℕ} (hn : 0 < n)
    (h : padicValNat 2 (a n) = 0) : padicValNat 2 (a n + 2) = 0 := by
  have hnot : ¬ 2 ∣ a n := by
    intro hd
    have := one_le_padicValNat_of_dvd (a_pos hn).ne' hd
    omega
  have hiff : 2 ∣ a n + 2 ↔ 2 ∣ a n := by
    rw [add_comm]
    exact (Nat.dvd_add_iff_right (dvd_rfl : 2 ∣ 2)).symm
  exact padicValNat.eq_zero_of_not_dvd (hiff.not.mpr hnot)

lemma v2_x_succ_eq_of_le {n : ℕ} (hn : 0 < n)
    (h : padicValNat 2 (n + 1) ≤ padicValNat 2 (x n)) :
    padicValNat 2 (x (n + 1)) = padicValNat 2 (x n) := by
  rw [v2_x_succ hn, v2_add_two_of_v2_a_zero hn (v2_a_eq_zero_of_le hn h), add_zero]

lemma v2_lt_pow {t n : ℕ} (hn : n ≠ 0) (h : n < 2 ^ (t + 1)) : padicValNat 2 n ≤ t := by
  by_contra hne
  have hlt : t < padicValNat 2 n := Nat.lt_of_not_ge hne
  have : 2 ^ (t + 1) ∣ n := (padicValNat_dvd_iff_le hn).2 (Nat.succ_le_iff.2 hlt)
  exact (Nat.le_of_dvd (Nat.pos_of_ne_zero hn) this).not_gt h

lemma two_mul_four_pow (k : ℕ) : 2 * 4 ^ k = 2 ^ (2 * k + 1) := by
  rw [show (4 : ℕ) = 2 ^ 2 from rfl, ← pow_mul, Nat.mul_comm 2 k, pow_succ, mul_comm]

lemma v2_x_two : padicValNat 2 (x 2) = 2 := by
  have : x 2 = 4 := by decide
  rw [this, show (4 : ℕ) = 2 ^ 2 from rfl, padicValNat.prime_pow]

lemma exists_block {n : ℕ} (hn : 2 ≤ n) :
    ∃ k, 2 * 4 ^ k ≤ n ∧ n ≤ 2 * 4 ^ (k + 1) - 1 := by
  have hb : 1 < (4 : ℕ) := by decide
  have hpos : 0 < n / 2 := Nat.div_pos (le_trans (by decide : 2 ≤ 2) hn) (by decide)
  refine ⟨Nat.log 4 (n / 2), ?_, ?_⟩
  · have hle : 4 ^ Nat.log 4 (n / 2) ≤ n / 2 := Nat.pow_log_le_self 4 hpos.ne'
    have : 2 * 4 ^ Nat.log 4 (n / 2) ≤ 2 * (n / 2) := Nat.mul_le_mul_left 2 hle
    exact this.trans (Nat.mul_div_le n 2)
  · have hlt : n / 2 < 4 ^ (Nat.log 4 (n / 2) + 1) := Nat.lt_pow_succ_log_self hb (n / 2)
    have hlt' : n < 2 * 4 ^ (Nat.log 4 (n / 2) + 1) := by
      have h := (Nat.div_lt_iff_lt_mul (by decide : 0 < 2)).1 hlt
      rwa [mul_comm] at h
    exact Nat.le_sub_one_of_lt hlt'

/-- Cloitre's 2-adic identity in Lean indexing at the first staircase step. -/
theorem a_two_four_pow_zero : a (2 * 4 ^ 0 - 1) = 2 := a_1

#print axioms conjecture_of_mod_three
#print axioms twin_pair_inhibition
#print axioms larger_twin_eq_one
#print axioms conjecture_of_factor_dvd_x
#print axioms conjecture_of_injected
#print axioms inhibition
#print axioms conjecture_of_thirteen_dvd
#print axioms conjecture_of_eleven_dvd
#print axioms conjecture_of_nineteen_dvd
#print axioms conjecture_of_seven_dvd
#print axioms conjecture_of_five_dvd
#print axioms conjecture_two
#print axioms conjecture_three
#print axioms a_pos
#print axioms v2_a
#print axioms v2_x_succ
#print axioms a_two_four_pow_zero

end OeisA135508
