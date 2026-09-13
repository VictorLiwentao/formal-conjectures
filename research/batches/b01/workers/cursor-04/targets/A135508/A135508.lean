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
They also prove Cloitre's 2-adic staircase `a(2 · 4^k - 1) = 2`, the
remaining-class factor `q ≡ 2 (mod 3)` of `p-2`, injection of a factor of
`p-2` when some `kq-2` is a prime `≡ 2 (mod 3)`, McEachen when a factor of
`p-2` is a larger twin, Cloitre's valuation barrier, remaining McEachen
when `lpf(p-2) ≤ 101` or that least factor is a larger twin, Dirichlet
existence of some (unbounded) prime injector for every prime `q ≥ 5`,
and that `3 ∣ a n` for `n ≥ 3` forces `9 ∣ n+1`.
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

lemma two_dvd_x_two : 2 ∣ x 2 := by
  have : x 2 = 4 := by decide
  rw [this]
  decide

lemma two_dvd_x {n : ℕ} (hn : 2 ≤ n) : 2 ∣ x n :=
  two_dvd_x_two.trans (x_dvd_of_le (by decide : 0 < 2) hn)

/-- If `3 ∣ n+1` and `n ≥ 4`, then `x n` and `n+1` are not coprime. -/
lemma gcd_gt_one_of_three_dvd_succ {n : ℕ} (hn : 4 ≤ n) (h3 : 3 ∣ n + 1) :
    1 < Nat.gcd (x n) (n + 1) := by
  have hx := three_dvd_x hn
  have hg : 3 ∣ Nat.gcd (x n) (n + 1) := Nat.dvd_gcd hx h3
  have : 3 ≤ Nat.gcd (x n) (n + 1) :=
    Nat.le_of_dvd (Nat.gcd_pos_of_pos_right _ (by omega)) hg
  omega

/-- If `n ≥ 3` and `3 ∣ a n`, then `9 ∣ n+1`. In particular `3 ∤ a n`
whenever `9` does not divide `n+1`. -/
lemma nine_dvd_succ_of_three_dvd_a {n : ℕ} (hn : 3 ≤ n) (h3 : 3 ∣ a n) :
    9 ∣ n + 1 := by
  have hnpos : 0 < n := by omega
  by_cases hn4 : 4 ≤ n
  · have hsucc : 3 ∣ n + 1 := h3.trans (a_dvd hnpos)
    have hg3 : 3 ∣ Nat.gcd (x n) (n + 1) :=
      Nat.dvd_gcd (three_dvd_x hn4) hsucc
    have hmul := a_mul_gcd hnpos
    have : 3 * 3 ∣ a n * Nat.gcd (x n) (n + 1) := Nat.mul_dvd_mul h3 hg3
    rwa [hmul] at this
  · have heq : n = 3 := by omega
    subst heq
    have : ¬ 3 ∣ a 3 := by
      rw [a_3]
      decide
    exact False.elim (this h3)

lemma not_three_dvd_a_of_not_nine {n : ℕ} (hn : 3 ≤ n) (h9 : ¬ 9 ∣ n + 1) :
    ¬ 3 ∣ a n := fun h => h9 (nine_dvd_succ_of_three_dvd_a hn h)

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

lemma larger_twin_dvd_x {q : ℕ} (hq : q.Prime) (h13 : 13 ≤ q)
    (htwin : (q - 2).Prime) : q ∣ x (q - 1) :=
  (a_eq_one_iff_dvd hq).1 (larger_twin_eq_one hq h13 htwin)

/-- McEachen at `p` if some prime factor of `p-2` is a larger twin `≥ 13`. -/
theorem conjecture_of_larger_twin_dvd {p q : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p)
    (hp_twin : ¬ (p - 2).Prime) (hq : q.Prime) (h13 : 13 ≤ q)
    (htwin : (q - 2).Prime) (hqp : q ∣ p - 2) : a (p - 1) = p := by
  have hx : q ∣ x (q - 1) := larger_twin_dvd_x hq h13 htwin
  have hle : q - 1 ≤ p - 3 := by
    have hpos : 0 < p - 2 := by omega
    have hqle : q ≤ p - 2 := Nat.le_of_dvd hpos hqp
    have hne : q ≠ p - 2 := by
      intro h
      exact hp_twin (h ▸ hq)
    omega
  have hx2 : q ∣ x (p - 3) :=
    hx.trans (x_dvd_of_le (by omega : 0 < q - 1) hle)
  exact conjecture_of_factor_dvd_x hp hp5 (lt_of_lt_of_le (by decide : 1 < 13) h13) hqp hx2

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

lemma a_eq_succ_iff {n : ℕ} (hn : 0 < n) :
    a n = n + 1 ↔ Nat.gcd (x n) (n + 1) = 1 := by
  have hmul := a_mul_gcd hn
  constructor
  · intro h
    rw [h] at hmul
    exact Nat.eq_of_mul_eq_mul_left (Nat.succ_pos n) (by simpa using hmul)
  · intro h
    rw [a_eq hn, h, Nat.div_one]

/-- If `gcd(x n, n+1) = 1`, then `n+3` enters `x` at the next index. -/
lemma dvd_add_three_of_coprime {n : ℕ} (hn : 0 < n)
    (hc : Nat.gcd (x n) (n + 1) = 1) : n + 3 ∣ x (n + 1) := by
  have hstep := x_succ_a hn
  have ha : a n = n + 1 := (a_eq_succ_iff hn).2 hc
  rw [hstep, ha]
  have : n + 1 + 2 = n + 3 := by omega
  rw [this]
  exact dvd_mul_left _ _

/-- Composite injection: if `gcd(x(kq-3), kq-2) = 1`, then `kq` divides `x(kq-2)`.
This does not require `kq-2` to be prime. -/
lemma dvd_x_of_coprime_shift {k q : ℕ} (hpos : 0 < k * q - 3)
    (hc : Nat.gcd (x (k * q - 3)) (k * q - 2) = 1) :
    k * q ∣ x (k * q - 2) := by
  have hidx : k * q - 3 + 1 = k * q - 2 := by omega
  have hc' : Nat.gcd (x (k * q - 3)) (k * q - 3 + 1) = 1 := by
    rwa [hidx]
  have ha : a (k * q - 3) = k * q - 2 := by
    have h := (a_eq_succ_iff hpos).2 hc'
    rwa [hidx] at h
  have hstep := x_succ_a hpos
  rw [hidx, ha] at hstep
  have : k * q - 2 + 2 = k * q := by omega
  rw [hstep, this]
  exact dvd_mul_left _ _

lemma q_dvd_x_of_coprime_shift {k q : ℕ} (hpos : 0 < k * q - 3)
    (hc : Nat.gcd (x (k * q - 3)) (k * q - 2) = 1) :
    q ∣ x (k * q - 2) :=
  (Nat.dvd_mul_left q k).trans (dvd_x_of_coprime_shift hpos hc)

/-- A number `≡ 2 (mod 3)` has a prime factor `≡ 2 (mod 3)`. -/
lemma exists_prime_factor_mod_three (n : ℕ) :
    1 < n → n % 3 = 2 → ∃ q, q.Prime ∧ q ∣ n ∧ q % 3 = 2 := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro hn hmod
    have hminp : (Nat.minFac n).Prime := Nat.minFac_prime (ne_of_gt hn)
    have hdvd : Nat.minFac n ∣ n := Nat.minFac_dvd n
    have hne3 : Nat.minFac n ≠ 3 := by
      intro heq
      have : 3 ∣ n := by rwa [heq] at hdvd
      have : n % 3 = 0 := Nat.mod_eq_zero_of_dvd this
      omega
    have hmodp : Nat.minFac n % 3 = 1 ∨ Nat.minFac n % 3 = 2 := by
      have h2 : 2 ≤ Nat.minFac n := hminp.two_le
      have hcases : Nat.minFac n % 3 = 0 ∨ Nat.minFac n % 3 = 1 ∨
          Nat.minFac n % 3 = 2 := by omega
      rcases hcases with h0 | h | h
      · have : 3 ∣ Nat.minFac n := Nat.dvd_of_mod_eq_zero h0
        have heq : Nat.minFac n = 3 :=
          ((Nat.prime_dvd_prime_iff_eq Nat.prime_three hminp).1 this).symm
        exact (hne3 heq).elim
      · exact Or.inl h
      · exact Or.inr h
    rcases hmodp with h1 | h2
    · by_cases hpr : n.Prime
      · have : Nat.minFac n = n := hpr.minFac_eq
        have : n % 3 = 1 := by rwa [this] at h1
        omega
      · set m := n / Nat.minFac n
        have hmul : Nat.minFac n * m = n := Nat.mul_div_cancel' hdvd
        have hm1 : 1 < m := by
          have hge : Nat.minFac n ≤ m :=
            Nat.minFac_le_div (Nat.zero_lt_of_lt hn) hpr
          have : 2 ≤ Nat.minFac n := hminp.two_le
          omega
        have hmmod : m % 3 = 2 := by
          have hprod : (Nat.minFac n * m) % 3 = n % 3 := by rw [hmul]
          rw [Nat.mul_mod, h1, hmod] at hprod
          have hm3 : m % 3 = 0 ∨ m % 3 = 1 ∨ m % 3 = 2 := by omega
          rcases hm3 with hm0 | hm1' | hm2
          · simp [hm0] at hprod
          · simp [hm1'] at hprod
          · exact hm2
        have hmlt : m < n := by
          have hge : 2 ≤ Nat.minFac n := hminp.two_le
          have hmpos : 0 < m := Nat.zero_lt_of_lt hm1
          have hlt : m < Nat.minFac n * m := by
            have : 1 * m < Nat.minFac n * m :=
              Nat.mul_lt_mul_of_pos_right (Nat.lt_of_succ_le hge) hmpos
            rwa [Nat.one_mul] at this
          rwa [hmul] at hlt
        obtain ⟨q, hq, hdq, hqmod⟩ := ih m hmlt hm1 hmmod
        exact ⟨q, hq, hmul ▸ dvd_mul_of_dvd_right hdq (Nat.minFac n), hqmod⟩
    · exact ⟨n.minFac, hminp, hdvd, h2⟩

lemma p_sub_two_mod {p : ℕ} (hp4 : 4 ≤ p) (h : p % 3 = 1) : (p - 2) % 3 = 2 := by
  have hrep : p = 3 * (p / 3) + 1 := by
    simpa [Nat.mul_comm, h] using (Nat.div_add_mod p 3).symm
  omega

lemma exists_remaining_factor {p : ℕ} (hp : p.Prime) (hp7 : 7 ≤ p)
    (hmod : p % 3 = 1) :
    ∃ q, q.Prime ∧ q ∣ p - 2 ∧ q % 3 = 2 ∧ 5 ≤ q := by
  have hn : 1 < p - 2 := by omega
  have hpm : (p - 2) % 3 = 2 :=
    p_sub_two_mod (le_trans (by decide : 4 ≤ 7) hp7) hmod
  obtain ⟨q, hq, hd, hqmod⟩ := exists_prime_factor_mod_three (p - 2) hn hpm
  refine ⟨q, hq, hd, hqmod, ?_⟩
  have hq2 : q ≠ 2 := by
    intro h2
    have hd2 : 2 ∣ p - 2 := by rwa [h2] at hd
    have hpeq : p = p - 2 + 2 := by omega
    have hd2p : 2 ∣ p := by
      rw [hpeq]
      exact Nat.dvd_add hd2 (by decide)
    have : p = 2 := ((Nat.prime_dvd_prime_iff_eq Nat.prime_two hp).1 hd2p).symm
    omega
  have hq3 : q ≠ 3 := by
    intro h3
    have : 3 ∣ p - 2 := by rwa [h3] at hd
    have : (p - 2) % 3 = 0 := Nat.mod_eq_zero_of_dvd this
    omega
  have : 2 ≤ q := hq.two_le
  omega

/-- For odd composite `n ≡ 2 (mod 3)`, the least prime factor satisfies
`q(q+2) ≤ n`. Squares are `≡ 1 (mod 3)`, so the cofactor is at least `q+2`. -/
lemma sq_mod_three_of_ne_three {q : ℕ} (hq : q.Prime) (h3 : q ≠ 3) :
    (q * q) % 3 = 1 := by
  have h2 : 2 ≤ q := hq.two_le
  have hmod : q % 3 = 1 ∨ q % 3 = 2 := by
    have hcases : q % 3 = 0 ∨ q % 3 = 1 ∨ q % 3 = 2 := by omega
    rcases hcases with h0 | h | h
    · have : 3 ∣ q := Nat.dvd_of_mod_eq_zero h0
      have heq : q = 3 :=
        ((Nat.prime_dvd_prime_iff_eq Nat.prime_three hq).1 this).symm
      exact (h3 heq).elim
    · exact Or.inl h
    · exact Or.inr h
  rw [Nat.mul_mod]
  cases hmod with
  | inl h => simp [h]
  | inr h => simp [h]

lemma minFac_mul_add_two_le {n : ℕ} (hn : 1 < n) (hnp : ¬ n.Prime)
    (hmod : n % 3 = 2) (hodd : n % 2 = 1) :
    Nat.minFac n * (Nat.minFac n + 2) ≤ n := by
  have hminp : (Nat.minFac n).Prime := Nat.minFac_prime (ne_of_gt hn)
  have hd : Nat.minFac n ∣ n := Nat.minFac_dvd n
  have hq2 : Nat.minFac n ≠ 2 := by
    intro h
    have : 2 ∣ n := by
      rw [← Nat.minFac_eq_two_iff]
      exact h
    have : n % 2 = 0 := Nat.mod_eq_zero_of_dvd this
    omega
  have hq3 : Nat.minFac n ≠ 3 := by
    intro h
    have : 3 ∣ n := by rwa [h] at hd
    have : n % 3 = 0 := Nat.mod_eq_zero_of_dvd this
    omega
  have hq5 : 5 ≤ Nat.minFac n := by
    have h2 : 2 ≤ Nat.minFac n := hminp.two_le
    have hgt2 : 2 < Nat.minFac n := lt_of_le_of_ne h2 hq2.symm
    have hge3 : 3 ≤ Nat.minFac n := hgt2
    have hgt3 : 3 < Nat.minFac n := lt_of_le_of_ne hge3 hq3.symm
    have hge4 : 4 ≤ Nat.minFac n := hgt3
    have hne4 : Nat.minFac n ≠ 4 := by
      intro h4
      rw [h4] at hminp
      exact (by decide : ¬ Nat.Prime 4) hminp
    omega
  set q := Nat.minFac n
  set m := n / q
  have hmul : q * m = n := Nat.mul_div_cancel' hd
  have hmge : q ≤ m := Nat.minFac_le_div (Nat.zero_lt_of_lt hn) hnp
  have hne : m ≠ q := by
    intro hmeq
    have hn' : n = q * q := by rw [← hmul, hmeq]
    have : n % 3 = 1 := by
      rw [hn']
      exact sq_mod_three_of_ne_three hminp hq3
    omega
  have hoddq : q % 2 = 1 := by
    have h2 : 2 ≤ q := hminp.two_le
    have hcases : q % 2 = 0 ∨ q % 2 = 1 := by omega
    rcases hcases with h | h
    · have : 2 ∣ q := Nat.dvd_of_mod_eq_zero h
      have heq : q = 2 :=
        ((Nat.prime_dvd_prime_iff_eq Nat.prime_two hminp).1 this).symm
      exact (hq2 heq).elim
    · exact h
  have hoddm : m % 2 = 1 := by
    have : (q * m) % 2 = n % 2 := by rw [hmul]
    rw [Nat.mul_mod, hoddq, hodd] at this
    have hm2 : m % 2 = 0 ∨ m % 2 = 1 := by omega
    rcases hm2 with h0 | h1
    · simp [h0] at this
    · exact h1
  have hm2 : q + 2 ≤ m := by
    have : q + 1 ≤ m := by omega
    have hpar : (q + 1) % 2 = 0 := by omega
    have : m ≠ q + 1 := by
      intro hmeq
      have : m % 2 = 0 := by rw [hmeq]; exact hpar
      omega
    omega
  have : q * (q + 2) ≤ q * m := Nat.mul_le_mul_left q hm2
  rwa [hmul] at this

/-- If `kq-2` is an odd composite `≡ 2 (mod 3)` and its least prime factor
already divides `x` by the square-window index `s(s+2)-1`, then
`gcd(x(kq-3), kq-2) > 1`. That composite is not a coprime injector. -/
lemma gcd_gt_one_of_composite_shift {k q : ℕ}
    (_hpos : 0 < k * q - 3)
    (hgt : 1 < k * q - 2)
    (hcomp : ¬ (k * q - 2).Prime)
    (hmod : (k * q - 2) % 3 = 2)
    (hodd : (k * q - 2) % 2 = 1)
    (hind : Nat.minFac (k * q - 2) ∣
      x (Nat.minFac (k * q - 2) * (Nat.minFac (k * q - 2) + 2) - 1)) :
    1 < Nat.gcd (x (k * q - 3)) (k * q - 2) := by
  have hle := minFac_mul_add_two_le hgt hcomp hmod hodd
  have hminp : (Nat.minFac (k * q - 2)).Prime := Nat.minFac_prime (ne_of_gt hgt)
  have hs2 : 2 ≤ Nat.minFac (k * q - 2) := hminp.two_le
  have hmul : 2 * 4 ≤ Nat.minFac (k * q - 2) * (Nat.minFac (k * q - 2) + 2) :=
    Nat.mul_le_mul hs2 (Nat.add_le_add_right hs2 2)
  have hspos : 0 < Nat.minFac (k * q - 2) * (Nat.minFac (k * q - 2) + 2) - 1 :=
    Nat.sub_pos_of_lt (lt_of_lt_of_le (by decide : 1 < 8) hmul)
  have hidx : Nat.minFac (k * q - 2) * (Nat.minFac (k * q - 2) + 2) - 1 ≤
      k * q - 3 := by
    have hsub : Nat.minFac (k * q - 2) * (Nat.minFac (k * q - 2) + 2) - 1 ≤
        k * q - 2 - 1 := Nat.sub_le_sub_right hle 1
    have hidx' : k * q - 2 - 1 = k * q - 3 := Nat.sub_sub (k * q) 2 1
    exact hidx' ▸ hsub
  have hx : Nat.minFac (k * q - 2) ∣ x (k * q - 3) :=
    hind.trans (x_dvd_of_le hspos hidx)
  have hd : Nat.minFac (k * q - 2) ∣ k * q - 2 := Nat.minFac_dvd _
  have hg : Nat.minFac (k * q - 2) ∣ Nat.gcd (x (k * q - 3)) (k * q - 2) :=
    Nat.dvd_gcd hx hd
  have hge : Nat.minFac (k * q - 2) ≤ Nat.gcd (x (k * q - 3)) (k * q - 2) :=
    Nat.le_of_dvd (Nat.gcd_pos_of_pos_right _ (Nat.zero_lt_of_lt hgt)) hg
  exact Nat.lt_of_lt_of_le (by decide : 1 < 2) (le_trans hs2 hge)

lemma remaining_minFac_mul_add_two_le {p : ℕ} (hp : p.Prime) (hp7 : 7 ≤ p)
    (hmod : p % 3 = 1) (hcomp : ¬ (p - 2).Prime) :
    Nat.minFac (p - 2) * (Nat.minFac (p - 2) + 2) ≤ p - 2 := by
  have hn : 1 < p - 2 := by omega
  have hodd : (p - 2) % 2 = 1 := by
    have hpodd : p % 2 = 1 := by
      have hcases : p % 2 = 0 ∨ p % 2 = 1 := by omega
      rcases hcases with h0 | h1
      · have : 2 ∣ p := Nat.dvd_of_mod_eq_zero h0
        have : p = 2 :=
          ((Nat.prime_dvd_prime_iff_eq Nat.prime_two hp).1 this).symm
        omega
      · exact h1
    omega
  have hpm : (p - 2) % 3 = 2 :=
    p_sub_two_mod (le_trans (by decide : 4 ≤ 7) hp7) hmod
  exact minFac_mul_add_two_le hn hcomp hpm hodd

/-- Remaining McEachen reduces to first-entry of `lpf(p-2)` by index `q(q+2)-1`. -/
theorem conjecture_of_minFac_entered {p : ℕ} (hp : p.Prime) (hp7 : 7 ≤ p)
    (hmod : p % 3 = 1) (hcomp : ¬ (p - 2).Prime)
    (hin : Nat.minFac (p - 2) ∣
      x (Nat.minFac (p - 2) * (Nat.minFac (p - 2) + 2) - 1)) :
    a (p - 1) = p := by
  have hbound := remaining_minFac_mul_add_two_le hp hp7 hmod hcomp
  have hpr : (Nat.minFac (p - 2)).Prime := by
    refine Nat.minFac_prime ?_
    intro h
    have h2 : 2 ≤ p := le_trans (by decide : 2 ≤ 7) hp7
    have hp3 : p = 3 := by
      have hcancel := Nat.sub_add_cancel h2
      rw [h] at hcancel
      exact hcancel.symm
    exact Nat.ne_of_lt (lt_of_lt_of_le (by decide : 3 < 7) hp7) hp3.symm
  have hq2 : 2 ≤ Nat.minFac (p - 2) := hpr.two_le
  have hp5 : 5 ≤ p := le_trans (by decide : 5 ≤ 7) hp7
  have hmul : 2 * 4 ≤ Nat.minFac (p - 2) * (Nat.minFac (p - 2) + 2) :=
    Nat.mul_le_mul hq2 (Nat.add_le_add_right hq2 2)
  have hpos : 0 < Nat.minFac (p - 2) * (Nat.minFac (p - 2) + 2) - 1 :=
    Nat.sub_pos_of_lt (lt_of_lt_of_le (by decide : 1 < 8) hmul)
  have hle : Nat.minFac (p - 2) * (Nat.minFac (p - 2) + 2) - 1 ≤ p - 3 := by
    have hsub : Nat.minFac (p - 2) * (Nat.minFac (p - 2) + 2) - 1 ≤ p - 2 - 1 :=
      Nat.sub_le_sub_right hbound 1
    have : p - 2 - 1 = p - 3 := Nat.sub_sub p 2 1
    exact this ▸ hsub
  exact conjecture_of_factor_dvd_x hp hp5
    (lt_of_lt_of_le (by decide : 1 < 2) hq2) (Nat.minFac_dvd _)
    (hin.trans (x_dvd_of_le hpos hle))

lemma mul_sub_two_mod_three {k q : ℕ} (hk : k % 3 = 2) (hq : q % 3 = 2)
    (h4 : 4 ≤ k * q) : (k * q - 2) % 3 = 2 := by
  have hmul : (k * q) % 3 = 1 := by
    rw [Nat.mul_mod, hk, hq]
  have hrep : k * q = 3 * (k * q / 3) + 1 := by
    simpa [Nat.mul_comm, hmul] using (Nat.div_add_mod (k * q) 3).symm
  omega

/-- If `r = kq - 2` is a prime `≡ 2 (mod 3)`, then `q` enters `x` at index `r`.
This does not require `q ≡ 2 (mod 3)`. -/
lemma q_dvd_x_of_prime_index {k q : ℕ} (hpr : (k * q - 2).Prime)
    (h7 : 7 ≤ k * q - 2) (hmod : (k * q - 2) % 3 = 2) :
    q ∣ x (k * q - 2) := by
  have hx := add_two_dvd_x_of_mod_three hpr h7 hmod
  have : k * q - 2 + 2 = k * q := by omega
  rw [this] at hx
  exact (Nat.dvd_mul_left q k).trans hx

/-- If `r = kq - 2` is an odd prime `≡ 2 (mod 3)`, then `q` enters `x` at index `r`. -/
lemma q_dvd_x_of_prime_injector {k q : ℕ} (hmodk : k % 3 = 2) (hmodq : q % 3 = 2)
    (hpr : (k * q - 2).Prime) (h7 : 7 ≤ k * q - 2) :
    q ∣ x (k * q - 2) :=
  q_dvd_x_of_prime_index hpr h7 (mul_sub_two_mod_three hmodk hmodq (by omega))

/-- McEachen at `p` if some factor `q` of `p-2` is injected by a prime `kq-2 ≤ p-3`. -/
theorem conjecture_of_prime_injector {p k q : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p)
    (hmodk : k % 3 = 2) (hmodq : q % 3 = 2)
    (hpr : (k * q - 2).Prime) (h7 : 7 ≤ k * q - 2)
    (hle : k * q - 2 ≤ p - 3) (hqp : q ∣ p - 2) (hq1 : 1 < q) :
    a (p - 1) = p := by
  have hx := q_dvd_x_of_prime_injector hmodk hmodq hpr h7
  have hpos : 0 < k * q - 2 := by omega
  have hx2 : q ∣ x (p - 3) := hx.trans (x_dvd_of_le hpos hle)
  exact conjecture_of_factor_dvd_x hp hp5 hq1 hqp hx2

/-- McEachen at `p` if some factor of `p-2` is injected by a prime `kq-2 ≡ 2 (mod 3)`. -/
theorem conjecture_of_prime_index {p k q : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p)
    (hpr : (k * q - 2).Prime) (h7 : 7 ≤ k * q - 2)
    (hmod : (k * q - 2) % 3 = 2) (hle : k * q - 2 ≤ p - 3)
    (hqp : q ∣ p - 2) (hq1 : 1 < q) : a (p - 1) = p := by
  have hx := q_dvd_x_of_prime_index hpr h7 hmod
  have hpos : 0 < k * q - 2 := by omega
  have hx2 : q ∣ x (p - 3) := hx.trans (x_dvd_of_le hpos hle)
  exact conjecture_of_factor_dvd_x hp hp5 hq1 hqp hx2

lemma odd_of_prime_mod_three_two {q : ℕ} (hq : q.Prime) (h7 : 7 ≤ q)
    (_hmod : q % 3 = 2) : q % 2 = 1 := by
  rcases hq.eq_two_or_odd with h2 | hodd
  · omega
  · exact hodd

/-- Even `k` never yields a prime injector: `kq-2` is even and at least `8`. -/
lemma kq_sub_two_even {k q : ℕ} (hk : k % 2 = 0) (hq : q % 2 = 1)
    (h2 : 2 ≤ k * q) : (k * q - 2) % 2 = 0 := by
  have hmul : (k * q) % 2 = 0 := by
    rw [Nat.mul_mod, hk, hq]
  omega

lemma not_prime_kq_sub_two_of_even {k q : ℕ} (hk : k % 2 = 0) (hq : q % 2 = 1)
    (h2 : 2 ≤ k) (h5 : 5 ≤ q) : ¬ (k * q - 2).Prime := by
  have h10 : 10 ≤ k * q := Nat.mul_le_mul h2 h5
  have heven : (k * q - 2) % 2 = 0 :=
    kq_sub_two_even hk hq (le_trans (by decide : 2 ≤ 10) h10)
  intro hpr
  rcases hpr.eq_two_or_odd with h2' | hodd
  · omega
  · omega

lemma not_prime_kq_sub_two_of_even_prime {k q : ℕ} (hq : q.Prime) (h7 : 7 ≤ q)
    (hmod : q % 3 = 2) (hk : k % 2 = 0) (h2 : 2 ≤ k) :
    ¬ (k * q - 2).Prime :=
  not_prime_kq_sub_two_of_even hk (odd_of_prime_mod_three_two hq h7 hmod) h2
    (le_trans (by decide : 5 ≤ 7) h7)

/-- If `k ≡ 1 (mod 3)` then `3 ∣ kq-2`. For `q ≥ 11` this is composite. -/
lemma kq_sub_two_mod_three_of_k_one {k q : ℕ} (hk : k % 3 = 1) (hq : q % 3 = 2)
    (h4 : 4 ≤ k * q) : (k * q - 2) % 3 = 0 := by
  have hmul : (k * q) % 3 = 2 := by
    rw [Nat.mul_mod, hk, hq]
  have hrep : k * q = 3 * (k * q / 3) + 2 := by
    simpa [Nat.mul_comm, hmul] using (Nat.div_add_mod (k * q) 3).symm
  omega

lemma not_prime_kq_sub_two_of_k_mod_one {k q : ℕ} (hk : k % 3 = 1) (hq : q % 3 = 2)
    (h1 : 1 ≤ k) (h11 : 11 ≤ q) : ¬ (k * q - 2).Prime := by
  have h4 : 4 ≤ k * q := by
    have : 1 * 11 ≤ k * q := Nat.mul_le_mul h1 h11
    omega
  have hmod0 := kq_sub_two_mod_three_of_k_one hk hq h4
  have h3 : 3 ∣ k * q - 2 := Nat.dvd_of_mod_eq_zero hmod0
  have hgt : 3 < k * q - 2 := by
    have : 11 ≤ k * q := Nat.mul_le_mul h1 h11
    omega
  intro hpr
  have heq : k * q - 2 = 3 :=
    ((Nat.prime_dvd_prime_iff_eq Nat.prime_three hpr).1 h3).symm
  omega

lemma odd_k_mod_three_two_iff {k : ℕ} (hk2 : k % 2 = 1) :
    k % 3 = 2 ↔ k % 6 = 5 := by
  have h6 : k % 6 = 1 ∨ k % 6 = 3 ∨ k % 6 = 5 := by omega
  constructor
  · intro h3
    rcases h6 with h | h | h
    · omega
    · omega
    · exact h
  · intro h
    omega

/-- A prime `q ≡ 2 (mod 3)`, `q ≥ 7`, does not divide `x n` for `0 < n ≤ q`.
In particular it does not enter at its own index. -/
lemma not_q_dvd_x_le {q n : ℕ} (hq : q.Prime) (hmod : q % 3 = 2) (h7 : 7 ≤ q)
    (hn : 0 < n) (hle : n ≤ q) : ¬ q ∣ x n := by
  intro hd
  obtain ⟨m, hmpos, hmle, hdm, hmin⟩ := exists_least_dvd hn hd
  have hmle' : m ≤ q := hmle.trans hle
  have hmne1 : m ≠ 1 := by
    intro hm1
    subst hm1
    exact not_prime_dvd_x_one hq hdm
  have hmpred : 0 < m - 1 := by omega
  have hnot : ¬ q ∣ x (m - 1) :=
    hmin (m - 1) hmpred (Nat.sub_lt hmpos (by decide))
  have hstep := x_succ_a hmpred
  have hm1 : m - 1 + 1 = m := Nat.sub_add_cancel (by omega)
  rw [hm1] at hstep
  have hmul : q ∣ x (m - 1) * (a (m - 1) + 2) := by
    rwa [← hstep]
  have hfac : q ∣ a (m - 1) + 2 :=
    (hq.dvd_mul.mp hmul).resolve_left hnot
  have hale := a_le_succ hmpred
  have hle_a : a (m - 1) + 2 ≤ m + 2 := by
    have h1 : a (m - 1) + 2 ≤ m - 1 + 1 + 2 := Nat.add_le_add_right hale 2
    have : m - 1 + 1 + 2 = m + 2 := by omega
    exact h1.trans this.le
  have hle2 : a (m - 1) + 2 ≤ q + 2 :=
    hle_a.trans (Nat.add_le_add_right hmle' 2)
  have hge : q ≤ a (m - 1) + 2 :=
    Nat.le_of_dvd (by omega) hfac
  have hcases : a (m - 1) + 2 = q ∨ a (m - 1) + 2 = q + 1 ∨
      a (m - 1) + 2 = q + 2 := by omega
  rcases hcases with h | h | h
  · have ha : a (m - 1) = q - 2 := by omega
    have hdivn : q - 2 ∣ m := by
      have h := a_dvd hmpred
      rwa [hm1, ha] at h
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
      · have hle2' : 2 * (q - 2) ≤ (q - 2) * k := by
          have := Nat.mul_le_mul_left (q - 2) h
          simpa [mul_comm] using this
        have : 2 * (q - 2) ≤ m := by
          rwa [← hk] at hle2'
        have : 2 * (q - 2) ≤ q := this.trans hmle'
        omega
    have hm2 : m = q - 2 := by
      rw [hk, hk1, Nat.mul_one]
    have hidx : m - 1 = q - 3 := by omega
    have hpos : 0 < q - 3 := by omega
    have hsum : q - 3 + 1 = q - 2 := by omega
    have hg : 1 < Nat.gcd (x (q - 3)) (q - 2) :=
      three_dvd_gcd h7 (three_dvd_of_mod (le_trans (by decide : 2 ≤ 7) h7) hmod)
    have haeq : a (q - 3) = q - 2 := by
      rw [← hidx, ha]
    have hcop : Nat.gcd (x (q - 3)) (q - 2) = 1 := by
      have ha' : a (q - 3) = q - 3 + 1 := by
        rwa [hsum]
      have hgcd := (a_eq_succ_iff hpos).1 ha'
      rwa [hsum] at hgcd
    omega
  · have : q ∣ q + 1 := by rwa [h] at hfac
    have : (q + 1) % q = 0 := Nat.mod_eq_zero_of_dvd this
    have : (q + 1) % q = 1 := by
      rw [Nat.add_comm q 1, Nat.add_mod_right]
      exact Nat.mod_eq_of_lt (by omega : 1 < q)
    omega
  · have hdq : q ∣ q + 2 := by rwa [h] at hfac
    have : q ∣ 2 :=
      (Nat.dvd_add_iff_left (dvd_rfl : q ∣ q)).mpr (by simpa [add_comm] using hdq)
    have : q = 2 := (Nat.prime_dvd_prime_iff_eq hq Nat.prime_two).1 this
    omega

lemma not_q_dvd_x_self {q : ℕ} (hq : q.Prime) (hmod : q % 3 = 2) (h7 : 7 ≤ q) :
    ¬ q ∣ x q :=
  not_q_dvd_x_le hq hmod h7 (by omega : 0 < q) le_rfl

/-- Specialization: a prime `5q-2` injects `q` at index `5q-2`. -/
lemma q_dvd_x_of_five_prime_injector {q : ℕ} (hmodq : q % 3 = 2)
    (hpr : (5 * q - 2).Prime) (h7 : 7 ≤ 5 * q - 2) :
    q ∣ x (5 * q - 2) :=
  q_dvd_x_of_prime_injector (k := 5) (by decide) hmodq hpr h7

theorem conjecture_of_five_prime_injector {p q : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p)
    (hmodq : q % 3 = 2) (hpr : (5 * q - 2).Prime) (h7 : 7 ≤ 5 * q - 2)
    (hle : 5 * q - 2 ≤ p - 3) (hqp : q ∣ p - 2) (hq1 : 1 < q) :
    a (p - 1) = p :=
  conjecture_of_prime_injector hp hp5 (by decide) hmodq hpr h7 hle hqp hq1

/-- Residue `5q-2` is coprime to the Dirichlet modulus `6q` when `q ≡ 2 (mod 3)`. -/
lemma coprime_five_mul_sub_two {q : ℕ} (hq : q.Prime) (h5 : 5 ≤ q)
    (hmod : q % 3 = 2) : Nat.Coprime (5 * q - 2) (6 * q) := by
  have h2le : 2 ≤ q := le_trans (by decide : 2 ≤ 5) h5
  have hrep : 5 * q - 2 = 4 * q + (q - 2) := by omega
  have hcopq : Nat.Coprime (5 * q - 2) q := by
    rw [hrep, Nat.coprime_mul_right_add_left, Nat.coprime_self_sub_left h2le]
    exact ((hq.coprime_iff_not_dvd).2 (by
      intro h
      have : q = 2 := (Nat.prime_dvd_prime_iff_eq hq Nat.prime_two).1 h
      omega)).symm
  have hcop2 : Nat.Coprime (5 * q - 2) 2 := by
    refine (Nat.prime_two.coprime_iff_not_dvd.2 ?_).symm
    intro h
    have hmod2 : (5 * q - 2) % 2 = 0 := Nat.mod_eq_zero_of_dvd h
    have hqodd : q % 2 = 1 := by
      rcases hq.eq_two_or_odd with h2 | hodd
      · omega
      · exact hodd
    omega
  have hcop3 : Nat.Coprime (5 * q - 2) 3 := by
    have hqrep : q = 3 * (q / 3) + 2 := by
      simpa [hmod] using (Nat.div_add_mod q 3).symm
    have hmod3 : (5 * q - 2) % 3 = 2 := by omega
    refine (Nat.prime_three.coprime_iff_not_dvd.2 ?_).symm
    intro h
    have : (5 * q - 2) % 3 = 0 := Nat.mod_eq_zero_of_dvd h
    omega
  have hcop6 : Nat.Coprime (5 * q - 2) 6 := hcop2.mul_right hcop3
  exact hcop6.mul_right hcopq

/-- Residue `q-2` is coprime to `6q` when `q ≡ 1 (mod 3)`. -/
lemma coprime_sub_two_six_mul {q : ℕ} (hq : q.Prime) (h7 : 7 ≤ q)
    (hmod : q % 3 = 1) : Nat.Coprime (q - 2) (6 * q) := by
  have h2le : 2 ≤ q := le_trans (by decide : 2 ≤ 7) h7
  have hcopq : Nat.Coprime (q - 2) q := by
    rw [Nat.coprime_self_sub_left h2le]
    exact ((hq.coprime_iff_not_dvd).2 (by
      intro h
      have : q = 2 := (Nat.prime_dvd_prime_iff_eq hq Nat.prime_two).1 h
      omega)).symm
  have hcop2 : Nat.Coprime (q - 2) 2 := by
    refine (Nat.prime_two.coprime_iff_not_dvd.2 ?_).symm
    intro h
    have hmod2 : (q - 2) % 2 = 0 := Nat.mod_eq_zero_of_dvd h
    have hqodd : q % 2 = 1 := by
      rcases hq.eq_two_or_odd with h2 | hodd
      · omega
      · exact hodd
    omega
  have hcop3 : Nat.Coprime (q - 2) 3 := by
    have hqrep : q = 3 * (q / 3) + 1 := by
      simpa [hmod] using (Nat.div_add_mod q 3).symm
    have hmod3 : (q - 2) % 3 = 2 := by omega
    refine (Nat.prime_three.coprime_iff_not_dvd.2 ?_).symm
    intro h
    have : (q - 2) % 3 = 0 := Nat.mod_eq_zero_of_dvd h
    omega
  have hcop6 : Nat.Coprime (q - 2) 6 := hcop2.mul_right hcop3
  exact hcop6.mul_right hcopq

lemma five_residue_add {q t : ℕ} (h2 : 2 ≤ 5 * q) :
    6 * q * t + (5 * q - 2) + 2 = (6 * t + 5) * q := by
  have hmul : (6 * t + 5) * q = 6 * q * t + 5 * q := by ring
  have h5 : (5 * q - 2) + 2 = 5 * q := Nat.sub_add_cancel h2
  omega

lemma injector_eq_of_five_residue {q r : ℕ} (h2 : 2 ≤ 5 * q)
    (hsum : 6 * q * (r / (6 * q)) + (5 * q - 2) = r) :
    (6 * (r / (6 * q)) + 5) * q - 2 = r := by
  have hplus : (6 * (r / (6 * q)) + 5) * q = r + 2 := by
    have := five_residue_add (t := r / (6 * q)) h2
    omega
  have hle : 2 ≤ (6 * (r / (6 * q)) + 5) * q := by
    omega
  exact (Nat.sub_eq_iff_eq_add hle).2 hplus

lemma r_mod_three_of_five_residue {q r : ℕ} (hmod : q % 3 = 2)
    (hr : r % (6 * q) = 5 * q - 2) : r % 3 = 2 := by
  have hdiv := Nat.div_add_mod r (6 * q)
  rw [hr] at hdiv
  have hqrep : q = 3 * (q / 3) + 2 := by
    simpa [hmod] using (Nat.div_add_mod q 3).symm
  have h52 : (5 * q - 2) % 3 = 2 := by omega
  have h60 : (6 * q * (r / (6 * q))) % 3 = 0 := by
    have : (6 * q) % 3 = 0 := by omega
    rw [Nat.mul_mod, this, Nat.zero_mul, Nat.zero_mod]
  have : r % 3 = (6 * q * (r / (6 * q)) + (5 * q - 2)) % 3 := by
    rw [hdiv]
  rw [this, Nat.add_mod, h60, Nat.zero_add, Nat.mod_mod, h52]

lemma injector_eq_of_one_residue {q r : ℕ} (h2 : 2 ≤ q)
    (hsum : 6 * q * (r / (6 * q)) + (q - 2) = r) :
    (6 * (r / (6 * q)) + 1) * q - 2 = r := by
  have hplus : (6 * (r / (6 * q)) + 1) * q = r + 2 := by
    have : (q - 2) + 2 = q := Nat.sub_add_cancel h2
    have hmul : (6 * (r / (6 * q)) + 1) * q =
        6 * q * (r / (6 * q)) + q := by ring
    omega
  have hle : 2 ≤ (6 * (r / (6 * q)) + 1) * q := by omega
  exact (Nat.sub_eq_iff_eq_add hle).2 hplus

lemma r_mod_three_of_one_residue {q r : ℕ} (h2 : 2 ≤ q) (hmod : q % 3 = 1)
    (hr : r % (6 * q) = q - 2) : r % 3 = 2 := by
  have hdiv := Nat.div_add_mod r (6 * q)
  rw [hr] at hdiv
  have hqrep : q = 3 * (q / 3) + 1 := by
    simpa [hmod] using (Nat.div_add_mod q 3).symm
  have h52 : (q - 2) % 3 = 2 := by omega
  have h60 : (6 * q * (r / (6 * q))) % 3 = 0 := by
    have : (6 * q) % 3 = 0 := by omega
    rw [Nat.mul_mod, this, Nat.zero_mul, Nat.zero_mod]
  have : r % 3 = (6 * q * (r / (6 * q)) + (q - 2)) % 3 := by
    rw [hdiv]
  rw [this, Nat.add_mod, h60, Nat.zero_add, Nat.mod_mod, h52]

/-- Dirichlet: some prime `r = kq-2` with `k ≡ 5 (mod 6)` and `r ≡ 2 (mod 3)`.
This does not bound `r` by `q(q+2)-1`. -/
lemma exists_prime_index_injector {q : ℕ} (hq : q.Prime) (h5 : 5 ≤ q)
    (hmod : q % 3 = 2) :
    ∃ k, (k * q - 2).Prime ∧ 7 ≤ k * q - 2 ∧ (k * q - 2) % 3 = 2 ∧ k % 6 = 5 := by
  obtain ⟨r, _hrgt, hpr, hrmod⟩ :=
    Nat.forall_exists_prime_gt_and_modEq 1 (q := 6 * q) (a := 5 * q - 2)
      (by omega : 6 * q ≠ 0) (coprime_five_mul_sub_two hq h5 hmod)
  have hlt : 5 * q - 2 < 6 * q := by omega
  have hres : (5 * q - 2) % (6 * q) = 5 * q - 2 := Nat.mod_eq_of_lt hlt
  have hr_mod : r % (6 * q) = 5 * q - 2 := by
    have : r % (6 * q) = (5 * q - 2) % (6 * q) := hrmod
    rwa [hres] at this
  have hsum : 6 * q * (r / (6 * q)) + (5 * q - 2) = r := by
    have := Nat.div_add_mod r (6 * q)
    rwa [hr_mod] at this
  have h2 : 2 ≤ 5 * q := by omega
  have heq := injector_eq_of_five_residue h2 hsum
  refine ⟨6 * (r / (6 * q)) + 5, ?_, ?_, ?_, ?_⟩
  · rwa [heq]
  · have : 5 * q - 2 ≤ r := by omega
    have : 23 ≤ 5 * q - 2 := by omega
    omega
  · have hmod3 := r_mod_three_of_five_residue hmod hr_mod
    rwa [heq]
  · omega

/-- Dirichlet: some prime `r = kq-2 ≡ 2 (mod 3)` when `q ≡ 1 (mod 3)`.
Typical residue is `k ≡ 1 (mod 6)`. No square-window bound. -/
lemma exists_prime_index_injector_mod_one {q : ℕ} (hq : q.Prime) (h7 : 7 ≤ q)
    (hmod : q % 3 = 1) :
    ∃ k, (k * q - 2).Prime ∧ 7 ≤ k * q - 2 ∧ (k * q - 2) % 3 = 2 ∧ k % 6 = 1 := by
  obtain ⟨r, hrgt, hpr, hrmod⟩ :=
    Nat.forall_exists_prime_gt_and_modEq 6 (q := 6 * q) (a := q - 2)
      (by omega : 6 * q ≠ 0) (coprime_sub_two_six_mul hq h7 hmod)
  have hlt : q - 2 < 6 * q := by omega
  have hres : (q - 2) % (6 * q) = q - 2 := Nat.mod_eq_of_lt hlt
  have hr_mod : r % (6 * q) = q - 2 := by
    have : r % (6 * q) = (q - 2) % (6 * q) := hrmod
    rwa [hres] at this
  have hsum : 6 * q * (r / (6 * q)) + (q - 2) = r := by
    have := Nat.div_add_mod r (6 * q)
    rwa [hr_mod] at this
  have h2 : 2 ≤ q := le_trans (by decide : 2 ≤ 7) h7
  have heq := injector_eq_of_one_residue h2 hsum
  refine ⟨6 * (r / (6 * q)) + 1, ?_, ?_, ?_, ?_⟩
  · rwa [heq]
  · have : 7 ≤ r := by omega
    omega
  · have hmod3 := r_mod_three_of_one_residue h2 hmod hr_mod
    rwa [heq]
  · omega

/-- Every prime `q ≡ 2 (mod 3)` eventually divides `x`. No index bound. -/
lemma q_dvd_x_eventually {q : ℕ} (hq : q.Prime) (h5 : 5 ≤ q)
    (hmod : q % 3 = 2) : ∃ n, q ∣ x n := by
  obtain ⟨k, hpr, h7, hrmod, _⟩ := exists_prime_index_injector hq h5 hmod
  exact ⟨k * q - 2, q_dvd_x_of_prime_index hpr h7 hrmod⟩

/-- Every prime `q ≡ 1 (mod 3)` with `q ≥ 7` eventually divides `x`. -/
lemma q_dvd_x_eventually_mod_one {q : ℕ} (hq : q.Prime) (h7 : 7 ≤ q)
    (hmod : q % 3 = 1) : ∃ n, q ∣ x n := by
  obtain ⟨k, hpr, h7k, hrmod, _⟩ := exists_prime_index_injector_mod_one hq h7 hmod
  exact ⟨k * q - 2, q_dvd_x_of_prime_index hpr h7k hrmod⟩

/-- Remaining McEachen primes reduce to one prime injector `kq-2 ≤ p-3`. -/
theorem conjecture_of_remaining_injector {p : ℕ} (hp : p.Prime) (hp7 : 7 ≤ p)
    (hmod : p % 3 = 1) (_hcomp : ¬ (p - 2).Prime)
    (hinj : ∃ q k, q.Prime ∧ q ∣ p - 2 ∧ q % 3 = 2 ∧ 1 < q ∧
        k % 3 = 2 ∧ (k * q - 2).Prime ∧ 7 ≤ k * q - 2 ∧ k * q - 2 ≤ p - 3) :
    a (p - 1) = p := by
  obtain ⟨q, k, _hq, hqp, hmodq, hq1, hmodk, hpr, h7k, hle⟩ := hinj
  exact conjecture_of_prime_injector hp (by omega) hmodk hmodq hpr h7k hle hqp hq1

/-- The frozen dichotomy: `2`, `3`, every `p ≡ 2 (mod 3)`, or a remaining injector. -/
theorem conjecture_of_cases {p : ℕ} (hp : p.Prime) (hp_twin : ¬ (p - 2).Prime)
    (hinj : p % 3 = 1 →
        ∃ q k, q.Prime ∧ q ∣ p - 2 ∧ q % 3 = 2 ∧ 1 < q ∧
          k % 3 = 2 ∧ (k * q - 2).Prime ∧ 7 ≤ k * q - 2 ∧ k * q - 2 ≤ p - 3) :
    a (p - 1) = p := by
  have h2le : 2 ≤ p := hp.two_le
  have hmod : p % 3 = 0 ∨ p % 3 = 1 ∨ p % 3 = 2 := by omega
  rcases hmod with h0 | h1 | h2
  · have h3p : 3 ∣ p := Nat.dvd_of_mod_eq_zero h0
    have hp3 : p = 3 :=
      ((Nat.prime_dvd_prime_iff_eq Nat.prime_three hp).1 h3p).symm
    subst hp3
    exact conjecture_three hp_twin
  · have : p ≠ 2 := by
      intro h
      subst h
      simp at h1
    have hp7 : 7 ≤ p := by omega
    exact conjecture_of_remaining_injector hp hp7 h1 hp_twin (hinj h1)
  · by_cases h7 : 7 ≤ p
    · exact conjecture_of_mod_three hp h7 h2
    · have hlt : p < 7 := by omega
      rcases hp.eq_two_or_odd with hp2 | hodd
      · subst hp2
        exact conjecture_two hp_twin
      · have hp5 : p = 5 := by omega
        subst hp5
        exact (hp_twin Nat.prime_three).elim

lemma seventeen_dvd_x_83 : 17 ∣ x 83 :=
  q_dvd_x_of_five_prime_injector (by decide) (by decide) (by decide)

lemma seventeen_dvd_x {n : ℕ} (hn : 83 ≤ n) : 17 ∣ x n :=
  seventeen_dvd_x_83.trans (x_dvd_of_le (by decide : 0 < 83) hn)

theorem conjecture_of_seventeen_dvd {p : ℕ} (hp : p.Prime) (hp86 : 86 ≤ p)
    (h17 : 17 ∣ p - 2) : a (p - 1) = p :=
  conjecture_of_factor_dvd_x hp (by omega) (by decide : 1 < 17) h17
    (seventeen_dvd_x (by omega : 83 ≤ p - 3))

lemma twentythree_dvd_x_113 : 23 ∣ x 113 :=
  q_dvd_x_of_five_prime_injector (by decide) (by decide) (by decide)

lemma twentythree_dvd_x {n : ℕ} (hn : 113 ≤ n) : 23 ∣ x n :=
  twentythree_dvd_x_113.trans (x_dvd_of_le (by decide : 0 < 113) hn)

theorem conjecture_of_twentythree_dvd {p : ℕ} (hp : p.Prime) (hp116 : 116 ≤ p)
    (h23 : 23 ∣ p - 2) : a (p - 1) = p :=
  conjecture_of_factor_dvd_x hp (by omega) (by decide : 1 < 23) h23
    (twentythree_dvd_x (by omega : 113 ≤ p - 3))

lemma twenty_nine_dvd_x_317 : 29 ∣ x 317 :=
  q_dvd_x_of_prime_injector (k := 11) (q := 29)
    (by decide) (by decide) (by norm_num) (by decide)

lemma twenty_nine_dvd_x {n : ℕ} (hn : 317 ≤ n) : 29 ∣ x n :=
  twenty_nine_dvd_x_317.trans (x_dvd_of_le (by decide : 0 < 317) hn)

theorem conjecture_of_twenty_nine_dvd {p : ℕ} (hp : p.Prime) (hp320 : 320 ≤ p)
    (h29 : 29 ∣ p - 2) : a (p - 1) = p :=
  conjecture_of_factor_dvd_x hp (by omega) (by decide : 1 < 29) h29
    (twenty_nine_dvd_x (by omega : 317 ≤ p - 3))

lemma thirty_seven_dvd_x_257 : 37 ∣ x 257 :=
  q_dvd_x_of_prime_index (k := 7) (q := 37)
    (by norm_num) (by decide) (by decide)

lemma thirty_seven_dvd_x {n : ℕ} (hn : 257 ≤ n) : 37 ∣ x n :=
  thirty_seven_dvd_x_257.trans (x_dvd_of_le (by decide : 0 < 257) hn)

theorem conjecture_of_thirty_seven_dvd {p : ℕ} (hp : p.Prime) (hp260 : 260 ≤ p)
    (h37 : 37 ∣ p - 2) : a (p - 1) = p :=
  conjecture_of_factor_dvd_x hp (by omega) (by decide : 1 < 37) h37
    (thirty_seven_dvd_x (by omega : 257 ≤ p - 3))

lemma forty_one_dvd_x_449 : 41 ∣ x 449 :=
  q_dvd_x_of_prime_index (k := 11) (q := 41)
    (by norm_num) (by decide) (by decide)

lemma forty_one_dvd_x {n : ℕ} (hn : 449 ≤ n) : 41 ∣ x n :=
  forty_one_dvd_x_449.trans (x_dvd_of_le (by decide : 0 < 449) hn)

theorem conjecture_of_forty_one_dvd {p : ℕ} (hp : p.Prime) (hp452 : 452 ≤ p)
    (h41 : 41 ∣ p - 2) : a (p - 1) = p :=
  conjecture_of_factor_dvd_x hp (by omega) (by decide : 1 < 41) h41
    (forty_one_dvd_x (by omega : 449 ≤ p - 3))

lemma forty_seven_dvd_x_233 : 47 ∣ x 233 :=
  q_dvd_x_of_prime_index (k := 5) (q := 47)
    (by norm_num) (by decide) (by decide)

lemma forty_seven_dvd_x {n : ℕ} (hn : 233 ≤ n) : 47 ∣ x n :=
  forty_seven_dvd_x_233.trans (x_dvd_of_le (by decide : 0 < 233) hn)

theorem conjecture_of_forty_seven_dvd {p : ℕ} (hp : p.Prime) (hp236 : 236 ≤ p)
    (h47 : 47 ∣ p - 2) : a (p - 1) = p :=
  conjecture_of_factor_dvd_x hp (by omega) (by decide : 1 < 47) h47
    (forty_seven_dvd_x (by omega : 233 ≤ p - 3))

lemma fifty_three_dvd_x_263 : 53 ∣ x 263 :=
  q_dvd_x_of_prime_index (k := 5) (q := 53)
    (by norm_num) (by decide) (by decide)

lemma fifty_three_dvd_x {n : ℕ} (hn : 263 ≤ n) : 53 ∣ x n :=
  fifty_three_dvd_x_263.trans (x_dvd_of_le (by decide : 0 < 263) hn)

theorem conjecture_of_fifty_three_dvd {p : ℕ} (hp : p.Prime) (hp266 : 266 ≤ p)
    (h53 : 53 ∣ p - 2) : a (p - 1) = p :=
  conjecture_of_factor_dvd_x hp (by omega) (by decide : 1 < 53) h53
    (fifty_three_dvd_x (by omega : 263 ≤ p - 3))

lemma fifty_nine_dvd_x_293 : 59 ∣ x 293 :=
  q_dvd_x_of_prime_index (k := 5) (q := 59)
    (by norm_num) (by decide) (by decide)

lemma fifty_nine_dvd_x {n : ℕ} (hn : 293 ≤ n) : 59 ∣ x n :=
  fifty_nine_dvd_x_293.trans (x_dvd_of_le (by decide : 0 < 293) hn)

theorem conjecture_of_fifty_nine_dvd {p : ℕ} (hp : p.Prime) (hp296 : 296 ≤ p)
    (h59 : 59 ∣ p - 2) : a (p - 1) = p :=
  conjecture_of_factor_dvd_x hp (by omega) (by decide : 1 < 59) h59
    (fifty_nine_dvd_x (by omega : 293 ≤ p - 3))

lemma sixty_seven_dvd_x_467 : 67 ∣ x 467 :=
  q_dvd_x_of_prime_index (k := 7) (q := 67)
    (by norm_num) (by decide) (by decide)

lemma sixty_seven_dvd_x {n : ℕ} (hn : 467 ≤ n) : 67 ∣ x n :=
  sixty_seven_dvd_x_467.trans (x_dvd_of_le (by decide : 0 < 467) hn)

theorem conjecture_of_sixty_seven_dvd {p : ℕ} (hp : p.Prime) (hp470 : 470 ≤ p)
    (h67 : 67 ∣ p - 2) : a (p - 1) = p :=
  conjecture_of_factor_dvd_x hp (by omega) (by decide : 1 < 67) h67
    (sixty_seven_dvd_x (by omega : 467 ≤ p - 3))

lemma seventy_one_dvd_x_353 : 71 ∣ x 353 :=
  q_dvd_x_of_prime_index (k := 5) (q := 71)
    (by norm_num) (by decide) (by decide)

lemma seventy_one_dvd_x {n : ℕ} (hn : 353 ≤ n) : 71 ∣ x n :=
  seventy_one_dvd_x_353.trans (x_dvd_of_le (by decide : 0 < 353) hn)

theorem conjecture_of_seventy_one_dvd {p : ℕ} (hp : p.Prime) (hp356 : 356 ≤ p)
    (h71 : 71 ∣ p - 2) : a (p - 1) = p :=
  conjecture_of_factor_dvd_x hp (by omega) (by decide : 1 < 71) h71
    (seventy_one_dvd_x (by omega : 353 ≤ p - 3))

lemma seventy_nine_dvd_x_1499 : 79 ∣ x 1499 :=
  q_dvd_x_of_prime_index (k := 19) (q := 79)
    (by norm_num) (by decide) (by decide)

lemma seventy_nine_dvd_x {n : ℕ} (hn : 1499 ≤ n) : 79 ∣ x n :=
  seventy_nine_dvd_x_1499.trans (x_dvd_of_le (by decide : 0 < 1499) hn)

theorem conjecture_of_seventy_nine_dvd {p : ℕ} (hp : p.Prime) (hp1502 : 1502 ≤ p)
    (h79 : 79 ∣ p - 2) : a (p - 1) = p :=
  conjecture_of_factor_dvd_x hp (by omega) (by decide : 1 < 79) h79
    (seventy_nine_dvd_x (by omega : 1499 ≤ p - 3))

lemma eighty_three_dvd_x_911 : 83 ∣ x 911 :=
  q_dvd_x_of_prime_index (k := 11) (q := 83)
    (by norm_num) (by decide) (by decide)

lemma eighty_three_dvd_x {n : ℕ} (hn : 911 ≤ n) : 83 ∣ x n :=
  eighty_three_dvd_x_911.trans (x_dvd_of_le (by decide : 0 < 911) hn)

theorem conjecture_of_eighty_three_dvd {p : ℕ} (hp : p.Prime) (hp914 : 914 ≤ p)
    (h83 : 83 ∣ p - 2) : a (p - 1) = p :=
  conjecture_of_factor_dvd_x hp (by omega) (by decide : 1 < 83) h83
    (eighty_three_dvd_x (by omega : 911 ≤ p - 3))

lemma eighty_nine_dvd_x_443 : 89 ∣ x 443 :=
  q_dvd_x_of_prime_index (k := 5) (q := 89)
    (by norm_num) (by decide) (by decide)

lemma eighty_nine_dvd_x {n : ℕ} (hn : 443 ≤ n) : 89 ∣ x n :=
  eighty_nine_dvd_x_443.trans (x_dvd_of_le (by decide : 0 < 443) hn)

theorem conjecture_of_eighty_nine_dvd {p : ℕ} (hp : p.Prime) (hp446 : 446 ≤ p)
    (h89 : 89 ∣ p - 2) : a (p - 1) = p :=
  conjecture_of_factor_dvd_x hp (by omega) (by decide : 1 < 89) h89
    (eighty_nine_dvd_x (by omega : 443 ≤ p - 3))

lemma ninety_seven_dvd_x_677 : 97 ∣ x 677 :=
  q_dvd_x_of_prime_index (k := 7) (q := 97)
    (by norm_num) (by decide) (by decide)

lemma ninety_seven_dvd_x {n : ℕ} (hn : 677 ≤ n) : 97 ∣ x n :=
  ninety_seven_dvd_x_677.trans (x_dvd_of_le (by decide : 0 < 677) hn)

theorem conjecture_of_ninety_seven_dvd {p : ℕ} (hp : p.Prime) (hp680 : 680 ≤ p)
    (h97 : 97 ∣ p - 2) : a (p - 1) = p :=
  conjecture_of_factor_dvd_x hp (by omega) (by decide : 1 < 97) h97
    (ninety_seven_dvd_x (by omega : 677 ≤ p - 3))

lemma one_hundred_one_dvd_x_503 : 101 ∣ x 503 :=
  q_dvd_x_of_prime_index (k := 5) (q := 101)
    (by norm_num) (by decide) (by decide)

lemma one_hundred_one_dvd_x {n : ℕ} (hn : 503 ≤ n) : 101 ∣ x n :=
  one_hundred_one_dvd_x_503.trans (x_dvd_of_le (by decide : 0 < 503) hn)

theorem conjecture_of_one_hundred_one_dvd {p : ℕ} (hp : p.Prime) (hp506 : 506 ≤ p)
    (h101 : 101 ∣ p - 2) : a (p - 1) = p :=
  conjecture_of_factor_dvd_x hp (by omega) (by decide : 1 < 101) h101
    (one_hundred_one_dvd_x (by omega : 503 ≤ p - 3))

lemma remaining_minFac_ge_five {p : ℕ} (hp : p.Prime) (hp7 : 7 ≤ p)
    (hmod : p % 3 = 1) : 5 ≤ Nat.minFac (p - 2) := by
  have hn : 1 < p - 2 := by omega
  have hminp : (Nat.minFac (p - 2)).Prime := Nat.minFac_prime (ne_of_gt hn)
  have hd : Nat.minFac (p - 2) ∣ p - 2 := Nat.minFac_dvd _
  have hq2 : Nat.minFac (p - 2) ≠ 2 := by
    intro h
    have : 2 ∣ p - 2 := by rwa [h] at hd
    have hpeq : p = p - 2 + 2 := by omega
    have : 2 ∣ p := by
      rw [hpeq]
      exact Nat.dvd_add this (by decide)
    have : p = 2 := ((Nat.prime_dvd_prime_iff_eq Nat.prime_two hp).1 this).symm
    omega
  have hq3 : Nat.minFac (p - 2) ≠ 3 := by
    intro h
    have : 3 ∣ p - 2 := by rwa [h] at hd
    have : (p - 2) % 3 = 0 := Nat.mod_eq_zero_of_dvd this
    have : (p - 2) % 3 = 2 :=
      p_sub_two_mod (le_trans (by decide : 4 ≤ 7) hp7) hmod
    omega
  have h2 : 2 ≤ Nat.minFac (p - 2) := hminp.two_le
  have hgt2 : 2 < Nat.minFac (p - 2) := lt_of_le_of_ne h2 hq2.symm
  have hge3 : 3 ≤ Nat.minFac (p - 2) := hgt2
  have hgt3 : 3 < Nat.minFac (p - 2) := lt_of_le_of_ne hge3 hq3.symm
  have hge4 : 4 ≤ Nat.minFac (p - 2) := hgt3
  have hne4 : Nat.minFac (p - 2) ≠ 4 := by
    intro h4
    rw [h4] at hminp
    exact (by decide : ¬ Nat.Prime 4) hminp
  omega

lemma prime_le_twentythree {q : ℕ} (hq : q.Prime) (h5 : 5 ≤ q) (h23 : q ≤ 23) :
    q = 5 ∨ q = 7 ∨ q = 11 ∨ q = 13 ∨ q = 17 ∨ q = 19 ∨ q = 23 := by
  interval_cases q
  · exact Or.inl rfl
  · exact ((by decide : ¬ Nat.Prime 6) hq).elim
  · exact Or.inr (Or.inl rfl)
  · exact ((by decide : ¬ Nat.Prime 8) hq).elim
  · exact ((by decide : ¬ Nat.Prime 9) hq).elim
  · exact ((by decide : ¬ Nat.Prime 10) hq).elim
  · exact Or.inr (Or.inr (Or.inl rfl))
  · exact ((by decide : ¬ Nat.Prime 12) hq).elim
  · exact Or.inr (Or.inr (Or.inr (Or.inl rfl)))
  · exact ((by decide : ¬ Nat.Prime 14) hq).elim
  · exact ((by decide : ¬ Nat.Prime 15) hq).elim
  · exact ((by decide : ¬ Nat.Prime 16) hq).elim
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  · exact ((by decide : ¬ Nat.Prime 18) hq).elim
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))
  · exact ((by decide : ¬ Nat.Prime 20) hq).elim
  · exact ((by decide : ¬ Nat.Prime 21) hq).elim
  · exact ((by decide : ¬ Nat.Prime 22) hq).elim
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr rfl)))))

/-- Remaining McEachen primes whose least prime factor is at most `23`.
The window `q(q+2) ≤ p-2` supplies the entry-index bounds used below. -/
theorem conjecture_of_minFac_le_twentythree {p : ℕ} (hp : p.Prime) (hp7 : 7 ≤ p)
    (hmod : p % 3 = 1) (hcomp : ¬ (p - 2).Prime)
    (hmin : Nat.minFac (p - 2) ≤ 23) : a (p - 1) = p := by
  have hq5 := remaining_minFac_ge_five hp hp7 hmod
  have hpr : (Nat.minFac (p - 2)).Prime :=
    Nat.minFac_prime (by omega : p - 2 ≠ 1)
  have hd : Nat.minFac (p - 2) ∣ p - 2 := Nat.minFac_dvd _
  have hcases := prime_le_twentythree hpr hq5 hmin
  have hbound := remaining_minFac_mul_add_two_le hp hp7 hmod hcomp
  rcases hcases with h | h | h | h | h | h | h
  · have hd5 : 5 ∣ p - 2 := by rwa [h] at hd
    exact conjecture_of_five_dvd hp hp7 hd5
  · have hd7 : 7 ∣ p - 2 := by rwa [h] at hd
    have hp50 : 50 ≤ p := by
      rw [h] at hbound
      omega
    exact conjecture_of_seven_dvd hp hp50 hd7
  · have hd11 : 11 ∣ p - 2 := by rwa [h] at hd
    have hp56 : 56 ≤ p := by
      rw [h] at hbound
      omega
    exact conjecture_of_eleven_dvd hp hp56 hd11
  · have hd13 : 13 ∣ p - 2 := by rwa [h] at hd
    have hp14 : 14 ≤ p := by
      rw [h] at hbound
      omega
    exact conjecture_of_thirteen_dvd hp hp14 hd13
  · have hd17 : 17 ∣ p - 2 := by rwa [h] at hd
    have hp86 : 86 ≤ p := by
      rw [h] at hbound
      omega
    exact conjecture_of_seventeen_dvd hp hp86 hd17
  · have hd19 : 19 ∣ p - 2 := by rwa [h] at hd
    have hp20 : 20 ≤ p := by
      rw [h] at hbound
      omega
    exact conjecture_of_nineteen_dvd hp hp20 hd19
  · have hd23 : 23 ∣ p - 2 := by rwa [h] at hd
    have hp116 : 116 ≤ p := by
      rw [h] at hbound
      omega
    exact conjecture_of_twentythree_dvd hp hp116 hd23

lemma eq_twenty_nine_of_prime_ge_twenty_four {q : ℕ}
    (hq : q.Prime) (h24 : 24 ≤ q) (h29 : q ≤ 29) : q = 29 := by
  interval_cases q
  · exact ((by decide : ¬ Nat.Prime 24) hq).elim
  · exact ((by decide : ¬ Nat.Prime 25) hq).elim
  · exact ((by decide : ¬ Nat.Prime 26) hq).elim
  · exact ((by decide : ¬ Nat.Prime 27) hq).elim
  · exact ((by decide : ¬ Nat.Prime 28) hq).elim
  · rfl

/-- Remaining McEachen primes whose least prime factor is at most `29`. -/
theorem conjecture_of_minFac_le_twenty_nine {p : ℕ} (hp : p.Prime) (hp7 : 7 ≤ p)
    (hmod : p % 3 = 1) (hcomp : ¬ (p - 2).Prime)
    (hmin : Nat.minFac (p - 2) ≤ 29) : a (p - 1) = p := by
  by_cases h23 : Nat.minFac (p - 2) ≤ 23
  · exact conjecture_of_minFac_le_twentythree hp hp7 hmod hcomp h23
  · have h24 : 24 ≤ Nat.minFac (p - 2) := by omega
    have hpr : (Nat.minFac (p - 2)).Prime :=
      Nat.minFac_prime (by omega : p - 2 ≠ 1)
    have hd : Nat.minFac (p - 2) ∣ p - 2 := Nat.minFac_dvd _
    have heq : Nat.minFac (p - 2) = 29 :=
      eq_twenty_nine_of_prime_ge_twenty_four hpr h24 hmin
    have hd29 : 29 ∣ p - 2 := by rwa [heq] at hd
    have hbound := remaining_minFac_mul_add_two_le hp hp7 hmod hcomp
    have hp320 : 320 ≤ p := by
      rw [heq] at hbound
      omega
    exact conjecture_of_twenty_nine_dvd hp hp320 hd29

/-- Remaining McEachen if `lpf(p-2) ≤ 29` or that least factor is a larger twin. -/
theorem conjecture_of_minFac_le_twenty_nine_or_twin {p : ℕ} (hp : p.Prime)
    (hp7 : 7 ≤ p) (hmod : p % 3 = 1) (hcomp : ¬ (p - 2).Prime)
    (h : Nat.minFac (p - 2) ≤ 29 ∨ (Nat.minFac (p - 2) - 2).Prime) :
    a (p - 1) = p := by
  rcases h with h29 | htwin
  · exact conjecture_of_minFac_le_twenty_nine hp hp7 hmod hcomp h29
  · by_cases hle : Nat.minFac (p - 2) ≤ 29
    · exact conjecture_of_minFac_le_twenty_nine hp hp7 hmod hcomp hle
    · have hpr : (Nat.minFac (p - 2)).Prime :=
        Nat.minFac_prime (by omega : p - 2 ≠ 1)
      have hd : Nat.minFac (p - 2) ∣ p - 2 := Nat.minFac_dvd _
      have h13 : 13 ≤ Nat.minFac (p - 2) := by omega
      exact conjecture_of_larger_twin_dvd hp (by omega) hcomp hpr h13 htwin hd

lemma remaining_prime_le_fifty_nine {q : ℕ} (hq : q.Prime) (h30 : 30 ≤ q) (h59 : q ≤ 59)
    (hnotwin : ¬ (q - 2).Prime) :
    q = 37 ∨ q = 41 ∨ q = 47 ∨ q = 53 ∨ q = 59 := by
  interval_cases q
  · exact ((by decide : ¬ Nat.Prime 30) hq).elim
  · exact (hnotwin (by decide : Nat.Prime 29)).elim
  · exact ((by decide : ¬ Nat.Prime 32) hq).elim
  · exact ((by decide : ¬ Nat.Prime 33) hq).elim
  · exact ((by decide : ¬ Nat.Prime 34) hq).elim
  · exact ((by decide : ¬ Nat.Prime 35) hq).elim
  · exact ((by decide : ¬ Nat.Prime 36) hq).elim
  · exact Or.inl rfl
  · exact ((by decide : ¬ Nat.Prime 38) hq).elim
  · exact ((by decide : ¬ Nat.Prime 39) hq).elim
  · exact ((by decide : ¬ Nat.Prime 40) hq).elim
  · exact Or.inr (Or.inl rfl)
  · exact ((by decide : ¬ Nat.Prime 42) hq).elim
  · exact (hnotwin (by decide : Nat.Prime 41)).elim
  · exact ((by decide : ¬ Nat.Prime 44) hq).elim
  · exact ((by decide : ¬ Nat.Prime 45) hq).elim
  · exact ((by decide : ¬ Nat.Prime 46) hq).elim
  · exact Or.inr (Or.inr (Or.inl rfl))
  · exact ((by decide : ¬ Nat.Prime 48) hq).elim
  · exact ((by decide : ¬ Nat.Prime 49) hq).elim
  · exact ((by decide : ¬ Nat.Prime 50) hq).elim
  · exact ((by decide : ¬ Nat.Prime 51) hq).elim
  · exact ((by decide : ¬ Nat.Prime 52) hq).elim
  · exact Or.inr (Or.inr (Or.inr (Or.inl rfl)))
  · exact ((by decide : ¬ Nat.Prime 54) hq).elim
  · exact ((by decide : ¬ Nat.Prime 55) hq).elim
  · exact ((by decide : ¬ Nat.Prime 56) hq).elim
  · exact ((by decide : ¬ Nat.Prime 57) hq).elim
  · exact ((by decide : ¬ Nat.Prime 58) hq).elim
  · exact Or.inr (Or.inr (Or.inr (Or.inr rfl)))

/-- Remaining McEachen if `lpf(p-2) ≤ 59` or that least factor is a larger twin. -/
theorem conjecture_of_minFac_le_fifty_nine_or_twin {p : ℕ} (hp : p.Prime)
    (hp7 : 7 ≤ p) (hmod : p % 3 = 1) (hcomp : ¬ (p - 2).Prime)
    (h : Nat.minFac (p - 2) ≤ 59 ∨ (Nat.minFac (p - 2) - 2).Prime) :
    a (p - 1) = p := by
  have hpr : (Nat.minFac (p - 2)).Prime :=
    Nat.minFac_prime (by omega : p - 2 ≠ 1)
  have hd : Nat.minFac (p - 2) ∣ p - 2 := Nat.minFac_dvd _
  have hbound := remaining_minFac_mul_add_two_le hp hp7 hmod hcomp
  rcases h with h59 | htwin
  · by_cases ht : (Nat.minFac (p - 2) - 2).Prime
    · by_cases h13 : 13 ≤ Nat.minFac (p - 2)
      · exact conjecture_of_larger_twin_dvd hp (by omega) hcomp hpr h13 ht hd
      · have : Nat.minFac (p - 2) ≤ 29 := by omega
        exact conjecture_of_minFac_le_twenty_nine hp hp7 hmod hcomp this
    · by_cases h29 : Nat.minFac (p - 2) ≤ 29
      · exact conjecture_of_minFac_le_twenty_nine hp hp7 hmod hcomp h29
      · have h30 : 30 ≤ Nat.minFac (p - 2) := by omega
        have hcases := remaining_prime_le_fifty_nine hpr h30 h59 ht
        rcases hcases with h | h | h | h | h
        · have hd37 : 37 ∣ p - 2 := by rwa [h] at hd
          have hp260 : 260 ≤ p := by
            rw [h] at hbound
            omega
          exact conjecture_of_thirty_seven_dvd hp hp260 hd37
        · have hd41 : 41 ∣ p - 2 := by rwa [h] at hd
          have hp452 : 452 ≤ p := by
            rw [h] at hbound
            omega
          exact conjecture_of_forty_one_dvd hp hp452 hd41
        · have hd47 : 47 ∣ p - 2 := by rwa [h] at hd
          have hp236 : 236 ≤ p := by
            rw [h] at hbound
            omega
          exact conjecture_of_forty_seven_dvd hp hp236 hd47
        · have hd53 : 53 ∣ p - 2 := by rwa [h] at hd
          have hp266 : 266 ≤ p := by
            rw [h] at hbound
            omega
          exact conjecture_of_fifty_three_dvd hp hp266 hd53
        · have hd59 : 59 ∣ p - 2 := by rwa [h] at hd
          have hp296 : 296 ≤ p := by
            rw [h] at hbound
            omega
          exact conjecture_of_fifty_nine_dvd hp hp296 hd59
  · by_cases h13 : 13 ≤ Nat.minFac (p - 2)
    · exact conjecture_of_larger_twin_dvd hp (by omega) hcomp hpr h13 htwin hd
    · have : Nat.minFac (p - 2) ≤ 29 := by omega
      exact conjecture_of_minFac_le_twenty_nine hp hp7 hmod hcomp this

lemma remaining_prime_le_one_hundred_one {q : ℕ} (hq : q.Prime)
    (h60 : 60 ≤ q) (h101 : q ≤ 101) (hnotwin : ¬ (q - 2).Prime) :
    q = 67 ∨ q = 71 ∨ q = 79 ∨ q = 83 ∨ q = 89 ∨ q = 97 ∨ q = 101 := by
  interval_cases q
  · exact ((by decide : ¬ Nat.Prime 60) hq).elim
  · exact (hnotwin (by decide : Nat.Prime 59)).elim
  · exact ((by decide : ¬ Nat.Prime 62) hq).elim
  · exact ((by decide : ¬ Nat.Prime 63) hq).elim
  · exact ((by decide : ¬ Nat.Prime 64) hq).elim
  · exact ((by decide : ¬ Nat.Prime 65) hq).elim
  · exact ((by decide : ¬ Nat.Prime 66) hq).elim
  · exact Or.inl rfl
  · exact ((by decide : ¬ Nat.Prime 68) hq).elim
  · exact ((by decide : ¬ Nat.Prime 69) hq).elim
  · exact ((by decide : ¬ Nat.Prime 70) hq).elim
  · exact Or.inr (Or.inl rfl)
  · exact ((by decide : ¬ Nat.Prime 72) hq).elim
  · exact (hnotwin (by decide : Nat.Prime 71)).elim
  · exact ((by decide : ¬ Nat.Prime 74) hq).elim
  · exact ((by decide : ¬ Nat.Prime 75) hq).elim
  · exact ((by decide : ¬ Nat.Prime 76) hq).elim
  · exact ((by decide : ¬ Nat.Prime 77) hq).elim
  · exact ((by decide : ¬ Nat.Prime 78) hq).elim
  · exact Or.inr (Or.inr (Or.inl rfl))
  · exact ((by decide : ¬ Nat.Prime 80) hq).elim
  · exact ((by decide : ¬ Nat.Prime 81) hq).elim
  · exact ((by decide : ¬ Nat.Prime 82) hq).elim
  · exact Or.inr (Or.inr (Or.inr (Or.inl rfl)))
  · exact ((by decide : ¬ Nat.Prime 84) hq).elim
  · exact ((by decide : ¬ Nat.Prime 85) hq).elim
  · exact ((by decide : ¬ Nat.Prime 86) hq).elim
  · exact ((by decide : ¬ Nat.Prime 87) hq).elim
  · exact ((by decide : ¬ Nat.Prime 88) hq).elim
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  · exact ((by decide : ¬ Nat.Prime 90) hq).elim
  · exact ((by decide : ¬ Nat.Prime 91) hq).elim
  · exact ((by decide : ¬ Nat.Prime 92) hq).elim
  · exact ((by decide : ¬ Nat.Prime 93) hq).elim
  · exact ((by decide : ¬ Nat.Prime 94) hq).elim
  · exact ((by decide : ¬ Nat.Prime 95) hq).elim
  · exact ((by decide : ¬ Nat.Prime 96) hq).elim
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))
  · exact ((by decide : ¬ Nat.Prime 98) hq).elim
  · exact ((by decide : ¬ Nat.Prime 99) hq).elim
  · exact ((by decide : ¬ Nat.Prime 100) hq).elim
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr rfl)))))

/-- Remaining McEachen if `lpf(p-2) ≤ 101` or that least factor is a larger twin. -/
theorem conjecture_of_minFac_le_one_hundred_one_or_twin {p : ℕ} (hp : p.Prime)
    (hp7 : 7 ≤ p) (hmod : p % 3 = 1) (hcomp : ¬ (p - 2).Prime)
    (h : Nat.minFac (p - 2) ≤ 101 ∨ (Nat.minFac (p - 2) - 2).Prime) :
    a (p - 1) = p := by
  have hpr : (Nat.minFac (p - 2)).Prime :=
    Nat.minFac_prime (by omega : p - 2 ≠ 1)
  have hd : Nat.minFac (p - 2) ∣ p - 2 := Nat.minFac_dvd _
  have hbound := remaining_minFac_mul_add_two_le hp hp7 hmod hcomp
  rcases h with h101 | htwin
  · by_cases ht : (Nat.minFac (p - 2) - 2).Prime
    · by_cases h13 : 13 ≤ Nat.minFac (p - 2)
      · exact conjecture_of_larger_twin_dvd hp (by omega) hcomp hpr h13 ht hd
      · have : Nat.minFac (p - 2) ≤ 29 := by omega
        exact conjecture_of_minFac_le_twenty_nine hp hp7 hmod hcomp this
    · by_cases h59 : Nat.minFac (p - 2) ≤ 59
      · exact conjecture_of_minFac_le_fifty_nine_or_twin hp hp7 hmod hcomp
          (Or.inl h59)
      · have h60 : 60 ≤ Nat.minFac (p - 2) := by omega
        have hcases := remaining_prime_le_one_hundred_one hpr h60 h101 ht
        rcases hcases with h | h | h | h | h | h | h
        · have hd67 : 67 ∣ p - 2 := by rwa [h] at hd
          have hp470 : 470 ≤ p := by
            rw [h] at hbound
            omega
          exact conjecture_of_sixty_seven_dvd hp hp470 hd67
        · have hd71 : 71 ∣ p - 2 := by rwa [h] at hd
          have hp356 : 356 ≤ p := by
            rw [h] at hbound
            omega
          exact conjecture_of_seventy_one_dvd hp hp356 hd71
        · have hd79 : 79 ∣ p - 2 := by rwa [h] at hd
          have hp1502 : 1502 ≤ p := by
            rw [h] at hbound
            omega
          exact conjecture_of_seventy_nine_dvd hp hp1502 hd79
        · have hd83 : 83 ∣ p - 2 := by rwa [h] at hd
          have hp914 : 914 ≤ p := by
            rw [h] at hbound
            omega
          exact conjecture_of_eighty_three_dvd hp hp914 hd83
        · have hd89 : 89 ∣ p - 2 := by rwa [h] at hd
          have hp446 : 446 ≤ p := by
            rw [h] at hbound
            omega
          exact conjecture_of_eighty_nine_dvd hp hp446 hd89
        · have hd97 : 97 ∣ p - 2 := by rwa [h] at hd
          have hp680 : 680 ≤ p := by
            rw [h] at hbound
            omega
          exact conjecture_of_ninety_seven_dvd hp hp680 hd97
        · have hd101 : 101 ∣ p - 2 := by rwa [h] at hd
          have hp506 : 506 ≤ p := by
            rw [h] at hbound
            omega
          exact conjecture_of_one_hundred_one_dvd hp hp506 hd101
  · by_cases h13 : 13 ≤ Nat.minFac (p - 2)
    · exact conjecture_of_larger_twin_dvd hp (by omega) hcomp hpr h13 htwin hd
    · have : Nat.minFac (p - 2) ≤ 29 := by omega
      exact conjecture_of_minFac_le_twenty_nine hp hp7 hmod hcomp this

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

lemma padicValNat_gcd (p m n : ℕ) [Fact p.Prime] (hm : 0 < m) (hn : 0 < n) :
    padicValNat p (Nat.gcd m n) = min (padicValNat p m) (padicValNat p n) := by
  have hg : Nat.gcd m n ≠ 0 := (Nat.gcd_pos_of_pos_left n hm).ne'
  have hm0 : m ≠ 0 := hm.ne'
  have hn0 : n ≠ 0 := hn.ne'
  apply le_antisymm
  · refine le_min ?_ ?_
    · exact (padicValNat_dvd_iff_le hm0).1 <|
        pow_padicValNat_dvd.trans (Nat.gcd_dvd_left m n)
    · exact (padicValNat_dvd_iff_le hn0).1 <|
        pow_padicValNat_dvd.trans (Nat.gcd_dvd_right m n)
  · have hpow : p ^ min (padicValNat p m) (padicValNat p n) ∣ Nat.gcd m n :=
      Nat.dvd_gcd ((padicValNat_dvd_iff_le hm0).2 (min_le_left _ _))
        ((padicValNat_dvd_iff_le hn0).2 (min_le_right _ _))
    exact (padicValNat_dvd_iff_le hg).1 hpow

lemma padicValNat_a (p n : ℕ) [Fact p.Prime] (hn : 0 < n) :
    padicValNat p (a n) =
      padicValNat p (n + 1) - min (padicValNat p (x n)) (padicValNat p (n + 1)) := by
  have hx := x_pos hn
  rw [a_eq hn, padicValNat.div_of_dvd (Nat.gcd_dvd_right _ _),
    padicValNat_gcd p (x n) (n + 1) hx (Nat.succ_pos n)]

/-- If `a n` equals a prime `ℓ` that already divides `x n`, then
`ℓ^{v_ℓ(x n)+1} ∣ n+1`. This is Cloitre Lemma 6.7 at a single index. -/
lemma a_eq_prime_padic_succ {ℓ n : ℕ} (hℓ : ℓ.Prime) (hn : 0 < n)
    (ha : a n = ℓ) (_hd : ℓ ∣ x n) :
    padicValNat ℓ (x n) + 1 ≤ padicValNat ℓ (n + 1) := by
  have : Fact ℓ.Prime := ⟨hℓ⟩
  have hva : padicValNat ℓ (a n) = 1 := by
    rw [ha]
    have h1 : padicValNat ℓ (ℓ ^ 1) = 1 := padicValNat.prime_pow (n := 1)
    rwa [pow_one] at h1
  have hformula := padicValNat_a ℓ n hn
  have hle : padicValNat ℓ (x n) ≤ padicValNat ℓ (n + 1) := by
    by_contra hne
    have hgt : padicValNat ℓ (n + 1) < padicValNat ℓ (x n) := Nat.lt_of_not_ge hne
    have hmin : min (padicValNat ℓ (x n)) (padicValNat ℓ (n + 1)) =
        padicValNat ℓ (n + 1) := min_eq_right (le_of_lt hgt)
    rw [hformula, hmin, Nat.sub_self] at hva
    omega
  have hmin : min (padicValNat ℓ (x n)) (padicValNat ℓ (n + 1)) =
      padicValNat ℓ (x n) := min_eq_left hle
  have : padicValNat ℓ (n + 1) - padicValNat ℓ (x n) = 1 := by
    rw [hformula, hmin] at hva
    exact hva
  omega

/-- Cloitre Lemma 6.7: after `ℓ` divides `x N`, any later `a n = ℓ` needs
`ℓ^{v_ℓ(x N)+1} ∣ n+1`. -/
lemma cloitre_valuation_barrier {ℓ N n : ℕ} (hℓ : ℓ.Prime) (hN : 0 < N)
    (hNle : N ≤ n) (hd : ℓ ∣ x N) (ha : a n = ℓ) :
    padicValNat ℓ (x N) + 1 ≤ padicValNat ℓ (n + 1) := by
  have : Fact ℓ.Prime := ⟨hℓ⟩
  have hx : ℓ ∣ x n := hd.trans (x_dvd_of_le hN hNle)
  have hn : 0 < n := lt_of_lt_of_le hN hNle
  have h := a_eq_prime_padic_succ hℓ hn ha hx
  have hvle : padicValNat ℓ (x N) ≤ padicValNat ℓ (x n) :=
    (padicValNat_dvd_iff_le (x_pos hn).ne').1
      (pow_padicValNat_dvd.trans (x_dvd_of_le hN hNle))
  omega

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

lemma v2_x_one : padicValNat 2 (x 1) = 0 :=
  padicValNat_one_right 2

/-- If `a` divides a power of two and `v₂(a) = 1`, then `a = 2`. -/
lemma eq_two_of_dvd_two_pow {a t : ℕ}
    (hd : a ∣ 2 ^ t) (hv : padicValNat 2 a = 1) : a = 2 := by
  obtain ⟨k, _hk, rfl⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 hd
  have hk1 : k = 1 := by
    simpa [padicValNat.prime_pow] using hv
  simp [hk1]

lemma four_pow_pred_div_two {k : ℕ} (_hk : 1 ≤ k) :
    (2 * 4 ^ k - 1) / 2 = 4 ^ k - 1 := by
  have hpow : 1 ≤ 4 ^ k := Nat.pow_pos (by decide)
  have h : 2 * (4 ^ k - 1) + 1 = 2 * 4 ^ k - 1 := by omega
  rw [← h, show 2 * (4 ^ k - 1) + 1 = 1 + 2 * (4 ^ k - 1) by omega]
  rw [Nat.add_mul_div_left 1 (4 ^ k - 1) (by decide : 0 < 2)]
  simp

lemma log4_four_pow_pred {k : ℕ} (hk : 1 ≤ k) :
    Nat.log 4 (4 ^ k - 1) = k - 1 := by
  have hpos : 0 < 4 ^ k := Nat.pow_pos (by decide)
  have hpred : 0 < 4 ^ (k - 1) := Nat.pow_pos (by decide)
  have hle : 4 ^ (k - 1) ≤ 4 ^ k - 1 := by
    have hmul : 4 ^ k = 4 ^ (k - 1 + 1) := by
      rw [Nat.sub_add_cancel hk]
    rw [hmul, pow_succ]
    have : 4 ^ (k - 1) ≤ 4 ^ (k - 1) * 4 - 1 := by
      have : 1 ≤ 4 ^ (k - 1) * 3 := by
        have : 1 ≤ 4 ^ (k - 1) := hpred
        omega
      omega
    simpa [Nat.mul_succ, mul_comm] using this
  have hlt : 4 ^ k - 1 < 4 ^ k := Nat.sub_lt hpos (by decide)
  have hlt' : 4 ^ k - 1 < 4 ^ (k - 1 + 1) := by
    rwa [Nat.sub_add_cancel hk]
  exact Nat.log_eq_of_pow_le_of_lt_pow hle hlt'

lemma log4_block {n : ℕ} (hn : 2 ≤ n) :
    2 * 4 ^ Nat.log 4 (n / 2) ≤ n ∧ n ≤ 2 * 4 ^ (Nat.log 4 (n / 2) + 1) - 1 := by
  have hb : 1 < (4 : ℕ) := by decide
  have hpos : 0 < n / 2 := Nat.div_pos (le_trans (by decide : 2 ≤ 2) hn) (by decide)
  refine ⟨?_, ?_⟩
  · have hle : 4 ^ Nat.log 4 (n / 2) ≤ n / 2 := Nat.pow_log_le_self 4 hpos.ne'
    have : 2 * 4 ^ Nat.log 4 (n / 2) ≤ 2 * (n / 2) := Nat.mul_le_mul_left 2 hle
    exact this.trans (Nat.mul_div_le n 2)
  · have hlt : n / 2 < 4 ^ (Nat.log 4 (n / 2) + 1) := Nat.lt_pow_succ_log_self hb (n / 2)
    have hlt' : n < 2 * 4 ^ (Nat.log 4 (n / 2) + 1) := by
      have h := (Nat.div_lt_iff_lt_mul (by decide : 0 < 2)).1 hlt
      rwa [mul_comm] at h
    exact Nat.le_sub_one_of_lt hlt'

lemma exists_block {n : ℕ} (hn : 2 ≤ n) :
    ∃ k, 2 * 4 ^ k ≤ n ∧ n ≤ 2 * 4 ^ (k + 1) - 1 :=
  ⟨Nat.log 4 (n / 2), log4_block hn⟩

/-- Cloitre's 2-adic staircase: `v₂(x n) = 2 k + 2` on the block
`2 · 4^k ≤ n ≤ 2 · 4^{k+1} - 1`. -/
lemma v2_x_stay {N k : ℕ} (hNpos : 0 < N)
    (hvN : padicValNat 2 (x N) = 2 * k + 2)
    (hv2le : padicValNat 2 (N + 1) ≤ 2 * k + 2) :
    padicValNat 2 (x (N + 1)) = 2 * k + 2 := by
  have hle : padicValNat 2 (N + 1) ≤ padicValNat 2 (x N) := by
    rwa [hvN]
  rw [v2_x_succ_eq_of_le hNpos hle, hvN]

lemma v2_x_ge_two (n : ℕ) :
    2 ≤ n → padicValNat 2 (x n) = 2 * Nat.log 4 (n / 2) + 2 := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro hn
    match n with
    | 0 => omega
    | 1 => omega
    | 2 =>
      have : Nat.log 4 (2 / 2) = 0 := Nat.log_one_right 4
      simp [this, v2_x_two]
    | m + 3 =>
      have hm : 2 ≤ m + 2 := by omega
      have hlt : m + 2 < m + 3 := Nat.lt_succ_self _
      have ihv := ih (m + 2) hlt hm
      set N := m + 2
      have hNpos : 0 < N := by omega
      have hblk := log4_block hm
      set k := Nat.log 4 (N / 2)
      have hleft : 2 * 4 ^ k ≤ N := by simpa [k, N] using hblk.1
      have hright : N ≤ 2 * 4 ^ (k + 1) - 1 := by simpa [k, N] using hblk.2
      have hvN : padicValNat 2 (x N) = 2 * k + 2 := by
        simpa [k, N] using ihv
      have hpow : 2 * 4 ^ (k + 1) = 2 ^ (2 * (k + 1) + 1) := two_mul_four_pow (k + 1)
      have hposb : 0 < 2 * 4 ^ (k + 1) :=
        Nat.mul_pos (by decide) (Nat.pow_pos (by decide))
      by_cases hlast : N = 2 * 4 ^ (k + 1) - 1
      · have hsucc : N + 1 = 2 * 4 ^ (k + 1) := by omega
        have hv2 : padicValNat 2 (N + 1) = 2 * (k + 1) + 1 := by
          rw [hsucc, hpow, padicValNat.prime_pow]
        have hva : padicValNat 2 (a N) = 1 := by
          rw [v2_a hNpos, hvN, hv2]
          have hmin : min (2 * k + 2) (2 * (k + 1) + 1) = 2 * k + 2 := by omega
          rw [hmin]
          omega
        have hdvd : a N ∣ 2 ^ (2 * (k + 1) + 1) := by
          have hd := a_dvd hNpos
          rwa [hsucc, hpow] at hd
        have haeq : a N = 2 := eq_two_of_dvd_two_pow hdvd hva
        have hvnext : padicValNat 2 (x (N + 1)) = 2 * k + 4 := by
          rw [v2_x_succ hNpos, haeq, hvN]
          have : padicValNat 2 (2 + 2) = 2 := by
            rw [show (2 + 2 : ℕ) = 2 ^ 2 from rfl, padicValNat.prime_pow]
          omega
        have hlog : Nat.log 4 ((N + 1) / 2) = k + 1 := by
          have : (N + 1) / 2 = 4 ^ (k + 1) := by
            rw [hsucc, Nat.mul_div_right _ (by decide : 0 < 2)]
          rw [this, Nat.log_pow (by decide : 1 < (4 : ℕ))]
        have hidx : N + 1 = m + 3 := by omega
        rw [← hidx, hvnext, hlog]
        omega
      · have hsucc_lt : N + 1 < 2 * 4 ^ (k + 1) := by omega
        have hsucc_lt_pow : N + 1 < 2 ^ (2 * (k + 1) + 1) := by
          rwa [← hpow]
        have hv2le : padicValNat 2 (N + 1) ≤ 2 * k + 2 := by
          have heq : 2 * (k + 1) + 1 = 2 * k + 2 + 1 := by omega
          exact v2_lt_pow (Nat.succ_ne_zero N) (heq ▸ hsucc_lt_pow)
        have hvstay : padicValNat 2 (x (N + 1)) = 2 * k + 2 :=
          v2_x_stay hNpos hvN hv2le
        have hlog : Nat.log 4 ((N + 1) / 2) = k := by
          refine Nat.log_eq_of_pow_le_of_lt_pow ?hle ?hlt
          · have : 4 ^ k * 2 ≤ N + 1 := by
              have h' : 2 * 4 ^ k ≤ N + 1 := hleft.trans (Nat.le_succ N)
              rwa [mul_comm] at h'
            rwa [Nat.le_div_iff_mul_le (by decide : 0 < 2)]
          · rw [Nat.div_lt_iff_lt_mul (by decide : 0 < 2), mul_comm]
            exact hsucc_lt
        have hidx : N + 1 = m + 3 := by omega
        rw [← hidx, hvstay, hlog]

/-- Cloitre Proposition 6.5 in Lean indexing: `a(2 · 4^k - 1) = 2`. -/
theorem a_two_four_pow (k : ℕ) : a (2 * 4 ^ k - 1) = 2 := by
  cases k with
  | zero => exact a_1
  | succ k =>
    set n := 2 * 4 ^ (k + 1) - 1
    have hn2 : 2 ≤ n := by
      have hpow : 4 ≤ 4 ^ (k + 1) :=
        Nat.pow_le_pow_right (by decide : 0 < 4) (Nat.succ_le_succ (Nat.zero_le _))
      have : 8 ≤ 2 * 4 ^ (k + 1) := by omega
      omega
    have hv := v2_x_ge_two n hn2
    have hdiv := four_pow_pred_div_two (Nat.succ_le_succ (Nat.zero_le k))
    have hlog : Nat.log 4 (n / 2) = k := by
      rw [hdiv]
      simpa using log4_four_pow_pred (Nat.succ_le_succ (Nat.zero_le k))
    have hv' : padicValNat 2 (x n) = 2 * k + 2 := by
      rw [hv, hlog]
    have hnpos : 0 < n := by omega
    have hsum : n + 1 = 2 * 4 ^ (k + 1) := by omega
    have hv2n : padicValNat 2 (n + 1) = 2 * (k + 1) + 1 := by
      rw [hsum, two_mul_four_pow (k + 1), padicValNat.prime_pow]
    have hva : padicValNat 2 (a n) = 1 := by
      rw [v2_a hnpos, hv', hv2n]
      have hmin : min (2 * k + 2) (2 * (k + 1) + 1) = 2 * k + 2 := by omega
      rw [hmin]
      omega
    have hdvd : a n ∣ 2 ^ (2 * (k + 1) + 1) := by
      have hd := a_dvd hnpos
      rwa [hsum, two_mul_four_pow (k + 1)] at hd
    exact eq_two_of_dvd_two_pow hdvd hva

theorem a_two_four_pow_zero : a (2 * 4 ^ 0 - 1) = 2 :=
  a_two_four_pow 0

lemma v2_x_two_four_pow_pred (k : ℕ) :
    padicValNat 2 (x (2 * 4 ^ k - 1)) = 2 * k := by
  cases k with
  | zero => simpa using v2_x_one
  | succ k =>
    have hn2 : 2 ≤ 2 * 4 ^ (k + 1) - 1 := by
      have hpow : 4 ≤ 4 ^ (k + 1) :=
        Nat.pow_le_pow_right (by decide : 0 < 4) (Nat.succ_le_succ (Nat.zero_le _))
      omega
    have hv := v2_x_ge_two (2 * 4 ^ (k + 1) - 1) hn2
    have hdiv := four_pow_pred_div_two (Nat.succ_le_succ (Nat.zero_le k))
    have hlog : Nat.log 4 ((2 * 4 ^ (k + 1) - 1) / 2) = k := by
      rw [hdiv]
      simpa using log4_four_pow_pred (Nat.succ_le_succ (Nat.zero_le k))
    rw [hv, hlog]
    omega

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
#print axioms a_two_four_pow
#print axioms a_two_four_pow_zero
#print axioms v2_x_two_four_pow_pred
#print axioms exists_prime_factor_mod_three
#print axioms exists_remaining_factor
#print axioms minFac_mul_add_two_le
#print axioms remaining_minFac_mul_add_two_le
#print axioms q_dvd_x_of_prime_injector
#print axioms conjecture_of_prime_injector
#print axioms q_dvd_x_of_coprime_shift
#print axioms v2_x_ge_two
#print axioms not_q_dvd_x_le
#print axioms not_q_dvd_x_self
#print axioms not_prime_kq_sub_two_of_even
#print axioms not_prime_kq_sub_two_of_k_mod_one
#print axioms odd_k_mod_three_two_iff
#print axioms conjecture_of_five_prime_injector
#print axioms conjecture_of_remaining_injector
#print axioms conjecture_of_cases
#print axioms conjecture_of_seventeen_dvd
#print axioms conjecture_of_twentythree_dvd
#print axioms conjecture_of_minFac_le_twentythree
#print axioms remaining_minFac_ge_five
#print axioms prime_le_twentythree
#print axioms gcd_gt_one_of_three_dvd_succ
#print axioms nine_dvd_succ_of_three_dvd_a
#print axioms not_three_dvd_a_of_not_nine
#print axioms larger_twin_dvd_x
#print axioms conjecture_of_larger_twin_dvd
#print axioms q_dvd_x_of_prime_index
#print axioms conjecture_of_prime_index
#print axioms twenty_nine_dvd_x_317
#print axioms conjecture_of_twenty_nine_dvd
#print axioms conjecture_of_minFac_le_twenty_nine
#print axioms conjecture_of_minFac_le_twenty_nine_or_twin
#print axioms thirty_seven_dvd_x_257
#print axioms conjecture_of_thirty_seven_dvd
#print axioms forty_one_dvd_x_449
#print axioms forty_seven_dvd_x_233
#print axioms fifty_three_dvd_x_263
#print axioms fifty_nine_dvd_x_293
#print axioms remaining_prime_le_fifty_nine
#print axioms conjecture_of_minFac_le_fifty_nine_or_twin
#print axioms a_eq_prime_padic_succ
#print axioms cloitre_valuation_barrier
#print axioms two_dvd_x
#print axioms gcd_gt_one_of_composite_shift
#print axioms conjecture_of_minFac_entered
#print axioms sixty_seven_dvd_x_467
#print axioms conjecture_of_sixty_seven_dvd
#print axioms seventy_one_dvd_x_353
#print axioms conjecture_of_seventy_one_dvd
#print axioms seventy_nine_dvd_x_1499
#print axioms conjecture_of_seventy_nine_dvd
#print axioms eighty_three_dvd_x_911
#print axioms conjecture_of_eighty_three_dvd
#print axioms eighty_nine_dvd_x_443
#print axioms conjecture_of_eighty_nine_dvd
#print axioms ninety_seven_dvd_x_677
#print axioms conjecture_of_ninety_seven_dvd
#print axioms one_hundred_one_dvd_x_503
#print axioms conjecture_of_one_hundred_one_dvd
#print axioms remaining_prime_le_one_hundred_one
#print axioms conjecture_of_minFac_le_one_hundred_one_or_twin
#print axioms coprime_five_mul_sub_two
#print axioms coprime_sub_two_six_mul
#print axioms exists_prime_index_injector
#print axioms exists_prime_index_injector_mod_one
#print axioms q_dvd_x_eventually
#print axioms q_dvd_x_eventually_mod_one

end OeisA135508
