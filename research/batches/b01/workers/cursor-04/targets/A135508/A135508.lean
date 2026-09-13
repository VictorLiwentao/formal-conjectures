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
when `lpf(p-2) ≤ 107` or that least factor is a larger twin, first-entry of
`163`, `167`, `179`, `227`, `251` and `389` at the recorded injector indices, Dirichlet
existence of some (unbounded) prime injector for every prime `q ≥ 5`,
that `3 ∣ a n` for `n ≥ 3` forces `9 ∣ n+1`, that `3 ∣ a n` for `n ≥ 6`
forces `81 ∣ n+1`, that `3 ∣ a n` for `n ≥ 7` forces `729 ∣ n+1`, that
`3 ∣ a n` for `n ≥ 9` forces `2187 ∣ n+1`, that `3 ∣ a n` for `n ≥ 10`
forces `6561 ∣ n+1`, that `3 ∣ a n` for `n ≥ 12` forces `19683 ∣ n+1`,
that `3 ∣ a n` for `n ≥ 13` forces `59049 ∣ n+1`, that `3 ∣ a n` for
`n ≥ 14` forces `531441 ∣ n+1`, the values `a 9 = 1`, `a 10 = 11`,
`a 11 = 1`, `a 12 = 1`, `a 13 = 7` and `a 14 = 1`, McEachen when
`gcd(q+2, p-2) > 1` for a prime `q ≡ 2 (mod 3)`, Cloitre Corollary 6.6 as an
implication from `C₁`, remaining McEachen if a first aligned injector of
`lpf(p-2)` or of a complementary cofactor is prime, remaining McEachen if
some prime injector of `lpf(p-2)` has `k ≤ q+2`, remaining McEachen if
some prime factor of `p-2` has an injector with `k ≤ (p-2)/q`, leftover
polynomial candidates `k = q` and `k = q+6` in the add-eight window,
that an odd composite `n ≡ 2 (mod 3)` with `n < lpf(n)^3` has a prime
factor `≡ 1 (mod 3)`, remaining McEachen if some factor `≡ 1 (mod 3)`
has a prime injector `kr-2` with `k ≡ 1 (mod 6)` and `k ≥ 7` in the
McEachen window (in particular `k=7` fits once `5 ∤ p-2`), Type B
remaining numbers (every prime factor `≡ 2 (mod 3)`) satisfy
`lpf^2 ≤ (p-2)/lpf`, first-entry of `113`, `127`, `131`, `137` and
`149`, remaining McEachen when `lpf(p-2) ≤ 149` or that least factor
is a larger twin, that a remaining Type A number `p-2 < lpf^3` has
prime cofactor `(p-2)/lpf`, first-entry of `157`, `173`, `191` and
`197`, remaining McEachen when `lpf(p-2) ≤ 197` or that least factor
is a larger twin, remaining Type A McEachen if the least factor is
`≡ 1 (mod 3)` and `5r-2` is prime, first-entry of `211`, `223`, `233`
and `239`, remaining McEachen when `lpf(p-2) ≤ 239` or that least factor
is a larger twin, first-entry of `257`, remaining McEachen when
`lpf(p-2) ≤ 257` or that least factor is a larger twin, first-entry of
`263` and `269`, remaining McEachen when `lpf(p-2) ≤ 269` or that
least factor is a larger twin, first-entry of `277` and `281`, remaining
McEachen when `lpf(p-2) ≤ 281` or that least factor is a larger twin,
first-entry of `293`, remaining McEachen when `lpf(p-2) ≤ 293` or that
least factor is a larger twin, first-entry of leftover least factors
`307` through `383`, remaining McEachen when `lpf(p-2) ≤ 389` or that
least factor is a larger twin, the Euclid first-entry criterion, the
index identity `n+1 = g(kq-2)`, the shift criterion `q ∣ g-1` at
`kq-2`, the `30` and `210` stock lower bounds,
and that the frozen statement follows from first-entry of every prime
`q ≥ 5` by the square-window index `q(q+2)-1`. Existence of a window
injector for every leftover least factor is not proved.
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

/-- First-entry mechanism: a factor of `a n + 2` enters `x` at the next index. -/
lemma dvd_x_succ_of_dvd_a_add_two {q n : ℕ} (hn : 0 < n) (h : q ∣ a n + 2) :
    q ∣ x (n + 1) := by
  rw [x_succ_a hn]
  exact dvd_mul_of_dvd_right h _

/-- If `q` does not divide `x n` or `a n + 2`, then it does not divide `x (n+1)`. -/
lemma not_prime_dvd_x_succ {q n : ℕ} (hq : q.Prime) (hn : 0 < n)
    (hx : ¬ q ∣ x n) (ha : ¬ q ∣ a n + 2) : ¬ q ∣ x (n + 1) := by
  intro h
  have hmul : q ∣ x n * (a n + 2) := by
    rwa [x_succ_a hn] at h
  rcases hq.dvd_mul.mp hmul with hx' | ha'
  · exact hx hx'
  · exact ha ha'

/-- First-entry criterion: the first time `q` divides `x` is a step `a n ≡ -2 (mod q)`. -/
lemma prime_dvd_a_add_two_of_first_entry {q n : ℕ} (hq : q.Prime) (hn : 0 < n)
    (hnot : ¬ q ∣ x n) (hd : q ∣ x (n + 1)) : q ∣ a n + 2 := by
  have hmul : q ∣ x n * (a n + 2) := by
    rwa [x_succ_a hn] at hd
  exact (hq.dvd_mul.mp hmul).resolve_left hnot

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

/-- Product form of `a n + 2`. -/
lemma a_add_two_mul_gcd {n : ℕ} (hn : 0 < n) :
    Nat.gcd (x n) (n + 1) * (a n + 2) =
      n + 1 + 2 * Nat.gcd (x n) (n + 1) := by
  rw [a_eq hn]
  have hcancel :
      Nat.gcd (x n) (n + 1) * ((n + 1) / Nat.gcd (x n) (n + 1)) = n + 1 :=
    Nat.mul_div_cancel' (Nat.gcd_dvd_right _ _)
  calc
    Nat.gcd (x n) (n + 1) * ((n + 1) / Nat.gcd (x n) (n + 1) + 2) =
        Nat.gcd (x n) (n + 1) * ((n + 1) / Nat.gcd (x n) (n + 1)) +
          Nat.gcd (x n) (n + 1) * 2 := Nat.mul_add _ _ _
    _ = n + 1 + Nat.gcd (x n) (n + 1) * 2 := by rw [hcancel]
    _ = n + 1 + 2 * Nat.gcd (x n) (n + 1) := by rw [Nat.mul_comm]

/-- Complementary form of `a n + 2`. -/
lemma a_add_two_eq {n : ℕ} (hn : 0 < n) :
    a n + 2 =
      (n + 1 + 2 * Nat.gcd (x n) (n + 1)) / Nat.gcd (x n) (n + 1) := by
  have hg : 0 < Nat.gcd (x n) (n + 1) :=
    Nat.gcd_pos_of_pos_right _ (Nat.succ_pos n)
  rw [← a_add_two_mul_gcd hn, Nat.mul_div_cancel_left _ hg]

/-- Euclid form of first-entry: `q` divides `n+1+2g` and not `g`. -/
lemma dvd_a_add_two_of_dvd_add {q n : ℕ} (hq : q.Prime) (hn : 0 < n)
    (h : q ∣ n + 1 + 2 * Nat.gcd (x n) (n + 1))
    (hqg : ¬ q ∣ Nat.gcd (x n) (n + 1)) : q ∣ a n + 2 := by
  have hmul : q ∣ Nat.gcd (x n) (n + 1) * (a n + 2) := by
    rwa [a_add_two_mul_gcd hn]
  exact (hq.dvd_mul.mp hmul).resolve_left hqg

lemma q_dvd_x_succ_of_dvd_add {q n : ℕ} (hq : q.Prime) (hn : 0 < n)
    (h : q ∣ n + 1 + 2 * Nat.gcd (x n) (n + 1))
    (hqg : ¬ q ∣ Nat.gcd (x n) (n + 1)) : q ∣ x (n + 1) :=
  dvd_x_succ_of_dvd_a_add_two hn (dvd_a_add_two_of_dvd_add hq hn h hqg)

lemma not_dvd_gcd_of_not_dvd_x {q n : ℕ} (hx : ¬ q ∣ x n) :
    ¬ q ∣ Nat.gcd (x n) (n + 1) :=
  fun hg => hx (hg.trans (Nat.gcd_dvd_left _ _))

/-- Converse Euclid form: a genuine first-entry forces `q ∣ n+1+2g`. -/
lemma dvd_add_of_first_entry {q n : ℕ} (hq : q.Prime) (hn : 0 < n)
    (hx : ¬ q ∣ x n) (hd : q ∣ x (n + 1)) :
    q ∣ n + 1 + 2 * Nat.gcd (x n) (n + 1) := by
  have ha := prime_dvd_a_add_two_of_first_entry hq hn hx hd
  have hmul : q ∣ Nat.gcd (x n) (n + 1) * (a n + 2) :=
    dvd_mul_of_dvd_right ha _
  rwa [a_add_two_mul_gcd hn] at hmul

/-- First-entry criterion: if `q` has not entered `x n`, then it enters at
`n+1` if and only if it divides `n+1+2g`. -/
lemma first_entry_iff_dvd_add {q n : ℕ} (hq : q.Prime) (hn : 0 < n)
    (hx : ¬ q ∣ x n) :
    q ∣ x (n + 1) ↔ q ∣ n + 1 + 2 * Nat.gcd (x n) (n + 1) :=
  ⟨fun hd => dvd_add_of_first_entry hq hn hx hd,
    fun h => q_dvd_x_succ_of_dvd_add hq hn h (not_dvd_gcd_of_not_dvd_x hx)⟩

/-- If `q` divides `a n + 2`, the first-entry index is `g(kq-2)`.
The rewrite is local so it does not touch an outer `n+1` goal. -/
lemma succ_eq_gcd_mul_kq_sub_two {q n k : ℕ} (hn : 0 < n)
    (h : a n + 2 = q * k) :
    n + 1 = Nat.gcd (x n) (n + 1) * (q * k - 2) := by
  have hmul := a_mul_gcd hn
  have hsub : a n + 2 - 2 = a n := Nat.add_sub_cancel (a n) 2
  calc
    n + 1 = a n * Nat.gcd (x n) (n + 1) := hmul.symm
    _ = Nat.gcd (x n) (n + 1) * a n := Nat.mul_comm _ _
    _ = Nat.gcd (x n) (n + 1) * (a n + 2 - 2) := by rw [hsub]
    _ = Nat.gcd (x n) (n + 1) * (q * k - 2) := by rw [h]

/-- First-entry of `q` occurs at index `g(kq-2)` for `k = (a n + 2)/q`. -/
lemma exists_first_entry_index {q n : ℕ} (hn : 0 < n) (h : q ∣ a n + 2) :
    ∃ k, n + 1 = Nat.gcd (x n) (n + 1) * (q * k - 2) :=
  ⟨(a n + 2) / q, succ_eq_gcd_mul_kq_sub_two hn (Nat.mul_div_cancel' h).symm⟩

/-- An odd prime dividing `2m` divides `m`. -/
lemma odd_prime_dvd_two_mul {q m : ℕ} (hq : q.Prime) (h2 : 2 < q)
    (h : q ∣ 2 * m) : q ∣ m :=
  (hq.dvd_mul.mp h).resolve_left fun hd2 =>
    Nat.ne_of_gt h2 ((Nat.prime_dvd_prime_iff_eq hq Nat.prime_two).mp hd2)

/-- Euclid identity at a shift index `n+1 = kq-2`. -/
lemma add_two_gcd_eq_of_kq_sub_two {n k q : ℕ}
    (h : n + 1 = k * q - 2) (h2 : 2 ≤ k * q)
    (hg : 1 ≤ Nat.gcd (x n) (n + 1)) :
    n + 1 + 2 * Nat.gcd (x n) (n + 1) =
      k * q + 2 * (Nat.gcd (x n) (n + 1) - 1) := by
  set g := Nat.gcd (x n) (n + 1)
  have h2g : 2 * g = 2 * (g - 1) + 2 := by
    have hg1 : g = g - 1 + 1 := (Nat.sub_add_cancel hg).symm
    calc
      2 * g = 2 * (g - 1 + 1) := by rw [hg1]
      _ = 2 * (g - 1) + 2 * 1 := Nat.mul_add 2 _ _
      _ = 2 * (g - 1) + 2 := by rw [Nat.mul_one]
  calc
    n + 1 + 2 * g = (k * q - 2) + 2 * g := by rw [h]
    _ = (k * q - 2) + (2 * (g - 1) + 2) := by rw [h2g]
    _ = (k * q - 2) + (2 + 2 * (g - 1)) := by rw [Nat.add_comm (2 * (g - 1))]
    _ = (k * q - 2 + 2) + 2 * (g - 1) := by rw [← Nat.add_assoc]
    _ = k * q + 2 * (g - 1) := by rw [Nat.sub_add_cancel h2]

/-- `n+1 = kq-2` after the predecessor index `kq-3`. -/
lemma succ_pred_kq_sub_two {k q : ℕ} (hpos : 0 < k * q - 3) :
    k * q - 3 + 1 = k * q - 2 := by
  have h3lt : 3 < k * q := by
    have : 0 < k * q - 3 := hpos
    omega
  have h3le : 3 ≤ k * q := Nat.le_of_lt h3lt
  have h1le : 1 ≤ k * q - 2 :=
    Nat.le_sub_of_add_le (by
      have : 1 + 2 = 3 := rfl
      rwa [this])
  have hsub : k * q - 3 = k * q - 2 - 1 := (Nat.sub_sub (k * q) 2 1).symm
  rw [hsub]
  exact Nat.sub_add_cancel h1le

/-- At a candidate index `kq-2`, first-entry of an odd prime `q` is
equivalent to `q ∣ g-1`. In particular `g = 1` is sufficient. -/
lemma first_entry_iff_dvd_gcd_pred {q k : ℕ}
    (hq : q.Prime) (h2 : 2 < q) (hpos : 0 < k * q - 3)
    (hx : ¬ q ∣ x (k * q - 3)) :
    q ∣ x (k * q - 2) ↔
      q ∣ Nat.gcd (x (k * q - 3)) (k * q - 2) - 1 := by
  have h3lt : 3 < k * q := by
    have : 0 < k * q - 3 := hpos
    omega
  have h2le : 2 ≤ k * q :=
    le_trans (by decide : 2 ≤ 4) (Nat.succ_le_of_lt h3lt)
  have hsucc := succ_pred_kq_sub_two hpos
  have hg : 1 ≤ Nat.gcd (x (k * q - 3)) (k * q - 2) :=
    Nat.succ_le_of_lt (Nat.gcd_pos_of_pos_right _
      (Nat.sub_pos_of_lt (lt_trans (by decide : 2 < 3) h3lt)))
  have hrep := add_two_gcd_eq_of_kq_sub_two (n := k * q - 3) (k := k)
    (q := q) hsucc h2le (by simpa [hsucc] using hg)
  constructor
  · intro hd
    have hd' : q ∣ x (k * q - 3 + 1) := by rwa [hsucc]
    have hadd := (first_entry_iff_dvd_add hq hpos hx).mp hd'
    have hadd1 :
        q ∣ k * q +
          2 * (Nat.gcd (x (k * q - 3)) (k * q - 3 + 1) - 1) := by
      rwa [hrep] at hadd
    have hadd2 :
        q ∣ k * q + 2 * (Nat.gcd (x (k * q - 3)) (k * q - 2) - 1) := by
      simpa [hsucc] using hadd1
    have hqk : q ∣ k * q := Nat.dvd_mul_left q k
    exact odd_prime_dvd_two_mul hq h2 ((Nat.dvd_add_iff_right hqk).mp hadd2)
  · intro hgpred
    have hqk : q ∣ k * q := Nat.dvd_mul_left q k
    have htwo :
        q ∣ 2 * (Nat.gcd (x (k * q - 3)) (k * q - 2) - 1) :=
      dvd_mul_of_dvd_right hgpred 2
    have hadd :
        q ∣ k * q + 2 * (Nat.gcd (x (k * q - 3)) (k * q - 2) - 1) :=
      (Nat.dvd_add_iff_right hqk).mpr htwo
    have hadd1 :
        q ∣ k * q +
          2 * (Nat.gcd (x (k * q - 3)) (k * q - 3 + 1) - 1) := by
      simpa [hsucc] using hadd
    have hadd' :
        q ∣ k * q - 3 + 1 +
          2 * Nat.gcd (x (k * q - 3)) (k * q - 3 + 1) := by
      rwa [← hrep]
    have : q ∣ x (k * q - 3 + 1) :=
      (first_entry_iff_dvd_add hq hpos hx).mpr hadd'
    rwa [hsucc] at this

/-- If `1 ≤ g < q`, then `q ∣ g-1` forces `g = 1`. -/
lemma eq_one_of_prime_dvd_pred {q g : ℕ} (_hq : q.Prime)
    (hg1 : 1 ≤ g) (hg : g < q) (h : q ∣ g - 1) : g = 1 := by
  have hlt : g - 1 < q :=
    lt_trans (Nat.sub_lt (Nat.succ_le_iff.mp hg1) (by decide : 0 < 1)) hg
  have h0 : g - 1 = 0 := Nat.eq_zero_of_dvd_of_lt h hlt
  have hcancel := Nat.sub_add_cancel hg1
  rw [h0, Nat.zero_add] at hcancel
  exact hcancel.symm

/-- If `1 < g < q` at a shift, then `q` does not divide `g-1`. -/
lemma not_dvd_gcd_pred_of_mem {q n : ℕ} (hq : q.Prime)
    (hg1 : 1 < Nat.gcd (x n) (n + 1))
    (hglt : Nat.gcd (x n) (n + 1) < q) :
    ¬ q ∣ Nat.gcd (x n) (n + 1) - 1 := by
  intro h
  exact (Nat.ne_of_gt hg1)
    (eq_one_of_prime_dvd_pred hq (Nat.le_of_lt hg1) hglt h)

/-- A coprime shift is exactly the `g = 1` case of `first_entry_iff_dvd_gcd_pred`. -/
lemma q_dvd_x_of_gcd_eq_one_at_shift {q k : ℕ}
    (hq : q.Prime) (h2 : 2 < q) (hpos : 0 < k * q - 3)
    (hx : ¬ q ∣ x (k * q - 3))
    (hg : Nat.gcd (x (k * q - 3)) (k * q - 2) = 1) :
    q ∣ x (k * q - 2) :=
  (first_entry_iff_dvd_gcd_pred hq h2 hpos hx).2 (by
    rw [hg]
    exact dvd_zero q)

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

/-- `a 5 = 1` because `6 ∣ x 5`. -/
lemma a_5 : a 5 = 1 := by
  have hn : 0 < (5 : ℕ) := by decide
  have h2 : 2 ∣ x 5 := two_dvd_x (by decide : 2 ≤ 5)
  have h3 : 3 ∣ x 5 := three_dvd_x (by decide : 4 ≤ 5)
  have hcop : Nat.Coprime 2 3 := Nat.coprime_iff_gcd_eq_one.2 (by decide)
  have h6 : 6 ∣ x 5 := hcop.mul_dvd_of_dvd_of_dvd h2 h3
  have hg : Nat.gcd (x 5) 6 = 6 := Nat.gcd_eq_right h6
  rw [a_eq hn, show (5 : ℕ) + 1 = 6 from rfl, hg, Nat.div_self (by decide : 0 < 6)]

/-- Three successive increments `a 3 = a 4 = a 5 = 1` give `27 ∣ x 6`. -/
lemma x_six_eq_mul : x 6 = x 3 * 27 := by
  have h4 := x_succ_a (by decide : 0 < (3 : ℕ))
  rw [a_3] at h4
  have h5 := x_succ_a (by decide : 0 < (4 : ℕ))
  rw [a_4] at h5
  have h6 := x_succ_a (by decide : 0 < (5 : ℕ))
  rw [a_5] at h6
  rw [h6, h5, h4]
  ring

lemma twenty_seven_dvd_x_six : 27 ∣ x 6 := by
  rw [x_six_eq_mul]
  exact dvd_mul_left _ _

lemma twenty_seven_dvd_x {n : ℕ} (hn : 6 ≤ n) : 27 ∣ x n :=
  twenty_seven_dvd_x_six.trans (x_dvd_of_le (by decide : 0 < 6) hn)

lemma x_three : x 3 = 20 := by decide

lemma not_seven_dvd_x_six : ¬ 7 ∣ x 6 := by
  rw [x_six_eq_mul, x_three]
  decide

lemma five_dvd_x_three : 5 ∣ x 3 := by
  have h := x_succ_a (n := 2) (by decide)
  rw [a_2] at h
  rw [h]
  exact dvd_mul_left 5 _

lemma five_dvd_x {n : ℕ} (hn : 3 ≤ n) : 5 ∣ x n :=
  five_dvd_x_three.trans (x_dvd_of_le (by decide : 0 < 3) hn)

/-- For `n ≥ 4`, the primes `2,3,5` have entered, so `30 ∣ x n`. -/
lemma thirty_dvd_x {n : ℕ} (hn : 4 ≤ n) : 30 ∣ x n := by
  have h2 : 2 ∣ x n := two_dvd_x (le_trans (by decide : 2 ≤ 4) hn)
  have h3 : 3 ∣ x n := three_dvd_x hn
  have h5 : 5 ∣ x n := five_dvd_x (le_trans (by decide : 3 ≤ 4) hn)
  have h6 : Nat.lcm 2 3 ∣ x n := Nat.lcm_dvd h2 h3
  have h6eq : Nat.lcm 2 3 = 6 := by decide
  rw [h6eq] at h6
  have h30 : Nat.lcm 6 5 ∣ x n := Nat.lcm_dvd h6 h5
  have h30eq : Nat.lcm 6 5 = 30 := by decide
  rwa [h30eq] at h30

/-- Stock lower bound: `gcd(n+1, 30)` has already entered for `n ≥ 4`. -/
lemma gcd_thirty_dvd_gcd_x {n : ℕ} (hn : 4 ≤ n) :
    Nat.gcd (n + 1) 30 ∣ Nat.gcd (x n) (n + 1) :=
  Nat.dvd_gcd ((Nat.gcd_dvd_right (n + 1) 30).trans (thirty_dvd_x hn))
    (Nat.gcd_dvd_left _ _)

lemma five_dvd_x_square_window : 5 ∣ x (5 * (5 + 2) - 1) :=
  five_dvd_x (by decide : 3 ≤ 5 * (5 + 2) - 1)

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

/-- The prime index `7` is the unique McEachen exception among twins. -/
lemma a_6 : a 6 = 7 := by
  rcases a_eq_one_or_self (p := 7) Nat.prime_seven with h | h
  · exact (not_seven_dvd_x_six ((a_eq_one_iff_dvd Nat.prime_seven).1 h)).elim
  · exact h

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

/-- McEachen if `p-2` shares a factor `2,3,5` with the entered 30-stock.
This packages the `2,3,5` families; leftover leftover primes have
`gcd(p-2, 30) = 1`. -/
theorem conjecture_of_gcd_thirty {p : ℕ} (hp : p.Prime) (hp7 : 7 ≤ p)
    (h : 1 < Nat.gcd (p - 2) 30) : a (p - 1) = p := by
  have hp5 : 5 ≤ p := le_trans (by decide : 5 ≤ 7) hp7
  have hle : 4 ≤ p - 3 := Nat.sub_le_sub_right hp7 3
  have hidx : p - 3 + 1 = p - 2 := by
    rw [Nat.sub_succ]
    exact Nat.succ_pred_eq_of_pos
      (Nat.sub_pos_of_lt (lt_of_lt_of_le (by decide : 2 < 7) hp7))
  have hg : Nat.gcd (p - 2) 30 ∣ Nat.gcd (x (p - 3)) (p - 2) :=
    hidx ▸ gcd_thirty_dvd_gcd_x hle
  have hpos : 0 < Nat.gcd (x (p - 3)) (p - 2) :=
    Nat.gcd_pos_of_pos_right _
      (Nat.sub_pos_of_lt (lt_of_lt_of_le (by decide : 2 < 7) hp7))
  have hgt : 1 < Nat.gcd (x (p - 3)) (p - 2) :=
    lt_of_lt_of_le h (Nat.le_of_dvd hpos hg)
  exact a_eq_self_of_gcd_gt_one hp hp5 hgt

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

/-- For `n ≥ 47`, the primes `2,3,5,7` have entered, so `210 ∣ x n`. -/
lemma two_hundred_ten_dvd_x {n : ℕ} (hn : 47 ≤ n) : 210 ∣ x n := by
  have h30 : 30 ∣ x n := thirty_dvd_x (le_trans (by decide : 4 ≤ 47) hn)
  have h7 : 7 ∣ x n := seven_dvd_x hn
  have h210 : Nat.lcm 30 7 ∣ x n := Nat.lcm_dvd h30 h7
  have h210eq : Nat.lcm 30 7 = 210 := by decide
  rwa [h210eq] at h210

/-- Stock lower bound: `gcd(n+1, 210)` has already entered for `n ≥ 47`. -/
lemma gcd_two_hundred_ten_dvd_gcd_x {n : ℕ} (hn : 47 ≤ n) :
    Nat.gcd (n + 1) 210 ∣ Nat.gcd (x n) (n + 1) :=
  Nat.dvd_gcd ((Nat.gcd_dvd_right (n + 1) 210).trans (two_hundred_ten_dvd_x hn))
    (Nat.gcd_dvd_left _ _)

/-- McEachen if `p-2` shares a factor `2,3,5,7` with the entered 210-stock.
Leftover least factors `≥ 281` remain coprime to `210`. -/
theorem conjecture_of_gcd_two_hundred_ten {p : ℕ} (hp : p.Prime)
    (hp50 : 50 ≤ p) (h : 1 < Nat.gcd (p - 2) 210) : a (p - 1) = p := by
  have hp5 : 5 ≤ p := le_trans (by decide : 5 ≤ 50) hp50
  have hle : 47 ≤ p - 3 := Nat.sub_le_sub_right hp50 3
  have hidx : p - 3 + 1 = p - 2 := by
    rw [Nat.sub_succ]
    exact Nat.succ_pred_eq_of_pos
      (Nat.sub_pos_of_lt (lt_of_lt_of_le (by decide : 2 < 50) hp50))
  have hg : Nat.gcd (p - 2) 210 ∣ Nat.gcd (x (p - 3)) (p - 2) :=
    hidx ▸ gcd_two_hundred_ten_dvd_gcd_x hle
  have hpos : 0 < Nat.gcd (x (p - 3)) (p - 2) :=
    Nat.gcd_pos_of_pos_right _
      (Nat.sub_pos_of_lt (lt_of_lt_of_le (by decide : 2 < 50) hp50))
  have hgt : 1 < Nat.gcd (x (p - 3)) (p - 2) :=
    lt_of_lt_of_le h (Nat.le_of_dvd hpos hg)
  exact a_eq_self_of_gcd_gt_one hp hp5 hgt

/-- If `lpf(n) ≥ 11`, then `n` is coprime to the 210-stock. Leftover remaining
numbers therefore cannot be injected by `2,3,5,7`. -/
lemma gcd_two_hundred_ten_eq_one_of_minFac {n : ℕ} (_hn : 1 < n)
    (h : 11 ≤ Nat.minFac n) : Nat.gcd n 210 = 1 := by
  have nd2 : ¬ 2 ∣ n := fun hd =>
    Nat.lt_le_asymm (lt_of_lt_of_le (by decide : 2 < 11) h)
      (Nat.minFac_le_of_dvd (by decide : 1 < 2) hd)
  have nd3 : ¬ 3 ∣ n := fun hd =>
    Nat.lt_le_asymm (lt_of_lt_of_le (by decide : 3 < 11) h)
      (Nat.minFac_le_of_dvd (by decide : 1 < 3) hd)
  have nd5 : ¬ 5 ∣ n := fun hd =>
    Nat.lt_le_asymm (lt_of_lt_of_le (by decide : 5 < 11) h)
      (Nat.minFac_le_of_dvd (by decide : 1 < 5) hd)
  have nd7 : ¬ 7 ∣ n := fun hd =>
    Nat.lt_le_asymm (lt_of_lt_of_le (by decide : 7 < 11) h)
      (Nat.minFac_le_of_dvd (by decide : 1 < 7) hd)
  have h2 : n.Coprime 2 :=
    Nat.coprime_comm.mp (Nat.prime_two.coprime_iff_not_dvd.2 nd2)
  have h3 : n.Coprime 3 :=
    Nat.coprime_comm.mp (Nat.prime_three.coprime_iff_not_dvd.2 nd3)
  have h5 : n.Coprime 5 :=
    Nat.coprime_comm.mp ((by decide : Nat.Prime 5).coprime_iff_not_dvd.2 nd5)
  have h7 : n.Coprime 7 :=
    Nat.coprime_comm.mp ((by decide : Nat.Prime 7).coprime_iff_not_dvd.2 nd7)
  have h210 : (2 * 3 * 5 * 7 : ℕ) = 210 := by decide
  have hcop : n.Coprime (2 * 3 * 5 * 7) :=
    ((h2.mul_right h3).mul_right h5).mul_right h7
  have hcop' : n.Coprime 210 := by rwa [h210] at hcop
  exact hcop'.gcd_eq_one

lemma seven_dvd_x_square_window : 7 ∣ x (7 * (7 + 2) - 1) :=
  seven_dvd_x (by decide : 47 ≤ 7 * (7 + 2) - 1)

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

/-- McEachen at `p` if some prime `q ≡ 2 (mod 3)` has `gcd(q+2, p-2) > 1`.
Then a factor of `q+2` already divides `x q` and also divides `p-2`. -/
theorem conjecture_of_add_two_overlap {p q : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p)
    (hq : q.Prime) (h7 : 7 ≤ q) (hmod : q % 3 = 2) (hle : q ≤ p - 3)
    (hgt : 1 < Nat.gcd (q + 2) (p - 2)) : a (p - 1) = p := by
  have hdq : q + 2 ∣ x q := add_two_dvd_x_of_mod_three hq h7 hmod
  have hg : Nat.gcd (q + 2) (p - 2) ∣ q + 2 := Nat.gcd_dvd_left _ _
  have hp2 : Nat.gcd (q + 2) (p - 2) ∣ p - 2 := Nat.gcd_dvd_right _ _
  have hx : Nat.gcd (q + 2) (p - 2) ∣ x q := hg.trans hdq
  have hx2 : Nat.gcd (q + 2) (p - 2) ∣ x (p - 3) :=
    hx.trans (x_dvd_of_le (by omega : 0 < q) hle)
  exact conjecture_of_factor_dvd_x hp hp5 hgt hp2 hx2

/-- Remaining McEachen if a factor `q ≡ 2 (mod 3)` of `p-2` shares a
prime factor with `q+2`. -/
theorem conjecture_of_remaining_add_two_overlap {p q : ℕ} (hp : p.Prime)
    (hp7 : 7 ≤ p) (_hmod : p % 3 = 1) (hcomp : ¬ (p - 2).Prime)
    (hq : q.Prime) (hd : q ∣ p - 2) (hmodq : q % 3 = 2) (h7 : 7 ≤ q)
    (hgt : 1 < Nat.gcd (q + 2) (p - 2)) : a (p - 1) = p := by
  have hp5 : 5 ≤ p := le_trans (by decide : 5 ≤ 7) hp7
  have hle : q ≤ p - 3 := by
    have hqp : q ≤ p - 2 :=
      Nat.le_of_dvd (Nat.sub_pos_of_lt (lt_of_lt_of_le (by decide : 2 < 7) hp7)) hd
    have hne : q ≠ p - 2 := by
      intro heq
      exact hcomp (heq ▸ hq)
    omega
  exact conjecture_of_add_two_overlap hp hp5 hq h7 hmodq hle hgt

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

/-- After excluding overlap `q+2 ∣ p-2`, a remaining least factor
`q ≡ 2 (mod 3)` satisfies `p-2 ≥ q(q+8)`. -/
lemma remaining_minFac_mul_add_eight_le {p : ℕ} (hp : p.Prime) (hp7 : 7 ≤ p)
    (hmod : p % 3 = 1) (hcomp : ¬ (p - 2).Prime)
    (hqmod : Nat.minFac (p - 2) % 3 = 2)
    (hno : ¬ (Nat.minFac (p - 2) + 2) ∣ p - 2) :
    Nat.minFac (p - 2) * (Nat.minFac (p - 2) + 8) ≤ p - 2 := by
  set q := Nat.minFac (p - 2)
  have hbound := remaining_minFac_mul_add_two_le hp hp7 hmod hcomp
  have hqpos : 0 < q := Nat.minFac_pos _
  have hd : q ∣ p - 2 := Nat.minFac_dvd _
  have hqs : q * ((p - 2) / q) = p - 2 := Nat.mul_div_cancel' hd
  have hs2 : q + 2 ≤ (p - 2) / q :=
    (Nat.le_div_iff_mul_le hqpos).2 (by rwa [Nat.mul_comm (q + 2)])
  have hne : (p - 2) / q ≠ q + 2 := by
    intro heq
    have : p - 2 = q * (q + 2) := by rw [← hqs, heq]
    exact hno (this ▸ dvd_mul_left (q + 2) q)
  have hoddn : (p - 2) % 2 = 1 := by
    have hpodd : p % 2 = 1 := by
      have hcases : p % 2 = 0 ∨ p % 2 = 1 := by omega
      rcases hcases with h0 | h1
      · have : 2 ∣ p := Nat.dvd_of_mod_eq_zero h0
        have : p = 2 :=
          ((Nat.prime_dvd_prime_iff_eq Nat.prime_two hp).1 this).symm
        omega
      · exact h1
    omega
  have hqodd : q % 2 = 1 := by
    have hmul : (q * ((p - 2) / q)) % 2 = 1 := by rwa [hqs]
    rw [Nat.mul_mod] at hmul
    have hq2 : q % 2 = 0 ∨ q % 2 = 1 := Nat.mod_two_eq_zero_or_one q
    rcases hq2 with h0 | h1
    · rw [h0, Nat.zero_mul, Nat.zero_mod] at hmul
      exact False.elim ((by decide : ¬ (0 : ℕ) = 1) hmul)
    · exact h1
  have hsodd : ((p - 2) / q) % 2 = 1 := by
    have hmul : (q * ((p - 2) / q)) % 2 = 1 := by rwa [hqs]
    rw [Nat.mul_mod, hqodd] at hmul
    have hs2' : ((p - 2) / q) % 2 = 0 ∨ ((p - 2) / q) % 2 = 1 :=
      Nat.mod_two_eq_zero_or_one _
    rcases hs2' with h0 | h1
    · rw [h0, Nat.mul_zero, Nat.zero_mod] at hmul
      exact False.elim ((by decide : ¬ (0 : ℕ) = 1) hmul)
    · exact h1
  have hpm : (p - 2) % 3 = 2 :=
    p_sub_two_mod (le_trans (by decide : 4 ≤ 7) hp7) hmod
  have hsmod : ((p - 2) / q) % 3 = 1 := by
    have hmul : (q * ((p - 2) / q)) % 3 = 2 := by rwa [hqs]
    rw [Nat.mul_mod, hqmod] at hmul
    have hs3 : ((p - 2) / q) % 3 < 3 := Nat.mod_lt _ (by decide)
    interval_cases ((p - 2) / q) % 3
    · rw [Nat.mul_zero, Nat.zero_mod] at hmul
      exact False.elim ((by decide : ¬ (0 : ℕ) = 2) hmul)
    · rfl
    · have hmul' : ((2 : ℕ) * 2) % 3 = 2 := hmul
      exact False.elim ((by decide : ¬ (1 : ℕ) = 2) (by
        have : ((2 : ℕ) * 2) % 3 = 1 := by decide
        exact this.symm.trans hmul'))
  have hs : q + 8 ≤ (p - 2) / q := by omega
  have : q * (q + 8) ≤ q * ((p - 2) / q) := Nat.mul_le_mul_left q hs
  rwa [hqs] at this

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

/-- Remaining McEachen, after overlap is excluded, reduces to first-entry
of `lpf(p-2)` by index `q(q+8)-1`. -/
theorem conjecture_of_minFac_entered_add_eight {p : ℕ} (hp : p.Prime)
    (hp7 : 7 ≤ p) (hmod : p % 3 = 1) (hcomp : ¬ (p - 2).Prime)
    (hqmod : Nat.minFac (p - 2) % 3 = 2)
    (hno : ¬ (Nat.minFac (p - 2) + 2) ∣ p - 2)
    (hin : Nat.minFac (p - 2) ∣
      x (Nat.minFac (p - 2) * (Nat.minFac (p - 2) + 8) - 1)) :
    a (p - 1) = p := by
  have hbound := remaining_minFac_mul_add_eight_le hp hp7 hmod hcomp hqmod hno
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
  have hmul : 2 * 10 ≤ Nat.minFac (p - 2) * (Nat.minFac (p - 2) + 8) :=
    Nat.mul_le_mul hq2 (Nat.add_le_add_right hq2 8)
  have hpos : 0 < Nat.minFac (p - 2) * (Nat.minFac (p - 2) + 8) - 1 :=
    Nat.sub_pos_of_lt (lt_of_lt_of_le (by decide : 1 < 20) hmul)
  have hle : Nat.minFac (p - 2) * (Nat.minFac (p - 2) + 8) - 1 ≤ p - 3 := by
    have hsub : Nat.minFac (p - 2) * (Nat.minFac (p - 2) + 8) - 1 ≤ p - 2 - 1 :=
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

/-- A prime injector inside the square window injects `q` by index `q(q+2)-1`. -/
lemma q_dvd_x_square_window_of_prime_index {k q : ℕ}
    (hpr : (k * q - 2).Prime) (h7 : 7 ≤ k * q - 2)
    (hmod : (k * q - 2) % 3 = 2)
    (hle : k * q - 2 ≤ q * (q + 2) - 1) :
    q ∣ x (q * (q + 2) - 1) := by
  have hx := q_dvd_x_of_prime_index hpr h7 hmod
  have hpos : 0 < k * q - 2 := by omega
  exact hx.trans (x_dvd_of_le hpos hle)

/-- Any injector index `k ≤ q+2` lies in the square window. -/
lemma k_mul_sub_two_le_square {q k : ℕ} (hk : k ≤ q + 2) :
    k * q - 2 ≤ q * (q + 2) - 1 := by
  have hle1 : k * q ≤ (q + 2) * q := Nat.mul_le_mul_right q hk
  have hle1' : k * q ≤ q * (q + 2) := by rwa [Nat.mul_comm (q + 2)] at hle1
  have h1 : k * q - 2 ≤ q * (q + 2) - 2 := Nat.sub_le_sub_right hle1' 2
  have h2 : q * (q + 2) - 2 ≤ q * (q + 2) - 1 :=
    Nat.sub_le_sub_left (by decide : 1 ≤ 2) (q * (q + 2))
  exact h1.trans h2

/-- A prime injector with `k ≤ q+2` injects `q` inside the square window. -/
lemma q_dvd_x_square_window_of_k_le {k q : ℕ}
    (hpr : (k * q - 2).Prime) (h7 : 7 ≤ k * q - 2)
    (hmod : (k * q - 2) % 3 = 2) (hk : k ≤ q + 2) :
    q ∣ x (q * (q + 2) - 1) :=
  q_dvd_x_square_window_of_prime_index hpr h7 hmod (k_mul_sub_two_le_square hk)

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

/-- Remaining McEachen if a cofactor `s ≡ 1 (mod 3)` of `p-2` is injected at `7s-2`.
The bound `7s-2 ≤ p-3` holds once the complementary factor is at least `7`. -/
theorem conjecture_of_cofactor_seven {p q s : ℕ} (hp : p.Prime) (hp7 : 7 ≤ p)
    (hqs : p - 2 = q * s) (hq7 : 7 ≤ q) (hs1 : 1 < s) (hsmod : s % 3 = 1)
    (hpr : (7 * s - 2).Prime) : a (p - 1) = p := by
  have hp5 : 5 ≤ p := le_trans (by decide : 5 ≤ 7) hp7
  have hs2 : 2 ≤ s := hs1
  have h7r : 7 ≤ 7 * s - 2 := by
    have : 14 ≤ 7 * s := Nat.mul_le_mul_left 7 hs2
    exact le_trans (by decide : 7 ≤ 12) (Nat.sub_le_sub_right this 2)
  have hmod : (7 * s - 2) % 3 = 2 := by
    have hmul : (7 * s) % 3 = 1 := by
      rw [Nat.mul_mod]
      have : (7 : ℕ) % 3 = 1 := by decide
      rw [this, hsmod]
    have hrep : 7 * s = 3 * (7 * s / 3) + 1 := by
      have := (Nat.div_add_mod (7 * s) 3).symm
      rwa [hmul] at this
    omega
  have hle : 7 * s - 2 ≤ p - 3 := by
    have h2p : 2 ≤ p := le_trans (by decide : 2 ≤ 7) hp7
    have hpqs : p = q * s + 2 := (Nat.sub_eq_iff_eq_add h2p).1 hqs
    have hmulqs : 7 * s ≤ q * s := Nat.mul_le_mul_right s hq7
    have hleft : 7 * s - 2 ≤ q * s - 1 :=
      (Nat.sub_le_sub_right hmulqs 2).trans
        (Nat.sub_le_sub_left (by decide : 1 ≤ 2) (q * s))
    have hright : q * s - 1 = p - 3 := by
      rw [hpqs]
      have hdecomp : q * s + 2 - 3 = q * s + 2 - 2 - 1 := by
        rw [show (3 : ℕ) = 2 + 1 from rfl, Nat.sub_add_eq]
      rw [hdecomp, Nat.add_sub_cancel]
    exact hright ▸ hleft
  exact conjecture_of_prime_index hp hp5 hpr h7r hmod hle
    (hqs ▸ Nat.dvd_mul_left s q) hs1

/-- `7q-2` lies in the square window once `q ≥ 7`. -/
lemma seven_mul_sub_two_le_square {q : ℕ} (h7 : 7 ≤ q) :
    7 * q - 2 ≤ q * (q + 2) - 1 := by
  have h1 : 7 * q ≤ q * q := Nat.mul_le_mul_right q h7
  have h2 : q * q ≤ q * (q + 2) := Nat.mul_le_mul_left q (Nat.le_add_right q 2)
  have h3 : 7 * q ≤ q * (q + 2) := h1.trans h2
  exact (Nat.sub_le_sub_right h3 2).trans
    (Nat.sub_le_sub_left (by decide : 1 ≤ 2) (q * (q + 2)))

lemma seven_mul_sub_two_mod_of_one {q : ℕ} (h1 : q % 3 = 1) :
    (7 * q) % 3 = 1 := by
  rw [Nat.mul_mod]
  have : (7 : ℕ) % 3 = 1 := by decide
  rw [this, h1]

lemma seven_mul_sub_two_mod_three {q : ℕ} (h1 : q % 3 = 1) (_h2 : 2 ≤ 7 * q) :
    (7 * q - 2) % 3 = 2 := by
  have hmul := seven_mul_sub_two_mod_of_one h1
  have hrep : 7 * q = 3 * (7 * q / 3) + 1 := by
    have := (Nat.div_add_mod (7 * q) 3).symm
    rwa [hmul] at this
  omega

/-- A prime `7q-2 ≡ 2 (mod 3)` injects `q` inside the square window. -/
lemma q_dvd_x_square_window_of_seven {q : ℕ} (hpr : (7 * q - 2).Prime)
    (h7 : 7 ≤ q) (hmod : (7 * q - 2) % 3 = 2) :
    q ∣ x (q * (q + 2) - 1) := by
  have h7r : 7 ≤ 7 * q - 2 := by
    have : 49 ≤ 7 * q := Nat.mul_le_mul_left 7 h7
    exact le_trans (by decide : 7 ≤ 47) (Nat.sub_le_sub_right this 2)
  exact q_dvd_x_square_window_of_prime_index hpr h7r hmod
    (seven_mul_sub_two_le_square h7)

/-- `5q-2` lies in the square window once `q ≥ 5`. -/
lemma five_mul_sub_two_le_square {q : ℕ} (h5 : 5 ≤ q) :
    5 * q - 2 ≤ q * (q + 2) - 1 := by
  have h1 : 5 * q ≤ q * q := Nat.mul_le_mul_right q h5
  have h2 : q * q ≤ q * (q + 2) := Nat.mul_le_mul_left q (Nat.le_add_right q 2)
  have h3 : 5 * q ≤ q * (q + 2) := h1.trans h2
  exact (Nat.sub_le_sub_right h3 2).trans
    (Nat.sub_le_sub_left (by decide : 1 ≤ 2) (q * (q + 2)))

lemma five_mul_sub_two_mod_of_two {q : ℕ} (h2 : q % 3 = 2) :
    (5 * q) % 3 = 1 := by
  have h5 : (5 : ℕ) % 3 = 2 := by decide
  calc
    (5 * q) % 3 = (5 % 3 * (q % 3)) % 3 := Nat.mul_mod _ _ 3
    _ = (2 * 2) % 3 := by rw [h5, h2]
    _ = 1 := by decide

lemma five_mul_sub_two_mod_three {q : ℕ} (h2 : q % 3 = 2) (_h : 2 ≤ 5 * q) :
    (5 * q - 2) % 3 = 2 := by
  have hmul := five_mul_sub_two_mod_of_two h2
  have hrep : 5 * q = 3 * (5 * q / 3) + 1 := by
    have := (Nat.div_add_mod (5 * q) 3).symm
    rwa [hmul] at this
  omega

/-- A prime `5q-2 ≡ 2 (mod 3)` injects `q` inside the square window.
Usable when `q ≡ 2 (mod 3)`; if `q ≡ 1 (mod 3)` then `3 ∣ 5q-2`. -/
lemma q_dvd_x_square_window_of_five {q : ℕ} (hpr : (5 * q - 2).Prime)
    (h5 : 5 ≤ q) (hmod : (5 * q - 2) % 3 = 2) :
    q ∣ x (q * (q + 2) - 1) := by
  have h7r : 7 ≤ 5 * q - 2 := by
    have : 25 ≤ 5 * q := Nat.mul_le_mul_left 5 h5
    exact le_trans (by decide : 7 ≤ 23) (Nat.sub_le_sub_right this 2)
  exact q_dvd_x_square_window_of_prime_index hpr h7r hmod
    (five_mul_sub_two_le_square h5)

/-- `11q-2` lies in the square window once `q ≥ 11`. -/
lemma eleven_mul_sub_two_le_square {q : ℕ} (h11 : 11 ≤ q) :
    11 * q - 2 ≤ q * (q + 2) - 1 := by
  have h1 : 11 * q ≤ q * q := Nat.mul_le_mul_right q h11
  have h2 : q * q ≤ q * (q + 2) := Nat.mul_le_mul_left q (Nat.le_add_right q 2)
  have h3 : 11 * q ≤ q * (q + 2) := h1.trans h2
  exact (Nat.sub_le_sub_right h3 2).trans
    (Nat.sub_le_sub_left (by decide : 1 ≤ 2) (q * (q + 2)))

lemma eleven_mul_sub_two_mod_of_two {q : ℕ} (h2 : q % 3 = 2) :
    (11 * q) % 3 = 1 := by
  have h11 : (11 : ℕ) % 3 = 2 := by decide
  calc
    (11 * q) % 3 = (11 % 3 * (q % 3)) % 3 := Nat.mul_mod _ _ 3
    _ = (2 * 2) % 3 := by rw [h11, h2]
    _ = 1 := by decide

lemma eleven_mul_sub_two_mod_three {q : ℕ} (h2 : q % 3 = 2) (_h : 2 ≤ 11 * q) :
    (11 * q - 2) % 3 = 2 := by
  have hmul := eleven_mul_sub_two_mod_of_two h2
  have hrep : 11 * q = 3 * (11 * q / 3) + 1 := by
    have := (Nat.div_add_mod (11 * q) 3).symm
    rwa [hmul] at this
  omega

lemma q_dvd_x_square_window_of_eleven {q : ℕ} (hpr : (11 * q - 2).Prime)
    (h11 : 11 ≤ q) (hmod : (11 * q - 2) % 3 = 2) :
    q ∣ x (q * (q + 2) - 1) := by
  have h7r : 7 ≤ 11 * q - 2 := by
    have : 121 ≤ 11 * q := Nat.mul_le_mul_left 11 h11
    exact le_trans (by decide : 7 ≤ 119) (Nat.sub_le_sub_right this 2)
  exact q_dvd_x_square_window_of_prime_index hpr h7r hmod
    (eleven_mul_sub_two_le_square h11)

/-- `13q-2` lies in the square window once `q ≥ 13`. -/
lemma thirteen_mul_sub_two_le_square {q : ℕ} (h13 : 13 ≤ q) :
    13 * q - 2 ≤ q * (q + 2) - 1 := by
  have h1 : 13 * q ≤ q * q := Nat.mul_le_mul_right q h13
  have h2 : q * q ≤ q * (q + 2) := Nat.mul_le_mul_left q (Nat.le_add_right q 2)
  have h3 : 13 * q ≤ q * (q + 2) := h1.trans h2
  exact (Nat.sub_le_sub_right h3 2).trans
    (Nat.sub_le_sub_left (by decide : 1 ≤ 2) (q * (q + 2)))

lemma thirteen_mul_sub_two_mod_of_one {q : ℕ} (h1 : q % 3 = 1) :
    (13 * q) % 3 = 1 := by
  rw [Nat.mul_mod]
  have : (13 : ℕ) % 3 = 1 := by decide
  rw [this, h1]

lemma thirteen_mul_sub_two_mod_three {q : ℕ} (h1 : q % 3 = 1) (_h : 2 ≤ 13 * q) :
    (13 * q - 2) % 3 = 2 := by
  have hmul := thirteen_mul_sub_two_mod_of_one h1
  have hrep : 13 * q = 3 * (13 * q / 3) + 1 := by
    have := (Nat.div_add_mod (13 * q) 3).symm
    rwa [hmul] at this
  omega

lemma q_dvd_x_square_window_of_thirteen {q : ℕ} (hpr : (13 * q - 2).Prime)
    (h13 : 13 ≤ q) (hmod : (13 * q - 2) % 3 = 2) :
    q ∣ x (q * (q + 2) - 1) := by
  have h7r : 7 ≤ 13 * q - 2 := by
    have : 169 ≤ 13 * q := Nat.mul_le_mul_left 13 h13
    exact le_trans (by decide : 7 ≤ 167) (Nat.sub_le_sub_right this 2)
  exact q_dvd_x_square_window_of_prime_index hpr h7r hmod
    (thirteen_mul_sub_two_le_square h13)

lemma q_dvd_x_square_window_of_seventeen {q : ℕ} (hpr : (17 * q - 2).Prime)
    (h17 : 17 ≤ q) (hmod : (17 * q - 2) % 3 = 2) :
    q ∣ x (q * (q + 2) - 1) := by
  have h7r : 7 ≤ 17 * q - 2 := by
    have : 289 ≤ 17 * q := Nat.mul_le_mul_left 17 h17
    exact le_trans (by decide : 7 ≤ 287) (Nat.sub_le_sub_right this 2)
  exact q_dvd_x_square_window_of_k_le hpr h7r hmod
    (le_trans h17 (Nat.le_add_right q 2))

lemma q_dvd_x_square_window_of_nineteen {q : ℕ} (hpr : (19 * q - 2).Prime)
    (h19 : 19 ≤ q) (hmod : (19 * q - 2) % 3 = 2) :
    q ∣ x (q * (q + 2) - 1) := by
  have h7r : 7 ≤ 19 * q - 2 := by
    have : 361 ≤ 19 * q := Nat.mul_le_mul_left 19 h19
    exact le_trans (by decide : 7 ≤ 359) (Nat.sub_le_sub_right this 2)
  exact q_dvd_x_square_window_of_k_le hpr h7r hmod
    (le_trans h19 (Nat.le_add_right q 2))

lemma q_dvd_x_square_window_of_twentythree {q : ℕ} (hpr : (23 * q - 2).Prime)
    (h23 : 23 ≤ q) (hmod : (23 * q - 2) % 3 = 2) :
    q ∣ x (q * (q + 2) - 1) := by
  have h7r : 7 ≤ 23 * q - 2 := by
    have : 529 ≤ 23 * q := Nat.mul_le_mul_left 23 h23
    exact le_trans (by decide : 7 ≤ 527) (Nat.sub_le_sub_right this 2)
  exact q_dvd_x_square_window_of_k_le hpr h7r hmod
    (le_trans h23 (Nat.le_add_right q 2))

lemma q_dvd_x_square_window_of_twentyfive {q : ℕ} (hpr : (25 * q - 2).Prime)
    (h25 : 25 ≤ q) (hmod : (25 * q - 2) % 3 = 2) :
    q ∣ x (q * (q + 2) - 1) := by
  have h7r : 7 ≤ 25 * q - 2 := by
    have : 625 ≤ 25 * q := Nat.mul_le_mul_left 25 h25
    exact le_trans (by decide : 7 ≤ 623) (Nat.sub_le_sub_right this 2)
  exact q_dvd_x_square_window_of_k_le hpr h7r hmod
    (le_trans h25 (Nat.le_add_right q 2))

lemma q_dvd_x_square_window_of_twenty_nine {q : ℕ} (hpr : (29 * q - 2).Prime)
    (h29 : 29 ≤ q) (hmod : (29 * q - 2) % 3 = 2) :
    q ∣ x (q * (q + 2) - 1) := by
  have h7r : 7 ≤ 29 * q - 2 := by
    have : 841 ≤ 29 * q := Nat.mul_le_mul_left 29 h29
    exact le_trans (by decide : 7 ≤ 839) (Nat.sub_le_sub_right this 2)
  exact q_dvd_x_square_window_of_k_le hpr h7r hmod
    (le_trans h29 (Nat.le_add_right q 2))

/-- If `q² - 2` is prime and `q ≡ 2 (mod 3)`, then `q` enters inside the
square window at `k = q`. This is a proper subfamily, not a window bound. -/
lemma q_dvd_x_square_window_of_sq_sub_two {q : ℕ}
    (hpr : (q * q - 2).Prime) (h7 : 7 ≤ q) (hmodq : q % 3 = 2) :
    q ∣ x (q * (q + 2) - 1) := by
  have h7r : 7 ≤ q * q - 2 := by
    have : 49 ≤ q * q := Nat.mul_le_mul h7 h7
    exact le_trans (by decide : 7 ≤ 47) (Nat.sub_le_sub_right this 2)
  have h4 : 4 ≤ q * q :=
    le_trans (by decide : 4 ≤ 49) (Nat.mul_le_mul h7 h7)
  have hmod : (q * q - 2) % 3 = 2 :=
    mul_sub_two_mod_three hmodq hmodq h4
  exact q_dvd_x_square_window_of_k_le hpr h7r hmod (Nat.le_add_right q 2)

/-- If `k ≤ q`, then the cofactor injector `ks-2` is at most `p-3`. -/
lemma cofactor_injector_le {p q s k : ℕ}
    (hqs : p - 2 = q * s) (hp2 : 2 ≤ p) (hk : k ≤ q) :
    k * s - 2 ≤ p - 3 := by
  have hpqs : p = q * s + 2 := (Nat.sub_eq_iff_eq_add hp2).1 hqs
  have hmul : k * s ≤ q * s := Nat.mul_le_mul_right s hk
  have hleft : k * s - 2 ≤ q * s - 2 := Nat.sub_le_sub_right hmul 2
  have heq : q * s - 2 = p - 4 := by
    rw [hpqs]
    have hdecomp : q * s + 2 - 4 = q * s + 2 - 2 - 2 := by
      rw [show (4 : ℕ) = 2 + 2 from rfl, Nat.sub_add_eq]
    rw [hdecomp, Nat.add_sub_cancel]
  have h34 : p - 4 ≤ p - 3 := Nat.sub_le_sub_left (by decide : 3 ≤ 4) p
  exact hleft.trans (heq ▸ h34)

/-- Remaining McEachen if a cofactor `s ≡ 2 (mod 3)` of `p-2` is injected at `5s-2`.
The bound `5s-2 ≤ p-3` holds once the complementary factor is at least `5`.
This is the `k=5` injector for cofactors `≡ 2 (mod 3)`, i.e. when
`lpf(p-2) ≡ 1 (mod 3)`. -/
theorem conjecture_of_cofactor_five {p q s : ℕ} (hp : p.Prime) (hp7 : 7 ≤ p)
    (hqs : p - 2 = q * s) (hq5 : 5 ≤ q) (hs1 : 1 < s) (hsmod : s % 3 = 2)
    (hpr : (5 * s - 2).Prime) : a (p - 1) = p := by
  have hp5 : 5 ≤ p := le_trans (by decide : 5 ≤ 7) hp7
  have hs2 : 2 ≤ s := hs1
  have h7r : 7 ≤ 5 * s - 2 := by
    have : 10 ≤ 5 * s := Nat.mul_le_mul_left 5 hs2
    exact le_trans (by decide : 7 ≤ 8) (Nat.sub_le_sub_right this 2)
  have hmod : (5 * s - 2) % 3 = 2 :=
    five_mul_sub_two_mod_three hsmod
      (le_trans (by decide : 2 ≤ 10) (Nat.mul_le_mul_left 5 hs2))
  have hle : 5 * s - 2 ≤ p - 3 :=
    cofactor_injector_le hqs (le_trans (by decide : 2 ≤ 7) hp7)
      (le_trans (by decide : 5 ≤ 5) hq5)
  exact conjecture_of_prime_index hp hp5 hpr h7r hmod hle
    (hqs ▸ Nat.dvd_mul_left s q) hs1

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

lemma k_mod_three_of_six_five {k : ℕ} (hk : k % 6 = 5) : k % 3 = 2 := by
  have hrep : 6 * (k / 6) + 5 = k := by
    have := Nat.div_add_mod k 6
    rwa [hk] at this
  have : k % 3 = (6 * (k / 6) + 5) % 3 := by rw [hrep]
  have h0 : (6 * (k / 6)) % 3 = 0 := by
    have : (6 : ℕ) % 3 = 0 := by decide
    rw [Nat.mul_mod, this, Nat.zero_mul, Nat.zero_mod]
  have h5 : (5 : ℕ) % 3 = 2 := by decide
  rw [this, Nat.add_mod, h0, Nat.zero_add, Nat.mod_mod, h5]

lemma k_ge_five_of_mod_six_five {k : ℕ} (hk : k % 6 = 5) : 5 ≤ k := by
  have hrep : 6 * (k / 6) + 5 = k := by
    have := Nat.div_add_mod k 6
    rwa [hk] at this
  have : 5 ≤ 6 * (k / 6) + 5 := Nat.le_add_left 5 _
  rwa [hrep] at this

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

/-- Remaining primes `q ≡ 2 (mod 3)` are `≡ 5 (mod 6)`, so `k = q` is an
admissible injector residue. Primality of `q² - 2` is not proved. -/
lemma q_mod_six_five {q : ℕ} (hq : q.Prime) (h7 : 7 ≤ q) (hmod : q % 3 = 2) :
    q % 6 = 5 :=
  (odd_k_mod_three_two_iff (odd_of_prime_mod_three_two hq h7 hmod)).1 hmod

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

lemma one_hundred_seven_dvd_x_2459 : 107 ∣ x 2459 :=
  q_dvd_x_of_prime_index (k := 23) (q := 107)
    (by norm_num) (by decide) (by decide)

lemma one_hundred_seven_dvd_x {n : ℕ} (hn : 2459 ≤ n) : 107 ∣ x n :=
  one_hundred_seven_dvd_x_2459.trans (x_dvd_of_le (by decide : 0 < 2459) hn)

theorem conjecture_of_one_hundred_seven_dvd {p : ℕ} (hp : p.Prime)
    (hp2462 : 2462 ≤ p) (h107 : 107 ∣ p - 2) : a (p - 1) = p :=
  conjecture_of_factor_dvd_x hp (by omega) (by decide : 1 < 107) h107
    (one_hundred_seven_dvd_x (by omega : 2459 ≤ p - 3))

lemma one_hundred_sixty_three_dvd_x_4073 : 163 ∣ x 4073 :=
  q_dvd_x_of_prime_index (k := 25) (q := 163)
    (by norm_num) (by decide) (by decide)

lemma one_hundred_sixty_three_dvd_x {n : ℕ} (hn : 4073 ≤ n) : 163 ∣ x n :=
  one_hundred_sixty_three_dvd_x_4073.trans (x_dvd_of_le (by decide : 0 < 4073) hn)

theorem conjecture_of_one_hundred_sixty_three_dvd {p : ℕ} (hp : p.Prime)
    (hp4076 : 4076 ≤ p) (h163 : 163 ∣ p - 2) : a (p - 1) = p :=
  conjecture_of_factor_dvd_x hp (by omega) (by decide : 1 < 163) h163
    (one_hundred_sixty_three_dvd_x (by omega : 4073 ≤ p - 3))

lemma one_hundred_sixty_seven_dvd_x_2837 : 167 ∣ x 2837 :=
  q_dvd_x_of_prime_index (k := 17) (q := 167)
    (by norm_num) (by decide) (by decide)

lemma one_hundred_sixty_seven_dvd_x {n : ℕ} (hn : 2837 ≤ n) : 167 ∣ x n :=
  one_hundred_sixty_seven_dvd_x_2837.trans (x_dvd_of_le (by decide : 0 < 2837) hn)

theorem conjecture_of_one_hundred_sixty_seven_dvd {p : ℕ} (hp : p.Prime)
    (hp2840 : 2840 ≤ p) (h167 : 167 ∣ p - 2) : a (p - 1) = p :=
  conjecture_of_factor_dvd_x hp (by omega) (by decide : 1 < 167) h167
    (one_hundred_sixty_seven_dvd_x (by omega : 2837 ≤ p - 3))

lemma one_hundred_seventy_nine_dvd_x_3041 : 179 ∣ x 3041 :=
  q_dvd_x_of_prime_index (k := 17) (q := 179)
    (by norm_num) (by decide) (by decide)

lemma one_hundred_seventy_nine_dvd_x {n : ℕ} (hn : 3041 ≤ n) : 179 ∣ x n :=
  one_hundred_seventy_nine_dvd_x_3041.trans (x_dvd_of_le (by decide : 0 < 3041) hn)

theorem conjecture_of_one_hundred_seventy_nine_dvd {p : ℕ} (hp : p.Prime)
    (hp3044 : 3044 ≤ p) (h179 : 179 ∣ p - 2) : a (p - 1) = p :=
  conjecture_of_factor_dvd_x hp (by omega) (by decide : 1 < 179) h179
    (one_hundred_seventy_nine_dvd_x (by omega : 3041 ≤ p - 3))

lemma two_hundred_twenty_seven_dvd_x_6581 : 227 ∣ x 6581 :=
  q_dvd_x_of_prime_index (k := 29) (q := 227)
    (by norm_num) (by decide) (by decide)

lemma two_hundred_twenty_seven_dvd_x {n : ℕ} (hn : 6581 ≤ n) : 227 ∣ x n :=
  two_hundred_twenty_seven_dvd_x_6581.trans (x_dvd_of_le (by decide : 0 < 6581) hn)

theorem conjecture_of_two_hundred_twenty_seven_dvd {p : ℕ} (hp : p.Prime)
    (hp6584 : 6584 ≤ p) (h227 : 227 ∣ p - 2) : a (p - 1) = p :=
  conjecture_of_factor_dvd_x hp (by omega) (by decide : 1 < 227) h227
    (two_hundred_twenty_seven_dvd_x (by omega : 6581 ≤ p - 3))

lemma two_hundred_fifty_one_dvd_x_8783 : 251 ∣ x 8783 :=
  q_dvd_x_of_prime_index (k := 35) (q := 251)
    (by norm_num) (by decide) (by decide)

lemma two_hundred_fifty_one_dvd_x {n : ℕ} (hn : 8783 ≤ n) : 251 ∣ x n :=
  two_hundred_fifty_one_dvd_x_8783.trans (x_dvd_of_le (by decide : 0 < 8783) hn)

theorem conjecture_of_two_hundred_fifty_one_dvd {p : ℕ} (hp : p.Prime)
    (hp8786 : 8786 ≤ p) (h251 : 251 ∣ p - 2) : a (p - 1) = p :=
  conjecture_of_factor_dvd_x hp (by omega) (by decide : 1 < 251) h251
    (two_hundred_fifty_one_dvd_x (by omega : 8783 ≤ p - 3))

lemma three_hundred_eighty_nine_dvd_x_11279 : 389 ∣ x 11279 :=
  q_dvd_x_of_prime_index (k := 29) (q := 389)
    (by norm_num) (by decide) (by decide)

lemma three_hundred_eighty_nine_dvd_x {n : ℕ} (hn : 11279 ≤ n) : 389 ∣ x n :=
  three_hundred_eighty_nine_dvd_x_11279.trans (x_dvd_of_le (by decide : 0 < 11279) hn)

theorem conjecture_of_three_hundred_eighty_nine_dvd {p : ℕ} (hp : p.Prime)
    (hp11282 : 11282 ≤ p) (h389 : 389 ∣ p - 2) : a (p - 1) = p :=
  conjecture_of_factor_dvd_x hp (by omega) (by decide : 1 < 389) h389
    (three_hundred_eighty_nine_dvd_x (by omega : 11279 ≤ p - 3))

lemma one_hundred_thirteen_dvd_x_563 : 113 ∣ x 563 :=
  q_dvd_x_of_prime_index (k := 5) (q := 113)
    (by norm_num) (by decide) (by decide)

lemma one_hundred_thirteen_dvd_x {n : ℕ} (hn : 563 ≤ n) : 113 ∣ x n :=
  one_hundred_thirteen_dvd_x_563.trans (x_dvd_of_le (by decide : 0 < 563) hn)

theorem conjecture_of_one_hundred_thirteen_dvd {p : ℕ} (hp : p.Prime)
    (hp566 : 566 ≤ p) (h113 : 113 ∣ p - 2) : a (p - 1) = p :=
  conjecture_of_factor_dvd_x hp (le_trans (by decide : 5 ≤ 566) hp566)
    (by decide : 1 < 113) h113
    (one_hundred_thirteen_dvd_x (Nat.sub_le_sub_right hp566 3))

lemma one_hundred_twenty_seven_dvd_x_887 : 127 ∣ x 887 :=
  q_dvd_x_of_prime_index (k := 7) (q := 127)
    (by norm_num) (by decide) (by decide)

lemma one_hundred_twenty_seven_dvd_x {n : ℕ} (hn : 887 ≤ n) : 127 ∣ x n :=
  one_hundred_twenty_seven_dvd_x_887.trans (x_dvd_of_le (by decide : 0 < 887) hn)

theorem conjecture_of_one_hundred_twenty_seven_dvd {p : ℕ} (hp : p.Prime)
    (hp890 : 890 ≤ p) (h127 : 127 ∣ p - 2) : a (p - 1) = p :=
  conjecture_of_factor_dvd_x hp (le_trans (by decide : 5 ≤ 890) hp890)
    (by decide : 1 < 127) h127
    (one_hundred_twenty_seven_dvd_x (Nat.sub_le_sub_right hp890 3))

lemma one_hundred_thirty_one_dvd_x_653 : 131 ∣ x 653 :=
  q_dvd_x_of_prime_index (k := 5) (q := 131)
    (by norm_num) (by decide) (by decide)

lemma one_hundred_thirty_one_dvd_x {n : ℕ} (hn : 653 ≤ n) : 131 ∣ x n :=
  one_hundred_thirty_one_dvd_x_653.trans (x_dvd_of_le (by decide : 0 < 653) hn)

theorem conjecture_of_one_hundred_thirty_one_dvd {p : ℕ} (hp : p.Prime)
    (hp656 : 656 ≤ p) (h131 : 131 ∣ p - 2) : a (p - 1) = p :=
  conjecture_of_factor_dvd_x hp (le_trans (by decide : 5 ≤ 656) hp656)
    (by decide : 1 < 131) h131
    (one_hundred_thirty_one_dvd_x (Nat.sub_le_sub_right hp656 3))

lemma one_hundred_thirty_seven_dvd_x_683 : 137 ∣ x 683 :=
  q_dvd_x_of_prime_index (k := 5) (q := 137)
    (by norm_num) (by decide) (by decide)

lemma one_hundred_thirty_seven_dvd_x {n : ℕ} (hn : 683 ≤ n) : 137 ∣ x n :=
  one_hundred_thirty_seven_dvd_x_683.trans (x_dvd_of_le (by decide : 0 < 683) hn)

theorem conjecture_of_one_hundred_thirty_seven_dvd {p : ℕ} (hp : p.Prime)
    (hp686 : 686 ≤ p) (h137 : 137 ∣ p - 2) : a (p - 1) = p :=
  conjecture_of_factor_dvd_x hp (le_trans (by decide : 5 ≤ 686) hp686)
    (by decide : 1 < 137) h137
    (one_hundred_thirty_seven_dvd_x (Nat.sub_le_sub_right hp686 3))

lemma one_hundred_forty_nine_dvd_x_743 : 149 ∣ x 743 :=
  q_dvd_x_of_prime_index (k := 5) (q := 149)
    (by norm_num) (by decide) (by decide)

lemma one_hundred_forty_nine_dvd_x {n : ℕ} (hn : 743 ≤ n) : 149 ∣ x n :=
  one_hundred_forty_nine_dvd_x_743.trans (x_dvd_of_le (by decide : 0 < 743) hn)

theorem conjecture_of_one_hundred_forty_nine_dvd {p : ℕ} (hp : p.Prime)
    (hp746 : 746 ≤ p) (h149 : 149 ∣ p - 2) : a (p - 1) = p :=
  conjecture_of_factor_dvd_x hp (le_trans (by decide : 5 ≤ 746) hp746)
    (by decide : 1 < 149) h149
    (one_hundred_forty_nine_dvd_x (Nat.sub_le_sub_right hp746 3))

lemma one_hundred_fifty_seven_dvd_x_1097 : 157 ∣ x 1097 :=
  q_dvd_x_of_prime_index (k := 7) (q := 157)
    (by norm_num) (by decide) (by decide)

lemma one_hundred_fifty_seven_dvd_x {n : ℕ} (hn : 1097 ≤ n) : 157 ∣ x n :=
  one_hundred_fifty_seven_dvd_x_1097.trans (x_dvd_of_le (by decide : 0 < 1097) hn)

theorem conjecture_of_one_hundred_fifty_seven_dvd {p : ℕ} (hp : p.Prime)
    (hp1100 : 1100 ≤ p) (h157 : 157 ∣ p - 2) : a (p - 1) = p :=
  conjecture_of_factor_dvd_x hp (le_trans (by decide : 5 ≤ 1100) hp1100)
    (by decide : 1 < 157) h157
    (one_hundred_fifty_seven_dvd_x (Nat.sub_le_sub_right hp1100 3))

lemma one_hundred_seventy_three_dvd_x_863 : 173 ∣ x 863 :=
  q_dvd_x_of_prime_index (k := 5) (q := 173)
    (by norm_num) (by decide) (by decide)

lemma one_hundred_seventy_three_dvd_x {n : ℕ} (hn : 863 ≤ n) : 173 ∣ x n :=
  one_hundred_seventy_three_dvd_x_863.trans (x_dvd_of_le (by decide : 0 < 863) hn)

theorem conjecture_of_one_hundred_seventy_three_dvd {p : ℕ} (hp : p.Prime)
    (hp866 : 866 ≤ p) (h173 : 173 ∣ p - 2) : a (p - 1) = p :=
  conjecture_of_factor_dvd_x hp (le_trans (by decide : 5 ≤ 866) hp866)
    (by decide : 1 < 173) h173
    (one_hundred_seventy_three_dvd_x (Nat.sub_le_sub_right hp866 3))

lemma one_hundred_ninety_one_dvd_x_953 : 191 ∣ x 953 :=
  q_dvd_x_of_prime_index (k := 5) (q := 191)
    (by norm_num) (by decide) (by decide)

lemma one_hundred_ninety_one_dvd_x {n : ℕ} (hn : 953 ≤ n) : 191 ∣ x n :=
  one_hundred_ninety_one_dvd_x_953.trans (x_dvd_of_le (by decide : 0 < 953) hn)

theorem conjecture_of_one_hundred_ninety_one_dvd {p : ℕ} (hp : p.Prime)
    (hp956 : 956 ≤ p) (h191 : 191 ∣ p - 2) : a (p - 1) = p :=
  conjecture_of_factor_dvd_x hp (le_trans (by decide : 5 ≤ 956) hp956)
    (by decide : 1 < 191) h191
    (one_hundred_ninety_one_dvd_x (Nat.sub_le_sub_right hp956 3))

lemma one_hundred_ninety_seven_dvd_x_983 : 197 ∣ x 983 :=
  q_dvd_x_of_prime_index (k := 5) (q := 197)
    (by norm_num) (by decide) (by decide)

lemma one_hundred_ninety_seven_dvd_x {n : ℕ} (hn : 983 ≤ n) : 197 ∣ x n :=
  one_hundred_ninety_seven_dvd_x_983.trans (x_dvd_of_le (by decide : 0 < 983) hn)

theorem conjecture_of_one_hundred_ninety_seven_dvd {p : ℕ} (hp : p.Prime)
    (hp986 : 986 ≤ p) (h197 : 197 ∣ p - 2) : a (p - 1) = p :=
  conjecture_of_factor_dvd_x hp (le_trans (by decide : 5 ≤ 986) hp986)
    (by decide : 1 < 197) h197
    (one_hundred_ninety_seven_dvd_x (Nat.sub_le_sub_right hp986 3))

lemma two_hundred_eleven_dvd_x_2741 : 211 ∣ x 2741 :=
  q_dvd_x_of_prime_index (k := 13) (q := 211)
    (by norm_num) (by decide) (by decide)

lemma two_hundred_eleven_dvd_x {n : ℕ} (hn : 2741 ≤ n) : 211 ∣ x n :=
  two_hundred_eleven_dvd_x_2741.trans (x_dvd_of_le (by decide : 0 < 2741) hn)

theorem conjecture_of_two_hundred_eleven_dvd {p : ℕ} (hp : p.Prime)
    (hp2744 : 2744 ≤ p) (h211 : 211 ∣ p - 2) : a (p - 1) = p :=
  conjecture_of_factor_dvd_x hp (le_trans (by decide : 5 ≤ 2744) hp2744)
    (by decide : 1 < 211) h211
    (two_hundred_eleven_dvd_x (Nat.sub_le_sub_right hp2744 3))

lemma two_hundred_twenty_three_dvd_x_1559 : 223 ∣ x 1559 :=
  q_dvd_x_of_prime_index (k := 7) (q := 223)
    (by norm_num) (by decide) (by decide)

lemma two_hundred_twenty_three_dvd_x {n : ℕ} (hn : 1559 ≤ n) : 223 ∣ x n :=
  two_hundred_twenty_three_dvd_x_1559.trans (x_dvd_of_le (by decide : 0 < 1559) hn)

theorem conjecture_of_two_hundred_twenty_three_dvd {p : ℕ} (hp : p.Prime)
    (hp1562 : 1562 ≤ p) (h223 : 223 ∣ p - 2) : a (p - 1) = p :=
  conjecture_of_factor_dvd_x hp (le_trans (by decide : 5 ≤ 1562) hp1562)
    (by decide : 1 < 223) h223
    (two_hundred_twenty_three_dvd_x (Nat.sub_le_sub_right hp1562 3))

lemma two_hundred_thirty_three_dvd_x_1163 : 233 ∣ x 1163 :=
  q_dvd_x_of_prime_index (k := 5) (q := 233)
    (by norm_num) (by decide) (by decide)

lemma two_hundred_thirty_three_dvd_x {n : ℕ} (hn : 1163 ≤ n) : 233 ∣ x n :=
  two_hundred_thirty_three_dvd_x_1163.trans (x_dvd_of_le (by decide : 0 < 1163) hn)

theorem conjecture_of_two_hundred_thirty_three_dvd {p : ℕ} (hp : p.Prime)
    (hp1166 : 1166 ≤ p) (h233 : 233 ∣ p - 2) : a (p - 1) = p :=
  conjecture_of_factor_dvd_x hp (le_trans (by decide : 5 ≤ 1166) hp1166)
    (by decide : 1 < 233) h233
    (two_hundred_thirty_three_dvd_x (Nat.sub_le_sub_right hp1166 3))

lemma two_hundred_thirty_nine_dvd_x_1193 : 239 ∣ x 1193 :=
  q_dvd_x_of_prime_index (k := 5) (q := 239)
    (by norm_num) (by decide) (by decide)

lemma two_hundred_thirty_nine_dvd_x {n : ℕ} (hn : 1193 ≤ n) : 239 ∣ x n :=
  two_hundred_thirty_nine_dvd_x_1193.trans (x_dvd_of_le (by decide : 0 < 1193) hn)

theorem conjecture_of_two_hundred_thirty_nine_dvd {p : ℕ} (hp : p.Prime)
    (hp1196 : 1196 ≤ p) (h239 : 239 ∣ p - 2) : a (p - 1) = p :=
  conjecture_of_factor_dvd_x hp (le_trans (by decide : 5 ≤ 1196) hp1196)
    (by decide : 1 < 239) h239
    (two_hundred_thirty_nine_dvd_x (Nat.sub_le_sub_right hp1196 3))

lemma two_hundred_fifty_seven_dvd_x_1283 : 257 ∣ x 1283 :=
  q_dvd_x_of_prime_index (k := 5) (q := 257)
    (by norm_num) (by decide) (by decide)

lemma two_hundred_fifty_seven_dvd_x {n : ℕ} (hn : 1283 ≤ n) : 257 ∣ x n :=
  two_hundred_fifty_seven_dvd_x_1283.trans (x_dvd_of_le (by decide : 0 < 1283) hn)

theorem conjecture_of_two_hundred_fifty_seven_dvd {p : ℕ} (hp : p.Prime)
    (hp1286 : 1286 ≤ p) (h257 : 257 ∣ p - 2) : a (p - 1) = p :=
  conjecture_of_factor_dvd_x hp (le_trans (by decide : 5 ≤ 1286) hp1286)
    (by decide : 1 < 257) h257
    (two_hundred_fifty_seven_dvd_x (Nat.sub_le_sub_right hp1286 3))

lemma two_hundred_sixty_three_dvd_x_6047 : 263 ∣ x 6047 :=
  q_dvd_x_of_prime_index (k := 23) (q := 263)
    (by norm_num) (by decide) (by decide)

lemma two_hundred_sixty_three_dvd_x {n : ℕ} (hn : 6047 ≤ n) : 263 ∣ x n :=
  two_hundred_sixty_three_dvd_x_6047.trans (x_dvd_of_le (by decide : 0 < 6047) hn)

theorem conjecture_of_two_hundred_sixty_three_dvd {p : ℕ} (hp : p.Prime)
    (hp6050 : 6050 ≤ p) (h263 : 263 ∣ p - 2) : a (p - 1) = p :=
  conjecture_of_factor_dvd_x hp (le_trans (by decide : 5 ≤ 6050) hp6050)
    (by decide : 1 < 263) h263
    (two_hundred_sixty_three_dvd_x (Nat.sub_le_sub_right hp6050 3))

lemma two_hundred_sixty_nine_dvd_x_2957 : 269 ∣ x 2957 :=
  q_dvd_x_of_prime_index (k := 11) (q := 269)
    (by norm_num) (by decide) (by decide)

lemma two_hundred_sixty_nine_dvd_x {n : ℕ} (hn : 2957 ≤ n) : 269 ∣ x n :=
  two_hundred_sixty_nine_dvd_x_2957.trans (x_dvd_of_le (by decide : 0 < 2957) hn)

theorem conjecture_of_two_hundred_sixty_nine_dvd {p : ℕ} (hp : p.Prime)
    (hp2960 : 2960 ≤ p) (h269 : 269 ∣ p - 2) : a (p - 1) = p :=
  conjecture_of_factor_dvd_x hp (le_trans (by decide : 5 ≤ 2960) hp2960)
    (by decide : 1 < 269) h269
    (two_hundred_sixty_nine_dvd_x (Nat.sub_le_sub_right hp2960 3))

lemma two_hundred_seventy_seven_dvd_x_5261 : 277 ∣ x 5261 :=
  q_dvd_x_of_prime_index (k := 19) (q := 277)
    (by norm_num) (by decide) (by decide)

lemma two_hundred_seventy_seven_dvd_x {n : ℕ} (hn : 5261 ≤ n) : 277 ∣ x n :=
  two_hundred_seventy_seven_dvd_x_5261.trans (x_dvd_of_le (by decide : 0 < 5261) hn)

theorem conjecture_of_two_hundred_seventy_seven_dvd {p : ℕ} (hp : p.Prime)
    (hp5264 : 5264 ≤ p) (h277 : 277 ∣ p - 2) : a (p - 1) = p :=
  conjecture_of_factor_dvd_x hp (le_trans (by decide : 5 ≤ 5264) hp5264)
    (by decide : 1 < 277) h277
    (two_hundred_seventy_seven_dvd_x (Nat.sub_le_sub_right hp5264 3))

lemma two_hundred_eighty_one_dvd_x_3089 : 281 ∣ x 3089 :=
  q_dvd_x_of_prime_index (k := 11) (q := 281)
    (by norm_num) (by decide) (by decide)

lemma two_hundred_eighty_one_dvd_x {n : ℕ} (hn : 3089 ≤ n) : 281 ∣ x n :=
  two_hundred_eighty_one_dvd_x_3089.trans (x_dvd_of_le (by decide : 0 < 3089) hn)

theorem conjecture_of_two_hundred_eighty_one_dvd {p : ℕ} (hp : p.Prime)
    (hp3092 : 3092 ≤ p) (h281 : 281 ∣ p - 2) : a (p - 1) = p :=
  conjecture_of_factor_dvd_x hp (le_trans (by decide : 5 ≤ 3092) hp3092)
    (by decide : 1 < 281) h281
    (two_hundred_eighty_one_dvd_x (Nat.sub_le_sub_right hp3092 3))

lemma two_hundred_ninety_three_dvd_x_3221 : 293 ∣ x 3221 :=
  q_dvd_x_of_prime_index (k := 11) (q := 293)
    (by norm_num) (by decide) (by decide)

lemma two_hundred_ninety_three_dvd_x {n : ℕ} (hn : 3221 ≤ n) : 293 ∣ x n :=
  two_hundred_ninety_three_dvd_x_3221.trans (x_dvd_of_le (by decide : 0 < 3221) hn)

theorem conjecture_of_two_hundred_ninety_three_dvd {p : ℕ} (hp : p.Prime)
    (hp3224 : 3224 ≤ p) (h293 : 293 ∣ p - 2) : a (p - 1) = p :=
  conjecture_of_factor_dvd_x hp (le_trans (by decide : 5 ≤ 3224) hp3224)
    (by decide : 1 < 293) h293
    (two_hundred_ninety_three_dvd_x (Nat.sub_le_sub_right hp3224 3))

lemma three_hundred_seven_dvd_x_3989 : 307 ∣ x 3989 :=
  q_dvd_x_of_prime_index (k := 13) (q := 307)
    (by norm_num) (by decide) (by decide)

lemma three_hundred_seven_dvd_x {n : ℕ} (hn : 3989 ≤ n) : 307 ∣ x n :=
  three_hundred_seven_dvd_x_3989.trans (x_dvd_of_le (by decide : 0 < 3989) hn)

theorem conjecture_of_three_hundred_seven_dvd {p : ℕ} (hp : p.Prime)
    (hp3992 : 3992 ≤ p) (h307 : 307 ∣ p - 2) : a (p - 1) = p :=
  conjecture_of_factor_dvd_x hp (le_trans (by decide : 5 ≤ 3992) hp3992)
    (by decide : 1 < 307) h307
    (three_hundred_seven_dvd_x (Nat.sub_le_sub_right hp3992 3))

lemma three_hundred_eleven_dvd_x_1553 : 311 ∣ x 1553 :=
  q_dvd_x_of_prime_index (k := 5) (q := 311)
    (by norm_num) (by decide) (by decide)

lemma three_hundred_eleven_dvd_x {n : ℕ} (hn : 1553 ≤ n) : 311 ∣ x n :=
  three_hundred_eleven_dvd_x_1553.trans (x_dvd_of_le (by decide : 0 < 1553) hn)

theorem conjecture_of_three_hundred_eleven_dvd {p : ℕ} (hp : p.Prime)
    (hp1556 : 1556 ≤ p) (h311 : 311 ∣ p - 2) : a (p - 1) = p :=
  conjecture_of_factor_dvd_x hp (le_trans (by decide : 5 ≤ 1556) hp1556)
    (by decide : 1 < 311) h311
    (three_hundred_eleven_dvd_x (Nat.sub_le_sub_right hp1556 3))

lemma three_hundred_seventeen_dvd_x_1583 : 317 ∣ x 1583 :=
  q_dvd_x_of_prime_index (k := 5) (q := 317)
    (by norm_num) (by decide) (by decide)

lemma three_hundred_seventeen_dvd_x {n : ℕ} (hn : 1583 ≤ n) : 317 ∣ x n :=
  three_hundred_seventeen_dvd_x_1583.trans (x_dvd_of_le (by decide : 0 < 1583) hn)

theorem conjecture_of_three_hundred_seventeen_dvd {p : ℕ} (hp : p.Prime)
    (hp1586 : 1586 ≤ p) (h317 : 317 ∣ p - 2) : a (p - 1) = p :=
  conjecture_of_factor_dvd_x hp (le_trans (by decide : 5 ≤ 1586) hp1586)
    (by decide : 1 < 317) h317
    (three_hundred_seventeen_dvd_x (Nat.sub_le_sub_right hp1586 3))

lemma three_hundred_thirty_one_dvd_x_6287 : 331 ∣ x 6287 :=
  q_dvd_x_of_prime_index (k := 19) (q := 331)
    (by norm_num) (by decide) (by decide)

lemma three_hundred_thirty_one_dvd_x {n : ℕ} (hn : 6287 ≤ n) : 331 ∣ x n :=
  three_hundred_thirty_one_dvd_x_6287.trans (x_dvd_of_le (by decide : 0 < 6287) hn)

theorem conjecture_of_three_hundred_thirty_one_dvd {p : ℕ} (hp : p.Prime)
    (hp6290 : 6290 ≤ p) (h331 : 331 ∣ p - 2) : a (p - 1) = p :=
  conjecture_of_factor_dvd_x hp (le_trans (by decide : 5 ≤ 6290) hp6290)
    (by decide : 1 < 331) h331
    (three_hundred_thirty_one_dvd_x (Nat.sub_le_sub_right hp6290 3))

lemma three_hundred_thirty_seven_dvd_x_2357 : 337 ∣ x 2357 :=
  q_dvd_x_of_prime_index (k := 7) (q := 337)
    (by norm_num) (by decide) (by decide)

lemma three_hundred_thirty_seven_dvd_x {n : ℕ} (hn : 2357 ≤ n) : 337 ∣ x n :=
  three_hundred_thirty_seven_dvd_x_2357.trans (x_dvd_of_le (by decide : 0 < 2357) hn)

theorem conjecture_of_three_hundred_thirty_seven_dvd {p : ℕ} (hp : p.Prime)
    (hp2360 : 2360 ≤ p) (h337 : 337 ∣ p - 2) : a (p - 1) = p :=
  conjecture_of_factor_dvd_x hp (le_trans (by decide : 5 ≤ 2360) hp2360)
    (by decide : 1 < 337) h337
    (three_hundred_thirty_seven_dvd_x (Nat.sub_le_sub_right hp2360 3))

lemma three_hundred_forty_seven_dvd_x_1733 : 347 ∣ x 1733 :=
  q_dvd_x_of_prime_index (k := 5) (q := 347)
    (by norm_num) (by decide) (by decide)

lemma three_hundred_forty_seven_dvd_x {n : ℕ} (hn : 1733 ≤ n) : 347 ∣ x n :=
  three_hundred_forty_seven_dvd_x_1733.trans (x_dvd_of_le (by decide : 0 < 1733) hn)

theorem conjecture_of_three_hundred_forty_seven_dvd {p : ℕ} (hp : p.Prime)
    (hp1736 : 1736 ≤ p) (h347 : 347 ∣ p - 2) : a (p - 1) = p :=
  conjecture_of_factor_dvd_x hp (le_trans (by decide : 5 ≤ 1736) hp1736)
    (by decide : 1 < 347) h347
    (three_hundred_forty_seven_dvd_x (Nat.sub_le_sub_right hp1736 3))

lemma three_hundred_fifty_three_dvd_x_3881 : 353 ∣ x 3881 :=
  q_dvd_x_of_prime_index (k := 11) (q := 353)
    (by norm_num) (by decide) (by decide)

lemma three_hundred_fifty_three_dvd_x {n : ℕ} (hn : 3881 ≤ n) : 353 ∣ x n :=
  three_hundred_fifty_three_dvd_x_3881.trans (x_dvd_of_le (by decide : 0 < 3881) hn)

theorem conjecture_of_three_hundred_fifty_three_dvd {p : ℕ} (hp : p.Prime)
    (hp3884 : 3884 ≤ p) (h353 : 353 ∣ p - 2) : a (p - 1) = p :=
  conjecture_of_factor_dvd_x hp (le_trans (by decide : 5 ≤ 3884) hp3884)
    (by decide : 1 < 353) h353
    (three_hundred_fifty_three_dvd_x (Nat.sub_le_sub_right hp3884 3))

lemma three_hundred_fifty_nine_dvd_x_3947 : 359 ∣ x 3947 :=
  q_dvd_x_of_prime_index (k := 11) (q := 359)
    (by norm_num) (by decide) (by decide)

lemma three_hundred_fifty_nine_dvd_x {n : ℕ} (hn : 3947 ≤ n) : 359 ∣ x n :=
  three_hundred_fifty_nine_dvd_x_3947.trans (x_dvd_of_le (by decide : 0 < 3947) hn)

theorem conjecture_of_three_hundred_fifty_nine_dvd {p : ℕ} (hp : p.Prime)
    (hp3950 : 3950 ≤ p) (h359 : 359 ∣ p - 2) : a (p - 1) = p :=
  conjecture_of_factor_dvd_x hp (le_trans (by decide : 5 ≤ 3950) hp3950)
    (by decide : 1 < 359) h359
    (three_hundred_fifty_nine_dvd_x (Nat.sub_le_sub_right hp3950 3))

lemma three_hundred_sixty_seven_dvd_x_6971 : 367 ∣ x 6971 :=
  q_dvd_x_of_prime_index (k := 19) (q := 367)
    (by norm_num) (by decide) (by decide)

lemma three_hundred_sixty_seven_dvd_x {n : ℕ} (hn : 6971 ≤ n) : 367 ∣ x n :=
  three_hundred_sixty_seven_dvd_x_6971.trans (x_dvd_of_le (by decide : 0 < 6971) hn)

theorem conjecture_of_three_hundred_sixty_seven_dvd {p : ℕ} (hp : p.Prime)
    (hp6974 : 6974 ≤ p) (h367 : 367 ∣ p - 2) : a (p - 1) = p :=
  conjecture_of_factor_dvd_x hp (le_trans (by decide : 5 ≤ 6974) hp6974)
    (by decide : 1 < 367) h367
    (three_hundred_sixty_seven_dvd_x (Nat.sub_le_sub_right hp6974 3))

lemma three_hundred_seventy_three_dvd_x_2609 : 373 ∣ x 2609 :=
  q_dvd_x_of_prime_index (k := 7) (q := 373)
    (by norm_num) (by decide) (by decide)

lemma three_hundred_seventy_three_dvd_x {n : ℕ} (hn : 2609 ≤ n) : 373 ∣ x n :=
  three_hundred_seventy_three_dvd_x_2609.trans (x_dvd_of_le (by decide : 0 < 2609) hn)

theorem conjecture_of_three_hundred_seventy_three_dvd {p : ℕ} (hp : p.Prime)
    (hp2612 : 2612 ≤ p) (h373 : 373 ∣ p - 2) : a (p - 1) = p :=
  conjecture_of_factor_dvd_x hp (le_trans (by decide : 5 ≤ 2612) hp2612)
    (by decide : 1 < 373) h373
    (three_hundred_seventy_three_dvd_x (Nat.sub_le_sub_right hp2612 3))

lemma three_hundred_seventy_nine_dvd_x_9473 : 379 ∣ x 9473 :=
  q_dvd_x_of_prime_index (k := 25) (q := 379)
    (by norm_num) (by decide) (by decide)

lemma three_hundred_seventy_nine_dvd_x {n : ℕ} (hn : 9473 ≤ n) : 379 ∣ x n :=
  three_hundred_seventy_nine_dvd_x_9473.trans (x_dvd_of_le (by decide : 0 < 9473) hn)

theorem conjecture_of_three_hundred_seventy_nine_dvd {p : ℕ} (hp : p.Prime)
    (hp9476 : 9476 ≤ p) (h379 : 379 ∣ p - 2) : a (p - 1) = p :=
  conjecture_of_factor_dvd_x hp (le_trans (by decide : 5 ≤ 9476) hp9476)
    (by decide : 1 < 379) h379
    (three_hundred_seventy_nine_dvd_x (Nat.sub_le_sub_right hp9476 3))

lemma three_hundred_eighty_three_dvd_x_1913 : 383 ∣ x 1913 :=
  q_dvd_x_of_prime_index (k := 5) (q := 383)
    (by norm_num) (by decide) (by decide)

lemma three_hundred_eighty_three_dvd_x {n : ℕ} (hn : 1913 ≤ n) : 383 ∣ x n :=
  three_hundred_eighty_three_dvd_x_1913.trans (x_dvd_of_le (by decide : 0 < 1913) hn)

theorem conjecture_of_three_hundred_eighty_three_dvd {p : ℕ} (hp : p.Prime)
    (hp1916 : 1916 ≤ p) (h383 : 383 ∣ p - 2) : a (p - 1) = p :=
  conjecture_of_factor_dvd_x hp (le_trans (by decide : 5 ≤ 1916) hp1916)
    (by decide : 1 < 383) h383
    (three_hundred_eighty_three_dvd_x (Nat.sub_le_sub_right hp1916 3))

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

/-- Remaining McEachen if `7·lpf(p-2)-2` is prime. For `lpf ≡ 1 (mod 3)`
this is the first non-twin injector and always fits in the square window.
If `lpf ≡ 2 (mod 3)` then `3 ∣ 7q-2`, so the hypothesis fails. -/
theorem conjecture_of_minFac_seven {p : ℕ} (hp : p.Prime) (hp7 : 7 ≤ p)
    (hmod : p % 3 = 1) (hcomp : ¬ (p - 2).Prime)
    (hpr : (7 * Nat.minFac (p - 2) - 2).Prime) : a (p - 1) = p := by
  have hq5 := remaining_minFac_ge_five hp hp7 hmod
  have hne1 : p - 2 ≠ 1 := by
    intro h
    have h2le : 2 ≤ p := le_trans (by decide : 2 ≤ 7) hp7
    have hcancel := Nat.sub_add_cancel h2le
    rw [h] at hcancel
    have hp3 : p = 3 := hcancel.symm
    exact Nat.ne_of_lt (lt_of_lt_of_le (by decide : 3 < 7) hp7) hp3.symm
  have hminp : (Nat.minFac (p - 2)).Prime := Nat.minFac_prime hne1
  have hne5 : Nat.minFac (p - 2) ≠ 5 := by
    intro h5
    have : ¬ Nat.Prime (7 * 5 - 2) := by decide
    exact this (by rwa [h5] at hpr)
  have hgt5 : 5 < Nat.minFac (p - 2) := lt_of_le_of_ne hq5 hne5.symm
  have hge6 : 6 ≤ Nat.minFac (p - 2) := Nat.succ_le_of_lt hgt5
  have hne6 : Nat.minFac (p - 2) ≠ 6 := fun h6 =>
    (by decide : ¬ Nat.Prime 6) (h6 ▸ hminp)
  have h7q : 7 ≤ Nat.minFac (p - 2) :=
    Nat.succ_le_of_lt (lt_of_le_of_ne hge6 hne6.symm)
  have hmod3 : (7 * Nat.minFac (p - 2) - 2) % 3 = 2 := by
    have hcases : Nat.minFac (p - 2) % 3 = 0 ∨
        Nat.minFac (p - 2) % 3 = 1 ∨ Nat.minFac (p - 2) % 3 = 2 := by omega
    rcases hcases with h0 | h1 | h2
    · have h3 : 3 ∣ Nat.minFac (p - 2) := Nat.dvd_of_mod_eq_zero h0
      have heq : Nat.minFac (p - 2) = 3 :=
        ((Nat.prime_dvd_prime_iff_eq Nat.prime_three hminp).1 h3).symm
      exact False.elim (Nat.ne_of_lt (lt_of_lt_of_le (by decide : 3 < 7) h7q) heq.symm)
    · exact seven_mul_sub_two_mod_three h1
        (le_trans (by decide : 2 ≤ 49) (Nat.mul_le_mul_left 7 h7q))
    · have hmul : (7 * Nat.minFac (p - 2)) % 3 = 2 := by
        rw [Nat.mul_mod]
        have : (7 : ℕ) % 3 = 1 := by decide
        rw [this, h2]
      have hrep : 7 * Nat.minFac (p - 2) =
          3 * (7 * Nat.minFac (p - 2) / 3) + 2 := by
        have := (Nat.div_add_mod (7 * Nat.minFac (p - 2)) 3).symm
        rwa [hmul] at this
      have h0 : (7 * Nat.minFac (p - 2) - 2) % 3 = 0 := by omega
      have h3d : 3 ∣ 7 * Nat.minFac (p - 2) - 2 := Nat.dvd_of_mod_eq_zero h0
      have hgt : 3 < 7 * Nat.minFac (p - 2) - 2 := by
        have : 49 ≤ 7 * Nat.minFac (p - 2) := Nat.mul_le_mul_left 7 h7q
        exact lt_of_lt_of_le (by decide : 3 < 47) (Nat.sub_le_sub_right this 2)
      have heq : 7 * Nat.minFac (p - 2) - 2 = 3 :=
        ((Nat.prime_dvd_prime_iff_eq Nat.prime_three hpr).1 h3d).symm
      exact False.elim (Nat.ne_of_lt hgt heq.symm)
  exact conjecture_of_minFac_entered hp hp7 hmod hcomp
    (q_dvd_x_square_window_of_seven hpr h7q hmod3)

/-- Remaining McEachen if a prime injector `k·lpf(p-2)-2` lies in the
square window. This packages `conjecture_of_minFac_entered`. -/
theorem conjecture_of_minFac_prime_index {p k : ℕ} (hp : p.Prime) (hp7 : 7 ≤ p)
    (hmod : p % 3 = 1) (hcomp : ¬ (p - 2).Prime)
    (hpr : (k * Nat.minFac (p - 2) - 2).Prime)
    (h7 : 7 ≤ k * Nat.minFac (p - 2) - 2)
    (hrmod : (k * Nat.minFac (p - 2) - 2) % 3 = 2)
    (hle : k * Nat.minFac (p - 2) - 2 ≤
      Nat.minFac (p - 2) * (Nat.minFac (p - 2) + 2) - 1) :
    a (p - 1) = p :=
  conjecture_of_minFac_entered hp hp7 hmod hcomp
    (q_dvd_x_square_window_of_prime_index hpr h7 hrmod hle)

/-- Remaining McEachen if some prime injector of `lpf(p-2)` has `k ≤ q+2`.
This is the square-window packaging of `conjecture_of_minFac_prime_index`.
Existence of such a `k` is not proved. -/
theorem conjecture_of_minFac_k_le {p k : ℕ} (hp : p.Prime) (hp7 : 7 ≤ p)
    (hmod : p % 3 = 1) (hcomp : ¬ (p - 2).Prime)
    (hpr : (k * Nat.minFac (p - 2) - 2).Prime)
    (h7 : 7 ≤ k * Nat.minFac (p - 2) - 2)
    (hrmod : (k * Nat.minFac (p - 2) - 2) % 3 = 2)
    (hk : k ≤ Nat.minFac (p - 2) + 2) :
    a (p - 1) = p :=
  conjecture_of_minFac_prime_index hp hp7 hmod hcomp hpr h7 hrmod
    (k_mul_sub_two_le_square hk)

/-- Any injector index `k ≤ q+8` lies in the enlarged leftover window. -/
lemma k_mul_sub_two_le_add_eight {q k : ℕ} (hk : k ≤ q + 8) :
    k * q - 2 ≤ q * (q + 8) - 1 := by
  have hle1 : k * q ≤ (q + 8) * q := Nat.mul_le_mul_right q hk
  have hle1' : k * q ≤ q * (q + 8) := by rwa [Nat.mul_comm (q + 8)] at hle1
  have h1 : k * q - 2 ≤ q * (q + 8) - 2 := Nat.sub_le_sub_right hle1' 2
  have h2 : q * (q + 8) - 2 ≤ q * (q + 8) - 1 :=
    Nat.sub_le_sub_left (by decide : 1 ≤ 2) (q * (q + 8))
  exact h1.trans h2

lemma q_dvd_x_add_eight_window_of_k_le {k q : ℕ}
    (hpr : (k * q - 2).Prime) (h7 : 7 ≤ k * q - 2)
    (hmod : (k * q - 2) % 3 = 2) (hk : k ≤ q + 8) :
    q ∣ x (q * (q + 8) - 1) := by
  have hx := q_dvd_x_of_prime_index hpr h7 hmod
  have hpos : 0 < k * q - 2 := lt_of_lt_of_le (by decide : 0 < 7) h7
  exact hx.trans (x_dvd_of_le hpos (k_mul_sub_two_le_add_eight hk))

/-- Remaining McEachen after overlap is excluded, if some prime injector
of `lpf(p-2)` has `k ≤ q+8`. Existence of such a `k` is not proved. -/
theorem conjecture_of_minFac_k_le_add_eight {p k : ℕ} (hp : p.Prime)
    (hp7 : 7 ≤ p) (hmod : p % 3 = 1) (hcomp : ¬ (p - 2).Prime)
    (hqmod : Nat.minFac (p - 2) % 3 = 2)
    (hno : ¬ (Nat.minFac (p - 2) + 2) ∣ p - 2)
    (hpr : (k * Nat.minFac (p - 2) - 2).Prime)
    (h7 : 7 ≤ k * Nat.minFac (p - 2) - 2)
    (hrmod : (k * Nat.minFac (p - 2) - 2) % 3 = 2)
    (hk : k ≤ Nat.minFac (p - 2) + 8) :
    a (p - 1) = p :=
  conjecture_of_minFac_entered_add_eight hp hp7 hmod hcomp hqmod hno
    (q_dvd_x_add_eight_window_of_k_le hpr h7 hrmod hk)

/-- Remaining McEachen for `lpf ≡ 2 (mod 3)` if either overlap holds or
some prime injector has `k ≤ q+8`. Existence of such a `k` is not proved. -/
theorem conjecture_of_minFac_mod_two_overlap_or_k_le_add_eight {p k : ℕ}
    (hp : p.Prime) (hp7 : 7 ≤ p) (hmod : p % 3 = 1)
    (hcomp : ¬ (p - 2).Prime)
    (hqmod : Nat.minFac (p - 2) % 3 = 2)
    (h7q : 7 ≤ Nat.minFac (p - 2))
    (hpr : (k * Nat.minFac (p - 2) - 2).Prime)
    (h7r : 7 ≤ k * Nat.minFac (p - 2) - 2)
    (hrmod : (k * Nat.minFac (p - 2) - 2) % 3 = 2)
    (hk : k ≤ Nat.minFac (p - 2) + 8) :
    a (p - 1) = p := by
  have hminp : (Nat.minFac (p - 2)).Prime := by
    refine Nat.minFac_prime ?_
    intro h
    have h2 : 2 ≤ p := le_trans (by decide : 2 ≤ 7) hp7
    have hp3 : p = 3 := by
      have hcancel := Nat.sub_add_cancel h2
      rw [h] at hcancel
      exact hcancel.symm
    exact Nat.ne_of_lt (lt_of_lt_of_le (by decide : 3 < 7) hp7) hp3.symm
  by_cases hov : (Nat.minFac (p - 2) + 2) ∣ p - 2
  · have hg : Nat.gcd (Nat.minFac (p - 2) + 2) (p - 2) =
        Nat.minFac (p - 2) + 2 :=
      Nat.dvd_antisymm (Nat.gcd_dvd_left _ _) (Nat.dvd_gcd dvd_rfl hov)
    have hgt : 1 < Nat.gcd (Nat.minFac (p - 2) + 2) (p - 2) := by
      rw [hg]
      exact Nat.lt_of_lt_of_le (by decide : 1 < 9)
        (Nat.add_le_add_right h7q 2)
    exact conjecture_of_remaining_add_two_overlap hp hp7 hmod hcomp hminp
      (Nat.minFac_dvd _) hqmod h7q hgt
  · exact conjecture_of_minFac_k_le_add_eight hp hp7 hmod hcomp hqmod hov
      hpr h7r hrmod hk

/-- If `q ∣ p-2` and `k ≤ (p-2)/q`, then the injector index `kq-2` is at
most `p-3`. This is the actual McEachen window for that factor. -/
lemma k_mul_sub_two_le_of_cofactor {p q k : ℕ}
    (hd : q ∣ p - 2) (_hq : 0 < q) (_hp2 : 2 ≤ p) (hk : k ≤ (p - 2) / q)
    (_h2 : 2 ≤ k * q) : k * q - 2 ≤ p - 3 := by
  have hmul : k * q ≤ ((p - 2) / q) * q := Nat.mul_le_mul_right q hk
  have hcancel : ((p - 2) / q) * q = p - 2 := by
    rw [Nat.mul_comm]
    exact Nat.mul_div_cancel' hd
  have hle : k * q ≤ p - 2 := by rwa [hcancel] at hmul
  have h1 : k * q - 2 ≤ p - 2 - 2 := Nat.sub_le_sub_right hle 2
  have hsub : p - 2 - 2 = p - 4 := Nat.sub_sub p 2 2
  have h34 : p - 4 ≤ p - 3 := Nat.sub_le_sub_left (by decide : 3 ≤ 4) p
  exact (hsub ▸ h1).trans h34

/-- McEachen at `p` if some prime factor `q` of `p-2` has a prime injector
with `k ≤ (p-2)/q`. Existence of such a pair is not proved. -/
theorem conjecture_of_factor_k_le_cofactor {p q k : ℕ}
    (hp : p.Prime) (hp5 : 5 ≤ p) (hq1 : 1 < q) (hqp : q ∣ p - 2)
    (hpr : (k * q - 2).Prime) (h7 : 7 ≤ k * q - 2)
    (hmod : (k * q - 2) % 3 = 2) (hk : k ≤ (p - 2) / q) :
    a (p - 1) = p := by
  have hqpos : 0 < q := Nat.zero_lt_of_lt hq1
  have hp2 : 2 ≤ p := le_trans (by decide : 2 ≤ 5) hp5
  have h2 : 2 ≤ k * q :=
    (le_trans (by decide : 2 ≤ 7) h7).trans (Nat.sub_le (k * q) 2)
  have hle := k_mul_sub_two_le_of_cofactor hqp hqpos hp2 hk h2
  exact conjecture_of_prime_index hp hp5 hpr h7 hmod hle hqp hq1

/-- McEachen at `p` if some prime factor of `p-2` has an in-window injector.
This is the remaining sufficient arithmetic condition. Existence is not
proved. -/
theorem conjecture_of_exists_factor_injector {p : ℕ} (hp : p.Prime)
    (hp5 : 5 ≤ p)
    (hex : ∃ q k, 1 < q ∧ q ∣ p - 2 ∧ (k * q - 2).Prime ∧
      7 ≤ k * q - 2 ∧ (k * q - 2) % 3 = 2 ∧ k ≤ (p - 2) / q) :
    a (p - 1) = p := by
  rcases hex with ⟨q, k, hq1, hqp, hpr, h7, hmod, hk⟩
  exact conjecture_of_factor_k_le_cofactor hp hp5 hq1 hqp hpr h7 hmod hk

lemma one_ne_two : ¬ (1 : ℕ) = 2 := (Nat.succ_ne_self 1).symm

lemma zero_ne_two : ¬ (0 : ℕ) = 2 := Nat.zero_ne_add_one 1

lemma one_lt_three : (1 : ℕ) < 3 :=
  Nat.lt_trans Nat.one_lt_two (Nat.lt_succ_self 2)

lemma five_le_of_seven_le {p : ℕ} (h : 7 ≤ p) : 5 ≤ p :=
  le_trans (by decide : 5 ≤ 7) h

lemma four_le_seven : (4 : ℕ) ≤ 7 :=
  Nat.le_trans (Nat.le_succ 4) (Nat.le_trans (Nat.le_succ 5) (Nat.le_succ 6))

lemma two_mod_three : (2 : ℕ) % 3 = 2 := rfl

lemma five_mod_three : (5 : ℕ) % 3 = 2 := rfl

lemma not_prime_four : ¬ Nat.Prime 4 := fun h =>
  Nat.not_prime_mul (Nat.succ_ne_self 1) (Nat.succ_ne_self 1) h

lemma not_prime_six : ¬ Nat.Prime 6 := fun h =>
  Nat.not_prime_mul (Nat.succ_ne_self 1) (Ne.symm (ne_of_lt one_lt_three)) h

/-- Any odd prime `p ≥ 7` has odd `p-2`. -/
lemma remaining_p_sub_two_odd {p : ℕ} (hp : p.Prime) (hp7 : 7 ≤ p) :
    (p - 2) % 2 = 1 := by
  have hpodd : p % 2 = 1 := by
    have hcases : p % 2 = 0 ∨ p % 2 = 1 := Nat.mod_two_eq_zero_or_one p
    rcases hcases with h0 | h1
    · have : 2 ∣ p := Nat.dvd_of_mod_eq_zero h0
      have heq : p = 2 :=
        ((Nat.prime_dvd_prime_iff_eq Nat.prime_two hp).1 this).symm
      exact False.elim
        (Nat.ne_of_lt (lt_of_lt_of_le (by decide : 2 < 7) hp7) heq.symm)
    · exact h1
  have h2le : 2 ≤ p := le_trans (by decide : 2 ≤ 7) hp7
  have hsub : p - 2 + 2 = p := Nat.sub_add_cancel h2le
  have hsum := congrArg (fun n => n % 2) hsub
  have h2m : (2 : ℕ) % 2 = 0 := rfl
  rw [Nat.add_mod, h2m, Nat.add_zero, Nat.mod_mod, hpodd] at hsum
  exact hsum

lemma remaining_p_sub_two_gt_one {p : ℕ} (hp7 : 7 ≤ p) : 1 < p - 2 := by
  have h5 : 5 ≤ p := five_le_of_seven_le hp7
  have h3 : 3 ≤ p - 2 := Nat.sub_le_sub_right h5 2
  exact lt_of_lt_of_le one_lt_three h3

/-- For composite `p-2` and a prime factor `r`, the complementary cofactor
is at least the least prime factor. -/
lemma remaining_div_ge_minFac {p r : ℕ} (hp7 : 7 ≤ p)
    (hcomp : ¬ (p - 2).Prime) (hr : r.Prime) (hd : r ∣ p - 2) :
    Nat.minFac (p - 2) ≤ (p - 2) / r := by
  have hn : 1 < p - 2 := remaining_p_sub_two_gt_one hp7
  set m := (p - 2) / r
  have hmul : r * m = p - 2 := Nat.mul_div_cancel' hd
  have hne : r ≠ p - 2 := fun h => hcomp (h ▸ hr)
  have hquot_ne1 : m ≠ 1 := by
    intro h1
    apply hne
    calc
      r = r * 1 := (Nat.mul_one r).symm
      _ = r * m := by rw [h1]
      _ = p - 2 := hmul
  have hquot_ne0 : m ≠ 0 := by
    intro h0
    have hz : p - 2 = 0 := by
      rw [← hmul, h0, Nat.mul_zero]
    exact (Nat.not_lt_zero 1) (hz ▸ hn)
  have hge1 : 1 ≤ m := Nat.pos_iff_ne_zero.mpr hquot_ne0
  have hmge2 : 2 ≤ m :=
    Nat.succ_le_of_lt (lt_of_le_of_ne hge1 hquot_ne1.symm)
  have hdivm : m ∣ r * m := Nat.dvd_mul_left m r
  have hdiv : m ∣ p - 2 := hmul ▸ hdivm
  exact Nat.minFac_le_of_dvd hmge2 hdiv

/-- A prime factor `≡ 1 (mod 3)` of remaining `p-2` cannot be `2`, `3`,
or `5`, hence is at least `7`. -/
lemma remaining_mod_one_factor_ge_seven {p r : ℕ} (hp7 : 7 ≤ p)
    (hmod : p % 3 = 1) (hr : r.Prime) (hr1 : r % 3 = 1)
    (hd : r ∣ p - 2) : 7 ≤ r := by
  have hr2 : r ≠ 2 := fun h => one_ne_two ((h ▸ hr1).symm)
  have hr3 : r ≠ 3 := by
    intro h
    have : 3 ∣ p - 2 := by rwa [h] at hd
    have hz : (p - 2) % 3 = 0 := Nat.mod_eq_zero_of_dvd this
    have h2 : (p - 2) % 3 = 2 :=
      p_sub_two_mod (le_trans four_le_seven hp7) hmod
    exact zero_ne_two (hz.symm.trans h2)
  have hr5 : r ≠ 5 := fun h => one_ne_two ((h ▸ hr1).symm)
  have h2 : 2 ≤ r := hr.two_le
  have hge3 : 3 ≤ r := Nat.succ_le_of_lt (lt_of_le_of_ne h2 hr2.symm)
  have hge4 : 4 ≤ r := Nat.succ_le_of_lt (lt_of_le_of_ne hge3 hr3.symm)
  have hne4 : r ≠ 4 := fun h4 => not_prime_four (h4 ▸ hr)
  have hge5 : 5 ≤ r := Nat.succ_le_of_lt (lt_of_le_of_ne hge4 hne4.symm)
  have hge6 : 6 ≤ r := Nat.succ_le_of_lt (lt_of_le_of_ne hge5 hr5.symm)
  have hne6 : r ≠ 6 := fun h6 => not_prime_six (h6 ▸ hr)
  exact Nat.succ_le_of_lt (lt_of_le_of_ne hge6 hne6.symm)

/-- If `5` does not divide remaining `p-2`, then `lpf(p-2) ≥ 7`. -/
lemma remaining_minFac_ge_seven_of_not_five {p : ℕ} (hp : p.Prime)
    (hp7 : 7 ≤ p) (hmod : p % 3 = 1) (h5 : ¬ 5 ∣ p - 2) :
    7 ≤ Nat.minFac (p - 2) := by
  have hq5 := remaining_minFac_ge_five hp hp7 hmod
  have hn : 1 < p - 2 := remaining_p_sub_two_gt_one hp7
  have hminp : (Nat.minFac (p - 2)).Prime := Nat.minFac_prime (ne_of_gt hn)
  have hne5 : Nat.minFac (p - 2) ≠ 5 := by
    intro h
    exact h5 (h ▸ Nat.minFac_dvd (p - 2))
  have hge6 : 6 ≤ Nat.minFac (p - 2) :=
    Nat.succ_le_of_lt (lt_of_le_of_ne hq5 hne5.symm)
  have hne6 : Nat.minFac (p - 2) ≠ 6 := fun h6 => not_prime_six (h6 ▸ hminp)
  exact Nat.succ_le_of_lt (lt_of_le_of_ne hge6 hne6.symm)

lemma seven_le_div_of_minFac_seven {p r : ℕ} (hp7 : 7 ≤ p)
    (hcomp : ¬ (p - 2).Prime) (hr : r.Prime) (hd : r ∣ p - 2)
    (h7q : 7 ≤ Nat.minFac (p - 2)) : 7 ≤ (p - 2) / r :=
  le_trans h7q (remaining_div_ge_minFac hp7 hcomp hr hd)

lemma seven_mul_sub_two_ge_seven {r : ℕ} (h7 : 7 ≤ r) : 7 ≤ 7 * r - 2 := by
  have : 49 ≤ 7 * r := Nat.mul_le_mul_left 7 h7
  exact le_trans (by decide : 7 ≤ 47) (Nat.sub_le_sub_right this 2)

lemma two_le_seven_mul_of_ge_seven {r : ℕ} (h7 : 7 ≤ r) : 2 ≤ 7 * r :=
  le_trans (by decide : 2 ≤ 49) (Nat.mul_le_mul_left 7 h7)

lemma one_lt_five : (1 : ℕ) < 5 :=
  Nat.lt_trans one_lt_three (Nat.lt_trans (Nat.lt_succ_self 3) (Nat.lt_succ_self 4))

lemma one_lt_seven : (1 : ℕ) < 7 :=
  Nat.lt_trans one_lt_five (Nat.lt_trans (Nat.lt_succ_self 5) (Nat.lt_succ_self 6))

lemma mod_three_cases (n : ℕ) : n % 3 = 0 ∨ n % 3 = 1 ∨ n % 3 = 2 := by
  have hlt : n % 3 < 3 := Nat.mod_lt n (Nat.succ_pos 2)
  interval_cases n % 3
  · exact Or.inl rfl
  · exact Or.inr (Or.inl rfl)
  · exact Or.inr (Or.inr rfl)

lemma two_mul_two_mod_three : ((2 : ℕ) * 2) % 3 = 1 := rfl

lemma one_mul_one_mod_three : ((1 : ℕ) * 1) % 3 = 1 := rfl

/-- If an odd composite `n ≡ 2 (mod 3)` has least prime factor `q ≡ 2
(mod 3)` and `n < q^3`, then some prime factor of `n` is `≡ 1 (mod 3)`.
Three factors each at least `q` would be at least `q^3`, and a product of
two primes `≡ 2 (mod 3)` is `≡ 1 (mod 3)`. -/
lemma exists_prime_factor_mod_one_of_lt_cube {n : ℕ}
    (hn : 1 < n) (hnp : ¬ n.Prime) (hmod : n % 3 = 2) (hodd : n % 2 = 1)
    (hqmod : Nat.minFac n % 3 = 2)
    (hcube : n < Nat.minFac n * Nat.minFac n * Nat.minFac n) :
    ∃ r, r.Prime ∧ r ∣ n ∧ r % 3 = 1 := by
  have hminp : (Nat.minFac n).Prime := Nat.minFac_prime (ne_of_gt hn)
  have hd : Nat.minFac n ∣ n := Nat.minFac_dvd n
  have hq2 : Nat.minFac n ≠ 2 := by
    intro h
    have : 2 ∣ n := by rwa [h] at hd
    have hz : n % 2 = 0 := Nat.mod_eq_zero_of_dvd this
    exact Nat.zero_ne_one (hz.symm.trans hodd)
  have hq3 : Nat.minFac n ≠ 3 := by
    intro h
    have : 3 ∣ n := by rwa [h] at hd
    have hz : n % 3 = 0 := Nat.mod_eq_zero_of_dvd this
    exact zero_ne_two (hz.symm.trans hmod)
  set q := Nat.minFac n
  have hq5 : 5 ≤ q := by
    have h2 : 2 ≤ q := hminp.two_le
    have hgt2 : 2 < q := lt_of_le_of_ne h2 hq2.symm
    have hge3 : 3 ≤ q := hgt2
    have hgt3 : 3 < q := lt_of_le_of_ne hge3 hq3.symm
    have hge4 : 4 ≤ q := hgt3
    have hne4 : q ≠ 4 := fun h4 => not_prime_four (h4 ▸ hminp)
    exact Nat.succ_le_of_lt (lt_of_le_of_ne hge4 hne4.symm)
  by_cases hsq : q * q ∣ n
  · have hmul : q * q * (n / (q * q)) = n := Nat.mul_div_cancel' hsq
    have hm0 : n / (q * q) ≠ 0 := by
      intro h0
      have hz : n = 0 := by
        rw [← hmul, h0, Nat.mul_zero]
      exact (Nat.not_lt_zero 1) (hz ▸ hn)
    have hge1 : 1 ≤ n / (q * q) := Nat.pos_iff_ne_zero.mpr hm0
    rcases eq_or_lt_of_le hge1 with hm1 | hmgt
    · have hnqq : n = q * q := by
        have h := hmul
        rw [← hm1, Nat.mul_one] at h
        exact h.symm
      have hsqmod := sq_mod_three_of_ne_three hminp hq3
      have : n % 3 = 1 := by rwa [hnqq]
      exact False.elim (one_ne_two (this.symm.trans hmod))
    · set k := n / (q * q)
      have hmulk : q * q * k = n := hmul
      have hrmin : (Nat.minFac k).Prime := Nat.minFac_prime (ne_of_gt hmgt)
      have hrdk : Nat.minFac k ∣ q * q * k :=
        dvd_mul_of_dvd_right (Nat.minFac_dvd k) _
      have hrd : Nat.minFac k ∣ n := hmulk ▸ hrdk
      have hqle : q ≤ Nat.minFac k :=
        Nat.minFac_le_of_dvd hrmin.two_le hrd
      have hmge : q ≤ k :=
        le_trans hqle (Nat.minFac_le (Nat.zero_lt_of_lt hmgt))
      have hn3 : q * q * q ≤ n :=
        (Nat.mul_le_mul_left (q * q) hmge).trans_eq hmulk
      exact False.elim (not_le_of_gt hcube hn3)
  · set m := n / q
    have hmul : q * m = n := Nat.mul_div_cancel' hd
    have _hq_not : ¬ q ∣ m := by
      intro hqm
      have : q * q ∣ q * m := Nat.mul_dvd_mul_left q hqm
      exact hsq (hmul ▸ this)
    have hm1 : 1 < m := by
      have hge : q ≤ m :=
        Nat.minFac_le_div (Nat.zero_lt_of_lt hn) hnp
      exact lt_of_lt_of_le (lt_of_lt_of_le one_lt_five hq5) hge
    have hrmin : (Nat.minFac m).Prime := Nat.minFac_prime (ne_of_gt hm1)
    have hrdm : Nat.minFac m ∣ q * m :=
      dvd_mul_of_dvd_right (Nat.minFac_dvd m) q
    have hrd : Nat.minFac m ∣ n := hmul ▸ hrdm
    have hr3 : Nat.minFac m ≠ 3 := by
      intro h
      have : 3 ∣ n := by rwa [h] at hrd
      have hz : n % 3 = 0 := Nat.mod_eq_zero_of_dvd this
      exact zero_ne_two (hz.symm.trans hmod)
    have hrcases : Nat.minFac m % 3 = 1 ∨ Nat.minFac m % 3 = 2 := by
      rcases mod_three_cases (Nat.minFac m) with h0 | h1 | h2
      · have : 3 ∣ Nat.minFac m := Nat.dvd_of_mod_eq_zero h0
        have heq : Nat.minFac m = 3 :=
          ((Nat.prime_dvd_prime_iff_eq Nat.prime_three hrmin).1 this).symm
        exact (hr3 heq).elim
      · exact Or.inl h1
      · exact Or.inr h2
    rcases hrcases with h1 | hr2
    · exact ⟨Nat.minFac m, hrmin, hrd, h1⟩
    · by_cases hpr : m.Prime
      · have hrq : Nat.minFac m = m := hpr.minFac_eq
        have hprod : (q * Nat.minFac m) % 3 = 1 := by
          rw [Nat.mul_mod, hqmod, hr2]
        have : n % 3 = 1 := by
          have h := hprod
          rw [hrq, hmul] at h
          exact h
        exact False.elim (one_ne_two (this.symm.trans hmod))
      · set r := Nat.minFac m
        have hge : r ≤ m / r :=
          Nat.minFac_le_div (Nat.zero_lt_of_lt hm1) hpr
        have hmulr : r * (m / r) = m := Nat.mul_div_cancel' (Nat.minFac_dvd m)
        have hnq : r * r ≤ m :=
          (Nat.mul_le_mul_left r hge).trans_eq hmulr
        have hqle_r : q ≤ r := Nat.minFac_le_of_dvd hrmin.two_le hrd
        have hrr : q * q ≤ r * r := Nat.mul_le_mul hqle_r hqle_r
        have hassoc : q * q * q = q * (q * q) := Nat.mul_assoc _ _ _
        have hn3 : q * q * q ≤ n := by
          have h1 : q * (q * q) ≤ q * (r * r) := Nat.mul_le_mul_left q hrr
          have h2 : q * (r * r) ≤ q * m := Nat.mul_le_mul_left q hnq
          exact hassoc ▸ (h1.trans (h2.trans_eq hmul))
        exact False.elim (not_le_of_gt hcube hn3)

/-- Remaining `p-2 < lpf(p-2)^3` with least factor `≡ 2 (mod 3)` has a
prime factor `≡ 1 (mod 3)`. -/
lemma remaining_exists_mod_one_of_lt_cube {p : ℕ} (hp : p.Prime)
    (hp7 : 7 ≤ p) (hmod : p % 3 = 1) (hcomp : ¬ (p - 2).Prime)
    (hqmod : Nat.minFac (p - 2) % 3 = 2)
    (hcube : p - 2 <
      Nat.minFac (p - 2) * Nat.minFac (p - 2) * Nat.minFac (p - 2)) :
    ∃ r, r.Prime ∧ r ∣ p - 2 ∧ r % 3 = 1 :=
  exists_prime_factor_mod_one_of_lt_cube (remaining_p_sub_two_gt_one hp7) hcomp
    (p_sub_two_mod (le_trans four_le_seven hp7) hmod)
    (remaining_p_sub_two_odd hp hp7) hqmod hcube

/-- If every prime factor of an odd composite `n ≡ 2 (mod 3)` is
`≡ 2 (mod 3)`, then `lpf(n)^3 ≤ n`. -/
lemma cube_le_of_all_prime_factors_mod_two {n : ℕ}
    (hn : 1 < n) (hnp : ¬ n.Prime) (hmod : n % 3 = 2) (hodd : n % 2 = 1)
    (hall : ∀ r, r.Prime → r ∣ n → r % 3 = 2) :
    Nat.minFac n * Nat.minFac n * Nat.minFac n ≤ n := by
  have hqmod : Nat.minFac n % 3 = 2 :=
    hall (Nat.minFac n) (Nat.minFac_prime (ne_of_gt hn)) (Nat.minFac_dvd n)
  by_contra hlt
  obtain ⟨r, hr, hd, hr1⟩ :=
    exists_prime_factor_mod_one_of_lt_cube hn hnp hmod hodd hqmod
      (lt_of_not_ge hlt)
  exact one_ne_two (hr1.symm.trans (hall r hr hd))

/-- Remaining McEachen if some prime factor `r ≡ 1 (mod 3)` of `p-2`
has prime injector `7r-2`. The index `k = 7` lies in the McEachen window
once `5 ∤ p-2`; the `5 ∣ p-2` case is already `conjecture_of_five_dvd`.
Primality of `7r-2` is not proved. -/
theorem conjecture_of_remaining_mod_one_seven {p r : ℕ} (hp : p.Prime)
    (hp7 : 7 ≤ p) (hmod : p % 3 = 1) (hcomp : ¬ (p - 2).Prime)
    (hr : r.Prime) (hr1 : r % 3 = 1) (hd : r ∣ p - 2)
    (hpr : (7 * r - 2).Prime) : a (p - 1) = p := by
  by_cases h5 : 5 ∣ p - 2
  · exact conjecture_of_five_dvd hp hp7 h5
  · exact conjecture_of_factor_k_le_cofactor hp (five_le_of_seven_le hp7)
      (lt_of_lt_of_le one_lt_seven
        (remaining_mod_one_factor_ge_seven hp7 hmod hr hr1 hd)) hd hpr
      (seven_mul_sub_two_ge_seven
        (remaining_mod_one_factor_ge_seven hp7 hmod hr hr1 hd))
      (seven_mul_sub_two_mod_three hr1
        (two_le_seven_mul_of_ge_seven
          (remaining_mod_one_factor_ge_seven hp7 hmod hr hr1 hd)))
      (seven_le_div_of_minFac_seven hp7 hcomp hr hd
        (remaining_minFac_ge_seven_of_not_five hp hp7 hmod h5))

/-- Remaining McEachen if some factor `≡ 1 (mod 3)` has a prime `7r-2`
injector. Existence of that prime is not proved. -/
theorem conjecture_of_exists_mod_one_seven {p : ℕ} (hp : p.Prime)
    (hp7 : 7 ≤ p) (hmod : p % 3 = 1) (hcomp : ¬ (p - 2).Prime)
    (hex : ∃ r, r.Prime ∧ r ∣ p - 2 ∧ r % 3 = 1 ∧ (7 * r - 2).Prime) :
    a (p - 1) = p := by
  rcases hex with ⟨r, hr, hd, hr1, hpr⟩
  exact conjecture_of_remaining_mod_one_seven hp hp7 hmod hcomp hr hr1 hd hpr

/-- Remaining McEachen below the cube `lpf(p-2)^3` if some complementary
factor `≡ 1 (mod 3)` has prime injector `7r-2`. The cube forces such a
complementary residue class; primality of `7r-2` is not proved. -/
theorem conjecture_of_remaining_lt_cube_mod_one_seven {p r : ℕ}
    (hp : p.Prime) (hp7 : 7 ≤ p) (hmod : p % 3 = 1)
    (hcomp : ¬ (p - 2).Prime)
    (_hqmod : Nat.minFac (p - 2) % 3 = 2)
    (_hcube : p - 2 <
      Nat.minFac (p - 2) * Nat.minFac (p - 2) * Nat.minFac (p - 2))
    (hr : r.Prime) (hr1 : r % 3 = 1) (hd : r ∣ p - 2)
    (hpr : (7 * r - 2).Prime) : a (p - 1) = p :=
  conjecture_of_remaining_mod_one_seven hp hp7 hmod hcomp hr hr1 hd hpr

lemma k_mod_three_of_six_one {k : ℕ} (hk : k % 6 = 1) : k % 3 = 1 := by
  have hrep : 6 * (k / 6) + 1 = k := by
    have := Nat.div_add_mod k 6
    rwa [hk] at this
  have : k % 3 = (6 * (k / 6) + 1) % 3 := by rw [hrep]
  have h0 : (6 * (k / 6)) % 3 = 0 := by
    have : (6 : ℕ) % 3 = 0 := by decide
    rw [Nat.mul_mod, this, Nat.zero_mul, Nat.zero_mod]
  have h1 : (1 : ℕ) % 3 = 1 := rfl
  rw [this, Nat.add_mod, h0, Nat.zero_add, Nat.mod_mod, h1]

lemma k_ge_seven_of_mod_six_one {k : ℕ} (hk : k % 6 = 1) (hne : 1 < k) :
    7 ≤ k := by
  have hrep : 6 * (k / 6) + 1 = k := by
    have := Nat.div_add_mod k 6
    rwa [hk] at this
  have hdiv : 1 ≤ k / 6 := by
    have hpos : k / 6 ≠ 0 := by
      intro h0
      have hk1 : k = 1 := by
        rw [← hrep, h0, Nat.mul_zero, Nat.zero_add]
      exact Nat.ne_of_lt hne hk1.symm
    exact Nat.pos_iff_ne_zero.mpr hpos
  have : 6 * 1 + 1 ≤ 6 * (k / 6) + 1 :=
    Nat.add_le_add_right (Nat.mul_le_mul_left 6 hdiv) 1
  rwa [hrep] at this

lemma k_mul_sub_two_mod_of_six_one {k r : ℕ} (hk : k % 6 = 1)
    (hr : r % 3 = 1) (_h2 : 2 ≤ k * r) : (k * r - 2) % 3 = 2 := by
  have hk3 := k_mod_three_of_six_one hk
  have hmul : (k * r) % 3 = 1 := by
    rw [Nat.mul_mod, hk3, hr]
  have hrep : k * r = 3 * (k * r / 3) + 1 := by
    have := (Nat.div_add_mod (k * r) 3).symm
    rwa [hmul] at this
  omega

lemma k_mul_sub_two_ge_seven {k r : ℕ} (hk : 7 ≤ k) (hr : 7 ≤ r) :
    7 ≤ k * r - 2 := by
  have : 49 ≤ k * r := Nat.mul_le_mul hk hr
  exact le_trans (by decide : 7 ≤ 47) (Nat.sub_le_sub_right this 2)

lemma two_le_k_mul_of_ge_seven {k r : ℕ} (hk : 7 ≤ k) (hr : 7 ≤ r) :
    2 ≤ k * r :=
  le_trans (by decide : 2 ≤ 49) (Nat.mul_le_mul hk hr)

/-- Remaining McEachen if some prime factor `r ≡ 1 (mod 3)` of `p-2`
has a prime injector `kr-2` with `k ≡ 1 (mod 6)` and `k ≥ 7` inside
the McEachen window `k ≤ (p-2)/r`. Primality of `kr-2` is not proved. -/
theorem conjecture_of_remaining_mod_one_k {p r k : ℕ} (hp : p.Prime)
    (hp7 : 7 ≤ p) (hmod : p % 3 = 1) (_hcomp : ¬ (p - 2).Prime)
    (hr : r.Prime) (hr1 : r % 3 = 1) (hd : r ∣ p - 2)
    (hk6 : k % 6 = 1) (hk7 : 7 ≤ k) (hk : k ≤ (p - 2) / r)
    (hpr : (k * r - 2).Prime) : a (p - 1) = p := by
  by_cases h5 : 5 ∣ p - 2
  · exact conjecture_of_five_dvd hp hp7 h5
  · have hr7 := remaining_mod_one_factor_ge_seven hp7 hmod hr hr1 hd
    exact conjecture_of_factor_k_le_cofactor hp (five_le_of_seven_le hp7)
      (lt_of_lt_of_le one_lt_seven hr7) hd hpr
      (k_mul_sub_two_ge_seven hk7 hr7)
      (k_mul_sub_two_mod_of_six_one hk6 hr1 (two_le_k_mul_of_ge_seven hk7 hr7))
      hk

/-- Remaining McEachen if some factor `≡ 1 (mod 3)` has an in-window
injector `k ≡ 1 (mod 6)`, `k ≥ 7`. Existence of that prime is not
proved. -/
theorem conjecture_of_exists_mod_one_k {p : ℕ} (hp : p.Prime)
    (hp7 : 7 ≤ p) (hmod : p % 3 = 1) (hcomp : ¬ (p - 2).Prime)
    (hex : ∃ r k, r.Prime ∧ r ∣ p - 2 ∧ r % 3 = 1 ∧ k % 6 = 1 ∧
      7 ≤ k ∧ k ≤ (p - 2) / r ∧ (k * r - 2).Prime) :
    a (p - 1) = p := by
  rcases hex with ⟨r, k, hr, hd, hr1, hk6, hk7, hk, hpr⟩
  exact conjecture_of_remaining_mod_one_k hp hp7 hmod hcomp hr hr1 hd
    hk6 hk7 hk hpr

/-- Type B: if every prime factor of remaining `p-2` is `≡ 2 (mod 3)`,
then the complementary cofactor of the least factor is at least
`lpf(p-2)^2`. -/
lemma remaining_type_B_div_ge_sq {p : ℕ} (hp : p.Prime) (hp7 : 7 ≤ p)
    (hmod : p % 3 = 1) (hcomp : ¬ (p - 2).Prime)
    (hall : ∀ r, r.Prime → r ∣ p - 2 → r % 3 = 2) :
    Nat.minFac (p - 2) * Nat.minFac (p - 2) ≤
      (p - 2) / Nat.minFac (p - 2) := by
  have hn : 1 < p - 2 := remaining_p_sub_two_gt_one hp7
  have hcube := cube_le_of_all_prime_factors_mod_two hn hcomp
    (p_sub_two_mod (le_trans four_le_seven hp7) hmod)
    (remaining_p_sub_two_odd hp hp7) hall
  set q := Nat.minFac (p - 2)
  have hd : q ∣ p - 2 := Nat.minFac_dvd _
  have hmul : q * ((p - 2) / q) = p - 2 := Nat.mul_div_cancel' hd
  have hqpos : 0 < q := (Nat.minFac_prime (ne_of_gt hn)).pos
  have hassoc : q * q * q = q * (q * q) := Nat.mul_assoc q q q
  have hle : q * (q * q) ≤ q * ((p - 2) / q) :=
    (hassoc ▸ hcube).trans_eq hmul.symm
  exact Nat.le_of_mul_le_mul_left hle hqpos

/-- Remaining Type B McEachen if some prime injector of `lpf(p-2)` has
`k ≤ lpf(p-2)^2`. That window is implied by the cube lower bound.
Existence of such a `k` is not proved. -/
theorem conjecture_of_remaining_type_B_k_le {p k : ℕ} (hp : p.Prime)
    (hp7 : 7 ≤ p) (hmod : p % 3 = 1) (hcomp : ¬ (p - 2).Prime)
    (hall : ∀ r, r.Prime → r ∣ p - 2 → r % 3 = 2)
    (hpr : (k * Nat.minFac (p - 2) - 2).Prime)
    (h7 : 7 ≤ k * Nat.minFac (p - 2) - 2)
    (hrmod : (k * Nat.minFac (p - 2) - 2) % 3 = 2)
    (hk : k ≤ Nat.minFac (p - 2) * Nat.minFac (p - 2)) :
    a (p - 1) = p := by
  have hq1 : 1 < Nat.minFac (p - 2) :=
    lt_of_lt_of_le one_lt_five (remaining_minFac_ge_five hp hp7 hmod)
  have hk' : k ≤ (p - 2) / Nat.minFac (p - 2) :=
    hk.trans (remaining_type_B_div_ge_sq hp hp7 hmod hcomp hall)
  exact conjecture_of_factor_k_le_cofactor hp (five_le_of_seven_le hp7)
    hq1 (Nat.minFac_dvd _) hpr h7 hrmod hk'

/-- Type B remaining primes satisfy `lpf(p-2)^3 + 2 ≤ p`. After the
`lpf ≤ 257` family, any Type B leftover therefore has
`p ≥ 263^3 + 2`. -/
lemma remaining_type_B_p_ge {p : ℕ} (hp : p.Prime) (hp7 : 7 ≤ p)
    (hmod : p % 3 = 1) (hcomp : ¬ (p - 2).Prime)
    (hall : ∀ r, r.Prime → r ∣ p - 2 → r % 3 = 2) :
    Nat.minFac (p - 2) * Nat.minFac (p - 2) * Nat.minFac (p - 2) + 2 ≤ p := by
  have hn : 1 < p - 2 := remaining_p_sub_two_gt_one hp7
  have hcube := cube_le_of_all_prime_factors_mod_two hn hcomp
    (p_sub_two_mod (le_trans four_le_seven hp7) hmod)
    (remaining_p_sub_two_odd hp hp7) hall
  have h2le : 2 ≤ p := le_trans (by decide : 2 ≤ 7) hp7
  have : Nat.minFac (p - 2) * Nat.minFac (p - 2) * Nat.minFac (p - 2) + 2 ≤
      p - 2 + 2 := Nat.add_le_add_right hcube 2
  rwa [Nat.sub_add_cancel h2le] at this

/-- Remaining Type A: if `p-2 < lpf(p-2)^3`, then the complementary
cofactor `(p-2)/lpf` is prime. Three prime factors each at least
`lpf` would be at least `lpf^3`. -/
lemma remaining_type_A_cofactor_prime {p : ℕ} (hp : p.Prime) (hp7 : 7 ≤ p)
    (hmod : p % 3 = 1) (hcomp : ¬ (p - 2).Prime)
    (hcube : p - 2 <
      Nat.minFac (p - 2) * Nat.minFac (p - 2) * Nat.minFac (p - 2)) :
    ((p - 2) / Nat.minFac (p - 2)).Prime := by
  have hn : 1 < p - 2 := remaining_p_sub_two_gt_one hp7
  set q := Nat.minFac (p - 2)
  have hd : q ∣ p - 2 := Nat.minFac_dvd _
  set m := (p - 2) / q
  have hmul : q * m = p - 2 := Nat.mul_div_cancel' hd
  have hm1 : 1 < m := by
    have hge : q ≤ m := Nat.minFac_le_div (Nat.zero_lt_of_lt hn) hcomp
    have hq5 : 5 ≤ q := remaining_minFac_ge_five hp hp7 hmod
    exact lt_of_lt_of_le one_lt_five (le_trans hq5 hge)
  by_contra hm
  have hrmin : (Nat.minFac m).Prime := Nat.minFac_prime (ne_of_gt hm1)
  have hrd : Nat.minFac m ∣ p - 2 := by
    have hrdm : Nat.minFac m ∣ q * m :=
      dvd_mul_of_dvd_right (Nat.minFac_dvd m) q
    rwa [hmul] at hrdm
  have hqle : q ≤ Nat.minFac m := Nat.minFac_le_of_dvd hrmin.two_le hrd
  have hsq : Nat.minFac m * Nat.minFac m ≤ m := by
    have hge : Nat.minFac m ≤ m / Nat.minFac m :=
      Nat.minFac_le_div (Nat.zero_lt_of_lt hm1) hm
    have hmulr : Nat.minFac m * (m / Nat.minFac m) = m :=
      Nat.mul_div_cancel' (Nat.minFac_dvd m)
    exact (Nat.mul_le_mul_left (Nat.minFac m) hge).trans_eq hmulr
  have hqq : q * q ≤ Nat.minFac m * Nat.minFac m := Nat.mul_le_mul hqle hqle
  have hn3 : q * q * q ≤ p - 2 := by
    have h1 : q * (q * q) ≤ q * (Nat.minFac m * Nat.minFac m) :=
      Nat.mul_le_mul_left q hqq
    have h2 : q * (Nat.minFac m * Nat.minFac m) ≤ q * m :=
      Nat.mul_le_mul_left q hsq
    have hassoc : q * q * q = q * (q * q) := Nat.mul_assoc q q q
    exact hassoc ▸ (h1.trans (h2.trans_eq hmul))
  exact not_le_of_gt hcube hn3

/-- In remaining Type A with least factor `≡ 2 (mod 3)`, the prime
cofactor is `≡ 1 (mod 3)`. -/
lemma remaining_type_A_cofactor_mod_one {p : ℕ} (hp7 : 7 ≤ p)
    (hmod : p % 3 = 1)
    (hqmod : Nat.minFac (p - 2) % 3 = 2) :
    ((p - 2) / Nat.minFac (p - 2)) % 3 = 1 := by
  have hmul : Nat.minFac (p - 2) * ((p - 2) / Nat.minFac (p - 2)) =
      p - 2 := Nat.mul_div_cancel' (Nat.minFac_dvd _)
  have hprod : (Nat.minFac (p - 2) *
      ((p - 2) / Nat.minFac (p - 2))) % 3 = 2 := by
    rw [hmul]
    exact p_sub_two_mod (le_trans four_le_seven hp7) hmod
  have hmulmod : ((Nat.minFac (p - 2) % 3) *
      (((p - 2) / Nat.minFac (p - 2)) % 3)) % 3 = 2 := by
    rw [← Nat.mul_mod]
    exact hprod
  rw [hqmod] at hmulmod
  rcases mod_three_cases ((p - 2) / Nat.minFac (p - 2)) with h0 | h1 | h2
  · rw [h0, Nat.mul_zero, Nat.zero_mod] at hmulmod
    exact False.elim (zero_ne_two hmulmod)
  · exact h1
  · rw [h2] at hmulmod
    exact False.elim (one_ne_two (two_mul_two_mod_three.symm.trans hmulmod))

/-- Remaining Type A McEachen if the least factor is `≡ 2 (mod 3)` and
the complementary injector `7r-2` is prime. The cofactor `r` is prime
by `remaining_type_A_cofactor_prime`, and `k = 7` fits once
`5 ∤ p-2`. Primality of `7r-2` is not proved. -/
theorem conjecture_of_remaining_type_A_mod_two_seven {p : ℕ}
    (hp : p.Prime) (hp7 : 7 ≤ p) (hmod : p % 3 = 1)
    (hcomp : ¬ (p - 2).Prime)
    (hqmod : Nat.minFac (p - 2) % 3 = 2)
    (hcube : p - 2 <
      Nat.minFac (p - 2) * Nat.minFac (p - 2) * Nat.minFac (p - 2))
    (hpr : (7 * ((p - 2) / Nat.minFac (p - 2)) - 2).Prime) :
    a (p - 1) = p := by
  have hr := remaining_type_A_cofactor_prime hp hp7 hmod hcomp hcube
  have hr1 := remaining_type_A_cofactor_mod_one hp7 hmod hqmod
  have hdq : Nat.minFac (p - 2) ∣ p - 2 := Nat.minFac_dvd _
  have hmul : Nat.minFac (p - 2) * ((p - 2) / Nat.minFac (p - 2)) =
      p - 2 := Nat.mul_div_cancel' hdq
  have hdr : ((p - 2) / Nat.minFac (p - 2)) ∣ p - 2 := by
    have h := Nat.dvd_mul_left ((p - 2) / Nat.minFac (p - 2))
      (Nat.minFac (p - 2))
    rwa [hmul] at h
  exact conjecture_of_remaining_mod_one_seven hp hp7 hmod hcomp hr hr1 hdr hpr

/-- In remaining Type A with least factor `≡ 1 (mod 3)`, the prime
cofactor is `≡ 2 (mod 3)`. -/
lemma remaining_type_A_cofactor_mod_two {p : ℕ} (hp7 : 7 ≤ p)
    (hmod : p % 3 = 1)
    (hqmod : Nat.minFac (p - 2) % 3 = 1) :
    ((p - 2) / Nat.minFac (p - 2)) % 3 = 2 := by
  have hmul : Nat.minFac (p - 2) * ((p - 2) / Nat.minFac (p - 2)) =
      p - 2 := Nat.mul_div_cancel' (Nat.minFac_dvd _)
  have hprod : (Nat.minFac (p - 2) *
      ((p - 2) / Nat.minFac (p - 2))) % 3 = 2 := by
    rw [hmul]
    exact p_sub_two_mod (le_trans four_le_seven hp7) hmod
  have hmulmod : ((Nat.minFac (p - 2) % 3) *
      (((p - 2) / Nat.minFac (p - 2)) % 3)) % 3 = 2 := by
    rw [← Nat.mul_mod]
    exact hprod
  rw [hqmod, Nat.one_mul, Nat.mod_mod] at hmulmod
  exact hmulmod

/-- Remaining Type A McEachen if the least factor is `≡ 1 (mod 3)` and
the complementary injector `5r-2` is prime. The cofactor `r` is prime
by `remaining_type_A_cofactor_prime` and is `≡ 2 (mod 3)`, and `k = 5`
fits once the least factor is at least `5`. Primality of `5r-2` is not
proved. -/
theorem conjecture_of_remaining_type_A_mod_one_five {p : ℕ}
    (hp : p.Prime) (hp7 : 7 ≤ p) (hmod : p % 3 = 1)
    (hcomp : ¬ (p - 2).Prime)
    (hqmod : Nat.minFac (p - 2) % 3 = 1)
    (hcube : p - 2 <
      Nat.minFac (p - 2) * Nat.minFac (p - 2) * Nat.minFac (p - 2))
    (hpr : (5 * ((p - 2) / Nat.minFac (p - 2)) - 2).Prime) :
    a (p - 1) = p := by
  have hr := remaining_type_A_cofactor_prime hp hp7 hmod hcomp hcube
  have hr2 := remaining_type_A_cofactor_mod_two hp7 hmod hqmod
  have hdq : Nat.minFac (p - 2) ∣ p - 2 := Nat.minFac_dvd _
  have hmul : Nat.minFac (p - 2) * ((p - 2) / Nat.minFac (p - 2)) =
      p - 2 := Nat.mul_div_cancel' hdq
  exact conjecture_of_cofactor_five hp hp7 hmul.symm
    (remaining_minFac_ge_five hp hp7 hmod) hr.one_lt hr2 hpr

/-- `k = q` always lies in the leftover add-eight window. Primality of
`q²-2` is not proved. -/
lemma q_dvd_x_add_eight_window_of_sq_sub_two {q : ℕ}
    (hpr : (q * q - 2).Prime) (h7 : 7 ≤ q) (hmodq : q % 3 = 2) :
    q ∣ x (q * (q + 8) - 1) := by
  have h7r : 7 ≤ q * q - 2 := by
    have : 49 ≤ q * q := Nat.mul_le_mul h7 h7
    exact le_trans (by decide : 7 ≤ 47) (Nat.sub_le_sub_right this 2)
  have h4 : 4 ≤ q * q :=
    le_trans (by decide : 4 ≤ 49) (Nat.mul_le_mul h7 h7)
  have hmod : (q * q - 2) % 3 = 2 :=
    mul_sub_two_mod_three hmodq hmodq h4
  exact q_dvd_x_add_eight_window_of_k_le hpr h7r hmod (Nat.le_add_right q 8)

/-- `k = q+6` is the extra leftover candidate after overlap is excluded.
It is admissible for `q ≡ 2 (mod 3)`. Primality of `q(q+6)-2` is not
proved. -/
lemma q_dvd_x_add_eight_window_of_add_six {q : ℕ}
    (hpr : ((q + 6) * q - 2).Prime) (h7 : 7 ≤ q) (hmodq : q % 3 = 2) :
    q ∣ x (q * (q + 8) - 1) := by
  have hk : q + 6 ≤ q + 8 := Nat.add_le_add_left (by decide : 6 ≤ 8) q
  have h7r : 7 ≤ (q + 6) * q - 2 := by
    have hmul : 7 * 7 ≤ (q + 6) * q :=
      Nat.mul_le_mul (Nat.le_trans h7 (Nat.le_add_right q 6)) h7
    exact le_trans (by decide : 7 ≤ 47) (Nat.sub_le_sub_right hmul 2)
  have h4 : 4 ≤ (q + 6) * q := by
    have : 7 * 7 ≤ (q + 6) * q :=
      Nat.mul_le_mul (Nat.le_trans h7 (Nat.le_add_right q 6)) h7
    exact le_trans (by decide : 4 ≤ 49) this
  have hk3 : (q + 6) % 3 = 2 := by
    have hadd : (q + 6) % 3 = (q % 3 + 6 % 3) % 3 := Nat.add_mod q 6 3
    have h6 : (6 : ℕ) % 3 = 0 := by decide
    have hzero : (q % 3 + 0) % 3 = q % 3 := by
      rw [Nat.add_zero, Nat.mod_mod]
    rw [hadd, h6, hzero, hmodq]
  have hmod : ((q + 6) * q - 2) % 3 = 2 :=
    mul_sub_two_mod_three hk3 hmodq h4
  exact q_dvd_x_add_eight_window_of_k_le hpr h7r hmod hk

lemma remaining_p_ge_one_hundred_sixty_three {p : ℕ}
    (hp : p.Prime) (hp7 : 7 ≤ p) (hmod : p % 3 = 1)
    (hcomp : ¬ (p - 2).Prime)
    (h163 : Nat.minFac (p - 2) = 163) : 4076 ≤ p := by
  have hbound := remaining_minFac_mul_add_two_le hp hp7 hmod hcomp
  rw [h163] at hbound
  have h2le : 2 ≤ p := le_trans (by decide : 2 ≤ 7) hp7
  have hnum : 163 * (163 + 2) + 2 = 26897 := by decide
  have : 163 * (163 + 2) + 2 ≤ p - 2 + 2 := Nat.add_le_add_right hbound 2
  rw [hnum, Nat.sub_add_cancel h2le] at this
  exact le_trans (by decide : 4076 ≤ 26897) this

/-- Remaining McEachen if `lpf(p-2) = 163`. The injector is `k = 25`. -/
theorem conjecture_of_minFac_one_hundred_sixty_three {p : ℕ}
    (hp : p.Prime) (hp7 : 7 ≤ p) (hmod : p % 3 = 1)
    (hcomp : ¬ (p - 2).Prime)
    (h163 : Nat.minFac (p - 2) = 163) : a (p - 1) = p :=
  conjecture_of_one_hundred_sixty_three_dvd hp
    (remaining_p_ge_one_hundred_sixty_three hp hp7 hmod hcomp h163)
    (h163 ▸ Nat.minFac_dvd (p - 2))

lemma remaining_p_ge_one_hundred_sixty_seven {p : ℕ}
    (hp : p.Prime) (hp7 : 7 ≤ p) (hmod : p % 3 = 1)
    (hcomp : ¬ (p - 2).Prime)
    (h167 : Nat.minFac (p - 2) = 167) : 2840 ≤ p := by
  have hbound := remaining_minFac_mul_add_two_le hp hp7 hmod hcomp
  rw [h167] at hbound
  have h2le : 2 ≤ p := le_trans (by decide : 2 ≤ 7) hp7
  have hnum : 167 * (167 + 2) + 2 = 28225 := by decide
  have : 167 * (167 + 2) + 2 ≤ p - 2 + 2 := Nat.add_le_add_right hbound 2
  rw [hnum, Nat.sub_add_cancel h2le] at this
  exact le_trans (by decide : 2840 ≤ 28225) this

/-- Remaining McEachen if `lpf(p-2) = 167`. The injector is `k = 17`. -/
theorem conjecture_of_minFac_one_hundred_sixty_seven {p : ℕ}
    (hp : p.Prime) (hp7 : 7 ≤ p) (hmod : p % 3 = 1)
    (hcomp : ¬ (p - 2).Prime)
    (h167 : Nat.minFac (p - 2) = 167) : a (p - 1) = p :=
  conjecture_of_one_hundred_sixty_seven_dvd hp
    (remaining_p_ge_one_hundred_sixty_seven hp hp7 hmod hcomp h167)
    (h167 ▸ Nat.minFac_dvd (p - 2))

lemma remaining_p_ge_one_hundred_seventy_nine {p : ℕ}
    (hp : p.Prime) (hp7 : 7 ≤ p) (hmod : p % 3 = 1)
    (hcomp : ¬ (p - 2).Prime)
    (h179 : Nat.minFac (p - 2) = 179) : 3044 ≤ p := by
  have hbound := remaining_minFac_mul_add_two_le hp hp7 hmod hcomp
  rw [h179] at hbound
  have h2le : 2 ≤ p := le_trans (by decide : 2 ≤ 7) hp7
  have hnum : 179 * (179 + 2) + 2 = 32401 := by decide
  have : 179 * (179 + 2) + 2 ≤ p - 2 + 2 := Nat.add_le_add_right hbound 2
  rw [hnum, Nat.sub_add_cancel h2le] at this
  exact le_trans (by decide : 3044 ≤ 32401) this

/-- Remaining McEachen if `lpf(p-2) = 179`. The injector is `k = 17`. -/
theorem conjecture_of_minFac_one_hundred_seventy_nine {p : ℕ}
    (hp : p.Prime) (hp7 : 7 ≤ p) (hmod : p % 3 = 1)
    (hcomp : ¬ (p - 2).Prime)
    (h179 : Nat.minFac (p - 2) = 179) : a (p - 1) = p :=
  conjecture_of_one_hundred_seventy_nine_dvd hp
    (remaining_p_ge_one_hundred_seventy_nine hp hp7 hmod hcomp h179)
    (h179 ▸ Nat.minFac_dvd (p - 2))

lemma remaining_p_ge_two_hundred_twenty_seven {p : ℕ}
    (hp : p.Prime) (hp7 : 7 ≤ p) (hmod : p % 3 = 1)
    (hcomp : ¬ (p - 2).Prime)
    (h227 : Nat.minFac (p - 2) = 227) : 6584 ≤ p := by
  have hbound := remaining_minFac_mul_add_two_le hp hp7 hmod hcomp
  rw [h227] at hbound
  have h2le : 2 ≤ p := le_trans (by decide : 2 ≤ 7) hp7
  have hnum : 227 * (227 + 2) + 2 = 51985 := by decide
  have : 227 * (227 + 2) + 2 ≤ p - 2 + 2 := Nat.add_le_add_right hbound 2
  rw [hnum, Nat.sub_add_cancel h2le] at this
  exact le_trans (by decide : 6584 ≤ 51985) this

/-- Remaining McEachen if `lpf(p-2) = 227`. The injector is `k = 29`. -/
theorem conjecture_of_minFac_two_hundred_twenty_seven {p : ℕ}
    (hp : p.Prime) (hp7 : 7 ≤ p) (hmod : p % 3 = 1)
    (hcomp : ¬ (p - 2).Prime)
    (h227 : Nat.minFac (p - 2) = 227) : a (p - 1) = p :=
  conjecture_of_two_hundred_twenty_seven_dvd hp
    (remaining_p_ge_two_hundred_twenty_seven hp hp7 hmod hcomp h227)
    (h227 ▸ Nat.minFac_dvd (p - 2))

lemma remaining_p_ge_two_hundred_fifty_one {p : ℕ}
    (hp : p.Prime) (hp7 : 7 ≤ p) (hmod : p % 3 = 1)
    (hcomp : ¬ (p - 2).Prime)
    (h251 : Nat.minFac (p - 2) = 251) : 8786 ≤ p := by
  have hbound := remaining_minFac_mul_add_two_le hp hp7 hmod hcomp
  rw [h251] at hbound
  have h2le : 2 ≤ p := le_trans (by decide : 2 ≤ 7) hp7
  have hnum : 251 * (251 + 2) + 2 = 63505 := by decide
  have : 251 * (251 + 2) + 2 ≤ p - 2 + 2 := Nat.add_le_add_right hbound 2
  rw [hnum, Nat.sub_add_cancel h2le] at this
  exact le_trans (by decide : 8786 ≤ 63505) this

/-- Remaining McEachen if `lpf(p-2) = 251`. The injector is `k = 35`. -/
theorem conjecture_of_minFac_two_hundred_fifty_one {p : ℕ}
    (hp : p.Prime) (hp7 : 7 ≤ p) (hmod : p % 3 = 1)
    (hcomp : ¬ (p - 2).Prime)
    (h251 : Nat.minFac (p - 2) = 251) : a (p - 1) = p :=
  conjecture_of_two_hundred_fifty_one_dvd hp
    (remaining_p_ge_two_hundred_fifty_one hp hp7 hmod hcomp h251)
    (h251 ▸ Nat.minFac_dvd (p - 2))

lemma remaining_p_ge_three_hundred_eighty_nine {p : ℕ}
    (hp : p.Prime) (hp7 : 7 ≤ p) (hmod : p % 3 = 1)
    (hcomp : ¬ (p - 2).Prime)
    (h389 : Nat.minFac (p - 2) = 389) : 11282 ≤ p := by
  have hbound := remaining_minFac_mul_add_two_le hp hp7 hmod hcomp
  rw [h389] at hbound
  have h2le : 2 ≤ p := le_trans (by decide : 2 ≤ 7) hp7
  have hnum : 389 * (389 + 2) + 2 = 152101 := by decide
  have : 389 * (389 + 2) + 2 ≤ p - 2 + 2 := Nat.add_le_add_right hbound 2
  rw [hnum, Nat.sub_add_cancel h2le] at this
  exact le_trans (by decide : 11282 ≤ 152101) this

/-- Remaining McEachen if `lpf(p-2) = 389`. The injector is `k = 29`. -/
theorem conjecture_of_minFac_three_hundred_eighty_nine {p : ℕ}
    (hp : p.Prime) (hp7 : 7 ≤ p) (hmod : p % 3 = 1)
    (hcomp : ¬ (p - 2).Prime)
    (h389 : Nat.minFac (p - 2) = 389) : a (p - 1) = p :=
  conjecture_of_three_hundred_eighty_nine_dvd hp
    (remaining_p_ge_three_hundred_eighty_nine hp hp7 hmod hcomp h389)
    (h389 ▸ Nat.minFac_dvd (p - 2))

lemma remaining_p_ge_one_hundred_thirteen {p : ℕ}
    (hp : p.Prime) (hp7 : 7 ≤ p) (hmod : p % 3 = 1)
    (hcomp : ¬ (p - 2).Prime)
    (h113 : Nat.minFac (p - 2) = 113) : 566 ≤ p := by
  have hbound := remaining_minFac_mul_add_two_le hp hp7 hmod hcomp
  rw [h113] at hbound
  have h2le : 2 ≤ p := le_trans (by decide : 2 ≤ 7) hp7
  have hnum : 113 * (113 + 2) + 2 = 12997 := by decide
  have : 113 * (113 + 2) + 2 ≤ p - 2 + 2 := Nat.add_le_add_right hbound 2
  rw [hnum, Nat.sub_add_cancel h2le] at this
  exact le_trans (by decide : 566 ≤ 12997) this

/-- Remaining McEachen if `lpf(p-2) = 113`. The injector is `k = 5`. -/
theorem conjecture_of_minFac_one_hundred_thirteen {p : ℕ}
    (hp : p.Prime) (hp7 : 7 ≤ p) (hmod : p % 3 = 1)
    (hcomp : ¬ (p - 2).Prime)
    (h113 : Nat.minFac (p - 2) = 113) : a (p - 1) = p :=
  conjecture_of_one_hundred_thirteen_dvd hp
    (remaining_p_ge_one_hundred_thirteen hp hp7 hmod hcomp h113)
    (h113 ▸ Nat.minFac_dvd (p - 2))

lemma remaining_p_ge_one_hundred_twenty_seven {p : ℕ}
    (hp : p.Prime) (hp7 : 7 ≤ p) (hmod : p % 3 = 1)
    (hcomp : ¬ (p - 2).Prime)
    (h127 : Nat.minFac (p - 2) = 127) : 890 ≤ p := by
  have hbound := remaining_minFac_mul_add_two_le hp hp7 hmod hcomp
  rw [h127] at hbound
  have h2le : 2 ≤ p := le_trans (by decide : 2 ≤ 7) hp7
  have hnum : 127 * (127 + 2) + 2 = 16385 := by decide
  have : 127 * (127 + 2) + 2 ≤ p - 2 + 2 := Nat.add_le_add_right hbound 2
  rw [hnum, Nat.sub_add_cancel h2le] at this
  exact le_trans (by decide : 890 ≤ 16385) this

/-- Remaining McEachen if `lpf(p-2) = 127`. The injector is `k = 7`. -/
theorem conjecture_of_minFac_one_hundred_twenty_seven {p : ℕ}
    (hp : p.Prime) (hp7 : 7 ≤ p) (hmod : p % 3 = 1)
    (hcomp : ¬ (p - 2).Prime)
    (h127 : Nat.minFac (p - 2) = 127) : a (p - 1) = p :=
  conjecture_of_one_hundred_twenty_seven_dvd hp
    (remaining_p_ge_one_hundred_twenty_seven hp hp7 hmod hcomp h127)
    (h127 ▸ Nat.minFac_dvd (p - 2))

lemma remaining_p_ge_one_hundred_thirty_one {p : ℕ}
    (hp : p.Prime) (hp7 : 7 ≤ p) (hmod : p % 3 = 1)
    (hcomp : ¬ (p - 2).Prime)
    (h131 : Nat.minFac (p - 2) = 131) : 656 ≤ p := by
  have hbound := remaining_minFac_mul_add_two_le hp hp7 hmod hcomp
  rw [h131] at hbound
  have h2le : 2 ≤ p := le_trans (by decide : 2 ≤ 7) hp7
  have hnum : 131 * (131 + 2) + 2 = 17425 := by decide
  have : 131 * (131 + 2) + 2 ≤ p - 2 + 2 := Nat.add_le_add_right hbound 2
  rw [hnum, Nat.sub_add_cancel h2le] at this
  exact le_trans (by decide : 656 ≤ 17425) this

/-- Remaining McEachen if `lpf(p-2) = 131`. The injector is `k = 5`. -/
theorem conjecture_of_minFac_one_hundred_thirty_one {p : ℕ}
    (hp : p.Prime) (hp7 : 7 ≤ p) (hmod : p % 3 = 1)
    (hcomp : ¬ (p - 2).Prime)
    (h131 : Nat.minFac (p - 2) = 131) : a (p - 1) = p :=
  conjecture_of_one_hundred_thirty_one_dvd hp
    (remaining_p_ge_one_hundred_thirty_one hp hp7 hmod hcomp h131)
    (h131 ▸ Nat.minFac_dvd (p - 2))

lemma remaining_p_ge_one_hundred_thirty_seven {p : ℕ}
    (hp : p.Prime) (hp7 : 7 ≤ p) (hmod : p % 3 = 1)
    (hcomp : ¬ (p - 2).Prime)
    (h137 : Nat.minFac (p - 2) = 137) : 686 ≤ p := by
  have hbound := remaining_minFac_mul_add_two_le hp hp7 hmod hcomp
  rw [h137] at hbound
  have h2le : 2 ≤ p := le_trans (by decide : 2 ≤ 7) hp7
  have hnum : 137 * (137 + 2) + 2 = 19045 := by decide
  have : 137 * (137 + 2) + 2 ≤ p - 2 + 2 := Nat.add_le_add_right hbound 2
  rw [hnum, Nat.sub_add_cancel h2le] at this
  exact le_trans (by decide : 686 ≤ 19045) this

/-- Remaining McEachen if `lpf(p-2) = 137`. The injector is `k = 5`. -/
theorem conjecture_of_minFac_one_hundred_thirty_seven {p : ℕ}
    (hp : p.Prime) (hp7 : 7 ≤ p) (hmod : p % 3 = 1)
    (hcomp : ¬ (p - 2).Prime)
    (h137 : Nat.minFac (p - 2) = 137) : a (p - 1) = p :=
  conjecture_of_one_hundred_thirty_seven_dvd hp
    (remaining_p_ge_one_hundred_thirty_seven hp hp7 hmod hcomp h137)
    (h137 ▸ Nat.minFac_dvd (p - 2))

lemma remaining_p_ge_one_hundred_forty_nine {p : ℕ}
    (hp : p.Prime) (hp7 : 7 ≤ p) (hmod : p % 3 = 1)
    (hcomp : ¬ (p - 2).Prime)
    (h149 : Nat.minFac (p - 2) = 149) : 746 ≤ p := by
  have hbound := remaining_minFac_mul_add_two_le hp hp7 hmod hcomp
  rw [h149] at hbound
  have h2le : 2 ≤ p := le_trans (by decide : 2 ≤ 7) hp7
  have hnum : 149 * (149 + 2) + 2 = 22501 := by decide
  have : 149 * (149 + 2) + 2 ≤ p - 2 + 2 := Nat.add_le_add_right hbound 2
  rw [hnum, Nat.sub_add_cancel h2le] at this
  exact le_trans (by decide : 746 ≤ 22501) this

/-- Remaining McEachen if `lpf(p-2) = 149`. The injector is `k = 5`. -/
theorem conjecture_of_minFac_one_hundred_forty_nine {p : ℕ}
    (hp : p.Prime) (hp7 : 7 ≤ p) (hmod : p % 3 = 1)
    (hcomp : ¬ (p - 2).Prime)
    (h149 : Nat.minFac (p - 2) = 149) : a (p - 1) = p :=
  conjecture_of_one_hundred_forty_nine_dvd hp
    (remaining_p_ge_one_hundred_forty_nine hp hp7 hmod hcomp h149)
    (h149 ▸ Nat.minFac_dvd (p - 2))

lemma remaining_p_ge_one_hundred_fifty_seven {p : ℕ}
    (hp : p.Prime) (hp7 : 7 ≤ p) (hmod : p % 3 = 1)
    (hcomp : ¬ (p - 2).Prime)
    (h157 : Nat.minFac (p - 2) = 157) : 1100 ≤ p := by
  have hbound := remaining_minFac_mul_add_two_le hp hp7 hmod hcomp
  rw [h157] at hbound
  have h2le : 2 ≤ p := le_trans (by decide : 2 ≤ 7) hp7
  have hnum : 157 * (157 + 2) + 2 = 24965 := by decide
  have : 157 * (157 + 2) + 2 ≤ p - 2 + 2 := Nat.add_le_add_right hbound 2
  rw [hnum, Nat.sub_add_cancel h2le] at this
  exact le_trans (by decide : 1100 ≤ 24965) this

/-- Remaining McEachen if `lpf(p-2) = 157`. The injector is `k = 7`. -/
theorem conjecture_of_minFac_one_hundred_fifty_seven {p : ℕ}
    (hp : p.Prime) (hp7 : 7 ≤ p) (hmod : p % 3 = 1)
    (hcomp : ¬ (p - 2).Prime)
    (h157 : Nat.minFac (p - 2) = 157) : a (p - 1) = p :=
  conjecture_of_one_hundred_fifty_seven_dvd hp
    (remaining_p_ge_one_hundred_fifty_seven hp hp7 hmod hcomp h157)
    (h157 ▸ Nat.minFac_dvd (p - 2))

lemma remaining_p_ge_one_hundred_seventy_three {p : ℕ}
    (hp : p.Prime) (hp7 : 7 ≤ p) (hmod : p % 3 = 1)
    (hcomp : ¬ (p - 2).Prime)
    (h173 : Nat.minFac (p - 2) = 173) : 866 ≤ p := by
  have hbound := remaining_minFac_mul_add_two_le hp hp7 hmod hcomp
  rw [h173] at hbound
  have h2le : 2 ≤ p := le_trans (by decide : 2 ≤ 7) hp7
  have hnum : 173 * (173 + 2) + 2 = 30277 := by decide
  have : 173 * (173 + 2) + 2 ≤ p - 2 + 2 := Nat.add_le_add_right hbound 2
  rw [hnum, Nat.sub_add_cancel h2le] at this
  exact le_trans (by decide : 866 ≤ 30277) this

/-- Remaining McEachen if `lpf(p-2) = 173`. The injector is `k = 5`. -/
theorem conjecture_of_minFac_one_hundred_seventy_three {p : ℕ}
    (hp : p.Prime) (hp7 : 7 ≤ p) (hmod : p % 3 = 1)
    (hcomp : ¬ (p - 2).Prime)
    (h173 : Nat.minFac (p - 2) = 173) : a (p - 1) = p :=
  conjecture_of_one_hundred_seventy_three_dvd hp
    (remaining_p_ge_one_hundred_seventy_three hp hp7 hmod hcomp h173)
    (h173 ▸ Nat.minFac_dvd (p - 2))

lemma remaining_p_ge_one_hundred_ninety_one {p : ℕ}
    (hp : p.Prime) (hp7 : 7 ≤ p) (hmod : p % 3 = 1)
    (hcomp : ¬ (p - 2).Prime)
    (h191 : Nat.minFac (p - 2) = 191) : 956 ≤ p := by
  have hbound := remaining_minFac_mul_add_two_le hp hp7 hmod hcomp
  rw [h191] at hbound
  have h2le : 2 ≤ p := le_trans (by decide : 2 ≤ 7) hp7
  have hnum : 191 * (191 + 2) + 2 = 36865 := by decide
  have : 191 * (191 + 2) + 2 ≤ p - 2 + 2 := Nat.add_le_add_right hbound 2
  rw [hnum, Nat.sub_add_cancel h2le] at this
  exact le_trans (by decide : 956 ≤ 36865) this

/-- Remaining McEachen if `lpf(p-2) = 191`. The injector is `k = 5`. -/
theorem conjecture_of_minFac_one_hundred_ninety_one {p : ℕ}
    (hp : p.Prime) (hp7 : 7 ≤ p) (hmod : p % 3 = 1)
    (hcomp : ¬ (p - 2).Prime)
    (h191 : Nat.minFac (p - 2) = 191) : a (p - 1) = p :=
  conjecture_of_one_hundred_ninety_one_dvd hp
    (remaining_p_ge_one_hundred_ninety_one hp hp7 hmod hcomp h191)
    (h191 ▸ Nat.minFac_dvd (p - 2))

lemma remaining_p_ge_one_hundred_ninety_seven {p : ℕ}
    (hp : p.Prime) (hp7 : 7 ≤ p) (hmod : p % 3 = 1)
    (hcomp : ¬ (p - 2).Prime)
    (h197 : Nat.minFac (p - 2) = 197) : 986 ≤ p := by
  have hbound := remaining_minFac_mul_add_two_le hp hp7 hmod hcomp
  rw [h197] at hbound
  have h2le : 2 ≤ p := le_trans (by decide : 2 ≤ 7) hp7
  have hnum : 197 * (197 + 2) + 2 = 39205 := by decide
  have : 197 * (197 + 2) + 2 ≤ p - 2 + 2 := Nat.add_le_add_right hbound 2
  rw [hnum, Nat.sub_add_cancel h2le] at this
  exact le_trans (by decide : 986 ≤ 39205) this

/-- Remaining McEachen if `lpf(p-2) = 197`. The injector is `k = 5`. -/
theorem conjecture_of_minFac_one_hundred_ninety_seven {p : ℕ}
    (hp : p.Prime) (hp7 : 7 ≤ p) (hmod : p % 3 = 1)
    (hcomp : ¬ (p - 2).Prime)
    (h197 : Nat.minFac (p - 2) = 197) : a (p - 1) = p :=
  conjecture_of_one_hundred_ninety_seven_dvd hp
    (remaining_p_ge_one_hundred_ninety_seven hp hp7 hmod hcomp h197)
    (h197 ▸ Nat.minFac_dvd (p - 2))

lemma remaining_p_ge_two_hundred_eleven {p : ℕ}
    (hp : p.Prime) (hp7 : 7 ≤ p) (hmod : p % 3 = 1)
    (hcomp : ¬ (p - 2).Prime)
    (h211 : Nat.minFac (p - 2) = 211) : 2744 ≤ p := by
  have hbound := remaining_minFac_mul_add_two_le hp hp7 hmod hcomp
  rw [h211] at hbound
  have h2le : 2 ≤ p := le_trans (by decide : 2 ≤ 7) hp7
  have hnum : 211 * (211 + 2) + 2 = 44945 := by decide
  have : 211 * (211 + 2) + 2 ≤ p - 2 + 2 := Nat.add_le_add_right hbound 2
  rw [hnum, Nat.sub_add_cancel h2le] at this
  exact le_trans (by decide : 2744 ≤ 44945) this

/-- Remaining McEachen if `lpf(p-2) = 211`. The injector is `k = 13`. -/
theorem conjecture_of_minFac_two_hundred_eleven {p : ℕ}
    (hp : p.Prime) (hp7 : 7 ≤ p) (hmod : p % 3 = 1)
    (hcomp : ¬ (p - 2).Prime)
    (h211 : Nat.minFac (p - 2) = 211) : a (p - 1) = p :=
  conjecture_of_two_hundred_eleven_dvd hp
    (remaining_p_ge_two_hundred_eleven hp hp7 hmod hcomp h211)
    (h211 ▸ Nat.minFac_dvd (p - 2))

lemma remaining_p_ge_two_hundred_twenty_three {p : ℕ}
    (hp : p.Prime) (hp7 : 7 ≤ p) (hmod : p % 3 = 1)
    (hcomp : ¬ (p - 2).Prime)
    (h223 : Nat.minFac (p - 2) = 223) : 1562 ≤ p := by
  have hbound := remaining_minFac_mul_add_two_le hp hp7 hmod hcomp
  rw [h223] at hbound
  have h2le : 2 ≤ p := le_trans (by decide : 2 ≤ 7) hp7
  have hnum : 223 * (223 + 2) + 2 = 50177 := by decide
  have : 223 * (223 + 2) + 2 ≤ p - 2 + 2 := Nat.add_le_add_right hbound 2
  rw [hnum, Nat.sub_add_cancel h2le] at this
  exact le_trans (by decide : 1562 ≤ 50177) this

/-- Remaining McEachen if `lpf(p-2) = 223`. The injector is `k = 7`. -/
theorem conjecture_of_minFac_two_hundred_twenty_three {p : ℕ}
    (hp : p.Prime) (hp7 : 7 ≤ p) (hmod : p % 3 = 1)
    (hcomp : ¬ (p - 2).Prime)
    (h223 : Nat.minFac (p - 2) = 223) : a (p - 1) = p :=
  conjecture_of_two_hundred_twenty_three_dvd hp
    (remaining_p_ge_two_hundred_twenty_three hp hp7 hmod hcomp h223)
    (h223 ▸ Nat.minFac_dvd (p - 2))

lemma remaining_p_ge_two_hundred_thirty_three {p : ℕ}
    (hp : p.Prime) (hp7 : 7 ≤ p) (hmod : p % 3 = 1)
    (hcomp : ¬ (p - 2).Prime)
    (h233 : Nat.minFac (p - 2) = 233) : 1166 ≤ p := by
  have hbound := remaining_minFac_mul_add_two_le hp hp7 hmod hcomp
  rw [h233] at hbound
  have h2le : 2 ≤ p := le_trans (by decide : 2 ≤ 7) hp7
  have hnum : 233 * (233 + 2) + 2 = 54757 := by decide
  have : 233 * (233 + 2) + 2 ≤ p - 2 + 2 := Nat.add_le_add_right hbound 2
  rw [hnum, Nat.sub_add_cancel h2le] at this
  exact le_trans (by decide : 1166 ≤ 54757) this

/-- Remaining McEachen if `lpf(p-2) = 233`. The injector is `k = 5`. -/
theorem conjecture_of_minFac_two_hundred_thirty_three {p : ℕ}
    (hp : p.Prime) (hp7 : 7 ≤ p) (hmod : p % 3 = 1)
    (hcomp : ¬ (p - 2).Prime)
    (h233 : Nat.minFac (p - 2) = 233) : a (p - 1) = p :=
  conjecture_of_two_hundred_thirty_three_dvd hp
    (remaining_p_ge_two_hundred_thirty_three hp hp7 hmod hcomp h233)
    (h233 ▸ Nat.minFac_dvd (p - 2))

lemma remaining_p_ge_two_hundred_thirty_nine {p : ℕ}
    (hp : p.Prime) (hp7 : 7 ≤ p) (hmod : p % 3 = 1)
    (hcomp : ¬ (p - 2).Prime)
    (h239 : Nat.minFac (p - 2) = 239) : 1196 ≤ p := by
  have hbound := remaining_minFac_mul_add_two_le hp hp7 hmod hcomp
  rw [h239] at hbound
  have h2le : 2 ≤ p := le_trans (by decide : 2 ≤ 7) hp7
  have hnum : 239 * (239 + 2) + 2 = 57601 := by decide
  have : 239 * (239 + 2) + 2 ≤ p - 2 + 2 := Nat.add_le_add_right hbound 2
  rw [hnum, Nat.sub_add_cancel h2le] at this
  exact le_trans (by decide : 1196 ≤ 57601) this

/-- Remaining McEachen if `lpf(p-2) = 239`. The injector is `k = 5`. -/
theorem conjecture_of_minFac_two_hundred_thirty_nine {p : ℕ}
    (hp : p.Prime) (hp7 : 7 ≤ p) (hmod : p % 3 = 1)
    (hcomp : ¬ (p - 2).Prime)
    (h239 : Nat.minFac (p - 2) = 239) : a (p - 1) = p :=
  conjecture_of_two_hundred_thirty_nine_dvd hp
    (remaining_p_ge_two_hundred_thirty_nine hp hp7 hmod hcomp h239)
    (h239 ▸ Nat.minFac_dvd (p - 2))

lemma remaining_p_ge_two_hundred_fifty_seven {p : ℕ}
    (hp : p.Prime) (hp7 : 7 ≤ p) (hmod : p % 3 = 1)
    (hcomp : ¬ (p - 2).Prime)
    (h257 : Nat.minFac (p - 2) = 257) : 1286 ≤ p := by
  have hbound := remaining_minFac_mul_add_two_le hp hp7 hmod hcomp
  rw [h257] at hbound
  have h2le : 2 ≤ p := le_trans (by decide : 2 ≤ 7) hp7
  have hnum : 257 * (257 + 2) + 2 = 66565 := by decide
  have : 257 * (257 + 2) + 2 ≤ p - 2 + 2 := Nat.add_le_add_right hbound 2
  rw [hnum, Nat.sub_add_cancel h2le] at this
  exact le_trans (by decide : 1286 ≤ 66565) this

/-- Remaining McEachen if `lpf(p-2) = 257`. The injector is `k = 5`. -/
theorem conjecture_of_minFac_two_hundred_fifty_seven {p : ℕ}
    (hp : p.Prime) (hp7 : 7 ≤ p) (hmod : p % 3 = 1)
    (hcomp : ¬ (p - 2).Prime)
    (h257 : Nat.minFac (p - 2) = 257) : a (p - 1) = p :=
  conjecture_of_two_hundred_fifty_seven_dvd hp
    (remaining_p_ge_two_hundred_fifty_seven hp hp7 hmod hcomp h257)
    (h257 ▸ Nat.minFac_dvd (p - 2))

lemma remaining_p_ge_two_hundred_sixty_three {p : ℕ}
    (hp : p.Prime) (hp7 : 7 ≤ p) (hmod : p % 3 = 1)
    (hcomp : ¬ (p - 2).Prime)
    (h263 : Nat.minFac (p - 2) = 263) : 6050 ≤ p := by
  have hbound := remaining_minFac_mul_add_two_le hp hp7 hmod hcomp
  rw [h263] at hbound
  have h2le : 2 ≤ p := le_trans (by decide : 2 ≤ 7) hp7
  have hnum : 263 * (263 + 2) + 2 = 69697 := by decide
  have : 263 * (263 + 2) + 2 ≤ p - 2 + 2 := Nat.add_le_add_right hbound 2
  rw [hnum, Nat.sub_add_cancel h2le] at this
  exact le_trans (by decide : 6050 ≤ 69697) this

/-- Remaining McEachen if `lpf(p-2) = 263`. The injector is `k = 23`. -/
theorem conjecture_of_minFac_two_hundred_sixty_three {p : ℕ}
    (hp : p.Prime) (hp7 : 7 ≤ p) (hmod : p % 3 = 1)
    (hcomp : ¬ (p - 2).Prime)
    (h263 : Nat.minFac (p - 2) = 263) : a (p - 1) = p :=
  conjecture_of_two_hundred_sixty_three_dvd hp
    (remaining_p_ge_two_hundred_sixty_three hp hp7 hmod hcomp h263)
    (h263 ▸ Nat.minFac_dvd (p - 2))

lemma remaining_p_ge_two_hundred_sixty_nine {p : ℕ}
    (hp : p.Prime) (hp7 : 7 ≤ p) (hmod : p % 3 = 1)
    (hcomp : ¬ (p - 2).Prime)
    (h269 : Nat.minFac (p - 2) = 269) : 2960 ≤ p := by
  have hbound := remaining_minFac_mul_add_two_le hp hp7 hmod hcomp
  rw [h269] at hbound
  have h2le : 2 ≤ p := le_trans (by decide : 2 ≤ 7) hp7
  have hnum : 269 * (269 + 2) + 2 = 72901 := by decide
  have : 269 * (269 + 2) + 2 ≤ p - 2 + 2 := Nat.add_le_add_right hbound 2
  rw [hnum, Nat.sub_add_cancel h2le] at this
  exact le_trans (by decide : 2960 ≤ 72901) this

/-- Remaining McEachen if `lpf(p-2) = 269`. The injector is `k = 11`. -/
theorem conjecture_of_minFac_two_hundred_sixty_nine {p : ℕ}
    (hp : p.Prime) (hp7 : 7 ≤ p) (hmod : p % 3 = 1)
    (hcomp : ¬ (p - 2).Prime)
    (h269 : Nat.minFac (p - 2) = 269) : a (p - 1) = p :=
  conjecture_of_two_hundred_sixty_nine_dvd hp
    (remaining_p_ge_two_hundred_sixty_nine hp hp7 hmod hcomp h269)
    (h269 ▸ Nat.minFac_dvd (p - 2))

lemma remaining_p_ge_two_hundred_seventy_seven {p : ℕ}
    (hp : p.Prime) (hp7 : 7 ≤ p) (hmod : p % 3 = 1)
    (hcomp : ¬ (p - 2).Prime)
    (h277 : Nat.minFac (p - 2) = 277) : 5264 ≤ p := by
  have hbound := remaining_minFac_mul_add_two_le hp hp7 hmod hcomp
  rw [h277] at hbound
  have h2le : 2 ≤ p := le_trans (by decide : 2 ≤ 7) hp7
  have hnum : 277 * (277 + 2) + 2 = 77285 := by decide
  have : 277 * (277 + 2) + 2 ≤ p - 2 + 2 := Nat.add_le_add_right hbound 2
  rw [hnum, Nat.sub_add_cancel h2le] at this
  exact le_trans (by decide : 5264 ≤ 77285) this

/-- Remaining McEachen if `lpf(p-2) = 277`. The injector is `k = 19`. -/
theorem conjecture_of_minFac_two_hundred_seventy_seven {p : ℕ}
    (hp : p.Prime) (hp7 : 7 ≤ p) (hmod : p % 3 = 1)
    (hcomp : ¬ (p - 2).Prime)
    (h277 : Nat.minFac (p - 2) = 277) : a (p - 1) = p :=
  conjecture_of_two_hundred_seventy_seven_dvd hp
    (remaining_p_ge_two_hundred_seventy_seven hp hp7 hmod hcomp h277)
    (h277 ▸ Nat.minFac_dvd (p - 2))

lemma remaining_p_ge_two_hundred_eighty_one {p : ℕ}
    (hp : p.Prime) (hp7 : 7 ≤ p) (hmod : p % 3 = 1)
    (hcomp : ¬ (p - 2).Prime)
    (h281 : Nat.minFac (p - 2) = 281) : 3092 ≤ p := by
  have hbound := remaining_minFac_mul_add_two_le hp hp7 hmod hcomp
  rw [h281] at hbound
  have h2le : 2 ≤ p := le_trans (by decide : 2 ≤ 7) hp7
  have hnum : 281 * (281 + 2) + 2 = 79525 := by decide
  have : 281 * (281 + 2) + 2 ≤ p - 2 + 2 := Nat.add_le_add_right hbound 2
  rw [hnum, Nat.sub_add_cancel h2le] at this
  exact le_trans (by decide : 3092 ≤ 79525) this

/-- Remaining McEachen if `lpf(p-2) = 281`. The injector is `k = 11`. -/
theorem conjecture_of_minFac_two_hundred_eighty_one {p : ℕ}
    (hp : p.Prime) (hp7 : 7 ≤ p) (hmod : p % 3 = 1)
    (hcomp : ¬ (p - 2).Prime)
    (h281 : Nat.minFac (p - 2) = 281) : a (p - 1) = p :=
  conjecture_of_two_hundred_eighty_one_dvd hp
    (remaining_p_ge_two_hundred_eighty_one hp hp7 hmod hcomp h281)
    (h281 ▸ Nat.minFac_dvd (p - 2))

lemma remaining_p_ge_two_hundred_ninety_three {p : ℕ}
    (hp : p.Prime) (hp7 : 7 ≤ p) (hmod : p % 3 = 1)
    (hcomp : ¬ (p - 2).Prime)
    (h293 : Nat.minFac (p - 2) = 293) : 3224 ≤ p := by
  have hbound := remaining_minFac_mul_add_two_le hp hp7 hmod hcomp
  rw [h293] at hbound
  have h2le : 2 ≤ p := le_trans (by decide : 2 ≤ 7) hp7
  have hnum : 293 * (293 + 2) + 2 = 86437 := by decide
  have : 293 * (293 + 2) + 2 ≤ p - 2 + 2 := Nat.add_le_add_right hbound 2
  rw [hnum, Nat.sub_add_cancel h2le] at this
  exact le_trans (by decide : 3224 ≤ 86437) this

/-- Remaining McEachen if `lpf(p-2) = 293`. The injector is `k = 11`. -/
theorem conjecture_of_minFac_two_hundred_ninety_three {p : ℕ}
    (hp : p.Prime) (hp7 : 7 ≤ p) (hmod : p % 3 = 1)
    (hcomp : ¬ (p - 2).Prime)
    (h293 : Nat.minFac (p - 2) = 293) : a (p - 1) = p :=
  conjecture_of_two_hundred_ninety_three_dvd hp
    (remaining_p_ge_two_hundred_ninety_three hp hp7 hmod hcomp h293)
    (h293 ▸ Nat.minFac_dvd (p - 2))

lemma remaining_p_ge_three_hundred_seven {p : ℕ}
    (hp : p.Prime) (hp7 : 7 ≤ p) (hmod : p % 3 = 1)
    (hcomp : ¬ (p - 2).Prime)
    (h307 : Nat.minFac (p - 2) = 307) : 3992 ≤ p := by
  have hbound := remaining_minFac_mul_add_two_le hp hp7 hmod hcomp
  rw [h307] at hbound
  have h2le : 2 ≤ p := le_trans (by decide : 2 ≤ 7) hp7
  have hnum : 307 * (307 + 2) + 2 = 94865 := by decide
  have : 307 * (307 + 2) + 2 ≤ p - 2 + 2 := Nat.add_le_add_right hbound 2
  rw [hnum, Nat.sub_add_cancel h2le] at this
  exact le_trans (by decide : 3992 ≤ 94865) this

/-- Remaining McEachen if `lpf(p-2) = 307`. The injector is `k = 13`. -/
theorem conjecture_of_minFac_three_hundred_seven {p : ℕ}
    (hp : p.Prime) (hp7 : 7 ≤ p) (hmod : p % 3 = 1)
    (hcomp : ¬ (p - 2).Prime)
    (h307 : Nat.minFac (p - 2) = 307) : a (p - 1) = p :=
  conjecture_of_three_hundred_seven_dvd hp
    (remaining_p_ge_three_hundred_seven hp hp7 hmod hcomp h307)
    (h307 ▸ Nat.minFac_dvd (p - 2))

lemma remaining_p_ge_three_hundred_eleven {p : ℕ}
    (hp : p.Prime) (hp7 : 7 ≤ p) (hmod : p % 3 = 1)
    (hcomp : ¬ (p - 2).Prime)
    (h311 : Nat.minFac (p - 2) = 311) : 1556 ≤ p := by
  have hbound := remaining_minFac_mul_add_two_le hp hp7 hmod hcomp
  rw [h311] at hbound
  have h2le : 2 ≤ p := le_trans (by decide : 2 ≤ 7) hp7
  have hnum : 311 * (311 + 2) + 2 = 97345 := by decide
  have : 311 * (311 + 2) + 2 ≤ p - 2 + 2 := Nat.add_le_add_right hbound 2
  rw [hnum, Nat.sub_add_cancel h2le] at this
  exact le_trans (by decide : 1556 ≤ 97345) this

/-- Remaining McEachen if `lpf(p-2) = 311`. The injector is `k = 5`. -/
theorem conjecture_of_minFac_three_hundred_eleven {p : ℕ}
    (hp : p.Prime) (hp7 : 7 ≤ p) (hmod : p % 3 = 1)
    (hcomp : ¬ (p - 2).Prime)
    (h311 : Nat.minFac (p - 2) = 311) : a (p - 1) = p :=
  conjecture_of_three_hundred_eleven_dvd hp
    (remaining_p_ge_three_hundred_eleven hp hp7 hmod hcomp h311)
    (h311 ▸ Nat.minFac_dvd (p - 2))

lemma remaining_p_ge_three_hundred_seventeen {p : ℕ}
    (hp : p.Prime) (hp7 : 7 ≤ p) (hmod : p % 3 = 1)
    (hcomp : ¬ (p - 2).Prime)
    (h317 : Nat.minFac (p - 2) = 317) : 1586 ≤ p := by
  have hbound := remaining_minFac_mul_add_two_le hp hp7 hmod hcomp
  rw [h317] at hbound
  have h2le : 2 ≤ p := le_trans (by decide : 2 ≤ 7) hp7
  have hnum : 317 * (317 + 2) + 2 = 101125 := by decide
  have : 317 * (317 + 2) + 2 ≤ p - 2 + 2 := Nat.add_le_add_right hbound 2
  rw [hnum, Nat.sub_add_cancel h2le] at this
  exact le_trans (by decide : 1586 ≤ 101125) this

/-- Remaining McEachen if `lpf(p-2) = 317`. The injector is `k = 5`. -/
theorem conjecture_of_minFac_three_hundred_seventeen {p : ℕ}
    (hp : p.Prime) (hp7 : 7 ≤ p) (hmod : p % 3 = 1)
    (hcomp : ¬ (p - 2).Prime)
    (h317 : Nat.minFac (p - 2) = 317) : a (p - 1) = p :=
  conjecture_of_three_hundred_seventeen_dvd hp
    (remaining_p_ge_three_hundred_seventeen hp hp7 hmod hcomp h317)
    (h317 ▸ Nat.minFac_dvd (p - 2))

lemma remaining_p_ge_three_hundred_thirty_one {p : ℕ}
    (hp : p.Prime) (hp7 : 7 ≤ p) (hmod : p % 3 = 1)
    (hcomp : ¬ (p - 2).Prime)
    (h331 : Nat.minFac (p - 2) = 331) : 6290 ≤ p := by
  have hbound := remaining_minFac_mul_add_two_le hp hp7 hmod hcomp
  rw [h331] at hbound
  have h2le : 2 ≤ p := le_trans (by decide : 2 ≤ 7) hp7
  have hnum : 331 * (331 + 2) + 2 = 110225 := by decide
  have : 331 * (331 + 2) + 2 ≤ p - 2 + 2 := Nat.add_le_add_right hbound 2
  rw [hnum, Nat.sub_add_cancel h2le] at this
  exact le_trans (by decide : 6290 ≤ 110225) this

/-- Remaining McEachen if `lpf(p-2) = 331`. The injector is `k = 19`. -/
theorem conjecture_of_minFac_three_hundred_thirty_one {p : ℕ}
    (hp : p.Prime) (hp7 : 7 ≤ p) (hmod : p % 3 = 1)
    (hcomp : ¬ (p - 2).Prime)
    (h331 : Nat.minFac (p - 2) = 331) : a (p - 1) = p :=
  conjecture_of_three_hundred_thirty_one_dvd hp
    (remaining_p_ge_three_hundred_thirty_one hp hp7 hmod hcomp h331)
    (h331 ▸ Nat.minFac_dvd (p - 2))

lemma remaining_p_ge_three_hundred_thirty_seven {p : ℕ}
    (hp : p.Prime) (hp7 : 7 ≤ p) (hmod : p % 3 = 1)
    (hcomp : ¬ (p - 2).Prime)
    (h337 : Nat.minFac (p - 2) = 337) : 2360 ≤ p := by
  have hbound := remaining_minFac_mul_add_two_le hp hp7 hmod hcomp
  rw [h337] at hbound
  have h2le : 2 ≤ p := le_trans (by decide : 2 ≤ 7) hp7
  have hnum : 337 * (337 + 2) + 2 = 114245 := by decide
  have : 337 * (337 + 2) + 2 ≤ p - 2 + 2 := Nat.add_le_add_right hbound 2
  rw [hnum, Nat.sub_add_cancel h2le] at this
  exact le_trans (by decide : 2360 ≤ 114245) this

/-- Remaining McEachen if `lpf(p-2) = 337`. The injector is `k = 7`. -/
theorem conjecture_of_minFac_three_hundred_thirty_seven {p : ℕ}
    (hp : p.Prime) (hp7 : 7 ≤ p) (hmod : p % 3 = 1)
    (hcomp : ¬ (p - 2).Prime)
    (h337 : Nat.minFac (p - 2) = 337) : a (p - 1) = p :=
  conjecture_of_three_hundred_thirty_seven_dvd hp
    (remaining_p_ge_three_hundred_thirty_seven hp hp7 hmod hcomp h337)
    (h337 ▸ Nat.minFac_dvd (p - 2))

lemma remaining_p_ge_three_hundred_forty_seven {p : ℕ}
    (hp : p.Prime) (hp7 : 7 ≤ p) (hmod : p % 3 = 1)
    (hcomp : ¬ (p - 2).Prime)
    (h347 : Nat.minFac (p - 2) = 347) : 1736 ≤ p := by
  have hbound := remaining_minFac_mul_add_two_le hp hp7 hmod hcomp
  rw [h347] at hbound
  have h2le : 2 ≤ p := le_trans (by decide : 2 ≤ 7) hp7
  have hnum : 347 * (347 + 2) + 2 = 121105 := by decide
  have : 347 * (347 + 2) + 2 ≤ p - 2 + 2 := Nat.add_le_add_right hbound 2
  rw [hnum, Nat.sub_add_cancel h2le] at this
  exact le_trans (by decide : 1736 ≤ 121105) this

/-- Remaining McEachen if `lpf(p-2) = 347`. The injector is `k = 5`. -/
theorem conjecture_of_minFac_three_hundred_forty_seven {p : ℕ}
    (hp : p.Prime) (hp7 : 7 ≤ p) (hmod : p % 3 = 1)
    (hcomp : ¬ (p - 2).Prime)
    (h347 : Nat.minFac (p - 2) = 347) : a (p - 1) = p :=
  conjecture_of_three_hundred_forty_seven_dvd hp
    (remaining_p_ge_three_hundred_forty_seven hp hp7 hmod hcomp h347)
    (h347 ▸ Nat.minFac_dvd (p - 2))

lemma remaining_p_ge_three_hundred_fifty_three {p : ℕ}
    (hp : p.Prime) (hp7 : 7 ≤ p) (hmod : p % 3 = 1)
    (hcomp : ¬ (p - 2).Prime)
    (h353 : Nat.minFac (p - 2) = 353) : 3884 ≤ p := by
  have hbound := remaining_minFac_mul_add_two_le hp hp7 hmod hcomp
  rw [h353] at hbound
  have h2le : 2 ≤ p := le_trans (by decide : 2 ≤ 7) hp7
  have hnum : 353 * (353 + 2) + 2 = 125317 := by decide
  have : 353 * (353 + 2) + 2 ≤ p - 2 + 2 := Nat.add_le_add_right hbound 2
  rw [hnum, Nat.sub_add_cancel h2le] at this
  exact le_trans (by decide : 3884 ≤ 125317) this

/-- Remaining McEachen if `lpf(p-2) = 353`. The injector is `k = 11`. -/
theorem conjecture_of_minFac_three_hundred_fifty_three {p : ℕ}
    (hp : p.Prime) (hp7 : 7 ≤ p) (hmod : p % 3 = 1)
    (hcomp : ¬ (p - 2).Prime)
    (h353 : Nat.minFac (p - 2) = 353) : a (p - 1) = p :=
  conjecture_of_three_hundred_fifty_three_dvd hp
    (remaining_p_ge_three_hundred_fifty_three hp hp7 hmod hcomp h353)
    (h353 ▸ Nat.minFac_dvd (p - 2))

lemma remaining_p_ge_three_hundred_fifty_nine {p : ℕ}
    (hp : p.Prime) (hp7 : 7 ≤ p) (hmod : p % 3 = 1)
    (hcomp : ¬ (p - 2).Prime)
    (h359 : Nat.minFac (p - 2) = 359) : 3950 ≤ p := by
  have hbound := remaining_minFac_mul_add_two_le hp hp7 hmod hcomp
  rw [h359] at hbound
  have h2le : 2 ≤ p := le_trans (by decide : 2 ≤ 7) hp7
  have hnum : 359 * (359 + 2) + 2 = 129601 := by decide
  have : 359 * (359 + 2) + 2 ≤ p - 2 + 2 := Nat.add_le_add_right hbound 2
  rw [hnum, Nat.sub_add_cancel h2le] at this
  exact le_trans (by decide : 3950 ≤ 129601) this

/-- Remaining McEachen if `lpf(p-2) = 359`. The injector is `k = 11`. -/
theorem conjecture_of_minFac_three_hundred_fifty_nine {p : ℕ}
    (hp : p.Prime) (hp7 : 7 ≤ p) (hmod : p % 3 = 1)
    (hcomp : ¬ (p - 2).Prime)
    (h359 : Nat.minFac (p - 2) = 359) : a (p - 1) = p :=
  conjecture_of_three_hundred_fifty_nine_dvd hp
    (remaining_p_ge_three_hundred_fifty_nine hp hp7 hmod hcomp h359)
    (h359 ▸ Nat.minFac_dvd (p - 2))

lemma remaining_p_ge_three_hundred_sixty_seven {p : ℕ}
    (hp : p.Prime) (hp7 : 7 ≤ p) (hmod : p % 3 = 1)
    (hcomp : ¬ (p - 2).Prime)
    (h367 : Nat.minFac (p - 2) = 367) : 6974 ≤ p := by
  have hbound := remaining_minFac_mul_add_two_le hp hp7 hmod hcomp
  rw [h367] at hbound
  have h2le : 2 ≤ p := le_trans (by decide : 2 ≤ 7) hp7
  have hnum : 367 * (367 + 2) + 2 = 135425 := by decide
  have : 367 * (367 + 2) + 2 ≤ p - 2 + 2 := Nat.add_le_add_right hbound 2
  rw [hnum, Nat.sub_add_cancel h2le] at this
  exact le_trans (by decide : 6974 ≤ 135425) this

/-- Remaining McEachen if `lpf(p-2) = 367`. The injector is `k = 19`. -/
theorem conjecture_of_minFac_three_hundred_sixty_seven {p : ℕ}
    (hp : p.Prime) (hp7 : 7 ≤ p) (hmod : p % 3 = 1)
    (hcomp : ¬ (p - 2).Prime)
    (h367 : Nat.minFac (p - 2) = 367) : a (p - 1) = p :=
  conjecture_of_three_hundred_sixty_seven_dvd hp
    (remaining_p_ge_three_hundred_sixty_seven hp hp7 hmod hcomp h367)
    (h367 ▸ Nat.minFac_dvd (p - 2))

lemma remaining_p_ge_three_hundred_seventy_three {p : ℕ}
    (hp : p.Prime) (hp7 : 7 ≤ p) (hmod : p % 3 = 1)
    (hcomp : ¬ (p - 2).Prime)
    (h373 : Nat.minFac (p - 2) = 373) : 2612 ≤ p := by
  have hbound := remaining_minFac_mul_add_two_le hp hp7 hmod hcomp
  rw [h373] at hbound
  have h2le : 2 ≤ p := le_trans (by decide : 2 ≤ 7) hp7
  have hnum : 373 * (373 + 2) + 2 = 139877 := by decide
  have : 373 * (373 + 2) + 2 ≤ p - 2 + 2 := Nat.add_le_add_right hbound 2
  rw [hnum, Nat.sub_add_cancel h2le] at this
  exact le_trans (by decide : 2612 ≤ 139877) this

/-- Remaining McEachen if `lpf(p-2) = 373`. The injector is `k = 7`. -/
theorem conjecture_of_minFac_three_hundred_seventy_three {p : ℕ}
    (hp : p.Prime) (hp7 : 7 ≤ p) (hmod : p % 3 = 1)
    (hcomp : ¬ (p - 2).Prime)
    (h373 : Nat.minFac (p - 2) = 373) : a (p - 1) = p :=
  conjecture_of_three_hundred_seventy_three_dvd hp
    (remaining_p_ge_three_hundred_seventy_three hp hp7 hmod hcomp h373)
    (h373 ▸ Nat.minFac_dvd (p - 2))

lemma remaining_p_ge_three_hundred_seventy_nine {p : ℕ}
    (hp : p.Prime) (hp7 : 7 ≤ p) (hmod : p % 3 = 1)
    (hcomp : ¬ (p - 2).Prime)
    (h379 : Nat.minFac (p - 2) = 379) : 9476 ≤ p := by
  have hbound := remaining_minFac_mul_add_two_le hp hp7 hmod hcomp
  rw [h379] at hbound
  have h2le : 2 ≤ p := le_trans (by decide : 2 ≤ 7) hp7
  have hnum : 379 * (379 + 2) + 2 = 144401 := by decide
  have : 379 * (379 + 2) + 2 ≤ p - 2 + 2 := Nat.add_le_add_right hbound 2
  rw [hnum, Nat.sub_add_cancel h2le] at this
  exact le_trans (by decide : 9476 ≤ 144401) this

/-- Remaining McEachen if `lpf(p-2) = 379`. The injector is `k = 25`. -/
theorem conjecture_of_minFac_three_hundred_seventy_nine {p : ℕ}
    (hp : p.Prime) (hp7 : 7 ≤ p) (hmod : p % 3 = 1)
    (hcomp : ¬ (p - 2).Prime)
    (h379 : Nat.minFac (p - 2) = 379) : a (p - 1) = p :=
  conjecture_of_three_hundred_seventy_nine_dvd hp
    (remaining_p_ge_three_hundred_seventy_nine hp hp7 hmod hcomp h379)
    (h379 ▸ Nat.minFac_dvd (p - 2))

lemma remaining_p_ge_three_hundred_eighty_three {p : ℕ}
    (hp : p.Prime) (hp7 : 7 ≤ p) (hmod : p % 3 = 1)
    (hcomp : ¬ (p - 2).Prime)
    (h383 : Nat.minFac (p - 2) = 383) : 1916 ≤ p := by
  have hbound := remaining_minFac_mul_add_two_le hp hp7 hmod hcomp
  rw [h383] at hbound
  have h2le : 2 ≤ p := le_trans (by decide : 2 ≤ 7) hp7
  have hnum : 383 * (383 + 2) + 2 = 147457 := by decide
  have : 383 * (383 + 2) + 2 ≤ p - 2 + 2 := Nat.add_le_add_right hbound 2
  rw [hnum, Nat.sub_add_cancel h2le] at this
  exact le_trans (by decide : 1916 ≤ 147457) this

/-- Remaining McEachen if `lpf(p-2) = 383`. The injector is `k = 5`. -/
theorem conjecture_of_minFac_three_hundred_eighty_three {p : ℕ}
    (hp : p.Prime) (hp7 : 7 ≤ p) (hmod : p % 3 = 1)
    (hcomp : ¬ (p - 2).Prime)
    (h383 : Nat.minFac (p - 2) = 383) : a (p - 1) = p :=
  conjecture_of_three_hundred_eighty_three_dvd hp
    (remaining_p_ge_three_hundred_eighty_three hp hp7 hmod hcomp h383)
    (h383 ▸ Nat.minFac_dvd (p - 2))

/-- Remaining McEachen if `5·lpf(p-2)-2` is prime. For `lpf ≡ 2 (mod 3)`
this is the first remaining injector and always fits in the square window.
If `lpf ≡ 1 (mod 3)` then `3 ∣ 5q-2`, so the hypothesis fails. -/
theorem conjecture_of_minFac_five {p : ℕ} (hp : p.Prime) (hp7 : 7 ≤ p)
    (hmod : p % 3 = 1) (hcomp : ¬ (p - 2).Prime)
    (hpr : (5 * Nat.minFac (p - 2) - 2).Prime) : a (p - 1) = p := by
  have hq5 := remaining_minFac_ge_five hp hp7 hmod
  have hne1 : p - 2 ≠ 1 := by
    intro h
    have h2le : 2 ≤ p := le_trans (by decide : 2 ≤ 7) hp7
    have hcancel := Nat.sub_add_cancel h2le
    rw [h] at hcancel
    have hp3 : p = 3 := hcancel.symm
    exact Nat.ne_of_lt (lt_of_lt_of_le (by decide : 3 < 7) hp7) hp3.symm
  have hminp : (Nat.minFac (p - 2)).Prime := Nat.minFac_prime hne1
  have hmod3 : (5 * Nat.minFac (p - 2) - 2) % 3 = 2 := by
    have hcases : Nat.minFac (p - 2) % 3 = 0 ∨
        Nat.minFac (p - 2) % 3 = 1 ∨ Nat.minFac (p - 2) % 3 = 2 := by omega
    rcases hcases with h0 | h1 | h2
    · have h3 : 3 ∣ Nat.minFac (p - 2) := Nat.dvd_of_mod_eq_zero h0
      have heq : Nat.minFac (p - 2) = 3 :=
        ((Nat.prime_dvd_prime_iff_eq Nat.prime_three hminp).1 h3).symm
      exact False.elim (Nat.ne_of_lt (lt_of_lt_of_le (by decide : 3 < 5) hq5) heq.symm)
    · have hmul : (5 * Nat.minFac (p - 2)) % 3 = 2 := by
        rw [Nat.mul_mod]
        have : (5 : ℕ) % 3 = 2 := by decide
        rw [this, h1]
      have hrep : 5 * Nat.minFac (p - 2) =
          3 * (5 * Nat.minFac (p - 2) / 3) + 2 := by
        have := (Nat.div_add_mod (5 * Nat.minFac (p - 2)) 3).symm
        rwa [hmul] at this
      have h0 : (5 * Nat.minFac (p - 2) - 2) % 3 = 0 := by omega
      have h3d : 3 ∣ 5 * Nat.minFac (p - 2) - 2 := Nat.dvd_of_mod_eq_zero h0
      have hgt : 3 < 5 * Nat.minFac (p - 2) - 2 := by
        have : 25 ≤ 5 * Nat.minFac (p - 2) := Nat.mul_le_mul_left 5 hq5
        exact lt_of_lt_of_le (by decide : 3 < 23) (Nat.sub_le_sub_right this 2)
      have heq : 5 * Nat.minFac (p - 2) - 2 = 3 :=
        ((Nat.prime_dvd_prime_iff_eq Nat.prime_three hpr).1 h3d).symm
      exact False.elim (Nat.ne_of_lt hgt heq.symm)
    · exact five_mul_sub_two_mod_three h2
        (le_trans (by decide : 2 ≤ 25) (Nat.mul_le_mul_left 5 hq5))
  exact conjecture_of_minFac_entered hp hp7 hmod hcomp
    (q_dvd_x_square_window_of_five hpr hq5 hmod3)

/-- Remaining McEachen if `11·lpf(p-2)-2` is prime and that least factor is
at least `11`. Usable when `lpf ≡ 2 (mod 3)`. -/
theorem conjecture_of_minFac_eleven {p : ℕ} (hp : p.Prime) (hp7 : 7 ≤ p)
    (hmod : p % 3 = 1) (hcomp : ¬ (p - 2).Prime)
    (h11 : 11 ≤ Nat.minFac (p - 2))
    (hpr : (11 * Nat.minFac (p - 2) - 2).Prime) : a (p - 1) = p := by
  have hne1 : p - 2 ≠ 1 := by
    intro h
    have h2le : 2 ≤ p := le_trans (by decide : 2 ≤ 7) hp7
    have hcancel := Nat.sub_add_cancel h2le
    rw [h] at hcancel
    have hp3 : p = 3 := hcancel.symm
    exact Nat.ne_of_lt (lt_of_lt_of_le (by decide : 3 < 7) hp7) hp3.symm
  have hminp : (Nat.minFac (p - 2)).Prime := Nat.minFac_prime hne1
  have hmod3 : (11 * Nat.minFac (p - 2) - 2) % 3 = 2 := by
    have hcases : Nat.minFac (p - 2) % 3 = 0 ∨
        Nat.minFac (p - 2) % 3 = 1 ∨ Nat.minFac (p - 2) % 3 = 2 := by omega
    rcases hcases with h0 | h1 | h2
    · have h3 : 3 ∣ Nat.minFac (p - 2) := Nat.dvd_of_mod_eq_zero h0
      have heq : Nat.minFac (p - 2) = 3 :=
        ((Nat.prime_dvd_prime_iff_eq Nat.prime_three hminp).1 h3).symm
      exact False.elim (Nat.ne_of_lt (lt_of_lt_of_le (by decide : 3 < 11) h11) heq.symm)
    · have hmul : (11 * Nat.minFac (p - 2)) % 3 = 2 := by
        rw [Nat.mul_mod]
        have : (11 : ℕ) % 3 = 2 := by decide
        rw [this, h1]
      have hrep : 11 * Nat.minFac (p - 2) =
          3 * (11 * Nat.minFac (p - 2) / 3) + 2 := by
        have := (Nat.div_add_mod (11 * Nat.minFac (p - 2)) 3).symm
        rwa [hmul] at this
      have h0 : (11 * Nat.minFac (p - 2) - 2) % 3 = 0 := by omega
      have h3d : 3 ∣ 11 * Nat.minFac (p - 2) - 2 := Nat.dvd_of_mod_eq_zero h0
      have hgt : 3 < 11 * Nat.minFac (p - 2) - 2 := by
        have : 121 ≤ 11 * Nat.minFac (p - 2) := Nat.mul_le_mul_left 11 h11
        exact lt_of_lt_of_le (by decide : 3 < 119) (Nat.sub_le_sub_right this 2)
      have heq : 11 * Nat.minFac (p - 2) - 2 = 3 :=
        ((Nat.prime_dvd_prime_iff_eq Nat.prime_three hpr).1 h3d).symm
      exact False.elim (Nat.ne_of_lt hgt heq.symm)
    · exact eleven_mul_sub_two_mod_three h2
        (le_trans (by decide : 2 ≤ 121) (Nat.mul_le_mul_left 11 h11))
  exact conjecture_of_minFac_entered hp hp7 hmod hcomp
    (q_dvd_x_square_window_of_eleven hpr h11 hmod3)

/-- Remaining McEachen if `13·lpf(p-2)-2` is prime and that least factor is
at least `13`. Usable when `lpf ≡ 1 (mod 3)`. -/
theorem conjecture_of_minFac_thirteen {p : ℕ} (hp : p.Prime) (hp7 : 7 ≤ p)
    (hmod : p % 3 = 1) (hcomp : ¬ (p - 2).Prime)
    (h13 : 13 ≤ Nat.minFac (p - 2))
    (hpr : (13 * Nat.minFac (p - 2) - 2).Prime) : a (p - 1) = p := by
  have hne1 : p - 2 ≠ 1 := by
    intro h
    have h2le : 2 ≤ p := le_trans (by decide : 2 ≤ 7) hp7
    have hcancel := Nat.sub_add_cancel h2le
    rw [h] at hcancel
    have hp3 : p = 3 := hcancel.symm
    exact Nat.ne_of_lt (lt_of_lt_of_le (by decide : 3 < 7) hp7) hp3.symm
  have hminp : (Nat.minFac (p - 2)).Prime := Nat.minFac_prime hne1
  have hmod3 : (13 * Nat.minFac (p - 2) - 2) % 3 = 2 := by
    have hcases : Nat.minFac (p - 2) % 3 = 0 ∨
        Nat.minFac (p - 2) % 3 = 1 ∨ Nat.minFac (p - 2) % 3 = 2 := by omega
    rcases hcases with h0 | h1 | h2
    · have h3 : 3 ∣ Nat.minFac (p - 2) := Nat.dvd_of_mod_eq_zero h0
      have heq : Nat.minFac (p - 2) = 3 :=
        ((Nat.prime_dvd_prime_iff_eq Nat.prime_three hminp).1 h3).symm
      exact False.elim (Nat.ne_of_lt (lt_of_lt_of_le (by decide : 3 < 13) h13) heq.symm)
    · exact thirteen_mul_sub_two_mod_three h1
        (le_trans (by decide : 2 ≤ 169) (Nat.mul_le_mul_left 13 h13))
    · have hmul : (13 * Nat.minFac (p - 2)) % 3 = 2 := by
        rw [Nat.mul_mod]
        have : (13 : ℕ) % 3 = 1 := by decide
        rw [this, h2]
      have hrep : 13 * Nat.minFac (p - 2) =
          3 * (13 * Nat.minFac (p - 2) / 3) + 2 := by
        have := (Nat.div_add_mod (13 * Nat.minFac (p - 2)) 3).symm
        rwa [hmul] at this
      have h0 : (13 * Nat.minFac (p - 2) - 2) % 3 = 0 := by omega
      have h3d : 3 ∣ 13 * Nat.minFac (p - 2) - 2 := Nat.dvd_of_mod_eq_zero h0
      have hgt : 3 < 13 * Nat.minFac (p - 2) - 2 := by
        have : 169 ≤ 13 * Nat.minFac (p - 2) := Nat.mul_le_mul_left 13 h13
        exact lt_of_lt_of_le (by decide : 3 < 167) (Nat.sub_le_sub_right this 2)
      have heq : 13 * Nat.minFac (p - 2) - 2 = 3 :=
        ((Nat.prime_dvd_prime_iff_eq Nat.prime_three hpr).1 h3d).symm
      exact False.elim (Nat.ne_of_lt hgt heq.symm)
  exact conjecture_of_minFac_entered hp hp7 hmod hcomp
    (q_dvd_x_square_window_of_thirteen hpr h13 hmod3)

/-- If `qs ≡ 2 (mod 3)`, the factors are `1` and `2` modulo `3` in either order. -/
lemma mul_mod_three_eq_two {q s : ℕ} (h : (q * s) % 3 = 2) :
    (q % 3 = 1 ∧ s % 3 = 2) ∨ (q % 3 = 2 ∧ s % 3 = 1) := by
  have hmul : (q % 3 * (s % 3)) % 3 = 2 := by
    rwa [← Nat.mul_mod]
  have hql : q % 3 < 3 := Nat.mod_lt q (by decide)
  have hsl : s % 3 < 3 := Nat.mod_lt s (by decide)
  revert hmul
  interval_cases q % 3
  · intro hmul
    rw [Nat.zero_mul, Nat.zero_mod] at hmul
    exact False.elim ((by decide : ¬ (0 : ℕ) = 2) hmul)
  · intro hmul
    revert hmul
    interval_cases s % 3
    · intro hmul
      change (1 * 0) % 3 = 2 at hmul
      exact False.elim ((by decide : ¬ (0 : ℕ) = 2) hmul)
    · intro hmul
      change (1 * 1) % 3 = 2 at hmul
      exact False.elim ((by decide : ¬ (1 : ℕ) = 2) hmul)
    · intro _hmul
      exact Or.inl ⟨rfl, rfl⟩
  · intro hmul
    revert hmul
    interval_cases s % 3
    · intro hmul
      change (2 * 0) % 3 = 2 at hmul
      exact False.elim ((by decide : ¬ (0 : ℕ) = 2) hmul)
    · intro _hmul
      exact Or.inr ⟨rfl, rfl⟩
    · intro hmul
      change (2 * 2) % 3 = 2 at hmul
      exact False.elim ((by decide : ¬ (1 : ℕ) = 2) hmul)

lemma not_prime_five_mul_sub_two_of_mod_one {s : ℕ} (hs2 : 2 ≤ s)
    (hs1 : s % 3 = 1) : ¬ (5 * s - 2).Prime := by
  have hmul : (5 * s) % 3 = 2 := by
    have h5 : (5 : ℕ) % 3 = 2 := by decide
    calc
      (5 * s) % 3 = (5 % 3 * (s % 3)) % 3 := Nat.mul_mod _ _ 3
      _ = (2 * 1) % 3 := by rw [h5, hs1]
      _ = 2 := by decide
  have hrep : 5 * s = 3 * (5 * s / 3) + 2 := by
    have := (Nat.div_add_mod (5 * s) 3).symm
    rwa [hmul] at this
  have hsub : 5 * s - 2 = 3 * (5 * s / 3) := by
    conv_lhs => rw [hrep]
    exact Nat.add_sub_cancel _ 2
  have h3d : 3 ∣ 5 * s - 2 := by
    rw [hsub]
    exact Nat.dvd_mul_right _ _
  have hgt : 3 < 5 * s - 2 := by
    have : 10 ≤ 5 * s := Nat.mul_le_mul_left 5 hs2
    exact lt_of_lt_of_le (by decide : 3 < 8) (Nat.sub_le_sub_right this 2)
  intro hpr
  have heq : 5 * s - 2 = 3 :=
    ((Nat.prime_dvd_prime_iff_eq Nat.prime_three hpr).1 h3d).symm
  exact Nat.ne_of_lt hgt heq.symm

lemma not_prime_seven_mul_sub_two_of_mod_two {s : ℕ} (hs2 : 2 ≤ s)
    (hs2mod : s % 3 = 2) : ¬ (7 * s - 2).Prime := by
  have hmul : (7 * s) % 3 = 2 := by
    have h7 : (7 : ℕ) % 3 = 1 := by decide
    calc
      (7 * s) % 3 = (7 % 3 * (s % 3)) % 3 := Nat.mul_mod _ _ 3
      _ = (1 * 2) % 3 := by rw [h7, hs2mod]
      _ = 2 := by decide
  have hrep : 7 * s = 3 * (7 * s / 3) + 2 := by
    have := (Nat.div_add_mod (7 * s) 3).symm
    rwa [hmul] at this
  have hsub : 7 * s - 2 = 3 * (7 * s / 3) := by
    conv_lhs => rw [hrep]
    exact Nat.add_sub_cancel _ 2
  have h3d : 3 ∣ 7 * s - 2 := by
    rw [hsub]
    exact Nat.dvd_mul_right _ _
  have hgt : 3 < 7 * s - 2 := by
    have : 14 ≤ 7 * s := Nat.mul_le_mul_left 7 hs2
    exact lt_of_lt_of_le (by decide : 3 < 12) (Nat.sub_le_sub_right this 2)
  intro hpr
  have heq : 7 * s - 2 = 3 :=
    ((Nat.prime_dvd_prime_iff_eq Nat.prime_three hpr).1 h3d).symm
  exact Nat.ne_of_lt hgt heq.symm

lemma eq_five_of_prime_ge_five_lt_seven {q : ℕ} (hq : q.Prime) (h5 : 5 ≤ q)
    (h7 : q < 7) : q = 5 := by
  have hle6 : q ≤ 6 := Nat.lt_succ_iff.mp h7
  interval_cases q
  · rfl
  · exact ((by decide : ¬ Nat.Prime 6) hq).elim

/-- Remaining McEachen if one of the first aligned injectors of `lpf(p-2)`
or of the complementary cofactor is prime. This is a proper subfamily. -/
theorem conjecture_of_paired_injectors {p : ℕ} (hp : p.Prime) (hp7 : 7 ≤ p)
    (hmod : p % 3 = 1) (hcomp : ¬ (p - 2).Prime)
    (hor : (5 * Nat.minFac (p - 2) - 2).Prime ∨
      (7 * Nat.minFac (p - 2) - 2).Prime ∨
      (5 * ((p - 2) / Nat.minFac (p - 2)) - 2).Prime ∨
      (7 * ((p - 2) / Nat.minFac (p - 2)) - 2).Prime) :
    a (p - 1) = p := by
  have hq5 := remaining_minFac_ge_five hp hp7 hmod
  have hne1 : p - 2 ≠ 1 := by
    intro h
    have h2le : 2 ≤ p := le_trans (by decide : 2 ≤ 7) hp7
    have hcancel := Nat.sub_add_cancel h2le
    rw [h] at hcancel
    have hp3 : p = 3 := hcancel.symm
    exact Nat.ne_of_lt (lt_of_lt_of_le (by decide : 3 < 7) hp7) hp3.symm
  have hminp : (Nat.minFac (p - 2)).Prime := Nat.minFac_prime hne1
  have hd : Nat.minFac (p - 2) ∣ p - 2 := Nat.minFac_dvd _
  have hqs : p - 2 = Nat.minFac (p - 2) * ((p - 2) / Nat.minFac (p - 2)) :=
    (Nat.mul_div_cancel' hd).symm
  have hs1 : 1 < (p - 2) / Nat.minFac (p - 2) := by
    have hne0 : (p - 2) / Nat.minFac (p - 2) ≠ 0 := by
      intro h
      rw [h, mul_zero] at hqs
      have h2le : 2 ≤ p := le_trans (by decide : 2 ≤ 7) hp7
      have : p = 2 := by
        have := Nat.sub_add_cancel h2le
        rw [hqs] at this
        exact this.symm
      exact Nat.ne_of_lt (lt_of_lt_of_le (by decide : 2 < 7) hp7) this.symm
    have hge1 : 1 ≤ (p - 2) / Nat.minFac (p - 2) :=
      Nat.pos_iff_ne_zero.mpr hne0
    have hne1s : (p - 2) / Nat.minFac (p - 2) ≠ 1 := by
      intro h
      rw [h, mul_one] at hqs
      exact hcomp (hqs ▸ hminp)
    exact lt_of_le_of_ne hge1 hne1s.symm
  have hs2 : 2 ≤ (p - 2) / Nat.minFac (p - 2) := hs1
  have hpm : (p - 2) % 3 = 2 :=
    p_sub_two_mod (le_trans (by decide : 4 ≤ 7) hp7) hmod
  have hqsmod : (Nat.minFac (p - 2) * ((p - 2) / Nat.minFac (p - 2))) % 3 = 2 := by
    rwa [← hqs]
  have hsplit := mul_mod_three_eq_two hqsmod
  rcases hor with h5 | h7 | h5s | h7s
  · exact conjecture_of_minFac_five hp hp7 hmod hcomp h5
  · exact conjecture_of_minFac_seven hp hp7 hmod hcomp h7
  · have hsmod : ((p - 2) / Nat.minFac (p - 2)) % 3 = 2 := by
      rcases hsplit with h12 | h21
      · exact h12.2
      · exact False.elim (not_prime_five_mul_sub_two_of_mod_one hs2 h21.2 h5s)
    exact conjecture_of_cofactor_five hp hp7 hqs hq5 hs1 hsmod h5s
  · by_cases h7q : 7 ≤ Nat.minFac (p - 2)
    · have hsmod : ((p - 2) / Nat.minFac (p - 2)) % 3 = 1 := by
        rcases hsplit with h12 | h21
        · exact False.elim (not_prime_seven_mul_sub_two_of_mod_two hs2 h12.2 h7s)
        · exact h21.2
      exact conjecture_of_cofactor_seven hp hp7 hqs h7q hs1 hsmod h7s
    · have hlt : Nat.minFac (p - 2) < 7 := Nat.not_le.mp h7q
      have hqeq : Nat.minFac (p - 2) = 5 :=
        eq_five_of_prime_ge_five_lt_seven hminp hq5 hlt
      have hd5 : 5 ∣ p - 2 := by rwa [hqeq] at hd
      exact conjecture_of_five_dvd hp hp7 hd5

/-- The frozen McEachen statement, assuming every prime `q ≥ 5` divides
`x` by the square-window index `q(q+2)-1`. Larger twins already satisfy
that bound via `larger_twin_dvd_x`. This does not prove the window. -/
theorem conjecture_of_square_window
    (hwin : ∀ q, q.Prime → 5 ≤ q → q ∣ x (q * (q + 2) - 1))
    {p : ℕ} (hp : p.Prime) (hp_twin : ¬ (p - 2).Prime) : a (p - 1) = p := by
  have hmodlt : p % 3 < 3 := Nat.mod_lt p (by decide)
  interval_cases hmod : p % 3
  · have h3p : 3 ∣ p := Nat.dvd_of_mod_eq_zero hmod
    have hp3 : p = 3 :=
      ((Nat.prime_dvd_prime_iff_eq Nat.prime_three hp).1 h3p).symm
    subst hp3
    exact conjecture_three hp_twin
  · have hne2 : p ≠ 2 := by
      intro h
      subst h
      exact absurd hmod (by decide)
    have hgt2 : 2 < p := lt_of_le_of_ne hp.two_le hne2.symm
    have hge3 : 3 ≤ p := Nat.succ_le_of_lt hgt2
    have hne3 : p ≠ 3 := by
      intro h
      subst h
      exact absurd hmod (by decide)
    have hgt3 : 3 < p := lt_of_le_of_ne hge3 hne3.symm
    have hge4 : 4 ≤ p := Nat.succ_le_of_lt hgt3
    have hne4 : p ≠ 4 := by
      intro h
      subst h
      exact (by decide : ¬ Nat.Prime 4) hp
    have hgt4 : 4 < p := lt_of_le_of_ne hge4 hne4.symm
    have hge5 : 5 ≤ p := Nat.succ_le_of_lt hgt4
    have hne5 : p ≠ 5 := by
      intro h
      subst h
      exact absurd hmod (by decide)
    have hgt5 : 5 < p := lt_of_le_of_ne hge5 hne5.symm
    have hge6 : 6 ≤ p := Nat.succ_le_of_lt hgt5
    have hne6 : p ≠ 6 := by
      intro h
      subst h
      exact (by decide : ¬ Nat.Prime 6) hp
    have hp7 : 7 ≤ p := Nat.succ_le_of_lt (lt_of_le_of_ne hge6 hne6.symm)
    have hne1 : p - 2 ≠ 1 := by
      intro h
      have h2le : 2 ≤ p := le_trans (by decide : 2 ≤ 7) hp7
      have hcancel := Nat.sub_add_cancel h2le
      rw [h] at hcancel
      have hp3 : p = 3 := hcancel.symm
      exact Nat.ne_of_lt (lt_of_lt_of_le (by decide : 3 < 7) hp7) hp3.symm
    have hminp : (Nat.minFac (p - 2)).Prime := Nat.minFac_prime hne1
    have h5 := remaining_minFac_ge_five hp hp7 hmod
    exact conjecture_of_minFac_entered hp hp7 hmod hp_twin (hwin _ hminp h5)
  · by_cases h7 : 7 ≤ p
    · exact conjecture_of_mod_three hp h7 hmod
    · have hle6 : p ≤ 6 := Nat.lt_succ_iff.mp (Nat.not_le.mp h7)
      have h2le := hp.two_le
      interval_cases p
      · exact conjecture_two hp_twin
      · exact absurd hmod (by decide)
      · exact False.elim ((by decide : ¬ Nat.Prime 4) hp)
      · exact (hp_twin Nat.prime_three).elim
      · exact False.elim ((by decide : ¬ Nat.Prime 6) hp)

/-- Cloitre Corollary 6.6 as an implication: `C₁` on positive indices implies
McEachen. This does not assume `C₁`, and it is not a resolution. -/
theorem conjecture_of_C1
    (hC1 : ∀ n, 0 < n → a n = 1 ∨ (a n).Prime)
    {p : ℕ} (hp : p.Prime) (hp_twin : ¬ (p - 2).Prime) : a (p - 1) = p := by
  by_cases h2 : p = 2
  · subst h2
    exact conjecture_two hp_twin
  by_cases h3 : p = 3
  · subst h3
    exact conjecture_three hp_twin
  have hgt2 : 2 < p := lt_of_le_of_ne hp.two_le (Ne.symm h2)
  have hge3 : 3 ≤ p := Nat.succ_le_of_lt hgt2
  have hgt3 : 3 < p := lt_of_le_of_ne hge3 (Ne.symm h3)
  have hge4 : 4 ≤ p := Nat.succ_le_of_lt hgt3
  have hne4 : p ≠ 4 := fun h4 => (by decide : ¬ Nat.Prime 4) (h4 ▸ hp)
  have hp5 : 5 ≤ p := Nat.succ_le_of_lt (lt_of_le_of_ne hge4 hne4.symm)
  rcases a_eq_one_or_self hp with h1 | hpval
  · have ha : a (p - 3) = p - 2 :=
      (dvd_x_pred_iff_a hp hp5).1 ((a_eq_one_iff_dvd hp).1 h1)
    have hpos : 0 < p - 3 :=
      Nat.sub_pos_of_lt (lt_of_lt_of_le (by decide : 3 < 5) hp5)
    rcases hC1 (p - 3) hpos with h1' | hpr
    · have hpeq : p - 2 = 1 := ha.symm.trans h1'
      have h2le : 2 ≤ p := le_trans (by decide : 2 ≤ 5) hp5
      exact False.elim (h3 ((Nat.sub_eq_iff_eq_add h2le).1 hpeq))
    · exact False.elim (hp_twin (ha ▸ hpr))
  · exact hpval

lemma larger_twin_dvd_square_window {q : ℕ} (hq : q.Prime) (h13 : 13 ≤ q)
    (htwin : (q - 2).Prime) : q ∣ x (q * (q + 2) - 1) := by
  have hx := larger_twin_dvd_x hq h13 htwin
  have hpos : 0 < q - 1 :=
    Nat.sub_pos_of_lt (lt_of_lt_of_le (by decide : 1 < 13) h13)
  have hle : q - 1 ≤ q * (q + 2) - 1 := by
    have hpos2 : 0 < q + 2 := Nat.add_pos_right q (by decide : 0 < 2)
    have : q ≤ q * (q + 2) := Nat.le_mul_of_pos_right q hpos2
    exact Nat.sub_le_sub_right this 1
  exact hx.trans (x_dvd_of_le hpos hle)

/-- If `n < q²` and no prime `< q` divides `n`, then `n` is prime. -/
lemma prime_of_no_prime_dvd_lt {n q : ℕ} (hn1 : 1 < n) (hnq : n < q * q)
    (h : ∀ p, p.Prime → p < q → ¬ p ∣ n) : n.Prime := by
  by_contra hnpr
  have hpos : 0 < n := Nat.zero_lt_of_lt hn1
  have hsq : n.minFac ^ 2 ≤ n := Nat.minFac_sq_le_self hpos hnpr
  have hminp : n.minFac.Prime := Nat.minFac_prime (Nat.ne_of_gt hn1)
  have hminlt : n.minFac < q := by
    have hmul : n.minFac * n.minFac ≤ n := by rwa [pow_two] at hsq
    have hlt : n.minFac * n.minFac < q * q := lt_of_le_of_lt hmul hnq
    exact Nat.mul_self_lt_mul_self_iff.mp hlt
  exact h n.minFac hminp hminlt (Nat.minFac_dvd n)

/-- A prime injector in the square window, packaged as an existential. -/
lemma q_dvd_x_square_window_of_exists {q : ℕ}
    (hex : ∃ k, (k * q - 2).Prime ∧ 7 ≤ k * q - 2 ∧
      (k * q - 2) % 3 = 2 ∧ k * q - 2 ≤ q * (q + 2) - 1) :
    q ∣ x (q * (q + 2) - 1) := by
  rcases hex with ⟨k, hpr, h7, hmod, hle⟩
  exact q_dvd_x_square_window_of_prime_index hpr h7 hmod hle

/-- For `q ≡ 2 (mod 3)`, a candidate `k ≡ 5 (mod 6)` with `k ≤ q` and no prime
factor `< q` is necessarily a prime injector inside the square window. -/
lemma q_dvd_x_window_of_no_small_factor {k q : ℕ}
    (_hq : q.Prime) (h5 : 5 ≤ q) (hmodq : q % 3 = 2)
    (hk5 : k % 6 = 5) (hkq : k ≤ q)
    (hsmall : ∀ p, p.Prime → p < q → ¬ p ∣ k * q - 2) :
    q ∣ x (q * (q + 2) - 1) := by
  have hkge : 5 ≤ k := k_ge_five_of_mod_six_five hk5
  have hk3 : k % 3 = 2 := k_mod_three_of_six_five hk5
  have hmul : 5 * 5 ≤ k * q := Nat.mul_le_mul hkge h5
  have h2le : 2 ≤ k * q := le_trans (by decide : 2 ≤ 25) hmul
  have hn1 : 1 < k * q - 2 :=
    lt_of_lt_of_le (by decide : 1 < 23) (Nat.sub_le_sub_right hmul 2)
  have hnq : k * q - 2 < q * q :=
    lt_of_lt_of_le (Nat.sub_lt (lt_of_lt_of_le (by decide : 0 < 2) h2le)
      (by decide : 0 < 2)) (Nat.mul_le_mul_right q hkq)
  have hpr : (k * q - 2).Prime := prime_of_no_prime_dvd_lt hn1 hnq hsmall
  have h7 : 7 ≤ k * q - 2 :=
    le_trans (by decide : 7 ≤ 23) (Nat.sub_le_sub_right hmul 2)
  have hmod : (k * q - 2) % 3 = 2 :=
    mul_sub_two_mod_three hk3 hmodq (le_trans (by decide : 4 ≤ 25) hmul)
  have hle : k * q - 2 ≤ q * (q + 2) - 1 := by
    have hle1 : k * q ≤ q * (q + 2) := by
      rw [Nat.mul_comm q]
      exact Nat.mul_le_mul_right q (le_trans hkq (Nat.le_add_right q 2))
    have h1 : k * q - 2 ≤ q * (q + 2) - 2 := Nat.sub_le_sub_right hle1 2
    have h2 : q * (q + 2) - 2 ≤ q * (q + 2) - 1 :=
      Nat.sub_le_sub_left (by decide : 1 ≤ 2) (q * (q + 2))
    exact h1.trans h2
  exact q_dvd_x_square_window_of_prime_index hpr h7 hmod hle

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

lemma remaining_prime_eq_one_hundred_seven {q : ℕ} (hq : q.Prime)
    (h102 : 102 ≤ q) (h107 : q ≤ 107) (hnotwin : ¬ (q - 2).Prime) :
    q = 107 := by
  interval_cases q
  · exact ((by decide : ¬ Nat.Prime 102) hq).elim
  · exact (hnotwin (by decide : Nat.Prime 101)).elim
  · exact ((by decide : ¬ Nat.Prime 104) hq).elim
  · exact ((by decide : ¬ Nat.Prime 105) hq).elim
  · exact ((by decide : ¬ Nat.Prime 106) hq).elim
  · rfl

/-- Remaining McEachen if `lpf(p-2) ≤ 107` or that least factor is a larger twin. -/
theorem conjecture_of_minFac_le_one_hundred_seven_or_twin {p : ℕ} (hp : p.Prime)
    (hp7 : 7 ≤ p) (hmod : p % 3 = 1) (hcomp : ¬ (p - 2).Prime)
    (h : Nat.minFac (p - 2) ≤ 107 ∨ (Nat.minFac (p - 2) - 2).Prime) :
    a (p - 1) = p := by
  have hpr : (Nat.minFac (p - 2)).Prime :=
    Nat.minFac_prime (by omega : p - 2 ≠ 1)
  have hd : Nat.minFac (p - 2) ∣ p - 2 := Nat.minFac_dvd _
  have hbound := remaining_minFac_mul_add_two_le hp hp7 hmod hcomp
  rcases h with h107 | htwin
  · by_cases h101 : Nat.minFac (p - 2) ≤ 101
    · exact conjecture_of_minFac_le_one_hundred_one_or_twin hp hp7 hmod hcomp
        (Or.inl h101)
    · by_cases ht : (Nat.minFac (p - 2) - 2).Prime
      · have h13 : 13 ≤ Nat.minFac (p - 2) := by omega
        exact conjecture_of_larger_twin_dvd hp (by omega) hcomp hpr h13 ht hd
      · have h102 : 102 ≤ Nat.minFac (p - 2) := by omega
        have heq : Nat.minFac (p - 2) = 107 :=
          remaining_prime_eq_one_hundred_seven hpr h102 h107 ht
        have hd107 : 107 ∣ p - 2 := by rwa [heq] at hd
        have hp2462 : 2462 ≤ p := by
          rw [heq] at hbound
          have h2le : 2 ≤ p := le_trans (by decide : 2 ≤ 7) hp7
          have hnum : 107 * (107 + 2) + 2 = 11665 := by decide
          have : 107 * (107 + 2) + 2 ≤ p - 2 + 2 :=
            Nat.add_le_add_right hbound 2
          rw [hnum, Nat.sub_add_cancel h2le] at this
          exact le_trans (by decide : 2462 ≤ 11665) this
        exact conjecture_of_one_hundred_seven_dvd hp hp2462 hd107
  · by_cases h13 : 13 ≤ Nat.minFac (p - 2)
    · exact conjecture_of_larger_twin_dvd hp (by omega) hcomp hpr h13 htwin hd
    · have : Nat.minFac (p - 2) ≤ 29 := by omega
      exact conjecture_of_minFac_le_twenty_nine hp hp7 hmod hcomp this

lemma remaining_prime_le_one_hundred_forty_nine {q : ℕ} (hq : q.Prime)
    (h108 : 108 ≤ q) (h149 : q ≤ 149) (hnotwin : ¬ (q - 2).Prime) :
    q = 113 ∨ q = 127 ∨ q = 131 ∨ q = 137 ∨ q = 149 := by
  interval_cases q
  · exact ((by decide : ¬ Nat.Prime 108) hq).elim
  · exact (hnotwin (by decide : Nat.Prime 107)).elim
  · exact ((by decide : ¬ Nat.Prime 110) hq).elim
  · exact ((by decide : ¬ Nat.Prime 111) hq).elim
  · exact ((by decide : ¬ Nat.Prime 112) hq).elim
  · exact Or.inl rfl
  · exact ((by decide : ¬ Nat.Prime 114) hq).elim
  · exact ((by decide : ¬ Nat.Prime 115) hq).elim
  · exact ((by decide : ¬ Nat.Prime 116) hq).elim
  · exact ((by decide : ¬ Nat.Prime 117) hq).elim
  · exact ((by decide : ¬ Nat.Prime 118) hq).elim
  · exact ((by decide : ¬ Nat.Prime 119) hq).elim
  · exact ((by decide : ¬ Nat.Prime 120) hq).elim
  · exact ((by decide : ¬ Nat.Prime 121) hq).elim
  · exact ((by decide : ¬ Nat.Prime 122) hq).elim
  · exact ((by decide : ¬ Nat.Prime 123) hq).elim
  · exact ((by decide : ¬ Nat.Prime 124) hq).elim
  · exact ((by decide : ¬ Nat.Prime 125) hq).elim
  · exact ((by decide : ¬ Nat.Prime 126) hq).elim
  · exact Or.inr (Or.inl rfl)
  · exact ((by decide : ¬ Nat.Prime 128) hq).elim
  · exact ((by decide : ¬ Nat.Prime 129) hq).elim
  · exact ((by decide : ¬ Nat.Prime 130) hq).elim
  · exact Or.inr (Or.inr (Or.inl rfl))
  · exact ((by decide : ¬ Nat.Prime 132) hq).elim
  · exact ((by decide : ¬ Nat.Prime 133) hq).elim
  · exact ((by decide : ¬ Nat.Prime 134) hq).elim
  · exact ((by decide : ¬ Nat.Prime 135) hq).elim
  · exact ((by decide : ¬ Nat.Prime 136) hq).elim
  · exact Or.inr (Or.inr (Or.inr (Or.inl rfl)))
  · exact ((by decide : ¬ Nat.Prime 138) hq).elim
  · exact (hnotwin (by decide : Nat.Prime 137)).elim
  · exact ((by decide : ¬ Nat.Prime 140) hq).elim
  · exact ((by decide : ¬ Nat.Prime 141) hq).elim
  · exact ((by decide : ¬ Nat.Prime 142) hq).elim
  · exact ((by decide : ¬ Nat.Prime 143) hq).elim
  · exact ((by decide : ¬ Nat.Prime 144) hq).elim
  · exact ((by decide : ¬ Nat.Prime 145) hq).elim
  · exact ((by decide : ¬ Nat.Prime 146) hq).elim
  · exact ((by decide : ¬ Nat.Prime 147) hq).elim
  · exact ((by decide : ¬ Nat.Prime 148) hq).elim
  · exact Or.inr (Or.inr (Or.inr (Or.inr rfl)))

/-- Remaining McEachen if `lpf(p-2) ≤ 149` or that least factor is a larger twin. -/
theorem conjecture_of_minFac_le_one_hundred_forty_nine_or_twin {p : ℕ}
    (hp : p.Prime) (hp7 : 7 ≤ p) (hmod : p % 3 = 1)
    (hcomp : ¬ (p - 2).Prime)
    (h : Nat.minFac (p - 2) ≤ 149 ∨ (Nat.minFac (p - 2) - 2).Prime) :
    a (p - 1) = p := by
  have hpr : (Nat.minFac (p - 2)).Prime :=
    Nat.minFac_prime (ne_of_gt (remaining_p_sub_two_gt_one hp7))
  have hd : Nat.minFac (p - 2) ∣ p - 2 := Nat.minFac_dvd _
  rcases h with h149 | htwin
  · by_cases h107 : Nat.minFac (p - 2) ≤ 107
    · exact conjecture_of_minFac_le_one_hundred_seven_or_twin hp hp7 hmod hcomp
        (Or.inl h107)
    · by_cases ht : (Nat.minFac (p - 2) - 2).Prime
      · have h13 : 13 ≤ Nat.minFac (p - 2) :=
          le_trans (by decide : 13 ≤ 108)
            (Nat.succ_le_of_lt (lt_of_not_ge h107))
        exact conjecture_of_larger_twin_dvd hp (five_le_of_seven_le hp7)
          hcomp hpr h13 ht hd
      · have h108 : 108 ≤ Nat.minFac (p - 2) :=
          Nat.succ_le_of_lt (lt_of_not_ge h107)
        have hcases := remaining_prime_le_one_hundred_forty_nine hpr h108 h149 ht
        rcases hcases with h113 | h127 | h131 | h137 | h149eq
        · exact conjecture_of_minFac_one_hundred_thirteen hp hp7 hmod hcomp h113
        · exact conjecture_of_minFac_one_hundred_twenty_seven hp hp7 hmod hcomp
            h127
        · exact conjecture_of_minFac_one_hundred_thirty_one hp hp7 hmod hcomp
            h131
        · exact conjecture_of_minFac_one_hundred_thirty_seven hp hp7 hmod hcomp
            h137
        · exact conjecture_of_minFac_one_hundred_forty_nine hp hp7 hmod hcomp
            h149eq
  · by_cases h13 : 13 ≤ Nat.minFac (p - 2)
    · exact conjecture_of_larger_twin_dvd hp (five_le_of_seven_le hp7) hcomp
        hpr h13 htwin hd
    · have h12 : Nat.minFac (p - 2) ≤ 12 := Nat.lt_succ_iff.mp (lt_of_not_ge h13)
      exact conjecture_of_minFac_le_twenty_nine hp hp7 hmod hcomp
        (le_trans h12 (by decide : 12 ≤ 29))

lemma remaining_prime_le_one_hundred_seventy_three {q : ℕ} (hq : q.Prime)
    (h150 : 150 ≤ q) (h173 : q ≤ 173) (hnotwin : ¬ (q - 2).Prime) :
    q = 157 ∨ q = 163 ∨ q = 167 ∨ q = 173 := by
  interval_cases q
  · exact ((by norm_num : ¬ Nat.Prime 150) hq).elim
  · exact (hnotwin (by norm_num : Nat.Prime 149)).elim
  · exact ((by norm_num : ¬ Nat.Prime 152) hq).elim
  · exact ((by norm_num : ¬ Nat.Prime 153) hq).elim
  · exact ((by norm_num : ¬ Nat.Prime 154) hq).elim
  · exact ((by norm_num : ¬ Nat.Prime 155) hq).elim
  · exact ((by norm_num : ¬ Nat.Prime 156) hq).elim
  · exact Or.inl rfl
  · exact ((by norm_num : ¬ Nat.Prime 158) hq).elim
  · exact ((by norm_num : ¬ Nat.Prime 159) hq).elim
  · exact ((by norm_num : ¬ Nat.Prime 160) hq).elim
  · exact ((by norm_num : ¬ Nat.Prime 161) hq).elim
  · exact ((by norm_num : ¬ Nat.Prime 162) hq).elim
  · exact Or.inr (Or.inl rfl)
  · exact ((by norm_num : ¬ Nat.Prime 164) hq).elim
  · exact ((by norm_num : ¬ Nat.Prime 165) hq).elim
  · exact ((by norm_num : ¬ Nat.Prime 166) hq).elim
  · exact Or.inr (Or.inr (Or.inl rfl))
  · exact ((by norm_num : ¬ Nat.Prime 168) hq).elim
  · exact ((by norm_num : ¬ Nat.Prime 169) hq).elim
  · exact ((by norm_num : ¬ Nat.Prime 170) hq).elim
  · exact ((by norm_num : ¬ Nat.Prime 171) hq).elim
  · exact ((by norm_num : ¬ Nat.Prime 172) hq).elim
  · exact Or.inr (Or.inr (Or.inr rfl))

lemma remaining_prime_from_one_hundred_seventy_four_le_one_hundred_ninety_seven
    {q : ℕ} (hq : q.Prime) (h174 : 174 ≤ q) (h197 : q ≤ 197)
    (hnotwin : ¬ (q - 2).Prime) :
    q = 179 ∨ q = 191 ∨ q = 197 := by
  interval_cases q
  · exact ((by norm_num : ¬ Nat.Prime 174) hq).elim
  · exact ((by norm_num : ¬ Nat.Prime 175) hq).elim
  · exact ((by norm_num : ¬ Nat.Prime 176) hq).elim
  · exact ((by norm_num : ¬ Nat.Prime 177) hq).elim
  · exact ((by norm_num : ¬ Nat.Prime 178) hq).elim
  · exact Or.inl rfl
  · exact ((by norm_num : ¬ Nat.Prime 180) hq).elim
  · exact (hnotwin (by norm_num : Nat.Prime 179)).elim
  · exact ((by norm_num : ¬ Nat.Prime 182) hq).elim
  · exact ((by norm_num : ¬ Nat.Prime 183) hq).elim
  · exact ((by norm_num : ¬ Nat.Prime 184) hq).elim
  · exact ((by norm_num : ¬ Nat.Prime 185) hq).elim
  · exact ((by norm_num : ¬ Nat.Prime 186) hq).elim
  · exact ((by norm_num : ¬ Nat.Prime 187) hq).elim
  · exact ((by norm_num : ¬ Nat.Prime 188) hq).elim
  · exact ((by norm_num : ¬ Nat.Prime 189) hq).elim
  · exact ((by norm_num : ¬ Nat.Prime 190) hq).elim
  · exact Or.inr (Or.inl rfl)
  · exact ((by norm_num : ¬ Nat.Prime 192) hq).elim
  · exact (hnotwin (by norm_num : Nat.Prime 191)).elim
  · exact ((by norm_num : ¬ Nat.Prime 194) hq).elim
  · exact ((by norm_num : ¬ Nat.Prime 195) hq).elim
  · exact ((by norm_num : ¬ Nat.Prime 196) hq).elim
  · exact Or.inr (Or.inr rfl)

lemma remaining_prime_le_one_hundred_ninety_seven {q : ℕ} (hq : q.Prime)
    (h150 : 150 ≤ q) (h197 : q ≤ 197) (hnotwin : ¬ (q - 2).Prime) :
    q = 157 ∨ q = 163 ∨ q = 167 ∨ q = 173 ∨ q = 179 ∨ q = 191 ∨
      q = 197 := by
  by_cases h173 : q ≤ 173
  · have hcases := remaining_prime_le_one_hundred_seventy_three hq h150 h173
      hnotwin
    rcases hcases with h157 | h163 | h167 | h173eq
    · exact Or.inl h157
    · exact Or.inr (Or.inl h163)
    · exact Or.inr (Or.inr (Or.inl h167))
    · exact Or.inr (Or.inr (Or.inr (Or.inl h173eq)))
  · have h174 : 174 ≤ q := Nat.succ_le_of_lt (lt_of_not_ge h173)
    have hcases :=
      remaining_prime_from_one_hundred_seventy_four_le_one_hundred_ninety_seven
        hq h174 h197 hnotwin
    rcases hcases with h179 | h191 | h197eq
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h179))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h191)))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h197eq)))))

/-- Remaining McEachen if `lpf(p-2) ≤ 197` or that least factor is a larger twin.
After this cutoff the leftover least factor is at least `211`. -/
theorem conjecture_of_minFac_le_one_hundred_ninety_seven_or_twin {p : ℕ}
    (hp : p.Prime) (hp7 : 7 ≤ p) (hmod : p % 3 = 1)
    (hcomp : ¬ (p - 2).Prime)
    (h : Nat.minFac (p - 2) ≤ 197 ∨ (Nat.minFac (p - 2) - 2).Prime) :
    a (p - 1) = p := by
  have hpr : (Nat.minFac (p - 2)).Prime :=
    Nat.minFac_prime (ne_of_gt (remaining_p_sub_two_gt_one hp7))
  have hd : Nat.minFac (p - 2) ∣ p - 2 := Nat.minFac_dvd _
  rcases h with h197 | htwin
  · by_cases h149 : Nat.minFac (p - 2) ≤ 149
    · exact conjecture_of_minFac_le_one_hundred_forty_nine_or_twin hp hp7 hmod
        hcomp (Or.inl h149)
    · by_cases ht : (Nat.minFac (p - 2) - 2).Prime
      · have h13 : 13 ≤ Nat.minFac (p - 2) :=
          le_trans (by decide : 13 ≤ 150)
            (Nat.succ_le_of_lt (lt_of_not_ge h149))
        exact conjecture_of_larger_twin_dvd hp (five_le_of_seven_le hp7)
          hcomp hpr h13 ht hd
      · have h150 : 150 ≤ Nat.minFac (p - 2) :=
          Nat.succ_le_of_lt (lt_of_not_ge h149)
        have hcases := remaining_prime_le_one_hundred_ninety_seven hpr h150
          h197 ht
        rcases hcases with h157 | h163 | h167 | h173 | h179 | h191 | h197eq
        · exact conjecture_of_minFac_one_hundred_fifty_seven hp hp7 hmod hcomp
            h157
        · exact conjecture_of_minFac_one_hundred_sixty_three hp hp7 hmod hcomp
            h163
        · exact conjecture_of_minFac_one_hundred_sixty_seven hp hp7 hmod hcomp
            h167
        · exact conjecture_of_minFac_one_hundred_seventy_three hp hp7 hmod
            hcomp h173
        · exact conjecture_of_minFac_one_hundred_seventy_nine hp hp7 hmod hcomp
            h179
        · exact conjecture_of_minFac_one_hundred_ninety_one hp hp7 hmod hcomp
            h191
        · exact conjecture_of_minFac_one_hundred_ninety_seven hp hp7 hmod
            hcomp h197eq
  · by_cases h13 : 13 ≤ Nat.minFac (p - 2)
    · exact conjecture_of_larger_twin_dvd hp (five_le_of_seven_le hp7) hcomp
        hpr h13 htwin hd
    · have h12 : Nat.minFac (p - 2) ≤ 12 := Nat.lt_succ_iff.mp (lt_of_not_ge h13)
      exact conjecture_of_minFac_le_twenty_nine hp hp7 hmod hcomp
        (le_trans h12 (by decide : 12 ≤ 29))

lemma remaining_prime_from_one_hundred_ninety_eight_le_two_hundred_eleven
    {q : ℕ} (hq : q.Prime) (h198 : 198 ≤ q) (h211 : q ≤ 211)
    (hnotwin : ¬ (q - 2).Prime) : q = 211 := by
  interval_cases q
  · exact ((by norm_num : ¬ Nat.Prime 198) hq).elim
  · exact (hnotwin (by norm_num : Nat.Prime 197)).elim
  · exact ((by norm_num : ¬ Nat.Prime 200) hq).elim
  · exact ((by norm_num : ¬ Nat.Prime 201) hq).elim
  · exact ((by norm_num : ¬ Nat.Prime 202) hq).elim
  · exact ((by norm_num : ¬ Nat.Prime 203) hq).elim
  · exact ((by norm_num : ¬ Nat.Prime 204) hq).elim
  · exact ((by norm_num : ¬ Nat.Prime 205) hq).elim
  · exact ((by norm_num : ¬ Nat.Prime 206) hq).elim
  · exact ((by norm_num : ¬ Nat.Prime 207) hq).elim
  · exact ((by norm_num : ¬ Nat.Prime 208) hq).elim
  · exact ((by norm_num : ¬ Nat.Prime 209) hq).elim
  · exact ((by norm_num : ¬ Nat.Prime 210) hq).elim
  · rfl

lemma remaining_prime_from_two_hundred_twelve_le_two_hundred_twenty_seven
    {q : ℕ} (hq : q.Prime) (h212 : 212 ≤ q) (h227 : q ≤ 227)
    (hnotwin : ¬ (q - 2).Prime) : q = 223 ∨ q = 227 := by
  interval_cases q
  · exact ((by norm_num : ¬ Nat.Prime 212) hq).elim
  · exact ((by norm_num : ¬ Nat.Prime 213) hq).elim
  · exact ((by norm_num : ¬ Nat.Prime 214) hq).elim
  · exact ((by norm_num : ¬ Nat.Prime 215) hq).elim
  · exact ((by norm_num : ¬ Nat.Prime 216) hq).elim
  · exact ((by norm_num : ¬ Nat.Prime 217) hq).elim
  · exact ((by norm_num : ¬ Nat.Prime 218) hq).elim
  · exact ((by norm_num : ¬ Nat.Prime 219) hq).elim
  · exact ((by norm_num : ¬ Nat.Prime 220) hq).elim
  · exact ((by norm_num : ¬ Nat.Prime 221) hq).elim
  · exact ((by norm_num : ¬ Nat.Prime 222) hq).elim
  · exact Or.inl rfl
  · exact ((by norm_num : ¬ Nat.Prime 224) hq).elim
  · exact ((by norm_num : ¬ Nat.Prime 225) hq).elim
  · exact ((by norm_num : ¬ Nat.Prime 226) hq).elim
  · exact Or.inr rfl

lemma remaining_prime_from_two_hundred_twenty_eight_le_two_hundred_thirty_nine
    {q : ℕ} (hq : q.Prime) (h228 : 228 ≤ q) (h239 : q ≤ 239)
    (hnotwin : ¬ (q - 2).Prime) : q = 233 ∨ q = 239 := by
  interval_cases q
  · exact ((by norm_num : ¬ Nat.Prime 228) hq).elim
  · exact (hnotwin (by norm_num : Nat.Prime 227)).elim
  · exact ((by norm_num : ¬ Nat.Prime 230) hq).elim
  · exact ((by norm_num : ¬ Nat.Prime 231) hq).elim
  · exact ((by norm_num : ¬ Nat.Prime 232) hq).elim
  · exact Or.inl rfl
  · exact ((by norm_num : ¬ Nat.Prime 234) hq).elim
  · exact ((by norm_num : ¬ Nat.Prime 235) hq).elim
  · exact ((by norm_num : ¬ Nat.Prime 236) hq).elim
  · exact ((by norm_num : ¬ Nat.Prime 237) hq).elim
  · exact ((by norm_num : ¬ Nat.Prime 238) hq).elim
  · exact Or.inr rfl

lemma remaining_prime_from_one_hundred_ninety_eight_le_two_hundred_thirty_nine
    {q : ℕ} (hq : q.Prime) (h198 : 198 ≤ q) (h239 : q ≤ 239)
    (hnotwin : ¬ (q - 2).Prime) :
    q = 211 ∨ q = 223 ∨ q = 227 ∨ q = 233 ∨ q = 239 := by
  by_cases h211 : q ≤ 211
  · exact Or.inl
      (remaining_prime_from_one_hundred_ninety_eight_le_two_hundred_eleven
        hq h198 h211 hnotwin)
  · have h212 : 212 ≤ q := Nat.succ_le_of_lt (lt_of_not_ge h211)
    by_cases h227 : q ≤ 227
    · have hcases :=
        remaining_prime_from_two_hundred_twelve_le_two_hundred_twenty_seven
          hq h212 h227 hnotwin
      rcases hcases with h223 | h227eq
      · exact Or.inr (Or.inl h223)
      · exact Or.inr (Or.inr (Or.inl h227eq))
    · have h228 : 228 ≤ q := Nat.succ_le_of_lt (lt_of_not_ge h227)
      have hcases :=
        remaining_prime_from_two_hundred_twenty_eight_le_two_hundred_thirty_nine
          hq h228 h239 hnotwin
      rcases hcases with h233 | h239eq
      · exact Or.inr (Or.inr (Or.inr (Or.inl h233)))
      · exact Or.inr (Or.inr (Or.inr (Or.inr h239eq)))

/-- Remaining McEachen if `lpf(p-2) ≤ 239` or that least factor is a larger twin.
After this cutoff the leftover least factor is at least `251`. -/
theorem conjecture_of_minFac_le_two_hundred_thirty_nine_or_twin {p : ℕ}
    (hp : p.Prime) (hp7 : 7 ≤ p) (hmod : p % 3 = 1)
    (hcomp : ¬ (p - 2).Prime)
    (h : Nat.minFac (p - 2) ≤ 239 ∨ (Nat.minFac (p - 2) - 2).Prime) :
    a (p - 1) = p := by
  have hpr : (Nat.minFac (p - 2)).Prime :=
    Nat.minFac_prime (ne_of_gt (remaining_p_sub_two_gt_one hp7))
  have hd : Nat.minFac (p - 2) ∣ p - 2 := Nat.minFac_dvd _
  rcases h with h239 | htwin
  · by_cases h197 : Nat.minFac (p - 2) ≤ 197
    · exact conjecture_of_minFac_le_one_hundred_ninety_seven_or_twin hp hp7
        hmod hcomp (Or.inl h197)
    · by_cases ht : (Nat.minFac (p - 2) - 2).Prime
      · have h13 : 13 ≤ Nat.minFac (p - 2) :=
          le_trans (by decide : 13 ≤ 198)
            (Nat.succ_le_of_lt (lt_of_not_ge h197))
        exact conjecture_of_larger_twin_dvd hp (five_le_of_seven_le hp7)
          hcomp hpr h13 ht hd
      · have h198 : 198 ≤ Nat.minFac (p - 2) :=
          Nat.succ_le_of_lt (lt_of_not_ge h197)
        have hcases :=
          remaining_prime_from_one_hundred_ninety_eight_le_two_hundred_thirty_nine
            hpr h198 h239 ht
        rcases hcases with h211 | h223 | h227 | h233 | h239eq
        · exact conjecture_of_minFac_two_hundred_eleven hp hp7 hmod hcomp h211
        · exact conjecture_of_minFac_two_hundred_twenty_three hp hp7 hmod hcomp
            h223
        · exact conjecture_of_minFac_two_hundred_twenty_seven hp hp7 hmod
            hcomp h227
        · exact conjecture_of_minFac_two_hundred_thirty_three hp hp7 hmod hcomp
            h233
        · exact conjecture_of_minFac_two_hundred_thirty_nine hp hp7 hmod
            hcomp h239eq
  · by_cases h13 : 13 ≤ Nat.minFac (p - 2)
    · exact conjecture_of_larger_twin_dvd hp (five_le_of_seven_le hp7) hcomp
        hpr h13 htwin hd
    · have h12 : Nat.minFac (p - 2) ≤ 12 := Nat.lt_succ_iff.mp (lt_of_not_ge h13)
      exact conjecture_of_minFac_le_twenty_nine hp hp7 hmod hcomp
        (le_trans h12 (by decide : 12 ≤ 29))

lemma remaining_prime_from_two_hundred_forty_le_two_hundred_fifty_seven
    {q : ℕ} (hq : q.Prime) (h240 : 240 ≤ q) (h257 : q ≤ 257)
    (hnotwin : ¬ (q - 2).Prime) : q = 251 ∨ q = 257 := by
  interval_cases q
  · exact ((by norm_num : ¬ Nat.Prime 240) hq).elim
  · exact (hnotwin (by norm_num : Nat.Prime 239)).elim
  · exact ((by norm_num : ¬ Nat.Prime 242) hq).elim
  · exact ((by norm_num : ¬ Nat.Prime 243) hq).elim
  · exact ((by norm_num : ¬ Nat.Prime 244) hq).elim
  · exact ((by norm_num : ¬ Nat.Prime 245) hq).elim
  · exact ((by norm_num : ¬ Nat.Prime 246) hq).elim
  · exact ((by norm_num : ¬ Nat.Prime 247) hq).elim
  · exact ((by norm_num : ¬ Nat.Prime 248) hq).elim
  · exact ((by norm_num : ¬ Nat.Prime 249) hq).elim
  · exact ((by norm_num : ¬ Nat.Prime 250) hq).elim
  · exact Or.inl rfl
  · exact ((by norm_num : ¬ Nat.Prime 252) hq).elim
  · exact ((by norm_num : ¬ Nat.Prime 253) hq).elim
  · exact ((by norm_num : ¬ Nat.Prime 254) hq).elim
  · exact ((by norm_num : ¬ Nat.Prime 255) hq).elim
  · exact ((by norm_num : ¬ Nat.Prime 256) hq).elim
  · exact Or.inr rfl

/-- Remaining McEachen if `lpf(p-2) ≤ 257` or that least factor is a larger twin.
After this cutoff the leftover least factor is at least `263`. -/
theorem conjecture_of_minFac_le_two_hundred_fifty_seven_or_twin {p : ℕ}
    (hp : p.Prime) (hp7 : 7 ≤ p) (hmod : p % 3 = 1)
    (hcomp : ¬ (p - 2).Prime)
    (h : Nat.minFac (p - 2) ≤ 257 ∨ (Nat.minFac (p - 2) - 2).Prime) :
    a (p - 1) = p := by
  have hpr : (Nat.minFac (p - 2)).Prime :=
    Nat.minFac_prime (ne_of_gt (remaining_p_sub_two_gt_one hp7))
  have hd : Nat.minFac (p - 2) ∣ p - 2 := Nat.minFac_dvd _
  rcases h with h257 | htwin
  · by_cases h239 : Nat.minFac (p - 2) ≤ 239
    · exact conjecture_of_minFac_le_two_hundred_thirty_nine_or_twin hp hp7
        hmod hcomp (Or.inl h239)
    · by_cases ht : (Nat.minFac (p - 2) - 2).Prime
      · have h13 : 13 ≤ Nat.minFac (p - 2) :=
          le_trans (by decide : 13 ≤ 240)
            (Nat.succ_le_of_lt (lt_of_not_ge h239))
        exact conjecture_of_larger_twin_dvd hp (five_le_of_seven_le hp7)
          hcomp hpr h13 ht hd
      · have h240 : 240 ≤ Nat.minFac (p - 2) :=
          Nat.succ_le_of_lt (lt_of_not_ge h239)
        have hcases :=
          remaining_prime_from_two_hundred_forty_le_two_hundred_fifty_seven
            hpr h240 h257 ht
        rcases hcases with h251 | h257eq
        · exact conjecture_of_minFac_two_hundred_fifty_one hp hp7 hmod hcomp
            h251
        · exact conjecture_of_minFac_two_hundred_fifty_seven hp hp7 hmod
            hcomp h257eq
  · by_cases h13 : 13 ≤ Nat.minFac (p - 2)
    · exact conjecture_of_larger_twin_dvd hp (five_le_of_seven_le hp7) hcomp
        hpr h13 htwin hd
    · have h12 : Nat.minFac (p - 2) ≤ 12 := Nat.lt_succ_iff.mp (lt_of_not_ge h13)
      exact conjecture_of_minFac_le_twenty_nine hp hp7 hmod hcomp
        (le_trans h12 (by decide : 12 ≤ 29))

lemma remaining_prime_from_two_hundred_fifty_eight_le_two_hundred_sixty_three
    {q : ℕ} (hq : q.Prime) (h258 : 258 ≤ q) (h263 : q ≤ 263)
    (_hnotwin : ¬ (q - 2).Prime) : q = 263 := by
  interval_cases q
  · exact ((by norm_num : ¬ Nat.Prime 258) hq).elim
  · exact ((by norm_num : ¬ Nat.Prime 259) hq).elim
  · exact ((by norm_num : ¬ Nat.Prime 260) hq).elim
  · exact ((by norm_num : ¬ Nat.Prime 261) hq).elim
  · exact ((by norm_num : ¬ Nat.Prime 262) hq).elim
  · rfl

/-- Remaining McEachen if `lpf(p-2) ≤ 263` or that least factor is a larger twin.
After this cutoff the leftover least factor is at least `269`. -/
theorem conjecture_of_minFac_le_two_hundred_sixty_three_or_twin {p : ℕ}
    (hp : p.Prime) (hp7 : 7 ≤ p) (hmod : p % 3 = 1)
    (hcomp : ¬ (p - 2).Prime)
    (h : Nat.minFac (p - 2) ≤ 263 ∨ (Nat.minFac (p - 2) - 2).Prime) :
    a (p - 1) = p := by
  have hpr : (Nat.minFac (p - 2)).Prime :=
    Nat.minFac_prime (ne_of_gt (remaining_p_sub_two_gt_one hp7))
  have hd : Nat.minFac (p - 2) ∣ p - 2 := Nat.minFac_dvd _
  rcases h with h263 | htwin
  · by_cases h257 : Nat.minFac (p - 2) ≤ 257
    · exact conjecture_of_minFac_le_two_hundred_fifty_seven_or_twin hp hp7
        hmod hcomp (Or.inl h257)
    · by_cases ht : (Nat.minFac (p - 2) - 2).Prime
      · have h13 : 13 ≤ Nat.minFac (p - 2) :=
          le_trans (by decide : 13 ≤ 258)
            (Nat.succ_le_of_lt (lt_of_not_ge h257))
        exact conjecture_of_larger_twin_dvd hp (five_le_of_seven_le hp7)
          hcomp hpr h13 ht hd
      · have h258 : 258 ≤ Nat.minFac (p - 2) :=
          Nat.succ_le_of_lt (lt_of_not_ge h257)
        have h263eq :=
          remaining_prime_from_two_hundred_fifty_eight_le_two_hundred_sixty_three
            hpr h258 h263 ht
        exact conjecture_of_minFac_two_hundred_sixty_three hp hp7 hmod hcomp
          h263eq
  · by_cases h13 : 13 ≤ Nat.minFac (p - 2)
    · exact conjecture_of_larger_twin_dvd hp (five_le_of_seven_le hp7) hcomp
        hpr h13 htwin hd
    · have h12 : Nat.minFac (p - 2) ≤ 12 := Nat.lt_succ_iff.mp (lt_of_not_ge h13)
      exact conjecture_of_minFac_le_twenty_nine hp hp7 hmod hcomp
        (le_trans h12 (by decide : 12 ≤ 29))

lemma remaining_prime_from_two_hundred_sixty_four_le_two_hundred_sixty_nine
    {q : ℕ} (hq : q.Prime) (h264 : 264 ≤ q) (h269 : q ≤ 269)
    (_hnotwin : ¬ (q - 2).Prime) : q = 269 := by
  interval_cases q
  · exact ((by norm_num : ¬ Nat.Prime 264) hq).elim
  · exact ((by norm_num : ¬ Nat.Prime 265) hq).elim
  · exact ((by norm_num : ¬ Nat.Prime 266) hq).elim
  · exact ((by norm_num : ¬ Nat.Prime 267) hq).elim
  · exact ((by norm_num : ¬ Nat.Prime 268) hq).elim
  · rfl

/-- Remaining McEachen if `lpf(p-2) ≤ 269` or that least factor is a larger twin.
After this cutoff the leftover least factor is at least `277`. -/
theorem conjecture_of_minFac_le_two_hundred_sixty_nine_or_twin {p : ℕ}
    (hp : p.Prime) (hp7 : 7 ≤ p) (hmod : p % 3 = 1)
    (hcomp : ¬ (p - 2).Prime)
    (h : Nat.minFac (p - 2) ≤ 269 ∨ (Nat.minFac (p - 2) - 2).Prime) :
    a (p - 1) = p := by
  have hpr : (Nat.minFac (p - 2)).Prime :=
    Nat.minFac_prime (ne_of_gt (remaining_p_sub_two_gt_one hp7))
  have hd : Nat.minFac (p - 2) ∣ p - 2 := Nat.minFac_dvd _
  rcases h with h269 | htwin
  · by_cases h263 : Nat.minFac (p - 2) ≤ 263
    · exact conjecture_of_minFac_le_two_hundred_sixty_three_or_twin hp hp7
        hmod hcomp (Or.inl h263)
    · by_cases ht : (Nat.minFac (p - 2) - 2).Prime
      · have h13 : 13 ≤ Nat.minFac (p - 2) :=
          le_trans (by decide : 13 ≤ 264)
            (Nat.succ_le_of_lt (lt_of_not_ge h263))
        exact conjecture_of_larger_twin_dvd hp (five_le_of_seven_le hp7)
          hcomp hpr h13 ht hd
      · have h264 : 264 ≤ Nat.minFac (p - 2) :=
          Nat.succ_le_of_lt (lt_of_not_ge h263)
        have h269eq :=
          remaining_prime_from_two_hundred_sixty_four_le_two_hundred_sixty_nine
            hpr h264 h269 ht
        exact conjecture_of_minFac_two_hundred_sixty_nine hp hp7 hmod hcomp
          h269eq
  · by_cases h13 : 13 ≤ Nat.minFac (p - 2)
    · exact conjecture_of_larger_twin_dvd hp (five_le_of_seven_le hp7) hcomp
        hpr h13 htwin hd
    · have h12 : Nat.minFac (p - 2) ≤ 12 := Nat.lt_succ_iff.mp (lt_of_not_ge h13)
      exact conjecture_of_minFac_le_twenty_nine hp hp7 hmod hcomp
        (le_trans h12 (by decide : 12 ≤ 29))

lemma remaining_prime_from_two_hundred_seventy_le_two_hundred_seventy_seven
    {q : ℕ} (hq : q.Prime) (h270 : 270 ≤ q) (h277 : q ≤ 277)
    (hnotwin : ¬ (q - 2).Prime) : q = 277 := by
  interval_cases q
  · exact ((by norm_num : ¬ Nat.Prime 270) hq).elim
  · exact (hnotwin (by norm_num : Nat.Prime 269)).elim
  · exact ((by norm_num : ¬ Nat.Prime 272) hq).elim
  · exact ((by norm_num : ¬ Nat.Prime 273) hq).elim
  · exact ((by norm_num : ¬ Nat.Prime 274) hq).elim
  · exact ((by norm_num : ¬ Nat.Prime 275) hq).elim
  · exact ((by norm_num : ¬ Nat.Prime 276) hq).elim
  · rfl

/-- Remaining McEachen if `lpf(p-2) ≤ 277` or that least factor is a larger twin.
After this cutoff the leftover least factor is at least `281`. -/
theorem conjecture_of_minFac_le_two_hundred_seventy_seven_or_twin {p : ℕ}
    (hp : p.Prime) (hp7 : 7 ≤ p) (hmod : p % 3 = 1)
    (hcomp : ¬ (p - 2).Prime)
    (h : Nat.minFac (p - 2) ≤ 277 ∨ (Nat.minFac (p - 2) - 2).Prime) :
    a (p - 1) = p := by
  have hpr : (Nat.minFac (p - 2)).Prime :=
    Nat.minFac_prime (ne_of_gt (remaining_p_sub_two_gt_one hp7))
  have hd : Nat.minFac (p - 2) ∣ p - 2 := Nat.minFac_dvd _
  rcases h with h277 | htwin
  · by_cases h269 : Nat.minFac (p - 2) ≤ 269
    · exact conjecture_of_minFac_le_two_hundred_sixty_nine_or_twin hp hp7
        hmod hcomp (Or.inl h269)
    · by_cases ht : (Nat.minFac (p - 2) - 2).Prime
      · have h13 : 13 ≤ Nat.minFac (p - 2) :=
          le_trans (by decide : 13 ≤ 270)
            (Nat.succ_le_of_lt (lt_of_not_ge h269))
        exact conjecture_of_larger_twin_dvd hp (five_le_of_seven_le hp7)
          hcomp hpr h13 ht hd
      · have h270 : 270 ≤ Nat.minFac (p - 2) :=
          Nat.succ_le_of_lt (lt_of_not_ge h269)
        have h277eq :=
          remaining_prime_from_two_hundred_seventy_le_two_hundred_seventy_seven
            hpr h270 h277 ht
        exact conjecture_of_minFac_two_hundred_seventy_seven hp hp7 hmod hcomp
          h277eq
  · by_cases h13 : 13 ≤ Nat.minFac (p - 2)
    · exact conjecture_of_larger_twin_dvd hp (five_le_of_seven_le hp7) hcomp
        hpr h13 htwin hd
    · have h12 : Nat.minFac (p - 2) ≤ 12 := Nat.lt_succ_iff.mp (lt_of_not_ge h13)
      exact conjecture_of_minFac_le_twenty_nine hp hp7 hmod hcomp
        (le_trans h12 (by decide : 12 ≤ 29))

lemma remaining_prime_from_two_hundred_seventy_eight_le_two_hundred_eighty_one
    {q : ℕ} (hq : q.Prime) (h278 : 278 ≤ q) (h281 : q ≤ 281)
    (_hnotwin : ¬ (q - 2).Prime) : q = 281 := by
  interval_cases q
  · exact ((by norm_num : ¬ Nat.Prime 278) hq).elim
  · exact ((by norm_num : ¬ Nat.Prime 279) hq).elim
  · exact ((by norm_num : ¬ Nat.Prime 280) hq).elim
  · rfl

/-- Remaining McEachen if `lpf(p-2) ≤ 281` or that least factor is a larger twin.
After this cutoff the leftover least factor is at least `293`. -/
theorem conjecture_of_minFac_le_two_hundred_eighty_one_or_twin {p : ℕ}
    (hp : p.Prime) (hp7 : 7 ≤ p) (hmod : p % 3 = 1)
    (hcomp : ¬ (p - 2).Prime)
    (h : Nat.minFac (p - 2) ≤ 281 ∨ (Nat.minFac (p - 2) - 2).Prime) :
    a (p - 1) = p := by
  have hpr : (Nat.minFac (p - 2)).Prime :=
    Nat.minFac_prime (ne_of_gt (remaining_p_sub_two_gt_one hp7))
  have hd : Nat.minFac (p - 2) ∣ p - 2 := Nat.minFac_dvd _
  rcases h with h281 | htwin
  · by_cases h277 : Nat.minFac (p - 2) ≤ 277
    · exact conjecture_of_minFac_le_two_hundred_seventy_seven_or_twin hp hp7
        hmod hcomp (Or.inl h277)
    · by_cases ht : (Nat.minFac (p - 2) - 2).Prime
      · have h13 : 13 ≤ Nat.minFac (p - 2) :=
          le_trans (by decide : 13 ≤ 278)
            (Nat.succ_le_of_lt (lt_of_not_ge h277))
        exact conjecture_of_larger_twin_dvd hp (five_le_of_seven_le hp7)
          hcomp hpr h13 ht hd
      · have h278 : 278 ≤ Nat.minFac (p - 2) :=
          Nat.succ_le_of_lt (lt_of_not_ge h277)
        have h281eq :=
          remaining_prime_from_two_hundred_seventy_eight_le_two_hundred_eighty_one
            hpr h278 h281 ht
        exact conjecture_of_minFac_two_hundred_eighty_one hp hp7 hmod hcomp
          h281eq
  · by_cases h13 : 13 ≤ Nat.minFac (p - 2)
    · exact conjecture_of_larger_twin_dvd hp (five_le_of_seven_le hp7) hcomp
        hpr h13 htwin hd
    · have h12 : Nat.minFac (p - 2) ≤ 12 := Nat.lt_succ_iff.mp (lt_of_not_ge h13)
      exact conjecture_of_minFac_le_twenty_nine hp hp7 hmod hcomp
        (le_trans h12 (by decide : 12 ≤ 29))

lemma remaining_prime_from_two_hundred_eighty_two_le_two_hundred_ninety_three
    {q : ℕ} (hq : q.Prime) (h282 : 282 ≤ q) (h293 : q ≤ 293)
    (hnotwin : ¬ (q - 2).Prime) : q = 293 := by
  interval_cases q
  · exact ((by norm_num : ¬ Nat.Prime 282) hq).elim
  · exact (hnotwin (by norm_num : Nat.Prime 281)).elim
  · exact ((by norm_num : ¬ Nat.Prime 284) hq).elim
  · exact ((by norm_num : ¬ Nat.Prime 285) hq).elim
  · exact ((by norm_num : ¬ Nat.Prime 286) hq).elim
  · exact ((by norm_num : ¬ Nat.Prime 287) hq).elim
  · exact ((by norm_num : ¬ Nat.Prime 288) hq).elim
  · exact ((by norm_num : ¬ Nat.Prime 289) hq).elim
  · exact ((by norm_num : ¬ Nat.Prime 290) hq).elim
  · exact ((by norm_num : ¬ Nat.Prime 291) hq).elim
  · exact ((by norm_num : ¬ Nat.Prime 292) hq).elim
  · rfl

/-- Remaining McEachen if `lpf(p-2) ≤ 293` or that least factor is a larger twin.
After this cutoff the leftover least factor is at least `307`. -/
theorem conjecture_of_minFac_le_two_hundred_ninety_three_or_twin {p : ℕ}
    (hp : p.Prime) (hp7 : 7 ≤ p) (hmod : p % 3 = 1)
    (hcomp : ¬ (p - 2).Prime)
    (h : Nat.minFac (p - 2) ≤ 293 ∨ (Nat.minFac (p - 2) - 2).Prime) :
    a (p - 1) = p := by
  have hpr : (Nat.minFac (p - 2)).Prime :=
    Nat.minFac_prime (ne_of_gt (remaining_p_sub_two_gt_one hp7))
  have hd : Nat.minFac (p - 2) ∣ p - 2 := Nat.minFac_dvd _
  rcases h with h293 | htwin
  · by_cases h281 : Nat.minFac (p - 2) ≤ 281
    · exact conjecture_of_minFac_le_two_hundred_eighty_one_or_twin hp hp7
        hmod hcomp (Or.inl h281)
    · by_cases ht : (Nat.minFac (p - 2) - 2).Prime
      · have h13 : 13 ≤ Nat.minFac (p - 2) :=
          le_trans (by decide : 13 ≤ 282)
            (Nat.succ_le_of_lt (lt_of_not_ge h281))
        exact conjecture_of_larger_twin_dvd hp (five_le_of_seven_le hp7)
          hcomp hpr h13 ht hd
      · have h282 : 282 ≤ Nat.minFac (p - 2) :=
          Nat.succ_le_of_lt (lt_of_not_ge h281)
        have h293eq :=
          remaining_prime_from_two_hundred_eighty_two_le_two_hundred_ninety_three
            hpr h282 h293 ht
        exact conjecture_of_minFac_two_hundred_ninety_three hp hp7 hmod hcomp
          h293eq
  · by_cases h13 : 13 ≤ Nat.minFac (p - 2)
    · exact conjecture_of_larger_twin_dvd hp (five_le_of_seven_le hp7) hcomp
        hpr h13 htwin hd
    · have h12 : Nat.minFac (p - 2) ≤ 12 := Nat.lt_succ_iff.mp (lt_of_not_ge h13)
      exact conjecture_of_minFac_le_twenty_nine hp hp7 hmod hcomp
        (le_trans h12 (by decide : 12 ≤ 29))

lemma remaining_prime_from_two_hundred_ninety_four_le_three_hundred_seven
    {q : ℕ} (hq : q.Prime) (hlo : 294 ≤ q) (hhi : q ≤ 307)
    (_hnotwin : ¬ (q - 2).Prime) : q = 307 := by
  interval_cases q
  · exact ((by norm_num : ¬ Nat.Prime 294) hq).elim
  · exact ((by norm_num : ¬ Nat.Prime 295) hq).elim
  · exact ((by norm_num : ¬ Nat.Prime 296) hq).elim
  · exact ((by norm_num : ¬ Nat.Prime 297) hq).elim
  · exact ((by norm_num : ¬ Nat.Prime 298) hq).elim
  · exact ((by norm_num : ¬ Nat.Prime 299) hq).elim
  · exact ((by norm_num : ¬ Nat.Prime 300) hq).elim
  · exact ((by norm_num : ¬ Nat.Prime 301) hq).elim
  · exact ((by norm_num : ¬ Nat.Prime 302) hq).elim
  · exact ((by norm_num : ¬ Nat.Prime 303) hq).elim
  · exact ((by norm_num : ¬ Nat.Prime 304) hq).elim
  · exact ((by norm_num : ¬ Nat.Prime 305) hq).elim
  · exact ((by norm_num : ¬ Nat.Prime 306) hq).elim
  · rfl

lemma remaining_prime_from_three_hundred_eight_le_three_hundred_eleven
    {q : ℕ} (hq : q.Prime) (hlo : 308 ≤ q) (hhi : q ≤ 311)
    (_hnotwin : ¬ (q - 2).Prime) : q = 311 := by
  interval_cases q
  · exact ((by norm_num : ¬ Nat.Prime 308) hq).elim
  · exact ((by norm_num : ¬ Nat.Prime 309) hq).elim
  · exact ((by norm_num : ¬ Nat.Prime 310) hq).elim
  · rfl

lemma remaining_prime_from_three_hundred_twelve_le_three_hundred_seventeen
    {q : ℕ} (hq : q.Prime) (hlo : 312 ≤ q) (hhi : q ≤ 317)
    (hnotwin : ¬ (q - 2).Prime) : q = 317 := by
  interval_cases q
  · exact ((by norm_num : ¬ Nat.Prime 312) hq).elim
  · exact (hnotwin (by norm_num : Nat.Prime 311)).elim
  · exact ((by norm_num : ¬ Nat.Prime 314) hq).elim
  · exact ((by norm_num : ¬ Nat.Prime 315) hq).elim
  · exact ((by norm_num : ¬ Nat.Prime 316) hq).elim
  · rfl

lemma remaining_prime_from_three_hundred_eighteen_le_three_hundred_thirty_one
    {q : ℕ} (hq : q.Prime) (hlo : 318 ≤ q) (hhi : q ≤ 331)
    (_hnotwin : ¬ (q - 2).Prime) : q = 331 := by
  interval_cases q
  · exact ((by norm_num : ¬ Nat.Prime 318) hq).elim
  · exact ((by norm_num : ¬ Nat.Prime 319) hq).elim
  · exact ((by norm_num : ¬ Nat.Prime 320) hq).elim
  · exact ((by norm_num : ¬ Nat.Prime 321) hq).elim
  · exact ((by norm_num : ¬ Nat.Prime 322) hq).elim
  · exact ((by norm_num : ¬ Nat.Prime 323) hq).elim
  · exact ((by norm_num : ¬ Nat.Prime 324) hq).elim
  · exact ((by norm_num : ¬ Nat.Prime 325) hq).elim
  · exact ((by norm_num : ¬ Nat.Prime 326) hq).elim
  · exact ((by norm_num : ¬ Nat.Prime 327) hq).elim
  · exact ((by norm_num : ¬ Nat.Prime 328) hq).elim
  · exact ((by norm_num : ¬ Nat.Prime 329) hq).elim
  · exact ((by norm_num : ¬ Nat.Prime 330) hq).elim
  · rfl

lemma remaining_prime_from_three_hundred_thirty_two_le_three_hundred_thirty_seven
    {q : ℕ} (hq : q.Prime) (hlo : 332 ≤ q) (hhi : q ≤ 337)
    (_hnotwin : ¬ (q - 2).Prime) : q = 337 := by
  interval_cases q
  · exact ((by norm_num : ¬ Nat.Prime 332) hq).elim
  · exact ((by norm_num : ¬ Nat.Prime 333) hq).elim
  · exact ((by norm_num : ¬ Nat.Prime 334) hq).elim
  · exact ((by norm_num : ¬ Nat.Prime 335) hq).elim
  · exact ((by norm_num : ¬ Nat.Prime 336) hq).elim
  · rfl

lemma remaining_prime_from_three_hundred_thirty_eight_le_three_hundred_forty_seven
    {q : ℕ} (hq : q.Prime) (hlo : 338 ≤ q) (hhi : q ≤ 347)
    (_hnotwin : ¬ (q - 2).Prime) : q = 347 := by
  interval_cases q
  · exact ((by norm_num : ¬ Nat.Prime 338) hq).elim
  · exact ((by norm_num : ¬ Nat.Prime 339) hq).elim
  · exact ((by norm_num : ¬ Nat.Prime 340) hq).elim
  · exact ((by norm_num : ¬ Nat.Prime 341) hq).elim
  · exact ((by norm_num : ¬ Nat.Prime 342) hq).elim
  · exact ((by norm_num : ¬ Nat.Prime 343) hq).elim
  · exact ((by norm_num : ¬ Nat.Prime 344) hq).elim
  · exact ((by norm_num : ¬ Nat.Prime 345) hq).elim
  · exact ((by norm_num : ¬ Nat.Prime 346) hq).elim
  · rfl

lemma remaining_prime_from_three_hundred_forty_eight_le_three_hundred_fifty_three
    {q : ℕ} (hq : q.Prime) (hlo : 348 ≤ q) (hhi : q ≤ 353)
    (hnotwin : ¬ (q - 2).Prime) : q = 353 := by
  interval_cases q
  · exact ((by norm_num : ¬ Nat.Prime 348) hq).elim
  · exact (hnotwin (by norm_num : Nat.Prime 347)).elim
  · exact ((by norm_num : ¬ Nat.Prime 350) hq).elim
  · exact ((by norm_num : ¬ Nat.Prime 351) hq).elim
  · exact ((by norm_num : ¬ Nat.Prime 352) hq).elim
  · rfl

lemma remaining_prime_from_three_hundred_fifty_four_le_three_hundred_fifty_nine
    {q : ℕ} (hq : q.Prime) (hlo : 354 ≤ q) (hhi : q ≤ 359)
    (_hnotwin : ¬ (q - 2).Prime) : q = 359 := by
  interval_cases q
  · exact ((by norm_num : ¬ Nat.Prime 354) hq).elim
  · exact ((by norm_num : ¬ Nat.Prime 355) hq).elim
  · exact ((by norm_num : ¬ Nat.Prime 356) hq).elim
  · exact ((by norm_num : ¬ Nat.Prime 357) hq).elim
  · exact ((by norm_num : ¬ Nat.Prime 358) hq).elim
  · rfl

lemma remaining_prime_from_three_hundred_sixty_le_three_hundred_sixty_seven
    {q : ℕ} (hq : q.Prime) (hlo : 360 ≤ q) (hhi : q ≤ 367)
    (_hnotwin : ¬ (q - 2).Prime) : q = 367 := by
  interval_cases q
  · exact ((by norm_num : ¬ Nat.Prime 360) hq).elim
  · exact ((by norm_num : ¬ Nat.Prime 361) hq).elim
  · exact ((by norm_num : ¬ Nat.Prime 362) hq).elim
  · exact ((by norm_num : ¬ Nat.Prime 363) hq).elim
  · exact ((by norm_num : ¬ Nat.Prime 364) hq).elim
  · exact ((by norm_num : ¬ Nat.Prime 365) hq).elim
  · exact ((by norm_num : ¬ Nat.Prime 366) hq).elim
  · rfl

lemma remaining_prime_from_three_hundred_sixty_eight_le_three_hundred_seventy_three
    {q : ℕ} (hq : q.Prime) (hlo : 368 ≤ q) (hhi : q ≤ 373)
    (_hnotwin : ¬ (q - 2).Prime) : q = 373 := by
  interval_cases q
  · exact ((by norm_num : ¬ Nat.Prime 368) hq).elim
  · exact ((by norm_num : ¬ Nat.Prime 369) hq).elim
  · exact ((by norm_num : ¬ Nat.Prime 370) hq).elim
  · exact ((by norm_num : ¬ Nat.Prime 371) hq).elim
  · exact ((by norm_num : ¬ Nat.Prime 372) hq).elim
  · rfl

lemma remaining_prime_from_three_hundred_seventy_four_le_three_hundred_seventy_nine
    {q : ℕ} (hq : q.Prime) (hlo : 374 ≤ q) (hhi : q ≤ 379)
    (_hnotwin : ¬ (q - 2).Prime) : q = 379 := by
  interval_cases q
  · exact ((by norm_num : ¬ Nat.Prime 374) hq).elim
  · exact ((by norm_num : ¬ Nat.Prime 375) hq).elim
  · exact ((by norm_num : ¬ Nat.Prime 376) hq).elim
  · exact ((by norm_num : ¬ Nat.Prime 377) hq).elim
  · exact ((by norm_num : ¬ Nat.Prime 378) hq).elim
  · rfl

lemma remaining_prime_from_three_hundred_eighty_le_three_hundred_eighty_three
    {q : ℕ} (hq : q.Prime) (hlo : 380 ≤ q) (hhi : q ≤ 383)
    (_hnotwin : ¬ (q - 2).Prime) : q = 383 := by
  interval_cases q
  · exact ((by norm_num : ¬ Nat.Prime 380) hq).elim
  · exact ((by norm_num : ¬ Nat.Prime 381) hq).elim
  · exact ((by norm_num : ¬ Nat.Prime 382) hq).elim
  · rfl

lemma remaining_prime_from_three_hundred_eighty_four_le_three_hundred_eighty_nine
    {q : ℕ} (hq : q.Prime) (hlo : 384 ≤ q) (hhi : q ≤ 389)
    (_hnotwin : ¬ (q - 2).Prime) : q = 389 := by
  interval_cases q
  · exact ((by norm_num : ¬ Nat.Prime 384) hq).elim
  · exact ((by norm_num : ¬ Nat.Prime 385) hq).elim
  · exact ((by norm_num : ¬ Nat.Prime 386) hq).elim
  · exact ((by norm_num : ¬ Nat.Prime 387) hq).elim
  · exact ((by norm_num : ¬ Nat.Prime 388) hq).elim
  · rfl

/-- Remaining McEachen if `lpf(p-2) ≤ 389` or that least factor is a larger twin.
After this cutoff the leftover least factor is at least `397`. -/
theorem conjecture_of_minFac_le_three_hundred_eighty_nine_or_twin {p : ℕ}
    (hp : p.Prime) (hp7 : 7 ≤ p) (hmod : p % 3 = 1)
    (hcomp : ¬ (p - 2).Prime)
    (h : Nat.minFac (p - 2) ≤ 389 ∨ (Nat.minFac (p - 2) - 2).Prime) :
    a (p - 1) = p := by
  have hpr : (Nat.minFac (p - 2)).Prime :=
    Nat.minFac_prime (ne_of_gt (remaining_p_sub_two_gt_one hp7))
  have hd : Nat.minFac (p - 2) ∣ p - 2 := Nat.minFac_dvd _
  rcases h with h389 | htwin
  · by_cases h293 : Nat.minFac (p - 2) ≤ 293
    · exact conjecture_of_minFac_le_two_hundred_ninety_three_or_twin hp hp7
        hmod hcomp (Or.inl h293)
    · by_cases ht : (Nat.minFac (p - 2) - 2).Prime
      · have h13 : 13 ≤ Nat.minFac (p - 2) :=
          le_trans (by decide : 13 ≤ 294)
            (Nat.succ_le_of_lt (lt_of_not_ge h293))
        exact conjecture_of_larger_twin_dvd hp (five_le_of_seven_le hp7)
          hcomp hpr h13 ht hd
      · have h294 : 294 ≤ Nat.minFac (p - 2) :=
          Nat.succ_le_of_lt (lt_of_not_ge h293)
        by_cases h307 : Nat.minFac (p - 2) ≤ 307
        · have heq :=
            remaining_prime_from_two_hundred_ninety_four_le_three_hundred_seven
              hpr h294 h307 ht
          exact conjecture_of_minFac_three_hundred_seven hp hp7 hmod hcomp heq
        · by_cases h311 : Nat.minFac (p - 2) ≤ 311
          · have h308 : 308 ≤ Nat.minFac (p - 2) :=
              Nat.succ_le_of_lt (lt_of_not_ge h307)
            have heq :=
              remaining_prime_from_three_hundred_eight_le_three_hundred_eleven
                hpr h308 h311 ht
            exact conjecture_of_minFac_three_hundred_eleven hp hp7 hmod hcomp heq
          · by_cases h317 : Nat.minFac (p - 2) ≤ 317
            · have h312 : 312 ≤ Nat.minFac (p - 2) :=
                Nat.succ_le_of_lt (lt_of_not_ge h311)
              have heq :=
                remaining_prime_from_three_hundred_twelve_le_three_hundred_seventeen
                  hpr h312 h317 ht
              exact conjecture_of_minFac_three_hundred_seventeen hp hp7
                hmod hcomp heq
            · by_cases h331 : Nat.minFac (p - 2) ≤ 331
              · have h318 : 318 ≤ Nat.minFac (p - 2) :=
                  Nat.succ_le_of_lt (lt_of_not_ge h317)
                have heq :=
                  remaining_prime_from_three_hundred_eighteen_le_three_hundred_thirty_one
                    hpr h318 h331 ht
                exact conjecture_of_minFac_three_hundred_thirty_one hp hp7
                  hmod hcomp heq
              · by_cases h337 : Nat.minFac (p - 2) ≤ 337
                · have h332 : 332 ≤ Nat.minFac (p - 2) :=
                    Nat.succ_le_of_lt (lt_of_not_ge h331)
                  have heq :=
                    remaining_prime_from_three_hundred_thirty_two_le_three_hundred_thirty_seven
                      hpr h332 h337 ht
                  exact conjecture_of_minFac_three_hundred_thirty_seven hp hp7
                    hmod hcomp heq
                · by_cases h347 : Nat.minFac (p - 2) ≤ 347
                  · have h338 : 338 ≤ Nat.minFac (p - 2) :=
                      Nat.succ_le_of_lt (lt_of_not_ge h337)
                    have heq :=
                      remaining_prime_from_three_hundred_thirty_eight_le_three_hundred_forty_seven
                        hpr h338 h347 ht
                    exact conjecture_of_minFac_three_hundred_forty_seven hp hp7
                      hmod hcomp heq
                  · by_cases h353 : Nat.minFac (p - 2) ≤ 353
                    · have h348 : 348 ≤ Nat.minFac (p - 2) :=
                        Nat.succ_le_of_lt (lt_of_not_ge h347)
                      have heq :=
                        remaining_prime_from_three_hundred_forty_eight_le_three_hundred_fifty_three
                          hpr h348 h353 ht
                      exact conjecture_of_minFac_three_hundred_fifty_three hp hp7
                        hmod hcomp heq
                    · by_cases h359 : Nat.minFac (p - 2) ≤ 359
                      · have h354 : 354 ≤ Nat.minFac (p - 2) :=
                          Nat.succ_le_of_lt (lt_of_not_ge h353)
                        have heq :=
                          remaining_prime_from_three_hundred_fifty_four_le_three_hundred_fifty_nine
                            hpr h354 h359 ht
                        exact conjecture_of_minFac_three_hundred_fifty_nine hp hp7
                          hmod hcomp heq
                      · by_cases h367 : Nat.minFac (p - 2) ≤ 367
                        · have h360 : 360 ≤ Nat.minFac (p - 2) :=
                            Nat.succ_le_of_lt (lt_of_not_ge h359)
                          have heq :=
                            remaining_prime_from_three_hundred_sixty_le_three_hundred_sixty_seven
                              hpr h360 h367 ht
                          exact conjecture_of_minFac_three_hundred_sixty_seven hp hp7
                            hmod hcomp heq
                        · by_cases h373 : Nat.minFac (p - 2) ≤ 373
                          · have h368 : 368 ≤ Nat.minFac (p - 2) :=
                              Nat.succ_le_of_lt (lt_of_not_ge h367)
                            have heq :=
                              remaining_prime_from_three_hundred_sixty_eight_le_three_hundred_seventy_three
                                hpr h368 h373 ht
                            exact conjecture_of_minFac_three_hundred_seventy_three
                              hp hp7 hmod hcomp heq
                          · by_cases h379 : Nat.minFac (p - 2) ≤ 379
                            · have h374 : 374 ≤ Nat.minFac (p - 2) :=
                                Nat.succ_le_of_lt (lt_of_not_ge h373)
                              have heq :=
                                remaining_prime_from_three_hundred_seventy_four_le_three_hundred_seventy_nine
                                  hpr h374 h379 ht
                              exact conjecture_of_minFac_three_hundred_seventy_nine
                                hp hp7 hmod hcomp heq
                            · by_cases h383 : Nat.minFac (p - 2) ≤ 383
                              · have h380 : 380 ≤ Nat.minFac (p - 2) :=
                                  Nat.succ_le_of_lt (lt_of_not_ge h379)
                                have heq :=
                                  remaining_prime_from_three_hundred_eighty_le_three_hundred_eighty_three
                                    hpr h380 h383 ht
                                exact conjecture_of_minFac_three_hundred_eighty_three
                                  hp hp7 hmod hcomp heq
                              · have h384 : 384 ≤ Nat.minFac (p - 2) :=
                                  Nat.succ_le_of_lt (lt_of_not_ge h383)
                                have heq :=
                                  remaining_prime_from_three_hundred_eighty_four_le_three_hundred_eighty_nine
                                    hpr h384 h389 ht
                                exact conjecture_of_minFac_three_hundred_eighty_nine
                                  hp hp7 hmod hcomp heq
  · by_cases h13 : 13 ≤ Nat.minFac (p - 2)
    · exact conjecture_of_larger_twin_dvd hp (five_le_of_seven_le hp7) hcomp
        hpr h13 htwin hd
    · have h12 : Nat.minFac (p - 2) ≤ 12 := Nat.lt_succ_iff.mp (lt_of_not_ge h13)
      exact conjecture_of_minFac_le_twenty_nine hp hp7 hmod hcomp
        (le_trans h12 (by decide : 12 ≤ 29))


private instance : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩

private instance : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩

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

/-- If a prime `ℓ` already divides `x n` and also divides `a n`, then
`ℓ^{v_ℓ(x n)+1} ∣ n+1`. This is the valuation form of Cloitre 6.7 without
requiring `a n = ℓ`. -/
lemma prime_dvd_a_padic {ℓ n : ℕ} [Fact ℓ.Prime] (hn : 0 < n)
    (_hx : ℓ ∣ x n) (ha : ℓ ∣ a n) :
    padicValNat ℓ (x n) + 1 ≤ padicValNat ℓ (n + 1) := by
  have hva : 1 ≤ padicValNat ℓ (a n) :=
    one_le_padicValNat_of_dvd (a_pos hn).ne' ha
  have hformula := padicValNat_a ℓ n hn
  by_cases hle : padicValNat ℓ (x n) ≤ padicValNat ℓ (n + 1)
  · have hmin : min (padicValNat ℓ (x n)) (padicValNat ℓ (n + 1)) =
        padicValNat ℓ (x n) := min_eq_left hle
    have : padicValNat ℓ (a n) =
        padicValNat ℓ (n + 1) - padicValNat ℓ (x n) := by
      rw [hformula, hmin]
    omega
  · have hgt : padicValNat ℓ (n + 1) < padicValNat ℓ (x n) :=
      Nat.lt_of_not_ge hle
    have hmin : min (padicValNat ℓ (x n)) (padicValNat ℓ (n + 1)) =
        padicValNat ℓ (n + 1) := min_eq_right (le_of_lt hgt)
    have : padicValNat ℓ (a n) = 0 := by
      rw [hformula, hmin, Nat.sub_self]
    omega

/-- After `ℓ` divides `x N`, any later `ℓ ∣ a n` needs
`ℓ^{v_ℓ(x N)+1} ∣ n+1`. -/
lemma prime_dvd_a_padic_of_le {ℓ N n : ℕ} [Fact ℓ.Prime]
    (hN : 0 < N) (hNle : N ≤ n) (hd : ℓ ∣ x N) (ha : ℓ ∣ a n) :
    padicValNat ℓ (x N) + 1 ≤ padicValNat ℓ (n + 1) := by
  have hx : ℓ ∣ x n := hd.trans (x_dvd_of_le hN hNle)
  have hn : 0 < n := lt_of_lt_of_le hN hNle
  have h := prime_dvd_a_padic hn hx ha
  have hvle : padicValNat ℓ (x N) ≤ padicValNat ℓ (x n) :=
    (padicValNat_dvd_iff_le (x_pos hn).ne').1
      (pow_padicValNat_dvd.trans (x_dvd_of_le hN hNle))
  omega

/-- If `n ≥ 6` and `3 ∣ a n`, then `81 ∣ n+1`. -/
lemma eighty_one_dvd_succ_of_three_dvd_a {n : ℕ} (hn : 6 ≤ n) (h3 : 3 ∣ a n) :
    81 ∣ n + 1 := by
  have hn0 : 0 < n := by omega
  have hx : 3 ∣ x n := three_dvd_x (le_trans (by decide : 4 ≤ 6) hn)
  have hv := prime_dvd_a_padic hn0 hx h3
  have h27 : 27 ∣ x n := twenty_seven_dvd_x hn
  have hpow : (3 : ℕ) ^ 3 = 27 := by decide
  have hge : 3 ≤ padicValNat 3 (x n) :=
    (padicValNat_dvd_iff_le (x_pos hn0).ne').1 (hpow ▸ h27)
  have : 4 ≤ padicValNat 3 (n + 1) := by omega
  exact (padicValNat_dvd_iff_le (Nat.succ_ne_zero n)).2 this

lemma not_three_dvd_a_of_not_eighty_one {n : ℕ} (hn : 6 ≤ n)
    (h81 : ¬ 81 ∣ n + 1) : ¬ 3 ∣ a n :=
  fun h => h81 (eighty_one_dvd_succ_of_three_dvd_a hn h)

lemma two_hundred_forty_three_dvd_x_seven : 243 ∣ x 7 := by
  have hx : x 7 = x 6 * (a 6 + 2) := x_succ_a (by decide : 0 < (6 : ℕ))
  rw [hx, a_6, show (7 : ℕ) + 2 = 9 from rfl]
  have h27 : 27 ∣ x 6 := twenty_seven_dvd_x (by decide : 6 ≤ 6)
  exact Nat.mul_dvd_mul_right h27 9

lemma two_hundred_forty_three_dvd_x {n : ℕ} (hn : 7 ≤ n) : 243 ∣ x n :=
  two_hundred_forty_three_dvd_x_seven.trans
    (x_dvd_of_le (by decide : 0 < 7) hn)

lemma a_8 : a 8 = 1 := by
  have hn : 0 < (8 : ℕ) := by decide
  have h243 : 243 ∣ x 8 := two_hundred_forty_three_dvd_x (by decide : 7 ≤ 8)
  have h9 : 9 ∣ x 8 := dvd_trans (by decide : 9 ∣ 243) h243
  have hg : Nat.gcd (x 8) 9 = 9 := Nat.gcd_eq_right h9
  rw [a_eq hn, show (8 : ℕ) + 1 = 9 from rfl, hg,
    Nat.div_self (by decide : 0 < 9)]

/-- If `n ≥ 7` and `3 ∣ a n`, then `729 ∣ n+1`. -/
lemma seven_hundred_twenty_nine_dvd_succ_of_three_dvd_a {n : ℕ} (hn : 7 ≤ n)
    (h3 : 3 ∣ a n) : 729 ∣ n + 1 := by
  have hn0 : 0 < n := lt_of_lt_of_le (by decide : 0 < 7) hn
  have hx : 3 ∣ x n := three_dvd_x (le_trans (by decide : 4 ≤ 7) hn)
  have hv := prime_dvd_a_padic hn0 hx h3
  have h243 : 243 ∣ x n := two_hundred_forty_three_dvd_x hn
  have hpow : (3 : ℕ) ^ 5 = 243 := by decide
  have hge : 5 ≤ padicValNat 3 (x n) :=
    (padicValNat_dvd_iff_le (x_pos hn0).ne').1 (hpow ▸ h243)
  have : 6 ≤ padicValNat 3 (n + 1) :=
    (show 5 + 1 ≤ padicValNat 3 (x n) + 1 from Nat.add_le_add_right hge 1).trans hv
  exact (padicValNat_dvd_iff_le (Nat.succ_ne_zero n)).2 this

lemma not_three_dvd_a_of_not_seven_hundred_twenty_nine {n : ℕ} (hn : 7 ≤ n)
    (h729 : ¬ 729 ∣ n + 1) : ¬ 3 ∣ a n :=
  fun h => h729 (seven_hundred_twenty_nine_dvd_succ_of_three_dvd_a hn h)

lemma seven_hundred_twenty_nine_dvd_x_nine : 729 ∣ x 9 := by
  have hx : x 9 = x 8 * (a 8 + 2) := x_succ_a (by decide : 0 < (8 : ℕ))
  rw [hx, a_8, show (1 : ℕ) + 2 = 3 from rfl]
  have h243 : 243 ∣ x 8 := two_hundred_forty_three_dvd_x (by decide : 7 ≤ 8)
  exact Nat.mul_dvd_mul_right h243 3

lemma seven_hundred_twenty_nine_dvd_x {n : ℕ} (hn : 9 ≤ n) : 729 ∣ x n :=
  seven_hundred_twenty_nine_dvd_x_nine.trans
    (x_dvd_of_le (by decide : 0 < 9) hn)

/-- If `n ≥ 9` and `3 ∣ a n`, then `2187 ∣ n+1`. -/
lemma two_thousand_one_hundred_eighty_seven_dvd_succ_of_three_dvd_a
    {n : ℕ} (hn : 9 ≤ n) (h3 : 3 ∣ a n) : 2187 ∣ n + 1 := by
  have hn0 : 0 < n := lt_of_lt_of_le (by decide : 0 < 9) hn
  have hx : 3 ∣ x n := three_dvd_x (le_trans (by decide : 4 ≤ 9) hn)
  have hv := prime_dvd_a_padic hn0 hx h3
  have h729 : 729 ∣ x n := seven_hundred_twenty_nine_dvd_x hn
  have hpow : (3 : ℕ) ^ 6 = 729 := by decide
  have hge : 6 ≤ padicValNat 3 (x n) :=
    (padicValNat_dvd_iff_le (x_pos hn0).ne').1 (hpow ▸ h729)
  have : 7 ≤ padicValNat 3 (n + 1) :=
    (show 6 + 1 ≤ padicValNat 3 (x n) + 1 from Nat.add_le_add_right hge 1).trans hv
  exact (padicValNat_dvd_iff_le (Nat.succ_ne_zero n)).2 this

lemma not_three_dvd_a_of_not_two_thousand_one_hundred_eighty_seven
    {n : ℕ} (hn : 9 ≤ n) (h2187 : ¬ 2187 ∣ n + 1) : ¬ 3 ∣ a n :=
  fun h => h2187 (two_thousand_one_hundred_eighty_seven_dvd_succ_of_three_dvd_a hn h)

lemma ten_dvd_x_nine : 10 ∣ x 9 := by
  have h2 : 2 ∣ x 9 := two_dvd_x (by decide : 2 ≤ 9)
  have h5 : 5 ∣ x 9 := five_dvd_x (by decide : 3 ≤ 9)
  have hcop : Nat.Coprime 2 5 := by decide
  exact hcop.mul_dvd_of_dvd_of_dvd h2 h5

lemma a_9 : a 9 = 1 := by
  have hn : 0 < (9 : ℕ) := by decide
  have hg : Nat.gcd (x 9) 10 = 10 := Nat.gcd_eq_right ten_dvd_x_nine
  rw [a_eq hn, show (9 : ℕ) + 1 = 10 from rfl, hg,
    Nat.div_self (by decide : 0 < 10)]

lemma two_thousand_one_hundred_eighty_seven_dvd_x_ten : 2187 ∣ x 10 := by
  have hx : x 10 = x 9 * (a 9 + 2) := x_succ_a (by decide : 0 < (9 : ℕ))
  rw [hx, a_9, show (1 : ℕ) + 2 = 3 from rfl]
  exact Nat.mul_dvd_mul_right (seven_hundred_twenty_nine_dvd_x (by decide : 9 ≤ 9)) 3

lemma two_thousand_one_hundred_eighty_seven_dvd_x {n : ℕ} (hn : 10 ≤ n) :
    2187 ∣ x n :=
  two_thousand_one_hundred_eighty_seven_dvd_x_ten.trans
    (x_dvd_of_le (by decide : 0 < 10) hn)

/-- If `n ≥ 10` and `3 ∣ a n`, then `6561 ∣ n+1`. -/
lemma six_thousand_five_hundred_sixty_one_dvd_succ_of_three_dvd_a
    {n : ℕ} (hn : 10 ≤ n) (h3 : 3 ∣ a n) : 6561 ∣ n + 1 := by
  have hn0 : 0 < n := lt_of_lt_of_le (by decide : 0 < 10) hn
  have hx : 3 ∣ x n := three_dvd_x (le_trans (by decide : 4 ≤ 10) hn)
  have hv := prime_dvd_a_padic hn0 hx h3
  have h2187 : 2187 ∣ x n := two_thousand_one_hundred_eighty_seven_dvd_x hn
  have hpow : (3 : ℕ) ^ 7 = 2187 := by decide
  have hge : 7 ≤ padicValNat 3 (x n) :=
    (padicValNat_dvd_iff_le (x_pos hn0).ne').1 (hpow ▸ h2187)
  have : 8 ≤ padicValNat 3 (n + 1) :=
    (show 7 + 1 ≤ padicValNat 3 (x n) + 1 from Nat.add_le_add_right hge 1).trans hv
  exact (padicValNat_dvd_iff_le (Nat.succ_ne_zero n)).2 this

lemma not_three_dvd_a_of_not_six_thousand_five_hundred_sixty_one
    {n : ℕ} (hn : 10 ≤ n) (h6561 : ¬ 6561 ∣ n + 1) : ¬ 3 ∣ a n :=
  fun h => h6561 (six_thousand_five_hundred_sixty_one_dvd_succ_of_three_dvd_a hn h)

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

lemma a_7 : a 7 = 2 := by simpa using a_two_four_pow 1

lemma twelve_dvd_x_eleven : 12 ∣ x 11 := by
  have h3 : 3 ∣ x 11 := three_dvd_x (by decide : 4 ≤ 11)
  have hv := v2_x_ge_two 11 (by decide : 2 ≤ 11)
  have hlog : Nat.log 4 (11 / 2) = 1 := by
    have : 11 / 2 = 5 := by decide
    rw [this]
    exact Nat.log_eq_of_pow_le_of_lt_pow (by decide : (4 : ℕ) ^ 1 ≤ 5)
      (by decide : 5 < (4 : ℕ) ^ 2)
  have hge : 4 ≤ padicValNat 2 (x 11) := by
    rw [hv, hlog]
  have h16 : 16 ∣ x 11 := by
    have hpowdvd : (2 : ℕ) ^ 4 ∣ x 11 :=
      (padicValNat_dvd_iff_le (x_pos (by decide : 0 < (11 : ℕ))).ne').2 hge
    have hpow : (2 : ℕ) ^ 4 = 16 := by decide
    rwa [hpow] at hpowdvd
  have h4 : 4 ∣ x 11 := dvd_trans (by decide : 4 ∣ 16) h16
  have hcop : Nat.Coprime 4 3 := by decide
  exact hcop.mul_dvd_of_dvd_of_dvd h4 h3

lemma a_11 : a 11 = 1 := by
  have hn : 0 < (11 : ℕ) := by decide
  have hg : Nat.gcd (x 11) 12 = 12 := Nat.gcd_eq_right twelve_dvd_x_eleven
  rw [a_eq hn, show (11 : ℕ) + 1 = 12 from rfl, hg,
    Nat.div_self (by decide : 0 < 12)]

lemma six_thousand_five_hundred_sixty_one_dvd_x_twelve : 6561 ∣ x 12 := by
  have hx : x 12 = x 11 * (a 11 + 2) := x_succ_a (by decide : 0 < (11 : ℕ))
  rw [hx, a_11, show (1 : ℕ) + 2 = 3 from rfl]
  exact Nat.mul_dvd_mul_right
    (two_thousand_one_hundred_eighty_seven_dvd_x (by decide : 10 ≤ 11)) 3

lemma six_thousand_five_hundred_sixty_one_dvd_x {n : ℕ} (hn : 12 ≤ n) :
    6561 ∣ x n :=
  six_thousand_five_hundred_sixty_one_dvd_x_twelve.trans
    (x_dvd_of_le (by decide : 0 < 12) hn)

/-- If `n ≥ 12` and `3 ∣ a n`, then `19683 ∣ n+1`. -/
lemma nineteen_thousand_six_hundred_eighty_three_dvd_succ_of_three_dvd_a
    {n : ℕ} (hn : 12 ≤ n) (h3 : 3 ∣ a n) : 19683 ∣ n + 1 := by
  have hn0 : 0 < n := lt_of_lt_of_le (by decide : 0 < 12) hn
  have hx : 3 ∣ x n := three_dvd_x (le_trans (by decide : 4 ≤ 12) hn)
  have hv := prime_dvd_a_padic hn0 hx h3
  have h6561 : 6561 ∣ x n := six_thousand_five_hundred_sixty_one_dvd_x hn
  have hpow : (3 : ℕ) ^ 8 = 6561 := by decide
  have hge : 8 ≤ padicValNat 3 (x n) :=
    (padicValNat_dvd_iff_le (x_pos hn0).ne').1 (hpow ▸ h6561)
  have : 9 ≤ padicValNat 3 (n + 1) :=
    (show 8 + 1 ≤ padicValNat 3 (x n) + 1 from Nat.add_le_add_right hge 1).trans hv
  exact (padicValNat_dvd_iff_le (Nat.succ_ne_zero n)).2 this

lemma not_three_dvd_a_of_not_nineteen_thousand_six_hundred_eighty_three
    {n : ℕ} (hn : 12 ≤ n) (h19683 : ¬ 19683 ∣ n + 1) : ¬ 3 ∣ a n :=
  fun h => h19683
    (nineteen_thousand_six_hundred_eighty_three_dvd_succ_of_three_dvd_a hn h)

lemma a_12 : a 12 = 1 :=
  (a_eq_one_iff_dvd (by decide : Nat.Prime 13)).2
    (thirteen_dvd_x (by decide : 11 ≤ 12))

lemma not_seven_dvd_x_seven : ¬ 7 ∣ x 7 :=
  not_prime_dvd_x_succ Nat.prime_seven (by decide : 0 < (6 : ℕ))
    not_seven_dvd_x_six (by
      rw [a_6]
      exact (by decide : ¬ 7 ∣ (7 : ℕ) + 2))

lemma not_seven_dvd_x_eight : ¬ 7 ∣ x 8 :=
  not_prime_dvd_x_succ Nat.prime_seven (by decide : 0 < (7 : ℕ))
    not_seven_dvd_x_seven (by
      rw [a_7]
      exact (by decide : ¬ 7 ∣ (2 : ℕ) + 2))

lemma not_seven_dvd_x_nine : ¬ 7 ∣ x 9 :=
  not_prime_dvd_x_succ Nat.prime_seven (by decide : 0 < (8 : ℕ))
    not_seven_dvd_x_eight (by
      rw [a_8]
      exact (by decide : ¬ 7 ∣ (1 : ℕ) + 2))

lemma not_seven_dvd_x_ten : ¬ 7 ∣ x 10 :=
  not_prime_dvd_x_succ Nat.prime_seven (by decide : 0 < (9 : ℕ))
    not_seven_dvd_x_nine (by
      rw [a_9]
      exact (by decide : ¬ 7 ∣ (1 : ℕ) + 2))

lemma not_seven_dvd_x_eleven : ¬ 7 ∣ x 11 :=
  not_prime_dvd_x_succ Nat.prime_seven (by decide : 0 < (10 : ℕ))
    not_seven_dvd_x_ten (by
      rw [a_10]
      exact (by decide : ¬ 7 ∣ (11 : ℕ) + 2))

lemma not_seven_dvd_x_twelve : ¬ 7 ∣ x 12 :=
  not_prime_dvd_x_succ Nat.prime_seven (by decide : 0 < (11 : ℕ))
    not_seven_dvd_x_eleven (by
      rw [a_11]
      exact (by decide : ¬ 7 ∣ (1 : ℕ) + 2))

lemma not_seven_dvd_x_thirteen : ¬ 7 ∣ x 13 :=
  not_prime_dvd_x_succ Nat.prime_seven (by decide : 0 < (12 : ℕ))
    not_seven_dvd_x_twelve (by
      rw [a_12]
      exact (by decide : ¬ 7 ∣ (1 : ℕ) + 2))

lemma gcd_x_thirteen_fourteen : Nat.gcd (x 13) 14 = 2 := by
  have h2 : 2 ∣ x 13 := two_dvd_x (by decide : 2 ≤ 13)
  have h2g : 2 ∣ Nat.gcd (x 13) 14 := Nat.dvd_gcd h2 (by decide : 2 ∣ 14)
  have hnot7 : ¬ 7 ∣ Nat.gcd (x 13) 14 := fun h =>
    not_seven_dvd_x_thirteen (h.trans (Nat.gcd_dvd_left _ _))
  have hcop : Nat.Coprime (Nat.gcd (x 13) 14) 7 :=
    Nat.coprime_comm.mp (Nat.prime_seven.coprime_iff_not_dvd.2 hnot7)
  have h14 : Nat.gcd (x 13) 14 ∣ 2 * 7 := by
    simpa using Nat.gcd_dvd_right (x 13) 14
  have hdiv2 : Nat.gcd (x 13) 14 ∣ 2 := hcop.dvd_of_dvd_mul_right h14
  exact Nat.dvd_antisymm hdiv2 h2g

lemma a_13 : a 13 = 7 := by
  have hn : 0 < (13 : ℕ) := by decide
  rw [a_eq hn, show (13 : ℕ) + 1 = 14 from rfl, gcd_x_thirteen_fourteen]

lemma fifteen_dvd_x_fourteen : 15 ∣ x 14 := by
  have h3 : 3 ∣ x 14 := three_dvd_x (by decide : 4 ≤ 14)
  have h5 : 5 ∣ x 14 := five_dvd_x (by decide : 3 ≤ 14)
  have hcop : Nat.Coprime 3 5 := by decide
  exact hcop.mul_dvd_of_dvd_of_dvd h3 h5

lemma a_14 : a 14 = 1 := by
  have hn : 0 < (14 : ℕ) := by decide
  have hg : Nat.gcd (x 14) 15 = 15 := Nat.gcd_eq_right fifteen_dvd_x_fourteen
  rw [a_eq hn, show (14 : ℕ) + 1 = 15 from rfl, hg,
    Nat.div_self (by decide : 0 < 15)]

lemma nineteen_thousand_six_hundred_eighty_three_dvd_x_thirteen : 19683 ∣ x 13 := by
  have hx : x 13 = x 12 * (a 12 + 2) := x_succ_a (by decide : 0 < (12 : ℕ))
  rw [hx, a_12, show (1 : ℕ) + 2 = 3 from rfl]
  exact Nat.mul_dvd_mul_right
    (six_thousand_five_hundred_sixty_one_dvd_x (by decide : 12 ≤ 12)) 3

lemma nineteen_thousand_six_hundred_eighty_three_dvd_x {n : ℕ} (hn : 13 ≤ n) :
    19683 ∣ x n :=
  nineteen_thousand_six_hundred_eighty_three_dvd_x_thirteen.trans
    (x_dvd_of_le (by decide : 0 < 13) hn)

/-- If `n ≥ 13` and `3 ∣ a n`, then `59049 ∣ n+1`. -/
lemma fifty_nine_thousand_forty_nine_dvd_succ_of_three_dvd_a
    {n : ℕ} (hn : 13 ≤ n) (h3 : 3 ∣ a n) : 59049 ∣ n + 1 := by
  have hn0 : 0 < n := lt_of_lt_of_le (by decide : 0 < 13) hn
  have hx : 3 ∣ x n := three_dvd_x (le_trans (by decide : 4 ≤ 13) hn)
  have hv := prime_dvd_a_padic hn0 hx h3
  have h19683 : 19683 ∣ x n := nineteen_thousand_six_hundred_eighty_three_dvd_x hn
  have hpow : (3 : ℕ) ^ 9 = 19683 := by decide
  have hge : 9 ≤ padicValNat 3 (x n) :=
    (padicValNat_dvd_iff_le (x_pos hn0).ne').1 (hpow ▸ h19683)
  have : 10 ≤ padicValNat 3 (n + 1) :=
    (show 9 + 1 ≤ padicValNat 3 (x n) + 1 from Nat.add_le_add_right hge 1).trans hv
  exact (padicValNat_dvd_iff_le (Nat.succ_ne_zero n)).2 this

lemma not_three_dvd_a_of_not_fifty_nine_thousand_forty_nine
    {n : ℕ} (hn : 13 ≤ n) (h59049 : ¬ 59049 ∣ n + 1) : ¬ 3 ∣ a n :=
  fun h => h59049 (fifty_nine_thousand_forty_nine_dvd_succ_of_three_dvd_a hn h)

lemma three_pow_eleven_dvd_x_fourteen : 177147 ∣ x 14 := by
  have hx : x 14 = x 13 * (a 13 + 2) := x_succ_a (by decide : 0 < (13 : ℕ))
  rw [hx, a_13, show (7 : ℕ) + 2 = 9 from rfl]
  exact Nat.mul_dvd_mul_right
    (nineteen_thousand_six_hundred_eighty_three_dvd_x (by decide : 13 ≤ 13)) 9

lemma three_pow_eleven_dvd_x {n : ℕ} (hn : 14 ≤ n) : 177147 ∣ x n :=
  three_pow_eleven_dvd_x_fourteen.trans
    (x_dvd_of_le (by decide : 0 < 14) hn)

/-- If `n ≥ 14` and `3 ∣ a n`, then `531441 ∣ n+1`. -/
lemma three_pow_twelve_dvd_succ_of_three_dvd_a
    {n : ℕ} (hn : 14 ≤ n) (h3 : 3 ∣ a n) : 531441 ∣ n + 1 := by
  have hn0 : 0 < n := lt_of_lt_of_le (by decide : 0 < 14) hn
  have hx : 3 ∣ x n := three_dvd_x (le_trans (by decide : 4 ≤ 14) hn)
  have hv := prime_dvd_a_padic hn0 hx h3
  have h177147 : 177147 ∣ x n := three_pow_eleven_dvd_x hn
  have hpow : (3 : ℕ) ^ 11 = 177147 := by decide
  have hge : 11 ≤ padicValNat 3 (x n) :=
    (padicValNat_dvd_iff_le (x_pos hn0).ne').1 (hpow ▸ h177147)
  have : 12 ≤ padicValNat 3 (n + 1) :=
    (show 11 + 1 ≤ padicValNat 3 (x n) + 1 from Nat.add_le_add_right hge 1).trans hv
  exact (padicValNat_dvd_iff_le (Nat.succ_ne_zero n)).2 this

lemma not_three_dvd_a_of_not_three_pow_twelve
    {n : ℕ} (hn : 14 ≤ n) (h531441 : ¬ 531441 ∣ n + 1) : ¬ 3 ∣ a n :=
  fun h => h531441 (three_pow_twelve_dvd_succ_of_three_dvd_a hn h)

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
#print axioms a_5
#print axioms a_6
#print axioms twenty_seven_dvd_x
#print axioms conjecture_of_square_window
#print axioms q_dvd_x_square_window_of_prime_index
#print axioms prime_dvd_a_padic
#print axioms eighty_one_dvd_succ_of_three_dvd_a
#print axioms not_three_dvd_a_of_not_eighty_one
#print axioms conjecture_of_C1
#print axioms larger_twin_dvd_square_window
#print axioms prime_of_no_prime_dvd_lt
#print axioms q_dvd_x_square_window_of_exists
#print axioms q_dvd_x_window_of_no_small_factor
#print axioms conjecture_of_cofactor_seven
#print axioms five_dvd_x_square_window
#print axioms k_mod_three_of_six_five
#print axioms k_ge_five_of_mod_six_five
#print axioms two_hundred_forty_three_dvd_x
#print axioms a_8
#print axioms a_7
#print axioms seven_hundred_twenty_nine_dvd_succ_of_three_dvd_a
#print axioms not_three_dvd_a_of_not_seven_hundred_twenty_nine
#print axioms seven_dvd_x_square_window
#print axioms conjecture_of_minFac_seven
#print axioms q_dvd_x_square_window_of_seven
#print axioms seven_mul_sub_two_le_square
#print axioms five_mul_sub_two_le_square
#print axioms q_dvd_x_square_window_of_five
#print axioms eleven_mul_sub_two_le_square
#print axioms q_dvd_x_square_window_of_eleven
#print axioms thirteen_mul_sub_two_le_square
#print axioms q_dvd_x_square_window_of_thirteen
#print axioms cofactor_injector_le
#print axioms conjecture_of_cofactor_five
#print axioms conjecture_of_minFac_prime_index
#print axioms conjecture_of_minFac_five
#print axioms conjecture_of_minFac_eleven
#print axioms conjecture_of_minFac_thirteen
#print axioms mul_mod_three_eq_two
#print axioms conjecture_of_paired_injectors
#print axioms seven_hundred_twenty_nine_dvd_x
#print axioms two_thousand_one_hundred_eighty_seven_dvd_succ_of_three_dvd_a
#print axioms one_hundred_seven_dvd_x_2459
#print axioms conjecture_of_one_hundred_seven_dvd
#print axioms remaining_prime_eq_one_hundred_seven
#print axioms conjecture_of_minFac_le_one_hundred_seven_or_twin
#print axioms conjecture_of_add_two_overlap
#print axioms conjecture_of_remaining_add_two_overlap
#print axioms a_9
#print axioms a_10
#print axioms two_thousand_one_hundred_eighty_seven_dvd_x
#print axioms six_thousand_five_hundred_sixty_one_dvd_succ_of_three_dvd_a
#print axioms a_11
#print axioms six_thousand_five_hundred_sixty_one_dvd_x
#print axioms nineteen_thousand_six_hundred_eighty_three_dvd_succ_of_three_dvd_a
#print axioms k_mul_sub_two_le_square
#print axioms q_dvd_x_square_window_of_k_le
#print axioms conjecture_of_minFac_k_le
#print axioms q_dvd_x_square_window_of_seventeen
#print axioms q_dvd_x_square_window_of_nineteen
#print axioms q_dvd_x_square_window_of_twentythree
#print axioms q_dvd_x_square_window_of_twentyfive
#print axioms q_dvd_x_square_window_of_twenty_nine
#print axioms q_dvd_x_square_window_of_sq_sub_two
#print axioms q_mod_six_five
#print axioms dvd_x_succ_of_dvd_a_add_two
#print axioms not_prime_dvd_x_succ
#print axioms prime_dvd_a_add_two_of_first_entry
#print axioms a_12
#print axioms a_13
#print axioms a_14
#print axioms not_seven_dvd_x_thirteen
#print axioms nineteen_thousand_six_hundred_eighty_three_dvd_x
#print axioms fifty_nine_thousand_forty_nine_dvd_succ_of_three_dvd_a
#print axioms three_pow_eleven_dvd_x
#print axioms three_pow_twelve_dvd_succ_of_three_dvd_a
#print axioms remaining_minFac_mul_add_eight_le
#print axioms conjecture_of_minFac_entered_add_eight
#print axioms k_mul_sub_two_le_add_eight
#print axioms q_dvd_x_add_eight_window_of_k_le
#print axioms conjecture_of_minFac_k_le_add_eight
#print axioms conjecture_of_minFac_mod_two_overlap_or_k_le_add_eight
#print axioms one_hundred_sixty_three_dvd_x_4073
#print axioms conjecture_of_one_hundred_sixty_three_dvd
#print axioms one_hundred_sixty_seven_dvd_x_2837
#print axioms conjecture_of_one_hundred_sixty_seven_dvd
#print axioms one_hundred_seventy_nine_dvd_x_3041
#print axioms conjecture_of_one_hundred_seventy_nine_dvd
#print axioms two_hundred_twenty_seven_dvd_x_6581
#print axioms conjecture_of_two_hundred_twenty_seven_dvd
#print axioms k_mul_sub_two_le_of_cofactor
#print axioms conjecture_of_factor_k_le_cofactor
#print axioms conjecture_of_exists_factor_injector
#print axioms q_dvd_x_add_eight_window_of_sq_sub_two
#print axioms q_dvd_x_add_eight_window_of_add_six
#print axioms remaining_p_ge_one_hundred_sixty_three
#print axioms conjecture_of_minFac_one_hundred_sixty_three
#print axioms remaining_p_ge_one_hundred_sixty_seven
#print axioms conjecture_of_minFac_one_hundred_sixty_seven
#print axioms remaining_p_ge_one_hundred_seventy_nine
#print axioms conjecture_of_minFac_one_hundred_seventy_nine
#print axioms remaining_p_ge_two_hundred_twenty_seven
#print axioms conjecture_of_minFac_two_hundred_twenty_seven
#print axioms two_hundred_fifty_one_dvd_x_8783
#print axioms conjecture_of_two_hundred_fifty_one_dvd
#print axioms remaining_p_ge_two_hundred_fifty_one
#print axioms conjecture_of_minFac_two_hundred_fifty_one
#print axioms three_hundred_eighty_nine_dvd_x_11279
#print axioms conjecture_of_three_hundred_eighty_nine_dvd
#print axioms remaining_p_ge_three_hundred_eighty_nine
#print axioms conjecture_of_minFac_three_hundred_eighty_nine
#print axioms one_hundred_thirteen_dvd_x_563
#print axioms conjecture_of_one_hundred_thirteen_dvd
#print axioms remaining_p_ge_one_hundred_thirteen
#print axioms conjecture_of_minFac_one_hundred_thirteen
#print axioms one_hundred_twenty_seven_dvd_x_887
#print axioms conjecture_of_one_hundred_twenty_seven_dvd
#print axioms remaining_p_ge_one_hundred_twenty_seven
#print axioms conjecture_of_minFac_one_hundred_twenty_seven
#print axioms one_hundred_thirty_one_dvd_x_653
#print axioms conjecture_of_one_hundred_thirty_one_dvd
#print axioms remaining_p_ge_one_hundred_thirty_one
#print axioms conjecture_of_minFac_one_hundred_thirty_one
#print axioms one_hundred_thirty_seven_dvd_x_683
#print axioms conjecture_of_one_hundred_thirty_seven_dvd
#print axioms remaining_p_ge_one_hundred_thirty_seven
#print axioms conjecture_of_minFac_one_hundred_thirty_seven
#print axioms one_hundred_forty_nine_dvd_x_743
#print axioms conjecture_of_one_hundred_forty_nine_dvd
#print axioms remaining_p_ge_one_hundred_forty_nine
#print axioms conjecture_of_minFac_one_hundred_forty_nine
#print axioms remaining_prime_le_one_hundred_forty_nine
#print axioms conjecture_of_minFac_le_one_hundred_forty_nine_or_twin
#print axioms k_mod_three_of_six_one
#print axioms k_ge_seven_of_mod_six_one
#print axioms k_mul_sub_two_mod_of_six_one
#print axioms conjecture_of_remaining_mod_one_k
#print axioms conjecture_of_exists_mod_one_k
#print axioms remaining_type_B_div_ge_sq
#print axioms conjecture_of_remaining_type_B_k_le
#print axioms remaining_type_B_p_ge
#print axioms remaining_p_sub_two_odd
#print axioms remaining_p_sub_two_gt_one
#print axioms remaining_div_ge_minFac
#print axioms remaining_mod_one_factor_ge_seven
#print axioms remaining_minFac_ge_seven_of_not_five
#print axioms seven_le_div_of_minFac_seven
#print axioms seven_mul_sub_two_ge_seven
#print axioms two_le_seven_mul_of_ge_seven
#print axioms five_le_of_seven_le
#print axioms one_ne_two
#print axioms zero_ne_two
#print axioms one_lt_three
#print axioms one_lt_five
#print axioms one_lt_seven
#print axioms exists_prime_factor_mod_one_of_lt_cube
#print axioms remaining_exists_mod_one_of_lt_cube
#print axioms cube_le_of_all_prime_factors_mod_two
#print axioms conjecture_of_remaining_mod_one_seven
#print axioms conjecture_of_exists_mod_one_seven
#print axioms conjecture_of_remaining_lt_cube_mod_one_seven
#print axioms remaining_type_A_cofactor_prime
#print axioms remaining_type_A_cofactor_mod_one
#print axioms conjecture_of_remaining_type_A_mod_two_seven
#print axioms one_hundred_fifty_seven_dvd_x_1097
#print axioms conjecture_of_one_hundred_fifty_seven_dvd
#print axioms remaining_p_ge_one_hundred_fifty_seven
#print axioms conjecture_of_minFac_one_hundred_fifty_seven
#print axioms one_hundred_seventy_three_dvd_x_863
#print axioms conjecture_of_one_hundred_seventy_three_dvd
#print axioms remaining_p_ge_one_hundred_seventy_three
#print axioms conjecture_of_minFac_one_hundred_seventy_three
#print axioms one_hundred_ninety_one_dvd_x_953
#print axioms conjecture_of_one_hundred_ninety_one_dvd
#print axioms remaining_p_ge_one_hundred_ninety_one
#print axioms conjecture_of_minFac_one_hundred_ninety_one
#print axioms one_hundred_ninety_seven_dvd_x_983
#print axioms conjecture_of_one_hundred_ninety_seven_dvd
#print axioms remaining_p_ge_one_hundred_ninety_seven
#print axioms conjecture_of_minFac_one_hundred_ninety_seven
#print axioms remaining_prime_le_one_hundred_seventy_three
#print axioms remaining_prime_from_one_hundred_seventy_four_le_one_hundred_ninety_seven
#print axioms remaining_prime_le_one_hundred_ninety_seven
#print axioms conjecture_of_minFac_le_one_hundred_ninety_seven_or_twin
#print axioms remaining_type_A_cofactor_mod_two
#print axioms conjecture_of_remaining_type_A_mod_one_five
#print axioms two_hundred_eleven_dvd_x_2741
#print axioms conjecture_of_two_hundred_eleven_dvd
#print axioms remaining_p_ge_two_hundred_eleven
#print axioms conjecture_of_minFac_two_hundred_eleven
#print axioms two_hundred_twenty_three_dvd_x_1559
#print axioms conjecture_of_two_hundred_twenty_three_dvd
#print axioms remaining_p_ge_two_hundred_twenty_three
#print axioms conjecture_of_minFac_two_hundred_twenty_three
#print axioms two_hundred_thirty_three_dvd_x_1163
#print axioms conjecture_of_two_hundred_thirty_three_dvd
#print axioms remaining_p_ge_two_hundred_thirty_three
#print axioms conjecture_of_minFac_two_hundred_thirty_three
#print axioms two_hundred_thirty_nine_dvd_x_1193
#print axioms conjecture_of_two_hundred_thirty_nine_dvd
#print axioms remaining_p_ge_two_hundred_thirty_nine
#print axioms conjecture_of_minFac_two_hundred_thirty_nine
#print axioms remaining_prime_from_one_hundred_ninety_eight_le_two_hundred_eleven
#print axioms remaining_prime_from_two_hundred_twelve_le_two_hundred_twenty_seven
#print axioms remaining_prime_from_two_hundred_twenty_eight_le_two_hundred_thirty_nine
#print axioms remaining_prime_from_one_hundred_ninety_eight_le_two_hundred_thirty_nine
#print axioms conjecture_of_minFac_le_two_hundred_thirty_nine_or_twin
#print axioms two_hundred_fifty_seven_dvd_x_1283
#print axioms conjecture_of_two_hundred_fifty_seven_dvd
#print axioms remaining_p_ge_two_hundred_fifty_seven
#print axioms conjecture_of_minFac_two_hundred_fifty_seven
#print axioms remaining_prime_from_two_hundred_forty_le_two_hundred_fifty_seven
#print axioms conjecture_of_minFac_le_two_hundred_fifty_seven_or_twin
#print axioms two_hundred_sixty_three_dvd_x_6047
#print axioms conjecture_of_two_hundred_sixty_three_dvd
#print axioms remaining_p_ge_two_hundred_sixty_three
#print axioms conjecture_of_minFac_two_hundred_sixty_three
#print axioms remaining_prime_from_two_hundred_fifty_eight_le_two_hundred_sixty_three
#print axioms conjecture_of_minFac_le_two_hundred_sixty_three_or_twin
#print axioms a_add_two_eq
#print axioms two_hundred_sixty_nine_dvd_x_2957
#print axioms conjecture_of_two_hundred_sixty_nine_dvd
#print axioms remaining_p_ge_two_hundred_sixty_nine
#print axioms conjecture_of_minFac_two_hundred_sixty_nine
#print axioms remaining_prime_from_two_hundred_sixty_four_le_two_hundred_sixty_nine
#print axioms conjecture_of_minFac_le_two_hundred_sixty_nine_or_twin
#print axioms a_add_two_mul_gcd
#print axioms dvd_a_add_two_of_dvd_add
#print axioms q_dvd_x_succ_of_dvd_add
#print axioms thirty_dvd_x
#print axioms gcd_thirty_dvd_gcd_x
#print axioms conjecture_of_gcd_thirty
#print axioms two_hundred_seventy_seven_dvd_x_5261
#print axioms conjecture_of_two_hundred_seventy_seven_dvd
#print axioms remaining_p_ge_two_hundred_seventy_seven
#print axioms conjecture_of_minFac_two_hundred_seventy_seven
#print axioms remaining_prime_from_two_hundred_seventy_le_two_hundred_seventy_seven
#print axioms conjecture_of_minFac_le_two_hundred_seventy_seven_or_twin
#print axioms first_entry_iff_dvd_add
#print axioms two_hundred_ten_dvd_x
#print axioms gcd_two_hundred_ten_dvd_gcd_x
#print axioms conjecture_of_gcd_two_hundred_ten
#print axioms two_hundred_eighty_one_dvd_x_3089
#print axioms conjecture_of_two_hundred_eighty_one_dvd
#print axioms remaining_p_ge_two_hundred_eighty_one
#print axioms conjecture_of_minFac_two_hundred_eighty_one
#print axioms remaining_prime_from_two_hundred_seventy_eight_le_two_hundred_eighty_one
#print axioms conjecture_of_minFac_le_two_hundred_eighty_one_or_twin
#print axioms succ_eq_gcd_mul_kq_sub_two
#print axioms exists_first_entry_index
#print axioms gcd_two_hundred_ten_eq_one_of_minFac
#print axioms two_hundred_ninety_three_dvd_x_3221
#print axioms conjecture_of_two_hundred_ninety_three_dvd
#print axioms remaining_p_ge_two_hundred_ninety_three
#print axioms conjecture_of_minFac_two_hundred_ninety_three
#print axioms remaining_prime_from_two_hundred_eighty_two_le_two_hundred_ninety_three
#print axioms conjecture_of_minFac_le_two_hundred_ninety_three_or_twin

#print axioms odd_prime_dvd_two_mul
#print axioms add_two_gcd_eq_of_kq_sub_two
#print axioms succ_pred_kq_sub_two
#print axioms first_entry_iff_dvd_gcd_pred
#print axioms eq_one_of_prime_dvd_pred
#print axioms not_dvd_gcd_pred_of_mem
#print axioms q_dvd_x_of_gcd_eq_one_at_shift
#print axioms three_hundred_seven_dvd_x_3989
#print axioms conjecture_of_three_hundred_seven_dvd
#print axioms remaining_p_ge_three_hundred_seven
#print axioms conjecture_of_minFac_three_hundred_seven
#print axioms three_hundred_eleven_dvd_x_1553
#print axioms conjecture_of_minFac_three_hundred_eleven
#print axioms three_hundred_seventeen_dvd_x_1583
#print axioms conjecture_of_minFac_three_hundred_seventeen
#print axioms three_hundred_thirty_one_dvd_x_6287
#print axioms conjecture_of_minFac_three_hundred_thirty_one
#print axioms three_hundred_thirty_seven_dvd_x_2357
#print axioms conjecture_of_minFac_three_hundred_thirty_seven
#print axioms three_hundred_forty_seven_dvd_x_1733
#print axioms conjecture_of_minFac_three_hundred_forty_seven
#print axioms three_hundred_fifty_three_dvd_x_3881
#print axioms conjecture_of_minFac_three_hundred_fifty_three
#print axioms three_hundred_fifty_nine_dvd_x_3947
#print axioms conjecture_of_minFac_three_hundred_fifty_nine
#print axioms three_hundred_sixty_seven_dvd_x_6971
#print axioms conjecture_of_minFac_three_hundred_sixty_seven
#print axioms three_hundred_seventy_three_dvd_x_2609
#print axioms conjecture_of_minFac_three_hundred_seventy_three
#print axioms three_hundred_seventy_nine_dvd_x_9473
#print axioms conjecture_of_minFac_three_hundred_seventy_nine
#print axioms three_hundred_eighty_three_dvd_x_1913
#print axioms conjecture_of_minFac_three_hundred_eighty_three
#print axioms remaining_prime_from_two_hundred_ninety_four_le_three_hundred_seven
#print axioms remaining_prime_from_three_hundred_eighty_four_le_three_hundred_eighty_nine
#print axioms conjecture_of_minFac_le_three_hundred_eighty_nine_or_twin

end OeisA135508
