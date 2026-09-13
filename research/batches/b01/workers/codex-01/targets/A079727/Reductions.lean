/-
Copyright 2026 The Formal Conjectures Authors.
Copyright 2026 Wentao Li.

Original Lean formalization: The Formal Conjectures Authors.
New proof development and write-up: Wentao Li.

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.
-/

import FormalConjectures.OEIS.«79727»

/-!
# Truncation reductions for A079727

*References:*
- [A079727](https://oeis.org/A079727), Peter Bala's 2024 conjectures.
-/

namespace A079727Reduction

/-- A carry at the $p^r$ digit makes the central binomial coefficient divisible by $p$. -/
theorem prime_dvd_central_binom (p r k : ℕ) (hp : p.Prime) (hr : 0 < r)
    (hk : k < p ^ r) (hcarry : p ^ r ≤ 2 * k) : p ∣ Nat.choose (2 * k) k := by
  apply Nat.dvd_of_factorization_pos
  rw [two_mul, Nat.factorization_choose' hp (show Nat.log p (k + k) <
    Nat.log p (k + k) + r + 1 by omega)]
  apply Nat.ne_of_gt
  apply Finset.card_pos.mpr
  refine ⟨r, ?_⟩
  simp only [Finset.mem_filter, Finset.mem_Ico, Nat.mod_eq_of_lt hk]
  omega

/-- The sequence has constant residue modulo $p^3$ above the halfway point of $p^2$. -/
theorem tail_mod_eq (p m : ℕ) (hp : p.Prime)
    (hlo : (p ^ 2 - 1) / 2 ≤ m) (hhi : m < p ^ 2) :
    OeisA79727.a m ≡ OeisA79727.a ((p ^ 2 - 1) / 2) [MOD p ^ 3] := by
  let n := (p ^ 2 - 1) / 2
  change OeisA79727.a m ≡ OeisA79727.a n [MOD p ^ 3]
  revert hhi
  induction m, hlo using Nat.le_induction with
  | base => intro _; rfl
  | succ m hm ih =>
    intro hhi
    have hbound : m < p ^ 2 := by omega
    have ih' := ih hbound
    have hdiv : p ^ 3 ∣ (Nat.choose (2 * (m + 1)) (m + 1)) ^ 3 := by
      exact pow_dvd_pow_of_dvd (prime_dvd_central_binom p 2 (m + 1) hp (by decide)
        hhi (by omega)) 3
    have hz := Nat.modEq_zero_iff_dvd.mpr hdiv
    simpa only [OeisA79727.a, Finset.sum_range_succ, Nat.add_zero] using ih'.add hz

/-- The second conjecture is equivalent to its half-sum version for each admissible prime. -/
theorem conjecture2_iff_half_sum (p : ℕ) (hp : OeisA3625.A p) :
    (OeisA79727.a (p * (p - 1)) ≡ p ^ 2 [MOD p ^ 3]) ↔
      OeisA79727.a ((p ^ 2 - 1) / 2) ≡ p ^ 2 [MOD p ^ 3] := by
  have hp2 := hp.1.two_le
  have heq : p * (p - 1) = p ^ 2 - p := by
    rw [Nat.mul_sub_left_distrib]
    ring_nf
  have ht := tail_mod_eq p (p * (p - 1)) hp.1
    (by
      rw [heq]
      have : 2 * p ≤ p ^ 2 := by nlinarith
      omega)
    (by
      rw [heq]
      have : 0 < p ^ 2 := by positivity
      omega)
  exact ⟨fun h => ht.symm.trans h, fun h => ht.trans h⟩

/-- The full third assertion implies the full second assertion. -/
theorem conjecture3_implies_conjecture2
    (h3 : ∀ p : ℕ, OeisA3625.A p →
      OeisA79727.a ((p ^ 2 - 1) / 2) ≡ p ^ 2 [MOD p ^ 4]) :
    ∀ p : ℕ, OeisA3625.A p →
      OeisA79727.a (p * (p - 1)) ≡ p ^ 2 [MOD p ^ 3] := by
  intro p hp
  apply (conjecture2_iff_half_sum p hp).mpr
  exact (h3 p hp).of_dvd (pow_dvd_pow p (by decide : 3 ≤ 4))

/-- Successive sequence values differ by one central-binomial cube. -/
theorem a_succ (n : ℕ) : OeisA79727.a (n + 1) =
    OeisA79727.a n + (Nat.choose (2 * (n + 1)) (n + 1)) ^ 3 := by
  change (∑ k ∈ Finset.range (n + 1 + 1), (Nat.choose (2 * k) k) ^ 3) = _
  rw [Finset.sum_range_succ]
  rfl

/-- The endpoint cube congruence reduces the first assertion to the same half sum. -/
theorem conjecture1_iff_half_sum (p : ℕ) (hp : OeisA3625.A p)
    (hendpoint : (Nat.choose (2 * p ^ 2) (p ^ 2)) ^ 3 ≡ 8 [MOD p ^ 3]) :
    (OeisA79727.a (p ^ 2) ≡ 8 + p ^ 2 [MOD p ^ 3]) ↔
      OeisA79727.a ((p ^ 2 - 1) / 2) ≡ p ^ 2 [MOD p ^ 3] := by
  have hpos : 0 < p ^ 2 := pow_pos hp.1.pos _
  have hsucc : p ^ 2 - 1 + 1 = p ^ 2 := by omega
  have hsum := a_succ (p ^ 2 - 1)
  rw [hsucc] at hsum
  have htail := tail_mod_eq p (p ^ 2 - 1) hp.1 (by omega) (by omega)
  have ht : OeisA79727.a (p ^ 2) ≡
      OeisA79727.a ((p ^ 2 - 1) / 2) + 8 [MOD p ^ 3] := by
    rw [hsum]
    exact htail.add hendpoint
  constructor
  · intro h
    apply Nat.ModEq.add_right_cancel' 8
    exact ht.symm.trans (by simpa only [Nat.add_comm] using h)
  · intro h
    exact ht.trans (by simpa only [Nat.add_comm] using h.add_right 8)

#print axioms prime_dvd_central_binom
#print axioms tail_mod_eq
#print axioms conjecture2_iff_half_sum
#print axioms conjecture3_implies_conjecture2
#print axioms a_succ
#print axioms conjecture1_iff_half_sum

end A079727Reduction
