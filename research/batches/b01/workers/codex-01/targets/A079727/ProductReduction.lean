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
import research.batches.b01.workers.«codex-01».targets.A079727.BlockSummation

/-!
# Product reduction for A079727 conjecture 4

*Reference:* [A079727](https://oeis.org/A079727), Peter Bala's 2024 conjectures.
-/

namespace A079727Product

/-- Divisibility by each prime square implies divisibility by the square of their product. -/
theorem square_prod_dvd (S : Finset ℕ) (M : ℕ) (hprime : ∀ p ∈ S, p.Prime)
    (hdiv : ∀ p ∈ S, p ^ 2 ∣ M) : (S.prod id) ^ 2 ∣ M := by
  induction S using Finset.induction_on with
  | empty => simp
  | @insert p S hp ih =>
    have hp' := hprime p (Finset.mem_insert_self p S)
    have hprime' : ∀ q ∈ S, q.Prime := fun q hq =>
      hprime q (Finset.mem_insert_of_mem hq)
    have hdiv' : ∀ q ∈ S, q ^ 2 ∣ M := fun q hq =>
      hdiv q (Finset.mem_insert_of_mem hq)
    have hcop : p.Coprime (S.prod id) := Nat.coprime_prod_right_iff.mpr (by
      intro q hq
      exact (Nat.coprime_primes hp' (hprime' q hq)).mpr (by
        intro heq
        exact hp (heq ▸ hq)))
    simpa only [Finset.prod_insert hp, id_eq, mul_pow] using
      (hcop.pow 2 2).mul_dvd_of_dvd_of_dvd
        (hdiv p (Finset.mem_insert_self p S)) (ih hprime' hdiv')

/-- An admissible prime is odd. -/
theorem admissible_odd (p : ℕ) (hp : OeisA3625.A p) : Odd p := by
  apply hp.1.odd_of_ne_two
  intro heq
  subst p
  norm_num [OeisA3625.A] at hp

/-- Prime-square divisibility at odd multiples suffices for the complete fourth conjecture. -/
theorem odd_multiple_implies_conjecture4
    (h : ∀ p, OeisA3625.A p → ∀ m, Odd m → p ^ 2 ∣ OeisA79727.a ((p * m - 1) / 2)) :
    ∀ S : Finset ℕ, (∀ p ∈ S, OeisA3625.A p) →
      (∏ p ∈ S, p) ^ 2 ∣ OeisA79727.a (((∏ p ∈ S, p) - 1) / 2) := by
  intro S hS
  apply square_prod_dvd S _ (fun p hp => (hS p hp).1)
  intro p hp
  have hodd : Odd ((S.erase p).prod id) := by
    apply Nat.coprime_two_left.mp
    apply Nat.coprime_prod_right_iff.mpr
    intro q hq
    exact (admissible_odd q (hS q (Finset.mem_of_mem_erase hq))).coprime_two_left
  have heq : p * (S.erase p).prod id = S.prod id := by
    simpa using Finset.mul_prod_erase S id hp
  change p ^ 2 ∣ OeisA79727.a ((S.prod id - 1) / 2)
  rw [← heq]
  exact h p (hS p hp) ((S.erase p).prod id) hodd

/-- Complete and half block congruences suffice for the fourth conjecture. -/
theorem blocks_implies_conjecture4
    (h : ∀ p, OeisA3625.A p →
      (∀ i, p ^ 2 ∣ ∑ j ∈ Finset.range p, (Nat.choose (2 * (p * i + j)) (p * i + j)) ^ 3) ∧
      (∀ i, p ^ 2 ∣ ∑ j ∈ Finset.range ((p - 1) / 2 + 1),
        (Nat.choose (2 * (p * i + j)) (p * i + j)) ^ 3)) :
    ∀ S : Finset ℕ, (∀ p ∈ S, OeisA3625.A p) →
      (∏ p ∈ S, p) ^ 2 ∣ OeisA79727.a (((∏ p ∈ S, p) - 1) / 2) := by
  apply odd_multiple_implies_conjecture4
  intro p hp m hm
  obtain ⟨t, rfl⟩ := hm
  rw [A079727Blocks.odd_multiple_index p t (admissible_odd p hp)]
  exact A079727Blocks.dvd_prefix_of_blocks
    (fun k => (Nat.choose (2 * k) k) ^ 3) (p ^ 2) p ((p - 1) / 2) t
    (h p hp).1 (h p hp).2

#print axioms square_prod_dvd
#print axioms admissible_odd
#print axioms odd_multiple_implies_conjecture4
#print axioms blocks_implies_conjecture4

end A079727Product
