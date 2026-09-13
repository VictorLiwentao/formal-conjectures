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
# Parsing and finite-case audit for A079727

*References:*
- [A079727](https://oeis.org/A079727), conjectured by Peter Bala in 2024.
-/

namespace A079727Audit

/-- Both members of $\{3,13\}$ belong to A003625. -/
theorem witness_admissible : ∀ p ∈ ({3, 13} : Finset ℕ), OeisA3625.A p := by
  intro p hp
  simp only [Finset.mem_insert, Finset.mem_singleton] at hp
  rcases hp with rfl | rfl <;> norm_num [OeisA3625.A]

/-- The frozen product notation subtracts one from the entire product. -/
theorem product_index (S : Finset ℕ) :
    (∏ p ∈ S, p - 1) / 2 = ((S.prod id) - 1) / 2 := by
  rfl

/-- The index for $\{3,13\}$ is $19$. -/
theorem witness_index : (∏ p ∈ ({3, 13} : Finset ℕ), p - 1) / 2 = 19 := by
  norm_num

/-- The witness index satisfies the intended divisibility. -/
theorem witness_divisibility : 39 ^ 2 ∣ OeisA79727.a 19 := by
  norm_num [OeisA79727.a, Finset.sum_range_succ,
    Nat.choose_eq_descFactorial_div_factorial, Nat.descFactorial, Nat.factorial]

/-- The parsed statement has the intended product-minus-one form. -/
theorem conjecture4_parsing :
    (∀ (S : Finset ℕ), (∀ p ∈ S, OeisA3625.A p) →
      (∏ p ∈ S, p) ^ 2 ∣ OeisA79727.a ((∏ p ∈ S, p - 1) / 2)) ↔
    (∀ (S : Finset ℕ), (∀ p ∈ S, OeisA3625.A p) →
      (S.prod id) ^ 2 ∣ OeisA79727.a ((S.prod id - 1) / 2)) := by
  rfl

#print axioms witness_admissible
#print axioms product_index
#print axioms witness_index
#print axioms witness_divisibility
#print axioms conjecture4_parsing

end A079727Audit
