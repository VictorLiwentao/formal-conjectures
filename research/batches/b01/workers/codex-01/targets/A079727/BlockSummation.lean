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

import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic

/-!
# Block summation for A079727

*Reference:* [A079727](https://oeis.org/A079727), Peter Bala's 2024 conjectures.
-/

namespace A079727Blocks

/-- Split an initial interval into blocks of equal length. -/
theorem sum_blocks (f : ℕ → ℕ) (p t : ℕ) :
    ∑ k ∈ Finset.range (p * t), f k =
      ∑ i ∈ Finset.range t, ∑ j ∈ Finset.range p, f (p * i + j) := by
  induction t with
  | zero => simp
  | succ t ih =>
    rw [Nat.mul_succ, Finset.sum_range_add, Finset.sum_range_succ, ih]

/-- Divisibility of complete and terminal blocks implies divisibility of the prefix. -/
theorem dvd_prefix_of_blocks (f : ℕ → ℕ) (d p h t : ℕ)
    (hfull : ∀ i, d ∣ ∑ j ∈ Finset.range p, f (p * i + j))
    (hhalf : ∀ i, d ∣ ∑ j ∈ Finset.range (h + 1), f (p * i + j)) :
    d ∣ ∑ k ∈ Finset.range (p * t + h + 1), f k := by
  rw [show p * t + h + 1 = p * t + (h + 1) by omega,
    Finset.sum_range_add, sum_blocks]
  exact dvd_add (Finset.dvd_sum (fun i _ => hfull i)) (hhalf t)

/-- The half of an odd multiple ends halfway through its last block. -/
theorem odd_multiple_index (p t : ℕ) (hp : Odd p) :
    (p * (2 * t + 1) - 1) / 2 = p * t + (p - 1) / 2 := by
  obtain ⟨u, hu⟩ := hp
  have hmul : p * (2 * t + 1) = 2 * (p * t) + p := by ring
  rw [hmul]
  omega

#print axioms sum_blocks
#print axioms dvd_prefix_of_blocks
#print axioms odd_multiple_index

end A079727Blocks
