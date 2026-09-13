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

import Mathlib.Algebra.Polynomial.Derivative
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic

/-!
# Constants of differentiation at the characteristic bound

*References:*
- [A079727](https://oeis.org/A079727), Peter Bala's 2024 conjectures.
-/

namespace A079727Polynomial

open Polynomial

/-- Below degree $p$, a zero derivative forces every positive-degree coefficient to vanish. -/
theorem coeff_eq_zero_of_derivative_eq_zero (p : ℕ) [Fact p.Prime]
    (f : (ZMod p)[X]) (hf : derivative f = 0) (k : ℕ) (hk : 0 < k) (hkp : k < p) :
    f.coeff k = 0 := by
  have h := congrArg (fun g : (ZMod p)[X] => g.coeff (k - 1)) hf
  simp only [coeff_derivative, coeff_zero, ← Nat.cast_succ, Nat.succ_eq_add_one, Nat.sub_add_cancel hk] at h
  have hne : (k : ZMod p) ≠ 0 := by
    intro hz
    have hd : p ∣ k := (ZMod.natCast_eq_zero_iff k p).mp hz
    exact (Nat.not_dvd_of_pos_of_lt hk hkp) hd
  exact (mul_eq_zero.mp h).resolve_right hne

/-- At degree at most $p$, the only possible terms with zero derivative are $1$ and $X^p$. -/
theorem eq_constant_add_top_of_derivative_eq_zero (p : ℕ) [Fact p.Prime]
    (f : (ZMod p)[X]) (hf : derivative f = 0) (hdeg : f.natDegree ≤ p) :
    f = C (f.coeff 0) + monomial p (f.coeff p) := by
  have hp : p ≠ 0 := (Fact.out : p.Prime).ne_zero
  ext k
  by_cases hk0 : k = 0
  · subst k
    simp [coeff_C, coeff_monomial, hp]
  by_cases hkp : k = p
  · subst k
    simp [coeff_C, hp]
  have hc : f.coeff k = 0 := by
    by_cases hlt : k < p
    · exact coeff_eq_zero_of_derivative_eq_zero p f hf k (Nat.pos_of_ne_zero hk0) hlt
    · exact coeff_eq_zero_of_natDegree_lt (lt_of_le_of_lt hdeg (by omega))
  simp [coeff_C, coeff_monomial, hc, hk0, Ne.symm hkp]

#print axioms coeff_eq_zero_of_derivative_eq_zero
#print axioms eq_constant_add_top_of_derivative_eq_zero

end A079727Polynomial
