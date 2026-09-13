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

import Mathlib.RingTheory.PowerSeries.Basic
import Mathlib.Tactic

/-!
# Coefficient divisibility for the A079727 formal-group route

*Reference:* [A079727](https://oeis.org/A079727), Peter Bala's 2024 conjectures.
-/

namespace A079727Coefficients

open PowerSeries

variable {R : Type*} [CommRing R]

/-- Below a fixed degree, divisibility of coefficients passes to powers. -/
theorem pow_dvd_coeff_pow_below (F : R⟦X⟧) (d : R) (q j n : ℕ)
    (hF : ∀ i < q, d ∣ coeff i F) (hn : n < q) : d ^ j ∣ coeff n (F ^ j) := by
  induction j generalizing n with
  | zero => simp
  | succ j ih =>
    rw [pow_succ F, coeff_mul, pow_succ d]
    apply Finset.dvd_sum
    intro ij hij
    have hsum := Finset.mem_antidiagonal.mp hij
    exact mul_dvd_mul (ih ij.1 (by omega)) (hF ij.2 (by omega))

/-- A zero constant term also controls the boundary coefficient of powers at least two. -/
theorem pow_dvd_coeff_pow_boundary (F : R⟦X⟧) (d : R) (q j : ℕ)
    (hF : ∀ i < q, d ∣ coeff i F) (hzero : coeff 0 F = 0) (hj : 2 ≤ j) :
    d ^ j ∣ coeff q (F ^ j) := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hj
  rw [show 2 + k = (k + 1) + 1 by omega, pow_succ F, coeff_mul, pow_succ d]
  apply Finset.dvd_sum
  intro ij hij
  have hsum := Finset.mem_antidiagonal.mp hij
  by_cases hi : ij.1 = 0
  · simp [hi, coeff_zero_eq_constantCoeff, map_pow,
      ← coeff_zero_eq_constantCoeff_apply, hzero]
  by_cases hj' : ij.2 = 0
  · simp [hj', hzero]
  exact mul_dvd_mul (pow_dvd_coeff_pow_below F d q (k + 1) ij.1 hF (by omega))
    (hF ij.2 (by omega))

/-- A vanishing second constant coefficient removes the boundary term of a product. -/
theorem dvd_coeff_mul_boundary (F D : R⟦X⟧) (d : R) (q : ℕ)
    (hF : ∀ i < q, d ∣ coeff i F) (hD : coeff 0 D = 0) : d ∣ coeff q (F * D) := by
  rw [coeff_mul]
  apply Finset.dvd_sum
  intro ij hij
  have hsum := Finset.mem_antidiagonal.mp hij
  by_cases hj : ij.2 = 0
  · simp [hj, hD]
  exact dvd_mul_of_dvd_left (hF ij.1 (by omega)) _

/-- A denominator congruent to one preserves the boundary coefficient modulo the square. -/
theorem square_dvd_numerator_sub_coeff (F D A : R⟦X⟧) (d : R) (q : ℕ)
    (hF : ∀ i < q, d ∣ coeff i F) (hD : coeff 0 D = 0)
    (hA : A = F * (1 + C d * D)) : d ^ 2 ∣ coeff q A - coeff q F := by
  rw [hA, mul_add, mul_one, map_add, add_sub_cancel_left]
  rw [show F * (C d * D) = C d * (F * D) by ring, coeff_C_mul, pow_two]
  exact mul_dvd_mul_left d (dvd_coeff_mul_boundary F D d q hF hD)

/-- A signed lift modulo the cube yields a square congruence modulo the fourth power. -/
theorem fourth_power_dvd_square_sub (p x e : R) (he : e ^ 2 = 1)
    (hx : p ^ 3 ∣ x - e * p) : p ^ 4 ∣ x ^ 2 - p ^ 2 := by
  obtain ⟨r, hr⟩ := hx
  have hx' : x = e * p + p ^ 3 * r := by linear_combination hr
  refine ⟨2 * e * r + p ^ 2 * r ^ 2, ?_⟩
  calc
    x ^ 2 - p ^ 2 = p ^ 2 * (e ^ 2 - 1) + p ^ 4 * (2 * e * r + p ^ 2 * r ^ 2) := by
      rw [hx']
      ring
    _ = p ^ 4 * (2 * e * r + p ^ 2 * r ^ 2) := by rw [he]; ring

#print axioms pow_dvd_coeff_pow_below
#print axioms pow_dvd_coeff_pow_boundary
#print axioms dvd_coeff_mul_boundary
#print axioms square_dvd_numerator_sub_coeff
#print axioms fourth_power_dvd_square_sub

end A079727Coefficients
