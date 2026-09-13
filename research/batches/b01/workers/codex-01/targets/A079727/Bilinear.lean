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

import Mathlib.RingTheory.Derivation.Basic
import Mathlib.Tactic.Ring

/-!
# Bilinear conservation algebra for the A079727 research route

*References:*
- [A079727](https://oeis.org/A079727), Peter Bala's 2024 conjectures.
-/

namespace A079727Bilinear

variable {R A : Type*} [CommRing R] [CommRing A] [Algebra R A]

/-- Four times the bilinear expression for the cubic hypergeometric equation. -/
def pairing (d : Derivation R A A) (x y z : A) : A :=
  4 * (1 - x) * (y * d (d z) + z * d (d y) - d y * d z) -
    2 * x * (y * d z + z * d y) - x * y * z

/-- Eight times the cubic hypergeometric differential operator. -/
def equation (d : Derivation R A A) (x y : A) : A :=
  8 * (1 - x) * d (d (d y)) - 12 * x * d (d y) - 6 * x * d y - x * y

/-- Differentiating the pairing gives a bilinear combination of the two equations. -/
theorem deriv_pairing (d : Derivation R A A) (x y z : A) (hx : d x = x) :
    2 * d (pairing d x y z) = y * equation d x z + z * equation d x y := by
  simp only [pairing, equation, map_sub, map_add, Derivation.leibniz,
    show d (4 : A) = 0 from d.map_natCast 4,
    show d (2 : A) = 0 from d.map_natCast 2, Derivation.map_one_eq_zero, smul_eq_mul, hx]
  ring

/-- The pairing has zero derivative for solutions over a ring where two is cancellable. -/
theorem pairing_conserved (d : Derivation R A A) (x y z : A) (hx : d x = x)
    (h2 : IsRegular (2 : A)) (hy : equation d x y = 0) (hz : equation d x z = 0) :
    d (pairing d x y z) = 0 := by
  have h := deriv_pairing d x y z hx
  rw [hy, hz, mul_zero, mul_zero, add_zero] at h
  exact h2.left (by simpa using h)

#print axioms deriv_pairing
#print axioms pairing_conserved

end A079727Bilinear
