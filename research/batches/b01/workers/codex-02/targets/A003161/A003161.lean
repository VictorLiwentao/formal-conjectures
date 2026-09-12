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

import FormalConjectures.OEIS.«3161»

/-!
# Conditional transfer for the A003161 literature reduction

The arithmetic inputs are explicit hypotheses, not axioms or proved instances.
Sources: https://ir.cwi.nl/pub/5804/5804D.pdf (Theorem 4) and
https://arxiv.org/abs/1602.04347 (Corollary 4.2).
-/

namespace B01Codex02

/-- The full cubic congruence for an integer sequence. -/
def Tower (f : ℕ → ℤ) : Prop :=
  ∀ (n k p : ℕ), 0 < n → 0 < k → p.Prime → 5 ≤ p →
    f (n * p ^ k) ≡ f (n * p ^ (k - 1)) [ZMOD (p : ℤ) ^ (3 * k)]

/-- The positive half of the central binomial coefficient. -/
def halfCentral (n : ℕ) : ℤ := (2 * n - 1).choose (n - 1)

/-- Coster's shifted squared-binomial sum, including its constant term. -/
def shiftedSquares (n : ℕ) : ℤ :=
  ∑ j ∈ Finset.range n, ((n - 1 + j).choose j : ℤ) ^ 2

/-- Cancel the factor $2$ in a congruence modulo a power of a prime at least $5$. -/
theorem cancel_two {p e : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) {a b : ℤ}
    (h : 2 * a ≡ 2 * b [ZMOD (p : ℤ) ^ e]) :
    a ≡ b [ZMOD (p : ℤ) ^ e] := by
  have hcop : (p ^ e).Coprime 2 :=
    (Nat.coprime_of_lt_prime (by decide : 2 ≠ 0) (by omega : 2 < p) hp).pow_left e
  rw [Int.modEq_iff_dvd] at h ⊢
  rw [← mul_sub] at h
  apply Int.dvd_of_dvd_mul_right_of_gcd_one h
  rw [← Nat.cast_pow]
  exact_mod_cast hcop

/-- Algebraic transfer from the two classical congruences and the normalization identity. -/
theorem raw_transfer
    (hs : Tower shiftedSquares) (hc : Tower halfCentral)
    (hidentity : ∀ n : ℕ, 0 < n →
      2 * (OeisA3161.b n : ℤ) =
        halfCentral n * (3 * shiftedSquares n - halfCentral n ^ 2)) :
    Tower (fun n ↦ (OeisA3161.b n : ℤ)) := by
  intro n k p hn hk hp hp5
  have hu : 0 < n * p ^ k := Nat.mul_pos hn (pow_pos hp.pos _)
  have hl : 0 < n * p ^ (k - 1) := Nat.mul_pos hn (pow_pos hp.pos _)
  apply cancel_two hp hp5
  rw [hidentity _ hu, hidentity _ hl]
  exact (hc n k p hn hk hp hp5).mul
    (((hs n k p hn hk hp hp5).mul_left 3).sub
      ((hc n k p hn hk hp hp5).pow 2))

#print axioms cancel_two
#print axioms raw_transfer

end B01Codex02
