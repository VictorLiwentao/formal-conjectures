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

Original statement formalization: The Formal Conjectures Authors.
New independent Lean development and write-up: Wentao Li.
Mathematics: classical successive greatest-square remainder bound, as
described by Ben Green, A list of open problems, problem 66. This is not a
proof of the open fixed-constant 1/10 question. The sharper Bambah–Chowla
gap theorem is not used.
-/
import FormalConjectures.GreensOpenProblems.66

/-!
Independent Lean proof of `Green66.green_66.variants.trivial_bound`.

This file imports the frozen source only for `IsSumOfTwoSquares`. It does
not apply the admitted `Green66.green_66.variants.trivial_bound` or
`Green66.green_66`.

Classification: known_mathematics_formalization, not new mathematics.
This does not settle Green problem 66 with constant `1/10`.
-/

set_option linter.unusedSectionVars false
set_option linter.style.moduleDocstring false
set_option autoImplicit false

open Filter Real

namespace Green66TrivialBound

open Green66 (IsSumOfTwoSquares)

/-- The greatest square `⌊√y⌋₊ ^ 2` does not exceed `y`. -/
lemma floor_sqrt_sq_le {y : ℝ} (hy : 0 ≤ y) :
    (⌊√y⌋₊ : ℝ) ^ 2 ≤ y := by
  have hm : (⌊√y⌋₊ : ℝ) ≤ √y := Nat.floor_le (sqrt_nonneg y)
  have h0 : 0 ≤ (⌊√y⌋₊ : ℝ) := Nat.cast_nonneg _
  have : (⌊√y⌋₊ : ℝ) ^ 2 ≤ √y ^ 2 := (sq_le_sq₀ h0 (sqrt_nonneg y)).2 hm
  rwa [sq_sqrt hy] at this

/-- `y` is strictly less than the next square after `⌊√y⌋₊`. -/
lemma lt_succ_floor_sqrt_sq {y : ℝ} (hy : 0 ≤ y) :
    y < ((⌊√y⌋₊ : ℝ) + 1) ^ 2 := by
  have hlt : √y < (⌊√y⌋₊ : ℝ) + 1 := Nat.lt_floor_add_one (√y)
  have h0 : 0 ≤ √y := sqrt_nonneg y
  have h1 : 0 ≤ (⌊√y⌋₊ : ℝ) + 1 := add_nonneg (Nat.cast_nonneg _) zero_le_one
  have : √y ^ 2 < ((⌊√y⌋₊ : ℝ) + 1) ^ 2 := (sq_lt_sq₀ h0 h1).2 hlt
  rwa [sq_sqrt hy] at this

/-- Remainder after the greatest square below `y` is `< 2⌊√y⌋₊ + 1`. -/
lemma sub_floor_sqrt_sq_lt {y : ℝ} (hy : 0 ≤ y) :
    y - (⌊√y⌋₊ : ℝ) ^ 2 < 2 * (⌊√y⌋₊ : ℝ) + 1 := by
  have hlt := lt_succ_floor_sqrt_sq hy
  have hexp : ((⌊√y⌋₊ : ℝ) + 1) ^ 2 =
      (⌊√y⌋₊ : ℝ) ^ 2 + 2 * (⌊√y⌋₊ : ℝ) + 1 := by ring
  linarith

/-- Remainder after the greatest square below `y` is `< 2√y + 1`. -/
lemma sub_floor_sqrt_sq_lt_sqrt {y : ℝ} (hy : 0 ≤ y) :
    y - (⌊√y⌋₊ : ℝ) ^ 2 < 2 * √y + 1 := by
  have hrem := sub_floor_sqrt_sq_lt hy
  have hm : (⌊√y⌋₊ : ℝ) ≤ √y := Nat.floor_le (sqrt_nonneg y)
  linarith

/-- Nested real square roots match the frozen `rpow` exponent `1/4`. -/
lemma sqrt_sqrt_eq_rpow_one_div_four {X : ℝ} (hX : 0 ≤ X) :
    √(√X) = X ^ (1 / 4 : ℝ) := by
  have hhalf : (1 / 2 : ℝ) * (1 / 2) = (1 / 4 : ℝ) := by norm_num
  calc
    √(√X) = (√X) ^ (1 / 2 : ℝ) := sqrt_eq_rpow _
    _ = (X ^ (1 / 2 : ℝ)) ^ (1 / 2 : ℝ) := by rw [sqrt_eq_rpow]
    _ = X ^ ((1 / 2 : ℝ) * (1 / 2)) := (rpow_mul hX _ _).symm
    _ = X ^ (1 / 4 : ℝ) := by rw [hhalf]

/-- For `X ≥ 1`, the first remainder is at most `3 √X`. -/
lemma remainder_le_three_sqrt {X : ℝ} (hX : 1 ≤ X) :
    X - (⌊√X⌋₊ : ℝ) ^ 2 ≤ 3 * √X := by
  have hX0 : 0 ≤ X := le_trans zero_le_one hX
  have hrem := sub_floor_sqrt_sq_lt_sqrt hX0
  have hsqrt1 : 1 ≤ √X := by
    have : √(1 : ℝ) ≤ √X := sqrt_le_sqrt hX
    simpa [sqrt_one] using this
  linarith

/-- Exact frozen proposition of `Green66.green_66.variants.trivial_bound`. -/
theorem trivial_bound :
    ∃ C > (0 : ℝ), ∀ᶠ X : ℝ in atTop,
      ∃ n : ℕ, IsSumOfTwoSquares n ∧
        (n : ℝ) ∈ Set.Icc (X - C * X ^ (1 / 4 : ℝ)) X := by
  refine ⟨(10 : ℝ), by norm_num, ?_⟩
  filter_upwards [eventually_ge_atTop (1 : ℝ)] with X hX
  have hX0 : 0 ≤ X := le_trans zero_le_one hX
  set u := ⌊√X⌋₊
  set R := X - (u : ℝ) ^ 2
  have hR0 : 0 ≤ R := sub_nonneg.mpr (floor_sqrt_sq_le hX0)
  set v := ⌊√R⌋₊
  set n := u ^ 2 + v ^ 2
  refine ⟨n, ⟨u, v, rfl⟩, ?_⟩
  have hncast : (n : ℝ) = (u : ℝ) ^ 2 + (v : ℝ) ^ 2 := by
    simp [n, Nat.cast_add, Nat.cast_pow]
  have hv2 : (v : ℝ) ^ 2 ≤ R := floor_sqrt_sq_le hR0
  have hnle : (n : ℝ) ≤ X := by
    have : (u : ℝ) ^ 2 + (v : ℝ) ^ 2 ≤ (u : ℝ) ^ 2 + R := add_le_add_left hv2 _
    simpa [hncast, R] using this
  have hgap : X - (n : ℝ) < 2 * √R + 1 := by
    have : R - (v : ℝ) ^ 2 < 2 * √R + 1 := sub_floor_sqrt_sq_lt_sqrt hR0
    simpa [hncast, R] using this
  have hRle : R ≤ 3 * √X := remainder_le_three_sqrt hX
  have hsqrtR : √R ≤ √3 * √(√X) := by
    have h3 : 0 ≤ (3 : ℝ) := by norm_num
    have hmul : √R ≤ √(3 * √X) := sqrt_le_sqrt hRle
    have : √(3 * √X) = √(3 : ℝ) * √(√X) := sqrt_mul h3 (√X)
    simpa [this] using hmul
  have hsqrt3 : √(3 : ℝ) ≤ 2 := by
    have hle : √(3 : ℝ) ≤ √(4 : ℝ) := sqrt_le_sqrt (by norm_num)
    have h4 : √(4 : ℝ) = 2 := by
      have := sqrt_sq (by positivity : (0 : ℝ) ≤ 2)
      simpa using this
    linarith
  have hone : 1 ≤ X ^ (1 / 4 : ℝ) := one_le_rpow hX (by norm_num : (0 : ℝ) ≤ 1 / 4)
  have hpow : √(√X) = X ^ (1 / 4 : ℝ) := sqrt_sqrt_eq_rpow_one_div_four hX0
  have hC : 2 * √R + 1 ≤ 10 * X ^ (1 / 4 : ℝ) := by
    have h1 : 2 * √R ≤ 2 * (√(3 : ℝ) * √(√X)) := by
      nlinarith [sqrt_nonneg R]
    have h2 : 2 * (√(3 : ℝ) * √(√X)) ≤ 4 * √(√X) := by
      nlinarith [sqrt_nonneg (√X), hsqrt3]
    have h3 : 4 * √(√X) + 1 ≤ 5 * X ^ (1 / 4 : ℝ) := by
      rw [hpow]
      nlinarith [hone]
    have h4 : 5 * X ^ (1 / 4 : ℝ) ≤ 10 * X ^ (1 / 4 : ℝ) := by
      nlinarith [rpow_nonneg hX0 (1 / 4 : ℝ)]
    linarith
  have hlow : X - 10 * X ^ (1 / 4 : ℝ) ≤ (n : ℝ) := by
    have : X - (n : ℝ) ≤ 10 * X ^ (1 / 4 : ℝ) := le_trans (le_of_lt hgap) hC
    linarith
  exact Set.mem_Icc.mpr ⟨hlow, hnle⟩

example :
    ∃ C > (0 : ℝ), ∀ᶠ X : ℝ in atTop,
      ∃ n : ℕ, IsSumOfTwoSquares n ∧
        (n : ℝ) ∈ Set.Icc (X - C * X ^ (1 / 4 : ℝ)) X :=
  trivial_bound

end Green66TrivialBound

#print axioms Green66TrivialBound.trivial_bound
#check Green66.green_66.variants.trivial_bound
#check Green66TrivialBound.trivial_bound
