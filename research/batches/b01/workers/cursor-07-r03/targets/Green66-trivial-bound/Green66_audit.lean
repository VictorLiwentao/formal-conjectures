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
-/
import FormalConjectures.GreensOpenProblems.«66»

open Filter

/-!
Exact-type audit against the frozen sorry declaration.

This file imports the sorry source only to `#check` its type. It is not
a proof of `Green66.green_66.variants.trivial_bound`.
-/

#check Green66.green_66.variants.trivial_bound
#print Green66.green_66.variants.trivial_bound

#check (Green66.green_66.variants.trivial_bound :
    ∃ C > (0 : ℝ), ∀ᶠ X : ℝ in atTop,
      ∃ n : ℕ, Green66.IsSumOfTwoSquares n ∧
        (n : ℝ) ∈ Set.Icc (X - C * X ^ (1 / 4 : ℝ)) X)
