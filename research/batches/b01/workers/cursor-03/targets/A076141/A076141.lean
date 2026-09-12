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

Original Lean formalization: The Formal Conjectures Authors.
New proof development and write-up: Wentao Li.
This file is a type/statement audit. It does not reproduce a public prior proof.
-/

import FormalConjectures.OEIS.«76141»

/-!
# A076141 type audit

Frozen declaration: `OeisA76141.conjecture`.
Exact type: `∀ (n : ℕ), OeisA76141.a n ≤ 1`.

A public Lean proof of this exact statement is recorded in `literature.md`.
This worker does not reproduce that argument.
-/

#check @OeisA76141.conjecture
#print OeisA76141.conjecture
#print axioms OeisA76141.conjecture

example : OeisA76141.binaryPattern 0 = [0] := rfl
example : OeisA76141.binaryPattern 1 = [1] := rfl
example : OeisA76141.a 0 = 1 := by decide
example : OeisA76141.a 1 = 1 := by decide
example : OeisA76141.a 2 = 1 := by decide
example : OeisA76141.a 3 = 0 := by decide
example : OeisA76141.a 27 = 1 := by decide
