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

import research.batches.b01.workers.«codex-01».targets.A079727.A079727
import research.batches.b01.workers.«codex-01».targets.A079727.Reductions
import research.batches.b01.workers.«codex-01».targets.A079727.ProductReduction

/-!
# Exact-type audit for A079727

The checks read source theorem types without using their proof terms.
*Reference:* [frozen A079727](https://github.com/google-deepmind/formal-conjectures/blob/a2f4a1bb12a28e04a969da78feefac7d1ce49565/FormalConjectures/OEIS/79727.lean).
-/

open Lean Meta in
run_cmd Lean.Elab.Command.liftTermElabM do
  let src ← getConstInfo `OeisA79727.conjecture4
  let parsing ← getConstInfo `A079727Audit.conjecture4_parsing
  let lhs := parsing.type.getAppArgs[0]!
  unless ← isDefEq lhs src.type do
    throwError "Parsing audit does not match the exact frozen type"
  logInfo "PASS: conjecture4_parsing audits the complete frozen conjecture4 type."
  let c2 ← getConstInfo `OeisA79727.conjecture2
  let c3 ← getConstInfo `OeisA79727.conjecture3
  let reduction ← getConstInfo `A079727Reduction.conjecture3_implies_conjecture2
  unless ← isDefEq reduction.type (← mkArrow c3.type c2.type) do
    throwError "Reduction does not connect the complete frozen types"
  logInfo "PASS: conjecture3_implies_conjecture2 connects the complete frozen types."
  for (sourceName, reductionName) in
      [(`OeisA79727.conjecture1, `A079727Reduction.conjecture1_iff_half_sum),
       (`OeisA79727.conjecture2, `A079727Reduction.conjecture2_iff_half_sum)] do
    let ci ← getConstInfo reductionName
    forallTelescope ci.type fun xs body => do
      let target ← inferType (mkAppN (mkConst sourceName) xs[:2].toArray)
      unless ← isDefEq body.getAppArgs[0]! target do
        throwError m!"Pointwise reduction does not match {sourceName}"
      logInfo m!"PASS: {reductionName} has the exact applied frozen assertion as its left side."
  for reductionName in
      [`A079727Product.odd_multiple_implies_conjecture4,
       `A079727Product.blocks_implies_conjecture4] do
    let ci ← getConstInfo reductionName
    unless ← isDefEq ci.type.bindingBody! src.type do
      throwError "Product reduction does not conclude the exact frozen conjecture4"
    logInfo m!"PASS: {reductionName} concludes the complete frozen conjecture4 type."
  for n in [`OeisA79727.conjecture1, `OeisA79727.conjecture2,
      `OeisA79727.conjecture3, `OeisA79727.conjecture4] do
    let ci ← getConstInfo n
    logInfo m!"FROZEN TYPE {n}: {ci.type}"

#print axioms A079727Audit.conjecture4_parsing
#print axioms A079727Reduction.conjecture3_implies_conjecture2
#print axioms A079727Reduction.conjecture1_iff_half_sum
#print axioms A079727Product.blocks_implies_conjecture4
