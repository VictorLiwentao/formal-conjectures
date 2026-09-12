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

import research.batches.b01.workers.«codex-02».targets.A003162.A003162

/-! Compare proposition expressions without using the original proof terms. -/

namespace B01Codex02

def RawStatement : Prop := Tower (fun n ↦ (OeisA3161.b n : ℤ))
def NormalizedStatement : Prop := Tower (fun n ↦ (OeisA3162.b n).num)

open Lean Meta in
run_meta do
  let raw ← getConstInfo ``OeisA3161.conjecture
  unless ← isDefEq raw.type (mkConst ``RawStatement) do
    throwError "A003161 type mismatch"
  let normalized ← getConstInfo ``OeisA3162.conjecture
  unless ← isDefEq normalized.type (mkConst ``NormalizedStatement) do
    throwError "A003162 type mismatch"
  logInfo "PASS: both Tower conclusions are definitionally equal to the full frozen theorem types."

#print axioms RawStatement
#print axioms NormalizedStatement
#print axioms raw_transfer
#print axioms normalized_transfer

end B01Codex02
