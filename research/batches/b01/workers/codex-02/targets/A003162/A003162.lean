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

import FormalConjectures.OEIS.«3162»
import research.batches.b01.workers.«codex-02».targets.A003161.A003161

/-!
# Conditional transfer for the A003162 literature reduction

The identity for the rational numerator includes the required integrality bridge.
It remains an explicit hypothesis in this formal certificate.
Sources: https://ir.cwi.nl/pub/5804/5804D.pdf (Theorem 4) and
https://arxiv.org/abs/1602.04347 (Corollary 4.2).
-/

namespace B01Codex02

/-- Transfer to the exact frozen numerator convention for the normalized sequence. -/
theorem normalized_transfer
    (hs : Tower shiftedSquares) (hc : Tower halfCentral)
    (hidentity : ∀ n : ℕ, 0 < n →
      2 * (OeisA3162.b n).num = 3 * shiftedSquares n - halfCentral n ^ 2) :
    Tower (fun n ↦ (OeisA3162.b n).num) := by
  intro n k p hn hk hp hp5
  have hu : 0 < n * p ^ k := Nat.mul_pos hn (pow_pos hp.pos _)
  have hl : 0 < n * p ^ (k - 1) := Nat.mul_pos hn (pow_pos hp.pos _)
  apply cancel_two hp hp5
  rw [hidentity _ hu, hidentity _ hl]
  exact ((hs n k p hn hk hp hp5).mul_left 3).sub
    ((hc n k p hn hk hp hp5).pow 2)

#print axioms normalized_transfer

end B01Codex02
