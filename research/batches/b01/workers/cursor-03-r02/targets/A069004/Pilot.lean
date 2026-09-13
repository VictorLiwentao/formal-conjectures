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

import Core

/-!
Pilot: one Pratt certificate from the Epoch Anthropic database, independently compiled.
Witness `s = 21`, `n = 512720`, `n^2 + s^2 = 262881798841`.
-/

set_option maxHeartbeats 0
set_option maxRecDepth 1000000

open Cert

def c21 : PC :=
  PC.node 262881798841 19 [(2, 3), (3, 3), (5, 1)]
    [(243409073, 1, PC.node 243409073 3 [(2, 4), (53, 1), (239, 1), (1201, 1)] [])]

theorem c21_ok : PC.ok c21 = true := by decide +kernel

theorem c21_pp : c21.pp = 512720 ^ 2 + 21 ^ 2 := by
  change 262881798841 = 512720 ^ 2 + 21 ^ 2
  norm_num

theorem c21_prime : Nat.Prime (512720 ^ 2 + 21 ^ 2) := by
  have h := PC.prime_of_ok c21_ok
  rwa [c21_pp] at h
