/-
Copyright 2026 The Formal Conjectures Authors.
Copyright 2026 Wentao Li.
Licensed under the Apache License, Version 2.0.
-/
import Core

/-! Pilot kernel count of primes in `[0, 1000)` via trial division. -/

set_option maxHeartbeats 0
set_option maxRecDepth 1000000

open Cert

theorem hc0 : countRange 0 1000 = 168 := by decide +kernel
