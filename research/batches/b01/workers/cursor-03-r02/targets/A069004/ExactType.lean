/-
Copyright 2026 The Formal Conjectures Authors.
Copyright 2026 Wentao Li.
Licensed under the Apache License, Version 2.0.
Original Lean formalization: The Formal Conjectures Authors.
New Lean proof development: Wentao Li.
-/
import FormalConjectures.OEIS.«69004»

/-!
Separately compiled exact-type audit of the frozen declarations.
Types are copied from `FormalConjectures/OEIS/69004.lean`, not from memory.
-/

#check (OeisA69004.conjecture2.variants.upper_bound_false :
    ¬ ∀ n : ℕ, 1 < n → Nat.primeCounting n ≥ OeisA69004.a n)

#check (OeisA69004.conjecture2 :
    ¬ ((∀ n : ℕ, 1 < n → Nat.primeCounting n ≥ OeisA69004.a n) ∧
      (∀ n : ℕ, 1 < n → 5 * OeisA69004.a n ≥ Nat.primeCounting n) ∧
      Nat.primeCounting 2 = OeisA69004.a 2 ∧
      Nat.primeCounting 10 = OeisA69004.a 10 ∧
      5 * OeisA69004.a 12 = Nat.primeCounting 12))
