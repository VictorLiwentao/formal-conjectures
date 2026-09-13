/-
Copyright 2026 The Formal Conjectures Authors.
Copyright 2026 Wentao Li.
Licensed under the Apache License, Version 2.0.
Original Lean formalization: The Formal Conjectures Authors.
New Lean proof development: Wentao Li.
-/
import FormalConjectures.OEIS.«69004»
import A069004

/-!
Separately compiled check that the worker theorems inhabit the frozen types.
-/

#check (Cursor03R02.A069004.upper_bound_false :
    ¬ ∀ n : ℕ, 1 < n → Nat.primeCounting n ≥ OeisA69004.a n)

#check (Cursor03R02.A069004.conjecture2 :
    ¬ ((∀ n : ℕ, 1 < n → Nat.primeCounting n ≥ OeisA69004.a n) ∧
      (∀ n : ℕ, 1 < n → 5 * OeisA69004.a n ≥ Nat.primeCounting n) ∧
      Nat.primeCounting 2 = OeisA69004.a 2 ∧
      Nat.primeCounting 10 = OeisA69004.a 10 ∧
      5 * OeisA69004.a 12 = Nat.primeCounting 12))

#print axioms Cursor03R02.A069004.upper_bound_false
#print axioms Cursor03R02.A069004.conjecture2
