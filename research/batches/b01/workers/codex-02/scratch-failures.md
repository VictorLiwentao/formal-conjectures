# Failed or unverified steps

The first conditional-transfer compilation failed in the cancellation lemma.
A `simp only` list included the reverse rewrite `Nat.cast_ofNat` and exhausted
Lean's recursion depth. Lean consequently printed `sorryAx` for declarations in
that failed run. That output is not an accepted proof artifact. The rewrite was
removed. The next attempt still had a natural/integer GCD type mismatch.
An isolated check confirmed that `exact_mod_cast` closes that conversion.
Only a later successful full build and its axiom output may be used.

The Epoch ant submission's proposed cross-digit lifting and freshman's-dream
claims were read as unverified leads. No proof or experiment here establishes
those claims. Their source is recorded in the literature audit. The worker did
not pursue a new p-adic proof after locating the published-theorem reduction.
