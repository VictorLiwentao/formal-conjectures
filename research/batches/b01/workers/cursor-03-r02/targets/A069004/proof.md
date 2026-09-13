# A069004 upper-bound certificate

## Claim

This is a kernel certificate of a known computational counterexample, not a new mathematical discovery.

T. D. Noe (OEIS A069004, 26 Feb 2007) conjectured `π(n) ≥ a(n)` for `n>1`.
PR https://github.com/google-deepmind/formal-conjectures/pull/5453 (j2d9w5xtjn-png, 2026-09-10)
reports `a(512720)=42666` and `π(512720)=42493`. Minimality is not claimed.

The Lean theorems proved here are exactly

- `¬ ∀ n, 1 < n → Nat.primeCounting n ≥ OeisA69004.a n`
- the same-group corollary negating the full `conjecture2` conjunction.

A list of 42494 distinct `s ∈ [1,512720)` with `512720²+s²` prime plus `π(512720)=42493` is enough.
The remaining 172 primes among the reported 42666 are unused.

## Method

1. Pratt/Lucas certificates (`Mathlib` `lucas_primality`) with kernel-reducible `powMod` of fuel 64.
2. Independently compiled chunks `C0`–`C283` of the Epoch Anthropic witness list.
3. Trial-division `countRange` blocks glued to `Nat.primeCounting 512720 = 42493`.
4. No `native_decide`, `Lean.trustCompiler`, or `sorry`.

## Credit

- Mathematics: T. D. Noe (conjecture); j2d9w5xtjn-png (counterexample computation).
- Original Lean statements: The Formal Conjectures Authors.
- Public resource-limited Lean scripts: Epoch OpenAI / Anthropic / Google `oeis_a069004_conjecture_2` runs (all score I).
- This file: Wentao Li, completing an audited kernel check of the Anthropic certificate data after repairing exponentiation fuel.

## Status

`candidate_proof`. Glue, `A069004.lean`, `ExactType.lean` and `TypeMatch.lean` compiled on this VM with `#print axioms` equal to `propext`, `Classical.choice`, `Quot.sound`. A coordinator must reproduce the compile before `independently_verified`.
