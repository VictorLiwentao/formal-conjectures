# Replacement screening 04: A051903 question 2

Screened 2026-09-13 UTC for cursor-01-r03. Substantive exact OEIS question; mathematical novelty remains provisional. The intended negative route is elementary and may be a known consequence of existing machinery. The user accepts known mathematics lacking exact public Lean; no novelty claim is needed for assignment.

## Exact statement

[Source](https://github.com/google-deepmind/formal-conjectures/blob/a2f4a1bb12a28e04a969da78feefac7d1ce49565/FormalConjectures/OEIS/51903.lean), declaration `OeisA51903.conjecture2`.
SHA-256 `3a694eccc4bd92c14e28e609563bad0ecdfb8895f45c6de887b46fcfcd483db4`.
Lean v4.33.1; frozen campaign baseline unchanged.

The source asks whether there exists a natural n with Odd n, a n>1 and b^n congruent to b^(a n) modulo n for every natural b. The function a is the existing maximum prime-factor exponent, using primeFactorsList/count/foldr max. Expected answer NO: prove the negation of the whole RHS existential and a False iff RHS wrapper resolving answer(False). Do not exploit answer(sorry), or change any mathematical domain/definition/quantifier.

Only C2 is assigned. C1 is equivalent to Lehmer's totient problem; C3 fixes base2 and is different. Neither is assigned. Reserve A051903 and [A327295](https://oeis.org/A327295)'s equivalent all-terms-even question together. A327295 explicitly supplies the same universal power-congruence definition. No overlap with current worker groups was found. All earlier retired groups remain excluded.

## Proposed argument and Lean obligations

Put e=a n>1; attain the maximum at an odd prime p with p^e dividing n, and prove e<n. Instantiate the all-b congruence at1+p and reduce modulo p^e. Odd-prime lifting the exponent yields p^(e−1) dividing n−e; since it divides n, it divides e. This contradicts p^(e−1)>e for p≥3 and e≥2. The proposed argument is mathematically screened, not yet Lean-verified.

Mathlib `padicValNat.pow_sub_pow` in NumberTheory/Multiplicity.lean provides relevant LTE machinery. Maximum attainment, factorization/list compatibility, modular reduction, unit cancellation and positivity of natural subtraction must be proved. Partial maximum/LTE helpers alone are not a resolution.

## Public screen and prior mathematics

- Live [A051903](https://oeis.org/A051903) and A327295 were checked for the question/equivalence. Pending OEIS edits and actual editability are unknown, not certified clear.
- All-state DeepMind A051903/51903 searches found ingestion PR5016 and [C1 documentation/Lehmer PR5449](https://github.com/google-deepmind/formal-conjectures/pull/5449), not an exact C2 Lean proof.
- Namespace/Lean/repository and equivalent-mathematics searches found no completed exact C2 artifact.
- No exact C2 result found in AlphaProof Nexus. All three A051903 Epoch attempts inspected have C1 specifications and failed verification; they do not establish anything about C2.
- [Dutta and Dutta preprint, February2026](https://rxiv.org/pdf/2602.0018v1.pdf), Theorem1, characterizes universal power exponents using the maximum prime exponent and Carmichael lambda. All five pages inspected: no explicit odd-number exclusion corollary and no Lean. Its existence makes elementary-corollary/known-machinery framing prudent, not a new-mathematics claim. Independently verify any used theorem rather than assume correctness from posting.

These are bounded search results, not global absence certification. The worker must repeat current public proof/equivalence checks before substantial work and final claims. A valid prior informal proof is acceptable with attribution; a verified prior exact Lean proof retires the target. Credit Thomas Ordowski for the question, The Formal Conjectures Authors for original Lean statement, Wentao Li for actual independent Lean development, and actual mathematical/Lean proof authors if identified. Disclose AI assistance.

The textbook existence helper `OeisA38771.a_n_exists` was considered but not selected: it would not solve either substantive A038771 conjecture. A051903-C2 is the sole replacement assignment.
