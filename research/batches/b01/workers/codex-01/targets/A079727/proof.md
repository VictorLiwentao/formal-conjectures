# A079727 proof status

**Partial. None of the four frozen conjectures, or its full negation, is proved
in this work.** There is no independent verification or mathematical novelty
claim. The `.lean` files prove supporting statements and conditional reductions.

Copyright 2026 The Formal Conjectures Authors.
Copyright 2026 Wentao Li. Apache-2.0.
Original Lean formalization: The Formal Conjectures Authors.
New proof development and write-up: Wentao Li.
AI assistance: OpenAI Codex, acting as codex-01. No additional agents or
independent reviewers participated. Mathematical conjectures: Peter Bala, 2024.

## Exact assigned assertions

Let `a(n)=sum_(k=0)^n binom(2k,k)^3` and let `A(p)` mean that `p` is prime
and `p mod 7` is 3, 5, or 6. The frozen assertions are:

1. For every natural `p` with `A(p)`, `a(p^2)=8+p^2 (mod p^3)`.
2. For every natural `p` with `A(p)`, `a(p(p-1))=p^2 (mod p^3)`.
3. For every natural `p` with `A(p)`, `a((p^2-1)/2)=p^2 (mod p^4)`.
4. For every finite set `S` of admissible primes, with `n=prod S`,
   `n^2` divides `a((n-1)/2)`.

`ExactTypeAudit.lean` reads the actual frozen declaration types. It checks the
C1/C2 reduction left sides, both sides of the C3-to-C2 implication, and the
full conclusions of the C4 reductions by definitional equality. It uses no
original proof as a proof of a new theorem. The exact types are in its log.

## Checked Lean results

| File | Result | Scope |
|---|---|---|
| `A079727.lean` | Product parsing; admissibility of `{3,13}`; its index 19 and divisibility | Audit and one finite case |
| `Reductions.lean` | Carry divisibility, constant tail modulo `p^3`, C2 iff half sum, C3 implies C2 | Unconditional supporting theorems |
| `Reductions.lean` | C1 iff half sum given the endpoint cube congruence | Endpoint hypothesis remains unproved here |
| `Bilinear.lean` | Derivative identity and conservation for the cubic hypergeometric pairing | General algebra; no hypergeometric family constructed |
| `PolynomialKernel.lean` | A degree-at-most-`p` polynomial over `ZMod p` with derivative zero has only constant and degree-`p` terms | Handles the characteristic-`p` degree boundary |
| `BlockSummation.lean` | Complete/partial block decomposition and odd-multiple index | General finite-sum arithmetic |
| `ProductReduction.lean` | Prime-square divisibility combines across a finite set; odd-multiple or block congruences imply exact C4 | Analytic block hypotheses remain unproved here |
| `PowerSeriesCoefficients.lean` | Divisibility of coefficients of powers, boundary coefficient control for a denominator congruent to one, and squaring a signed lift | General algebra; geometric hypotheses remain unproved |

Every printed dependency closure contains only `propext`, `Classical.choice`,
and/or `Quot.sound`. No supporting theorem invokes an upstream `sorry` result,
`native_decide`, an added axiom, or compiler trust. See `verification.md`.

## Informal routes and their limits

The detailed derivation is in `informal-route.md`. It separates three approaches:

- **C1/C2:** A two-digit unit-factor expansion reduces the half sum to three
  finite-field moments. Proposed bilinear identities determine those moments.
  Together with Sun's already-published prime-level theorem, this is a
  complete-looking informal route, awaiting independent mathematical review
  and substantial Lean formalization.
- **C4:** Complete and half blocks vanish modulo `p^2` using the older
  prime-level theorem and an older harmonic congruence. The final block and
  coprime-product deductions are in Lean. The uniform binomial block expansion
  and the published inputs are not proved in Lean here.
- **C3:** A terminating Clausen identity appears to reduce the claim to a
  Legendre square. A conditional formal-group argument would give the required
  precision if specified Jacobi multiplication-map properties hold. Those
  geometric properties, their application at `sqrt(-63)`, and the exact
  Clausen comparison still require proof. This is a proposed route, not a
  finished mathematical proof.

Sun's Theorem 3.2 and the older `a(p-1)` congruence are prior results and are
excluded from any novelty claim. Ordinary-reduction supercongruences cannot
be used directly at the assigned inert primes. The full Landweber chapter
was inaccessible; the literature audit remains bounded.

## Rejected approaches and boundary cases

The initial visual reading of C4 as a product of `(p-1)` was wrong.
For `{3,13}` that alternative gives index 12 and residue 676 modulo 1521,
but the frozen expression gives index 19 and residue zero. The failed Lean
attempt is preserved as text in `scratch/`; it is not a disproof. A later
suggestion that whitespace explained a proof error was also wrong. The
successful reduction uses an explicit `change` before rewriting, and the
exact-type audit verifies its conclusion.

The predicate excludes 0, 1, 2, and 7, and includes 3, 5, and 13. Natural
subtraction and division give the expected values because admissible primes
are odd and at least 3. A finite set imposes distinctness. The empty set gives
`n=1`, so its divisibility is immediate. The first three assertions at `p=3`
pass deterministic arithmetic; no universal conclusion follows from those
checks. The finite-field informal argument treats `p=3` separately and uses
`p!=7` to cancel `1-64` for the other admissible primes.

## Computational evidence

Deterministic screens found no counterexample: 49 admissible primes through
503 for C1–C3, 15 finite-set pairs for C4, 14 block expansions, and 44 primes
through 199 for the coefficientwise bilinear identities. A separate Legendre
screen tests 303 finite-field root lifts and 102 Legendre roots through 101.
All pass. The arithmetic recurrence was cross-checked against exact integers.
These checks are evidence only and are not used as Lean proof shortcuts.
