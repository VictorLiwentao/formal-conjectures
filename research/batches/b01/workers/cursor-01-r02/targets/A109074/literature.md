# Literature and novelty audit — A109074 / `OeisA109074.conjecture`

Audit dates: 2026-09-13. Worker: `cursor-01-r02`.
This is a bounded search, not a proof of absence of all prior Lean.

## Frozen statement

- File: `FormalConjectures/OEIS/109074.lean`
- SHA-256: `cd5a2af1993d52ae29df9480d9304cbecae195e24d2ab51a45919806899cfd1e`
- Source baseline: `a2f4a1bb12a28e04a969da78feefac7d1ce49565`
- Lean: `leanprover/lean4:v4.33.1`
- Exact target: `∀ n, frac (n + 1) = (b (n + 1) : ℚ) / (b n : ℚ)`
- `frac n = C(6n-2, 2n) / (2 C(4n-1, 2n))` as a rational
- `b n` is **natural division** of the A005156 factorial product
- Tests: `b 0 = 1`, `b 1 = 1`, `b 2 = 3`, `b 3 = 26`, `b 4 = 646`

Direct `https://oeis.org/A109074` HTML was Cloudflare-blocked in this environment.
Indexed OEIS text and `/internal` pages were used instead.

## OEIS

### A109074

- Title: numerator of `C(6n-2, 2n) / (2 C(4n-1, 2n))`
- Keywords: `nonn,frac`; status approved; offset 0
- Author: N. J. A. Sloane, 2008-05-04
- Comment still worded as a **conjecture**: the binomial ratio equals `A005156(n+1)/A005156(n)`
- Reference: D. M. Bressoud, *Proofs and Confirmations*, Cambridge, 1999, conjecture (6.18)
- Crossrefs: A134357, A005156
- Internal id line: `%I #7 Sep 29 2024 12:58:22`
- Editability: **unknown**. Public pages do not show a pending draft. A public page is not a proof that edits are allowed or forbidden.

### A134357

- Denominator of the same rational; same conjecture comment and Bressoud citation
- Equivalent ratio formulation; reserved to this worker with A109074/A005156

### A005156

- Counts VSASMs of order `2n+1`, also OSASMs of order `2n`
- Product `a(n) = 2^{-n} ∏_{k=1}^n (6k-2)! (2k-1)! / ((4k-1)! (4k-2)!)`
- OEIS attributes the enumeration to a conjecture of Robbins, proved by Kuperberg
- The displayed factorial product is attributed to Razumov–Stroganov
- This is exactly Lean `b` (0-based; empty product `b 0 = 1`)

## Original mathematics

- Robbins / Mills–Robbins–Rumsey: VSASM product conjectures
- Greg Kuperberg, *Symmetry classes of alternating-sign matrices under one roof*, arXiv:math/0008184 (2000–2001), journal Adv. Math. 2002. Ice/Yang–Baxter proof of the VSASM count. The Kuperberg product is a double product, not the factorial form in Lean `b`.
- A. V. Razumov and Yu. G. Stroganov, *On refined enumerations of some symmetry classes of alternating-sign matrices*, arXiv:math-ph/0312071. Factorial product matching Lean `b`.
- The ratio `frac(n+1) = b(n+1)/b n` is then an algebraic identity **once** `b n` is a positive integer equal to that product.

This worker does **not** claim a new ASM enumeration. The remaining Lean content is natural-division integrality of `b` and the rational identity.

## Formal-conjectures history

- Correction PR: https://github.com/google-deepmind/formal-conjectures/pull/5231 (`tadamcz`)
- Related issues: #5225, #5024 (misformalization)
- The old `n=1` counterexample used a different defective source (Fuss–Catalan / A001764 plus an index shift). It is **not** a disproof of this frozen file.
- Frozen `b` tests match A005156: 1, 1, 3, 26, 646

## Existing Lean / AI result screen (2026-09-13)

Searches: `A109074 Lean`, `OeisA109074.conjecture`, `A005156 Lean proof`, GitHub `A109074`, `oeis 109074`.

- No matching AlphaProof Nexus result for this declaration
- Epoch `109074` hits, if any, are coincidental integers, not this sequence (screen report: no A109074 result directories)
- GitHub repository search did not surface a completed proof of the **corrected** `OeisA109074.conjecture`
- A public “Lean proof of A109074” associated with an old Fuss–Catalan formalization is a proof/disproof of a **different** statement
- WOWII / `Kuberwastaken` repositories found in a `c5-k4` search are unrelated graph certificates

Status remains `known_mathematics_formalization_candidate`.
No independently verified exact public Lean proof of the frozen theorem was located.

## Formalization notes

- `b` uses `Nat` division. Rational cancellation of factorials is not a proof.
- `frac(n)` is not always an integer (`frac 3 = 26/3`). Termwise integrality of `frac` is false.
- Equivalent A005156/A134357 product-integrality work stays with this worker.
- Combinatorial integrality via Kuperberg’s ice proof is known mathematics but is out of the intended valuation-scale formalization path.
