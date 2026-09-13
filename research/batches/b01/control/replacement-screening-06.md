# Replacement screening: A001818-C1

Recommendation: PASS for a heavier known-mathematics Lean formalization portfolio. Complete proof within an eight-hour worker window is not guaranteed. No new informal-mathematics or first-formalization claim is justified by this bounded screen. Only C1 should be assigned; the companion claims and general identity remain ownership-related context/helpers, not additional assignments.

Screened 2026-09-13 UTC, read-only. No launch, repository edit, or publication performed.

## Exact source and target

Frozen commit `a2f4a1bb12a28e04a969da78feefac7d1ce49565`; file `FormalConjectures/OEIS/1818.lean` SHA256 `1e41db84e11a5adb981526a75330a597a13ceef8479eb4fb4ef832256496dffe`.

https://github.com/google-deepmind/formal-conjectures/blob/a2f4a1bb12a28e04a969da78feefac7d1ce49565/FormalConjectures/OEIS/1818.lean

Namespace `OeisA1818`. Existing definition:

```lean
def a (n : ℕ) : ℕ :=
  (∏ k ∈ Finset.range n, (2 * k + 1)) ^ 2
```

Exact target, currently research solved with sorry:

```lean
theorem conjecture1 (n : ℕ) (hn : 1 ≤ n) :
    ∀ (ζ : ℂ), IsPrimitiveRoot ζ (2 * n) →
      Matrix.permanent (fun (i j : Fin (2 * n)) =>
        if i = j then
          (1 : ℂ)
        else
          (1 + ζ ^ (i.val - j.val : ℤ)) / (1 - ζ ^ (i.val - j.val : ℤ))
      ) = (a n : ℂ) := by
  sorry
```

Meaning: a specific complex 2n-by-2n root-of-unity matrix has permanent equal to the square of the odd double factorial. This is a complete substantive former conjecture, not an existence helper or finite numerical instance. Preserve the original definition, integer exponent subtraction, diagonal, all primitive roots, and all positive n.

## Primary literature and status

1. She, Sun, Xia, *A novel permanent identity with applications*, arXiv:2208.12167v2, 15 September 2022, Theorem 1.3(ii), even-size case. https://arxiv.org/abs/2208.12167 ; https://arxiv.org/pdf/2208.12167 . Inspected the exact theorem and Section 5 proof. Substituting their matrix size N=2n gives this source statement; changing indices from 1..N to Fin N preserves exponent differences.
2. Zhi-Wei Sun's original MathOverflow question and his answer explicitly confirming the conjecture through that paper: https://mathoverflow.net/questions/427232/a-conjectural-permanent-identity . Answer dated 16 September 2022.
3. https://oeis.org/A001818 . OEIS lists the same paper.
4. DeepMind PR5568, merged, only corrects both declarations to research solved and adds references. Its body explicitly says both retain sorry because proofs are not formalized: https://github.com/google-deepmind/formal-conjectures/pull/5568 . Merge commit `acbe6f1a0623af7a33757e315bd8a76651664c23`.

## Fresh public Lean screening

All-state GitHub issue/PR searches through `gh api search/issues`:

- `repo:google-deepmind/formal-conjectures A001818`: zero.
- `repo:google-deepmind/formal-conjectures 1818`: PR5568 plus unrelated issue1818 (Serre's conjecture II).
- `"OeisA1818"`: zero.
- `"A001818" Lean`: zero.

Web exact-ID/Lean, namespace/conjecture1, and paper-ID/Lean searches located no exact public proof. A text search of the available AlphaProof Nexus results clone found no A1818 match.

Independently read score files for all six exact Epoch A1818 attempts in https://github.com/epoch-research/LeanOpenProblems-results :

- `oeis_1818_conjecture_0` (C1): Anthropic, Google, OpenAI all rejected with sorryAx.
- `oeis_1818_conjecture_2` (C2): Anthropic/OpenAI rejected with sorryAx; Google rejected for f_entry definition mismatch.

Caution: prefix search also returns A181830, which has accepted results and is a DIFFERENT sequence. Those are not evidence of an A001818 proof.

This is bounded absence evidence; later or unindexed public proofs may exist. No accepted exact C1 result was located in the checked sources.

## Ownership and related statements

Keep one owner across A001818-C1, A001818-C2, A002454, and the A356041 general permanent identity. Reserve/assign C1 only; other claims can be context or necessary helpers, not additional target assignments.

- A001818-C2 is the odd-prime permanent congruence modulo p². It is known by Yang–Zhang, *Sun-type determinant and permanent congruences*, arXiv:2605.19502, Proposition 17: https://arxiv.org/abs/2605.19502 . It uses the same general permanent identity but is a different target. Do not claim it from C1 alone.
- A002454: frozen `FormalConjectures/OEIS/2454.lean`, `OeisA2454.conjecture`, is the odd-root-size minor companion of Theorem 1.3(ii). Its frozen research-open label is stale: the same 2022 paper proves it. All three exact Epoch A2454 attempts are rejected. https://oeis.org/A002454 . Do not assign it separately or confuse it with C1.
- A356041 is the general rational permanent identity / zero-specialization motivating She–Sun–Xia. https://oeis.org/A356041 . No `FormalConjectures/OEIS/356041.lean` exists at the frozen baseline. Shared identity machinery makes it related, not a separate worker slot.

No 1818/2454/356041 ownership collision was found in the coordinator assignments, supervision state, or SUPERVISION at screening time.

## Route and implementation risk

Follow the published reduction: the general rational identity connects the matrix permanent to the zero-diagonal shifted matrix. Permutation-cycle cancellation reduces the relevant reciprocal-difference sums; then specialize to distinct powers of a primitive root and evaluate the root-of-unity derangement sum. Section 5 cites Guo–Li–Tao–Wei's identity (Lemma 5.2), arXiv:2206.02592: https://arxiv.org/abs/2206.02592 . Root-power row/column factors cancel, and the remaining scalar is the odd double-factorial square.

This is a proof plan from established literature, not a completed Lean proof. Needed library bridges include integer powers, primitive-root distinctness/nonzero denominators, permutation cycles/derangements, permanent reindexing and scalar factors, and the substantial general identity or its specialization. A quick Mathlib search found no ready Borchardt/hafnian/permanent-to-determinant theorem that removes the central work. The identity cannot simply be imported as an axiom, assumed helper, or cited informal theorem; any needed statement must have a clean formal proof. Start by constructing a dependency plan from the paper and validating the exact statement and base case, then implement reusable lemmas toward the full C1 theorem. A finite check or proved special case is partial progress only.

## Alternative assessed

A004290's global record conjecture remains open on live OEIS. The usual pigeonhole existence argument provides a digit-length bound depending on n, far weaker than the desired logarithmic-scale comparison with the 9k-digit repunit for n<10^k-1. No concrete shortcut was located. It was therefore not ranked ahead of the known permanent theorem. https://oeis.org/A004290 .
