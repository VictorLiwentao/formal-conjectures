# Literature and public-Lean screen

Target: `Green66.green_66.variants.trivial_bound`.
Screen dates: 2026-09-13 UTC (coordinator screening 03, then this worker
before substantial work and again before the candidate claim).
No search can prove universal absence of a prior proof.

## Mathematical sources

- Ben Green, A list of open problems, problem 66, printed p.32 / PDF
  index 31,
  https://people.maths.ox.ac.uk/greenbj/papers/open-problems.pdf
  Retrieved 2026-09-13. Green asks whether a sum of two squares always
  lies in `[X - (1/10) X^{1/4}, X]`. He records a well-known almost
  trivial `O(X^{1/4})` argument: subtract the greatest square `u^2` less
  than `X`, then the greatest square `v^2` less than `X - u^2`. He
  cites Littlewood, Montgomery, and Erdős as listing the open `1/10`
  question, already called old by Erdős. Green is an exposition source,
  not identified here as the discoverer of the `O(X^{1/4})` bound.
- R. P. Bambah and S. Chowla, On numbers which can be expressed as a sum
  of two squares, Proc. Nat. Inst. Sci. India 13 (1947), 101–103. This
  is the classical gap theorem with constant `> 2√2` on a forward
  interval. The present candidate uses only the coarser successive-square
  remainder bound with a generous `C = 10`, not the Bambah–Chowla
  constant.
- S. Uchiyama, On the distribution of integers representable as a sum of
  the h-th powers, J. Fac. Sci. Hokkaido Univ. Ser. I 18 (1964/65),
  124–127; discussed in arXiv:1712.07243. Not used.
- Erdős problem 222, https://www.erdosproblems.com/222 (retrieved
  2026-09-13): consecutive gaps among sums of two squares. The known
  upper bound recorded there is Bambah–Chowla `n_{k+1} - n_k ≪ n_k^{1/4}`.
  Equivalent fourth-root gap statements belong to this worker; this file
  proves only the frozen Green66 variant.
- OEIS A001481, numbers that are sums of two squares,
  https://oeis.org/A001481 (retrieved 2026-09-13). Public page; comments
  do not contain a Lean proof of the frozen bound. Editability not
  claimed.
- OEIS A256435, first differences of sums of two squares,
  https://oeis.org/A256435 (retrieved 2026-09-13). Comments cite
  Bambah–Chowla and Erdős 222. Unrelated sequence conjectures are not
  assigned. Editability not claimed.
- MathOverflow: https://mathoverflow.net/questions/146398 (Bambah–Chowla
  `x` to `x + C x^{1/4}`); https://mathoverflow.net/questions/121232
  (distribution of `r(n)`); https://mathoverflow.net/questions/402002
  (gap `2√2 n^{1/4}`). Informal mathematics only; no Lean proof of the
  frozen type found.

## Frozen Lean statement

- Campaign baseline `a2f4a1bb12a28e04a969da78feefac7d1ce49565`,
  https://github.com/google-deepmind/formal-conjectures/blob/a2f4a1bb12a28e04a969da78feefac7d1ce49565/FormalConjectures/GreensOpenProblems/66.lean
- SHA-256 `d38ab7e233260302ef58121037a02dc94866ddae820e9fc84308ce7264e07acb`.
- Live `main` retrieved 2026-09-13 still has `sorry` on both `green_66`
  and `green_66.variants.trivial_bound`, same type. An upstream sorry is
  not evidence that no public proof exists.
- Statement PR https://github.com/google-deepmind/formal-conjectures/pull/4398
  (merged 2026-07-16, `d2f4ee88c251c5f987e4d7f630501e8ef0d48ce9`):
  adds the file; no proof.
- Closed statement PR https://github.com/google-deepmind/formal-conjectures/pull/1729
  (closed 2026-01-17): includes a 66.lean statement draft; not a proof.
- Issue search in google-deepmind/formal-conjectures for
  `GreensOpenProblems/66`, `green_66`, `Green 66` on 2026-09-13 returned
  the statement-tracking issue closed by #4398 (#1686). No proof PR
  found.

## Related Lean, not an exact proof of this target

- LeanGenius
  https://github.com/rjwalters/lean-genius/blob/main/proofs/Proofs/Erdos222Problem.lean
  retrieved 2026-09-13. Defines `bambah_chowla_upper_bound` as an
  `axiom`. Downstream lemmas using it are not admissible proofs.
  `IsSumTwoSquares` uses integer witnesses and `Int.toNat`, not the
  frozen natural-square predicate. Inspected, not compiled.
- Epoch LeanOpenProblems-results, HEAD
  `8669ff224d86543fcc3ce192b2768ce175b734dd` (live `main` 2026-09-11),
  run `oeis-lite-200usd-grok46-j6r2uynasidzofcj`,
  `oeis_275409_conjecture_0/Submission/Spec.lean` blob
  `50edcd344d5fcbf633ba3fef760acca7fbd845f9`, lines 11938–11958,
  retrieved 2026-09-13. Lemma `bambah_chowla (X : ℕ)` concludes
  `∃ s t, X < s^2 + t^2 ∧ s^2 + t^2 ≤ X + 2 * X.sqrt + 1`.
  That is a forward interval of length `O(√X)` for natural `X`.
  It is not the frozen real backward `Icc` fourth-root statement.
  Inspected, not compiled. This candidate does not import or reuse
  that script.
- GitHub code search on 2026-09-13 for
  `green_66.variants.trivial_bound` found the DeepMind source file and
  a weiyangzen/awesome_theorems catalog row that treats the informal
  `O(X^{1/4})` bound as known mathematics and explicitly grants no new
  theorem credit and cites no Lean proof artifact
  (`reviewed_as_of` 2026-08-10). Not an exact public Lean proof.
- AlphaProof Nexus `APNOutputs/ErdosProblems` listing and recursive
  tree at `0647711a71183c1ea492ad60860776617ce1ea88` (live `main`
  2026-06-05) contained no `green_66`, `trivial_bound`, `bambah`, or
  Erdős 222 proof path.
- Some GitHub code searches returned HTTP 429. Those misses are
  recorded as inaccessible, not as negative proofs.
- Mathlib `NumberTheory/SumTwoSquares.lean` (v4.33.1 pin): Fermat's
  two-square theorem and the prime-factor criterion. No matching
  `O(X^{1/4})` interval lemma found.
- Mathlib `Data/Nat/Sqrt.lean`: `sqrt_le'`, `lt_succ_sqrt'`,
  `sqrt_le_add`. Ingredients, not the target.
- FormalBook Chapter 04 (Fermat two-squares, with `sorry` gaps):
  https://github.com/mo271/FormalBook/blob/main/FormalBook/Chapter_04.lean
  Not the Green66 interval bound.
- AlphaProof Nexus results
  https://github.com/google-deepmind/alphaproof-nexus-results
  The repository states it contains only successful proofs. Attempted
  Erdős list includes `erdos_66`, which is a different problem from
  Green 66 / Erdős 222. No `green_66` / `trivial_bound` / Bambah file
  was located in bounded search on 2026-09-13. Coordinator screening
  recorded HEAD `0647711a71183c1ea492ad60860776617ce1ea88`.
- Epoch results coordinator HEAD
  `8669ff224d86543fcc3ce192b2768ce175b734dd`. Bounded web and GitHub
  searches on 2026-09-13 did not surface an accepted exact Green66
  trivial-bound proof.

## Formalization novelty

Known informal mathematics. In the sources checked above, no completed
exact public Lean proof of the frozen type (or an equivalent
fourth-root backward-interval statement with natural square witnesses
and a uniform positive `C`) was found. That is not a global absence
guarantee. Later GitHub code searches hit rate limits.

This worker does not claim first-formalization priority and does not
claim a new mathematical theorem.
