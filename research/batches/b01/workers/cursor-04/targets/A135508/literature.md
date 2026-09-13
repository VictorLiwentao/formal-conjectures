# Literature and novelty audit: A135508 / McEachen

Target: `OeisA135508.conjecture` in `FormalConjectures/OEIS/135508.lean`.
Frozen source SHA-256: `3814549cee8601c96c59b923d7ece1c4b26a59b0fd134f49a93cbbc38e914b0b`
(matches `assignments.json` and the working tree).
Baseline commit: `a2f4a1bb12a28e04a969da78feefac7d1ce49565`.
Coordination seed: `238f78bdd5701ae4c97a0d70d4e22e2d45770d7a`.
Audit date: 2026-09-12/13 UTC. Re-checked Cloitre arXiv:2510.18891v3 and OEIS A135508 on 2026-09-13 (including the 07:06Z continuation). Live OEIS terms are `2, 3, 1, 1, 1, 7, 2, …`, matching Lean `a 1` through `a 6`. Direct HTML fetch of oeis.org previously hit Cloudflare; the public sequence page still lists McEachen as a comment and C1 as a comment. Cloitre’s Corollary 6.6 remains conditional on `C₁`. The paper still treats a complete proof of the prime-increment / McEachen statements as requiring a Linnik strengthening beyond current reach. Sequencelib (arXiv:2601.11757, 16 Jan 2026) formalizes OEIS *values*, not McEachen. A later GitHub project on Cloitre *stabilization* (OEIS A073117 / A117846) is a different conjecture and does not prove McEachen. No public exact proof of the square-window statement `q ∣ x(q(q+2)-1)` for every prime `q ≥ 5` was found. An elementary Chebyshev product bound on the leftover injector window, using Mathlib’s `θ(x) ≤ (log 4) x`, does not close at leftover `q ≥ 307`. First-order Bonferroni/Mertens on the square-window AP is not a `∀q` proof (`bonferroni.py`). Remaining Type A numbers are semiprime, and both complementary residue injectors `7r-2` and `5r-2` are packaged; that does not remove the Linnik barrier. Worker cursor-04 proved remaining McEachen for `lpf(p-2) ≤ 293` or a larger-twin least factor; that is not `∀p`.

This is a search log. “No match found” means no public exact solution was found in the sources below. It does not prove the problem is open.

## Statement (intended mathematics)

OEIS A135508, offset 1: `a(n) = x(n+1)/x(n) - 2` with `x(1)=1` and `x(n) = 2 x(n-1) + lcm(x(n-1), n)` for `n > 1`.

McEachen comment (26 Sep 2025): for prime `p` such that `p-2` is not prime, `a(p-1) = p`.

Lean pads `a 0 = 0`. For `n ≥ 1`, Lean `a n` is OEIS `a(n)`. Cloitre’s `c_n` satisfies Lean `a(n) = c_{n+1}` for `n ≥ 1`. McEachen `a(p-1)=p` is Cloitre `c_p = p`.

## Formalization audit (not defective)

Checked against https://oeis.org/A135508 (public page, 2026-09-12).

- Offset 1 vs Lean `a 0 = 0`: tests `a_0` through `a_4` are `rfl` and match the listed terms `2,3,1,1,1`.
- Quantifiers: `p.Prime`, `¬ (p-2).Prime`, conclusion `a (p-1) = p`.
- `p = 2`: `p-2 = 0` is not prime, `a 1 = 2`. Nonvacuous.
- `p = 3`: `p-2 = 1` is not prime, `a 2 = 3`. Nonvacuous.
- For prime `p`, `a(p-1) ∈ {1, p}` holds from `a(n) ∣ n+1`, independently of the conjecture.
- Empty-input / smallest cases are the `rfl` tests and the primes `2` and `3`.

OEIS formula comment `a(2*4^k) = 2` does not match the listed sequence (`a(2) = 3`). Cloitre’s proved identity is `c_{2·4^k} = 2`, i.e. Lean `a(2·4^k - 1) = 2`. That is a comment/index mismatch, not a defect in McEachen’s quantified statement.

## OEIS editability

Public sequence page: no draft banner. `/internal` and `/history` were not usable (Cloudflare challenge; history 404). Record: **unknown**. No OEIS edit was submitted.

## Cloitre (conditional prior result, not a resolution)

Benoit Cloitre, *Primes in LCM recurrences*, arXiv:2510.18891v3 (18 Oct 2025 / 21 Apr 2026).
- https://arxiv.org/abs/2510.18891
- https://arxiv.org/html/2510.18891v3

Unconditional in that paper: inhibition (Lemma 6.1); 2-adic staircase (Prop 6.5), which proves `c_{2·4^k}=2`. Worker cursor-04 formalized Prop. 6.5 as `a_two_four_pow` (Lean `a(2·4^k-1)=2`) without using Cloitre’s `C₁`. That identity is not McEachen.

Conditional on hypothesis `C₁` (`c_n ∈ {1} ∪ primes` for all `n`):
- Theorem 6.2: `c_q = 1` for prime `q ≥ 5` implies `q-2` prime.
- Corollary 6.6: McEachen for `p ≥ 5`. Proof: `c_p ∈ {1,p}`; `c_p=1` plus 6.2 would force `p-2` prime.
- Hypothesis 6.11 is the prime-index form of McEachen plus twin detection. Cloitre uses it as an assumption for the `K=2` density-1 theorem. Worker cursor-04 proved the twin-detection half unconditionally for larger twins `≥ 13` (`larger_twin_eq_one`) and McEachen for several infinite families, including remaining primes with `lpf(p-2) ≤ 293` or a larger-twin least factor, but not the remaining prime-index cases with `lpf(p-2) ≥ 307` not a twin. Reproducing Corollary 6.6 under `C₁` is not a batch resolution. Worker cursor-04 formalized that implication as `conjecture_of_C1` (no `sorryAx`); it does not assume `C₁` and does not prove McEachen. The square-window packaging `conjecture_of_minFac_k_le` (`k ≤ q+2`) is still an existence gap, not a public theorem.

OEIS `/internal` (retrieved 2026-09-13 via HTML snapshot): `%I #47 Oct 01 2025`; McEachen comment still present; C1 still appears as a comment (“1's or primes only”), not as a proof. Editability: **unknown**. No OEIS edit was submitted.

Even under GRH, the usual bound on the least prime in an arithmetic progression is larger than the square window `q(q+2)-1` by logarithmic factors. Pointwise first-entry of every `q ≡ 2 (mod 3)` by index `q(q+2)-1` is therefore beyond current analytic technology as well as beyond Mathlib. This does not forbid an elementary proof that uses more of the recurrence, but it does rule out quoting Linnik or Dirichlet as a finish.

## Schepke thesis (required)

Markus Schepke, *Über Primzahlerzeugende Folgen*, thesis, U. Hannover, 2009.
https://primes.recommend.games/schepke_primzahlerzeugende_folgen.pdf

Section 3.2 treats Cloitre LCM recurrences. Folge 3.5 is A135508 (`q_2(n)`), listed experimentally. No proof of McEachen (the comment is from 2025). McEachen is not in the 2009 thesis.

## Epoch LeanOpenProblems-results

GitHub code search `oeis_135508` in `epoch-research/LeanOpenProblems-results` (2026-09-12). Many runs of `oeis_135508_conjecture_0`; inspected scores include:

- `oeis-lite-200usd-gdm-7x8cgb9c5fw6y5d0`: compile failure; attempted an `r | x(r^2-1)` induction.
- `oeis-open-lite-fable51-wm0v421z5ygi8f6b`, `oeis-open-lite-gpt6astra-37ly1phzfwj2ech4`, `oeis-open-lite-gemini31pro-50xv1587jtk1ud5k`: `proof_scorer: I`, `sorryAx`.
- Several `oeis-lite-200usd-*` and `oeis-full-50usd-*` runs: `sorryAx` or type mismatch.

No accepted exact proof. Failed AI attempts do not quantify difficulty or prove novelty.

## DeepMind / AlphaProof

- `google-deepmind/formal-conjectures` issues search `135508`: no hits (2026-09-12).
- `alphaproof-nexus-results` code search `135508`: no matching path in the query used.
- Local frozen file remains `research open` with `sorry`.

## MathOverflow and other literature

Searches: `A135508`, `McEachen a(p-1)=p`, `LCM recurrence c_n gcd x_{n-1}`, Cloitre K=2.

No MathOverflow thread stating or proving this exact assertion. Nearby LCM-ratio questions are unrelated.

## Conclusion

No exact prior solution of the frozen proposition was found. Cloitre’s McEachen corollary is conditional on `C₁`. Reproducing that conditional corollary is not a batch resolution. Formalizing Dirichlet existence of unbounded injectors is not a resolution either. `conjecture_of_square_window` is a proved reduction of the frozen type to first-entry by `q(q+2)-1`; it is not a proof of that first-entry bound. `conjecture_of_C1` is Cloitre’s Corollary 6.6 as an implication, not a proof of `C₁`.
