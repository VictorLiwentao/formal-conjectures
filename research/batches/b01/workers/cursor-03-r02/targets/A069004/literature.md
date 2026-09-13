# A069004 literature and novelty audit

Worker: cursor-03-r02. Date: 2026-09-13. Frozen source commit `a2f4a1bb12a28e04a969da78feefac7d1ce49565`.
Source file SHA-256 `c29abb2a5c1e48761cc6d7ebb4332bd728071b6ea6059263ffcf153800282ca2` matched.

## Mathematical claim

`OeisA69004.a n` counts `s ∈ {1,…,n−1}` with `n²+s²` prime.
T. D. Noe, 26 Feb 2007, conjectured `π(n) ≥ a(n) ≥ π(n)/5` for `n>1` with three equalities.
The assigned theorems negate the upper bound, equivalently the full conjunction.

`Nat.primeCounting n` is `Nat.count Prime (n+1)`, i.e. primes `≤ n`. A `Nat.count Prime` bridge therefore uses cutoff `512721`.

## Original source

- https://oeis.org/A069004 (fetched 2026-09-13). Sequence, comments, PARI `sum(s=1,n-1,isprime(n^2+s^2))`. Offset 1. Author T. D. Noe, 2 Apr 2002.
- Stronger conjecture comment still present on the public page. The 512720 counterexample is not yet on that page.
- Draft URL `https://oeis.org/draft/A069004` returned a Cloudflare challenge. Editability: **unknown** from this environment. No pending-draft claim.

## Known computational disproof (not new mathematics)

- https://github.com/google-deepmind/formal-conjectures/pull/5453 merged 2026-09-10 by `j2d9w5xtjn-png`. Reports `n=512720=2^4·5·13·17·29`, `a(n)=42666`, `π(n)=42493`, two independent deterministic computations, no minimality claim.
- Original stronger conjecture: T. D. Noe, 26 Feb 2007, OEIS A069004.

## Existing Lean attempts (must be credited; not an accepted proof)

All three Epoch `oeis_a069004_conjecture_2` runs score I:

1. OpenAI GPT-5.5, `oeis-full-50usd-oai-jajpvieznaevpoyg`. Pocklington DB, 42494 targets, `native_decide` on the last three facts, compile timeout 1800s.
   https://github.com/epoch-research/LeanOpenProblems-results/blob/main/runs/oeis-full-50usd-oai-jajpvieznaevpoyg/oeis_a069004_conjecture_2/Submission/Spec.lean
2. Anthropic Claude Opus 4.8, `oeis-full-50usd-ant-j0j0g4uzligm1k41`. Pratt/Lucas `PC` trees, `decide +kernel`, no `native_decide`, prime-count chain to 512721, exit 137.
   https://github.com/epoch-research/LeanOpenProblems-results/blob/main/runs/oeis-full-50usd-ant-j0j0g4uzligm1k41/oeis_a069004_conjecture_2/Submission/Spec.lean
3. Google Gemini 3.5 Flash, `oeis-full-50usd-gdm-1s7vwp2si1ap0r6d`. Monolithic trial division / `decide`, exit 137.

This session reuses the Anthropic certificate database and checker, with `powMod` fuel repaired from `e` to `64`. Completing that script is not a newly discovered proof.

## Other searches (bounded)

- GitHub code search `A069004` / `512720` in google-deepmind/formal-conjectures: only the frozen sorry file / PR #5453.
- alphaproof-nexus-results: no A069004 hit in a bounded search.
- Web: `A069004 Lean`, `512720 Lean proof`, `OeisA69004`: no completed kernel proof found.
- MathOverflow: related MSE question on existence of some `n²+s²` prime cites A069004 as open for `a(n)>0`, not the upper bound.
- No match found does not prove absence of every private proof.

## Statement audit

Frozen types match the intended disproof of Noe's upper bound. They do not require minimality, the exact value 42666, or a decision of the lower bound. Nonvacuity: `n=512720>1`. Domain of `a` is `s ∈ Ico 1 n`. Endpoint of `π` is inclusive.

Not defective. `conjecture1` and `without_upper_bound` are outside this assignment.
