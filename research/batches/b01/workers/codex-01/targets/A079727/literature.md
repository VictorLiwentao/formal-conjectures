# A079727 literature audit

Audit date: 2026-09-12. AI assistance: OpenAI Codex, acting as codex-01 for Wentao Li.
This is a bounded search, not a certificate of mathematical novelty.

## Exact sources and source history

- [Live OEIS A079727](https://oeis.org/A079727), read with all comments and links.
  Peter Bala's 2024 conjectures 1–3 agree with the frozen natural-number indices
  and congruence moduli. Conjecture 4 uses `(n-1)/2` with `n` the product of
  distinct admissible primes. A kernel check confirms that the Lean product notation also subtracts one
  outside the entire product. An initial visual parsing suspicion was wrong.
- [OEIS revision history](https://oeis.org/history?seq=A079727), latest displayed
  revision #51, approved 2025-11-25. Revision #43 on 2024-08-01 removes an erroneous
  `/2` from conjecture 2's index. The frozen version has this correction.
  An initial `/A079727/history` request failed; the linked `history?seq=` works.
- [A003625](https://oeis.org/A003625) defines primes in residues 3, 5, 6 modulo 7;
  its terms begin 3, 5, 13. This agrees with `OeisA3625.A`.
- OEIS editability: **unknown**. The public page shows login and approved status;
  the latest public history has no visible pending draft. No authenticated edit
  screen was inspected and no edits were submitted.
- [Frozen Lean source](https://github.com/google-deepmind/formal-conjectures/blob/a2f4a1bb12a28e04a969da78feefac7d1ce49565/FormalConjectures/OEIS/79727.lean).
  SHA-256 verified: `5731cb2c5f91fe20862071d6d7f3331d164277c2107a38d53bbad359a43029c3`.
  Live upstream HEAD still `a2f4a1bb12a28e04a969da78feefac7d1ce49565` when checked
  through GitHub API. Path history contains one commit,
  `1bb238f2be65a7d796fb29a15f1c89f764062515`, from [PR #5016](https://github.com/google-deepmind/formal-conjectures/pull/5016).
  API issue/PR searches `repo:google-deepmind/formal-conjectures 79727` and
  `repo:google-deepmind/formal-conjectures central binomial cubes` returned zero.
  This is search coverage, not a claim that all PR discussions were read.

## Prior results that must not be claimed as new

- Zhi-Hong Sun, [Congruences concerning Legendre polynomials II](https://arxiv.org/abs/1012.3898),
  [v2 PDF](https://arxiv.org/pdf/1012.3898v2), 2012, Theorem 3.2 (printed p. 14).
  For admissible primes the half sum at `(p-1)/2` vanishes modulo `p^2`.
  Terms between that index and `p-1` have central binomial coefficient divisible
  by `p`, so the full sum at `p-1` vanishes modulo `p^2` too. This is the older
  result explicitly credited by OEIS. It is not conjecture 1, 2, or 3.
  Theorem 3.1 gives the prime-level Legendre-square congruence.
- Zhi-Wei Sun, [Open conjectures on congruences](https://arxiv.org/abs/0911.5665),
  Part A, conjecture A1, is the earlier source linked by OEIS; it is not evidence
  that Bala's later assertions have been proved.
- Kibelbek, Long, Moss, Sheller, Yuan,
  [Supercongruences and Complex Multiplication](https://arxiv.org/abs/1210.4489),
  [v3 PDF](https://arxiv.org/pdf/1210.4489v3), 2012; published JNT 164 (2016), 166–178.
  Their `F_3(64)_n` equals this sequence `a(n)`. Theorem 1's multilevel congruence
  assumes **ordinary** reduction. Theorem 2 covers the CM prime-level congruence
  modulo `p^2`, including the supersingular case with value zero. Neither statement
  directly proves the assigned `p^2`-level assertions at the inert primes.
  Corollary 4 of this arXiv version (Corollary 3 in the published paper) gives
  a weighted harmonic sum vanishing modulo `p`; this is relevant to block expansions.

## Formal proof repositories

Live HEADs were checked with `gh api repos/OWNER/REPO/commits/HEAD` and agreed
with the existing local read-only snapshots searched below.

- [AlphaProof Nexus results](https://github.com/google-deepmind/alphaproof-nexus-results/tree/0647711a71183c1ea492ad60860776617ce1ea88):
  `0647711a71183c1ea492ad60860776617ce1ea88`. No text/path match for 79727 or
  central-binomial cubes was located by the bounded local search.
- [Epoch harness](https://github.com/epoch-research/LeanOpenProblems/tree/30d502f684fa2fc2dcfc0a933f3648421ba75e8d):
  `30d502f684fa2fc2dcfc0a933f3648421ba75e8d`.
  `apn/data/oeis/Isolated/oeis_79727_conjecture_2.lean` and its source were inspected.
  They include the residue 7 modulo 14, admitting `p=7`, unlike the frozen predicate.
- [Epoch results](https://github.com/epoch-research/LeanOpenProblems-results/tree/8669ff224d86543fcc3ce192b2768ce175b734dd):
  `8669ff224d86543fcc3ce192b2768ce175b734dd`. The tree contains three submissions for
  `oeis_79727_conjecture_2`, in the ant, gdm and oai $50 runs. Actual `Spec.lean`
  and `scores.json` files were read. All have unfinished proofs and were rejected
  for `sorryAx`; the gdm submission includes finite cases but leaves the general
  residue cases unfinished. No accepted exact proof was found there.
  These failures are not evidence of openness or difficulty. Their broader
  prime predicate also precludes treating them as exact frozen-type submissions.
- Initial browser requests guessed `epochai` as the organization and failed;
  the verified organization is `epoch-research`, accessed through GitHub APIs
  and existing snapshots.

## Broader bounded searches

Queries included the sequence ID and combinations of central binomial cubes,
`p^2-1`, `p^4`, Bala congruences, supersingular/inert primes, Dwork, hypergeometric
supercongruences and complex multiplication. Searches included arXiv and
MathOverflow. No exact published solution to C1–C3 was located in this coverage.
The broad search returned many irrelevant results; no claim is based on those.

- [MathOverflow question 433264](https://mathoverflow.net/questions/433264/binomial-coefficient-congruence-modulo-pn)
  discusses binomial scaling, not this sum. It points to the classical
  Ljunggren–Jacobsthal–Kazandzidis congruence and warns against confusing a tower
  congruence with direct scaling to the first level.
- [R. Bajaj's public Bala campaign](https://github.com/rbajaj5/a183068-supercongruence/blob/main/related-results/Bala110ProofCampaign.md)
  appeared in assertion-based searches. The repository tree and 110-record TSV
  were inspected; the TSV has no A079727 row. Its other claimed solutions were
  not pursued because they are outside this assignment.

## Further checks on the Legendre route

- Coster and van Hamme, [Supercongruences of Atkin and Swinnerton-Dyer type for
  Legendre polynomials](https://ir.cwi.nl/pub/1600/1600D.pdf), 1991.
  Theorem 1 assumes the CM prime splits, so it cannot be applied at the assigned
  inert primes. Theorem 3.1 concerns a degree-`p` formal rational map with
  specified numerator/denominator bounds. Substituting `p^2` is not justified.
- Chisholm, Deines, Long, Nebe, Swisher,
  [p-Adic Analogues of Ramanujan Type Formulas for 1/pi](https://www.mdpi.com/2227-7390/1/1/9),
  2013, [accessible primary PDF](https://d-nb.info/1163276057/34).
  Theorems 1 and 2 give prime-level congruences modulo `p^2`; Proposition 16
  discusses Frobenius lifts and the supersingular case. The proof uses the
  degree-`p^2` multiplication-by-`-p` map. The paper does not directly give
  `P_((p^2-1)/2)(sqrt(-63)) = plus or minus p (mod p^3)`.
  The MDPI page initially returned HTTP 429; its PDF mirror was readable.
- Landweber, [Supersingular elliptic curves and congruences for Legendre
  polynomials](https://doi.org/10.1007/BFb0078039), LNM 1326 (1988), 69–93.
  The publisher page and two-page preview were accessible; the full chapter
  was subscription-only in this session. Its exact theorem scope is unverified.
- Baker, [A supersingular congruence for modular forms](https://www.maths.gla.ac.uk/~ajb/dvi-ps/modforms.pdf),
  Acta Arith. 86 (1998), 91–100, relates modular forms modulo the supersingular
  ideal to formal-group coefficients. The stated theorem is not an exact
  A079727 prime-power congruence.
- Honda, [Two congruence properties of Legendre polynomials](https://ir.library.osaka-u.ac.jp/repo/ouka/all/7242/),
  Osaka J. Math. 13 (1976), 131–133. The primary PDF was accessible from the
  repository; its equation extraction is poor. The first alternative PDF
  endpoint returned 429. No exact-target theorem is claimed from it.
- [Atkin and Swinnerton-Dyer congruences and noncongruence modular forms](https://www.kurims.kyoto-u.ac.jp/~kenkyubu/bessatsu/open/B51/pdf/B51_016.pdf)
  restates the KLMSY prime-level theorem and harmonic corollary, and explicitly
  limits the displayed multilevel conjecture to ordinary primes.

Additional queries included `"P_{(p^2-1)/2}"`, `Legendre supersingular p^3`,
`central binomial supersingular p^4`, and the equivalent terminating
Clausen-square formulation. No exact prior resolution was located. The
inaccessible Landweber chapter remains a literature gap, not evidence of a
new result.

## Checkpoint refresh

At 2026-09-12 23:58 UTC, all four GitHub HEADs above were rechecked and
unchanged; see `final_upstream_check.json`. The live OEIS entry still displays
the same four conjectures and its older-result attribution. The final history
request failed in the browsing tool; the successful earlier history reading
is the history evidence used here. No claim is made from the failed refresh.

- Noriko Yui, [Jacobi quartics, Legendre polynomials and formal groups](https://doi.org/10.1007/BFb0078046),
  LNM 1326 (1988), 182–215. The publisher page confirms the chapter and its
  references, including Landweber, Honda and Manin. The full chapter is
  subscription-only in this session. Its precise congruence statements were
  not read. It is a priority source for checking whether the proposed Jacobi
  argument is already covered by an older general theorem.
