# Literature audit

Checked 2026-09-12 UTC. Conclusion: both targets are consequences of published
results by the explicit [joint derivation](literature-reduction.md). Independent
review is pending. No complete formal solution was located or produced.

## Decisive sources

- M. J. Coster, *Supercongruences*, CWI AM-R8918 (1989),
  [catalogue](https://ir.cwi.nl/pub/5804),
  [original PDF](https://ir.cwi.nl/pub/5804/5804D.pdf), Theorem 4, printed page 5.
  The relevant page was rendered and read visually. See the joint derivation for
  exact parameters and the constant-term convention. The report cites the full
  proof in the 1988 thesis, pages 49–55; those pages were not inspected.
- P. J. Miana, H. Ohtsuka and N. Romero,
  [*Sums of powers of Catalan triangle numbers*, arXiv:1602.04347v1](https://arxiv.org/html/1602.04347),
  Corollary 4.2(i), supplies the cubic identity. Its integer quotient form is
  enough for the frozen rational numerator convention.
- [A112029](https://oeis.org/A112029) independently identifies the needed shifted
  square-sum congruence with Coster's Theorem 4 (Bala, November 29, 2024).

## Live OEIS and provenance

Read the comments, links, formulas and history of
[A003161](https://oeis.org/A003161) and [A003162](https://oeis.org/A003162),
plus the equivalent normalized odd-index record [A183069](https://oeis.org/A183069).
The live conjecture comments name Peter Bala, March 20 and March 26, 2023,
respectively. The frozen files' Sun/November 16, 2019 attribution is unsupported
by these sources and should be corrected only by the coordinator or a later
upstream contribution.

History evidence:
[A003161 revisions 37–46](https://oeis.org/history?seq=A003161),
[A003162 latest revisions](https://oeis.org/history?seq=A003162), and
[A003162 revisions 25–34](https://oeis.org/history?seq=A003162&start=10).
The March 2023 revisions show Bala introducing and generalizing the assertions.
Editability/pending status: **unknown** for both. The public pages show login
and approved published records, with no visible current draft. That is not
proof that edits are available or that no private draft exists. No edits attempted.
The initially guessed `/A003161/history` and `/A003162/history` URLs failed;
following the actual history links succeeded.

## Repository audit

The frozen baseline is `a2f4a1bb12a28e04a969da78feefac7d1ce49565`.
Both source hashes match the assignment register. GitHub current source files,
file histories, and issue/PR searches were queried through the public API.
See [upstream-audit.json](upstream-audit.json) for URLs and results.
File history:
[3161](https://github.com/google-deepmind/formal-conjectures/commits/main/FormalConjectures/OEIS/3161.lean),
[3162](https://github.com/google-deepmind/formal-conjectures/commits/main/FormalConjectures/OEIS/3162.lean).
The introduction is commit `1bb238f2be65a7d796fb29a15f1c89f764062515` (#5016).
3162 also has a documentation change in
`b8a21903c05a59fbfdd04615896deedd38163c8d` (#5449).
Bare numeric issue searches also return unrelated issues numbered 3161/3162;
those are not mathematical matches.

[AlphaProof Nexus results](https://github.com/google-deepmind/alphaproof-nexus-results)
was checked at `0647711a71183c1ea492ad60860776617ce1ea88`.
The complete tree was untruncated. All `APNOutputs/OEIS` source files were searched
for both IDs and ballot terminology; see [nexus-audit.json](nexus-audit.json).
No matching proof was found in this bounded audit.

[Epoch LeanOpenProblems](https://github.com/epoch-research/LeanOpenProblems)
was checked at `30d502f684fa2fc2dcfc0a933f3648421ba75e8d`.
Its isolated names are `oeis_3161_conjecture_1` and
`oeis_3162_supercongruence_conjecture`. The latter uses natural-number division,
so equivalence with the frozen rational-numerator formulation requires integrality.

[Epoch results](https://github.com/epoch-research/LeanOpenProblems-results)
was checked at `8669ff224d86543fcc3ce192b2768ce175b734dd`.
The recursive root response was truncated. To avoid a false negative, all 18
OEIS run directories were listed individually without recursive truncation.
Only the three `oeis-full-50usd` runs contain these target names. All six
`Submission/Spec.lean` files and score reports were read; see
[epoch-audit.json](epoch-audit.json) for exact source and result URLs. Four retain `sorry`.
The other two fail verification for changed division semantics and an unsafe
proof declaration. The long A003161 notes in the ant run contain numerical
claims and unproved lifting suggestions, not a proof; their claim that numerical
checks rule out all counterexamples is unjustified. No such claim is adopted here.

## Prior public partial work

[rbajaj5/a183068-supercongruence](https://github.com/rbajaj5/a183068-supercongruence)
was inspected at `3085b46fdbce945d156d2b5b8b9d1a66627b4375`.
Its [ballot audit](https://github.com/rbajaj5/a183068-supercongruence/blob/3085b46fdbce945d156d2b5b8b9d1a66627b4375/related-results/CatalanBallotPowerSupercongruenceAudit.md)
records only a reduction and finite checks for these targets.
Its [mixed-binomial report](https://github.com/rbajaj5/a183068-supercongruence/blob/3085b46fdbce945d156d2b5b8b9d1a66627b4375/related-results/BalaAugustMixedBinomialFollowOn.md)
section 6 separately cites Coster for the shifted square sum. The elementary
connection between those reports is made explicit in our joint derivation.
No claim about the rest of that repository is needed.

[Kuberwastaken/c5-k4](https://github.com/Kuberwastaken/c5-k4), commit
`9ae8ed4872fa5c9955b3380c82dcda73de6630e3`, had no path match for these targets
in its untruncated tree. Its entire unrelated content was not audited.

## Search coverage and limits

Web searches included both IDs with proof/supercongruence; A183069; ballot and
Catalan-triangle power sums; Gould's S(3,n); negative-binomial square sums;
Coster's Theorem 4; and exact-ID/Coster combinations. arXiv searches located the
2016 identity paper. MathOverflow-targeted searches for ballot congruences
returned unrelated ballot-probability material. No matching exact statement was
found there. Search indexing is incomplete; this is not an exhaustive priority
search. The positive source reduction, not absence of search matches, is the
reason for retiring these targets.

The CORE mirror of Coster's PDF timed out; the CWI original was accessible.
No journal-paywall access, author contact, OEIS submission, PR, or public claim
of independent verification was made. Final source reread confirmed the precise
Coster parameter cases and the cubic identity before the retirement decision.
