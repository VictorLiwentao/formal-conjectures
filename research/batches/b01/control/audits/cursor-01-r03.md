# Independent audit: A051903-C2

Status: **PASS — independently verified exact answered theorem and full negative RHS.**

Completed 2026-09-13T02:46:32.575559+00:00. Fresh frozen source, unmodified candidate, and separate exact-type audit all exited 0.

Reviewed 2026-09-13 UTC by independent Codex audit task. No worker or coordinator files edited. The sole git mutation was the authorized fetch of the worker branch. All compiler output is confined to this scratch directory.

## Provenance

- Frozen baseline: `a2f4a1bb12a28e04a969da78feefac7d1ce49565`.
- Worker branch: `origin/cursor/b01-cursor-01-r03-2609`; reviewed tip `9b10113c`, proof commit `c6ba241f`. Candidate proof is identical at both commits.
- Frozen source: `FormalConjectures/OEIS/51903.lean`, SHA256 `3a694eccc4bd92c14e28e609563bad0ecdfb8895f45c6de887b46fcfcd483db4`.
- Candidate: `research/batches/b01/workers/cursor-01-r03/targets/A051903-C2/A051903.lean`, SHA256 `88417287b950e6e0fdde7387ffb624dc5185efea62e7075c917137018d10593c`.
- Fresh upstream main source fetched through GitHub contents API has the same source SHA256.

## Independent reproduction

Uses `/Users/wentaoli/.elan/toolchains/leanprover--lean4---v4.33.1/bin/lean`, without lake writes. LEAN_PATH starts with this isolated scratch directory, then the read-only compatible cache at `/Users/wentaoli/.codex/worktrees/1974/formal-conjectures`. All nine package checkout revisions match the frozen manifest; all 23 FormalConjecturesUtil source files match the frozen baseline byte-for-byte. Thus the OEIS target is rebuilt freshly and takes precedence over any cached target; general library artifacts are reused.

Commands, from this directory:

```sh
python3 run_compile.py -o FormalConjectures/OEIS/51903.olean FormalConjectures/OEIS/51903.lean
python3 run_compile.py -DwarningAsError=true -o A051903.olean A051903.lean
python3 run_compile.py -DwarningAsError=true ExactTypeAudit.lean
```

The frozen admitted source intentionally uses ordinary warnings, while candidate and independent wrapper use warnings-as-errors. Source compilation exited 0 with exactly the three expected admitted-declaration warnings. Candidate strict compilation exited 0. Independent fully qualified exact-type wrapper strict compilation exited 0. Both final theorems and all seven additional audited helper/library declarations have axiom sets contained in `{propext, Classical.choice, Quot.sound}`. The separately printed original `OeisA51903.conjecture2` has `sorryAx` as an expected control; the new proofs do not. A whitespace-normalized statement comparison additionally confirms the only textual change is `answer(sorry)` to `answer(False)`; see `statement-comparison.log`. Logs: `source-compile.log`, `candidate-compile.log`, `exact-type-audit.log`.

## Mathematical and statement audit

The independent wrapper uses fully qualified `OeisA51903.a` and separately checks the entire existential negation and the exact `False ↔ RHS` answered statement. This resolves the answer to False and does not prove a statement with an arbitrary placeholder left-hand side.

1. `exists_eq_foldr_max` proves attainment for the original list fold, and `exists_prime_max_exponent` extracts an actual member of `n.primeFactorsList`. Its count is identified with `n.factorization p`; the original definition is unchanged.
2. A positive factorization exponent excludes zero. The prime-power divisibility follows with that nonzero hypothesis. Oddness excludes p=2, hence p≥3.
3. The induction `e < p^(e-1)` is valid for e≥2,p≥3. Prime-power divisibility and positivity imply p^e≤n and therefore e<n, before natural subtraction occurs.
4. Universal quantification is instantiated at 1+p and reduced to modulus p^e. The base is a unit; its e-th power is cancelled on the left to obtain u^(n-e)=1.
5. The Mathlib theorem `ZMod.orderOf_one_add_prime`, UnitsCyclic.lean:188, has exactly the prime / p≠2 hypotheses and modulus p^(k+1) needed. Substitution k=e-1 is justified by e≥1. The order divisibility then yields p^(e-1)|n-e.
6. Since the same power divides n, it divides e. The established strict inequality contradicts divisibility of positive e.

No step assumes C1 or C3, changes the maximum exponent definition, limits the base quantifier, or substitutes numerical evidence. No source admitted theorem is cited. The axiom audit checks transitive dependency closure, including the library order theorem and final results.

## Literature and credit

The proof header credits the original Formal Conjectures authors, Thomas Ordowski's 2019 question, Wentao Li's new Lean development, and the stated AI assistance. It explicitly disclaims new informal mathematics and distinguishes C1/C3.

Independent fresh all-state GitHub issue/PR searches for 51903/A051903 locate only ingestion PR5016 and documentation PR5449; A327295 query has no result. The live upstream source remains admitted. The local AlphaProof Nexus results clone has no 51903 match. All three Epoch submissions matching oeis_51903_conjecture_0 were independently checked to target the totient condition (C1): Anthropic and OpenAI fail with sorryAx; Google fails definition comparison. None establishes C2.

Primary sources: https://oeis.org/A051903 ; https://oeis.org/A327295 ; https://github.com/google-deepmind/formal-conjectures/pull/5016 ; https://github.com/google-deepmind/formal-conjectures/pull/5449 ; https://github.com/epoch-research/LeanOpenProblems-results ; https://github.com/google-deepmind/alphaproof-nexus-results .

The earlier independent screening directly read both OEIS pages; A327295 explicitly restates the universal congruence and asks whether all such numbers are even. It is the same question with reversed answer polarity: no odd witness, hence yes all terms even. Equivalent group must remain with this owner.

Dutta–Dutta, https://rxiv.org/pdf/2602.0018v1.pdf , Theorem 1, supplies the general exponent/Carmichael classification. Earlier independent screening read all five pages: no explicit odd-exclusion corollary and no Lean proof. The candidate uses existing Mathlib order results and does not depend on the preprint. Suitable classification: independently formalized elementary consequence of known machinery; no established claim of new informal mathematics or first public formalization. The absence search is bounded, not a global priority certificate.

## Nonblocking documentation correction

`proof.md` section 5 says the file answers the equivalent A327295 “are all terms even?” question “negatively.” The intended negative answer is to existence of an odd witness; the all-even question has answer yes. Correct that sentence before outward-facing reuse. This does not affect the Lean theorem or proof.

## Verification limits

This is an independent fresh compilation of the exact target and candidate against revision-matched cached libraries, plus Lean axiom-closure inspection and mathematical review. It is not a fresh rebuild of all Mathlib artifacts or a separate SafeVerify replay. No proof or mathematical issue remains outstanding. The prose polarity correction is nonblocking and was communicated to the coordinator; public novelty and publication are separate decisions.

## Coordinator documentation correction

Fetched final documentation tip `e4254e79d1fa492dfae5816e20abd46c469b3f4c`. Compared with audited `9b10113c`, only five documentation files changed; candidate Lean source is identical. The explanation now correctly states C2 odd-example NO and A327295 all-terms-even YES. C3 remains excluded.
