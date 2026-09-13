# Literature — A051903-C2

Screened 2026-09-13 UTC for `cursor-01-r03`. Bounded search; not a global absence certificate. Rechecked immediately before the candidate claim.

## Exact statement

- Frozen source: [FormalConjectures/OEIS/51903.lean](https://github.com/google-deepmind/formal-conjectures/blob/a2f4a1bb12a28e04a969da78feefac7d1ce49565/FormalConjectures/OEIS/51903.lean), declaration `OeisA51903.conjecture2`.
- SHA-256 (local working tree, frozen commit, and live `main` as of 2026-09-13): `3a694eccc4bd92c14e28e609563bad0ecdfb8895f45c6de887b46fcfcd483db4`.
- Question (Thomas Ordowski, 2019-12-02): existence of odd `n` with `a(n) > 1` and `b^n ≡ b^{a(n)} (mod n)` for all `b`, equivalently `n ≡ a(n) (mod λ(n))`.
- C1 is Lehmer's totient problem and is excluded. C3 is the weaker base-`2` congruence and is excluded.
- Equivalent family reserved, not separately proved: [A327295](https://oeis.org/A327295), numbers `k` with `e(k) > 1` and `k ≡ e(k) (mod λ(k))`. The page asks whether all such numbers are even; that is C2. It also restates the C3-style `ord_n(2)` problem, which this worker does not claim.

## OEIS

- [A051903](https://oeis.org/A051903) and [internal](https://oeis.org/A051903/internal): comments of Ordowski, 2019-12-02, including questions (*), (**), (***). Direct fetch of the HTML page on 2026-09-13 was intercepted by Cloudflare (`Ray ID: a3a3b0a3b89bc5ba`); content used from search/internal snippets and from the frozen Lean docstring.
- [A327295](https://oeis.org/A327295) / [internal](https://oeis.org/A327295/internal): same universal-power definition; listed terms begin `4, 12, 16, 48, …` (all even in the published table). Direct HTML fetch also Cloudflare-blocked (`Ray ID: a3a3be3109dcf685`).
- OEIS editability / pending drafts: **unknown**. No authenticated OEIS session. No edit was submitted.

## DeepMind formal-conjectures

- Ingestion: [PR 5016](https://github.com/google-deepmind/formal-conjectures/pull/5016) (merged), AutoOEIS addition. No C2 proof.
- C1 documentation only: [PR 5449](https://github.com/google-deepmind/formal-conjectures/pull/5449) (merged 2026-09-10). Patch to `51903.lean` adds the Lehmer-totient reduction in the **conjecture1** docstring. `conjecture2` remains `answer(sorry)` / `research open`.
- GitHub issue/PR search for `51903` and `A051903` on 2026-09-13 returned those two items. No C2 proof PR.
- Code search for `OeisA51903.conjecture2` proofs and for `no_odd_universal` on `google-deepmind/formal-conjectures` and `VictorLiwentao/formal-conjectures` found no prior proof artifact (one code-search call returned HTTP 429; retry on Nexus `oeis_51903` returned total_count 0).
- Live `main` source SHA-256 matched the frozen file.

## Epoch LeanOpenProblems-results

Inspected 2026-09-13 via GitHub API:

- Metadata key `oeis_51903_conjecture_0` is **C1**: "There is no composite integer n>4 such that n≡a(n) (mod φ(n))."
- Three runs, all failed SafeVerify (`proof_scorer.value = "I"`):
  - `oeis-full-50usd-ant-j0j0g4uzligm1k41` — `sorryAx`
  - `oeis-full-50usd-oai-jajpvieznaevpoyg` — `sorryAx`
  - `oeis-full-50usd-gdm-1s7vwp2si1ap0r6d` — definition mismatch
- The Anthropic `Spec.lean` redefines `a` as `n.factorization.support.sup n.factorization` (equivalent as mathematics, **not** the frozen list definition) and proves a C1 non-squarefree reduction, then stops at Lehmer. It is not a C2 proof.

## AlphaProof Nexus

- Repository search `A051903` / `oeis_51903` in `google-deepmind/alphaproof-nexus-results`: **0** files (2026-09-13).

## Related mathematics (not a Lean dependency)

- Dutta and Dutta, *Modular Exponentiation Identities: Classification and Minimal Exponents*, [viXra:2602.0018](https://vixra.org/abs/2602.0018), [PDF](https://rxiv.org/pdf/2602.0018v1.pdf) / [viXra PDF](https://vixra.org/pdf/2602.0018v1.pdf), v1 2026-02-03. Five-page preprint. Theorem 1: for `N>1` with max exponent `E` and `L=λ(N)`, the nonnegative `m` with `a^N ≡ a^m (mod N)` for all `a` are those with `m ≥ E` and `m ≡ N (mod L)`. The odd-exclusion `m=E` for odd `N` with `E>1` is not stated. No Lean. viXra is not peer review. The classification would make C2 an elementary corollary (`λ(p^E)` is divisible by `p^{E-1} > E`), but this worker proves the order/`1+p` route independently and does not import that paper.
- Carmichael λ of an odd prime power `p^e` is `p^{e-1}(p-1)`: standard, e.g. Carmichael 1910; Mathlib cyclicity of `(ZMod (p^e))ˣ` for odd `p`.
- Mathlib `ZMod.orderOf_one_add_prime` and `padicValNat.pow_sub_pow` (LTE) are library theorems, not a prior formalization of C2.

## Inaccessible or incomplete sources

- OEIS HTML (Cloudflare challenge).
- One GitHub code-search request returned 429; Nexus and Epoch were still retrieved by direct contents API.
- No MathOverflow thread located for the exact C2 wording in this pass.

## Classification

- `mathematical_novelty`: known elementary corollary / known machinery, not a new informal discovery.
- `formalization_novelty`: no completed public exact Lean proof of C2 found in the checked sources.
- A verified prior exact Lean proof of this declaration would have retired the target; none was found.
