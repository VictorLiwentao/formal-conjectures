# Literature and novelty audit: A237271 Carmichael observation

Target: `OeisA237271.observation_carmichael` on frozen source
`FormalConjectures/OEIS/237271.lean`, SHA-256
`4f5f9875d35bc3f009af89444945296942a5967d1f8af20a4a102460227da11b`.
Checked 2026-09-12.

## Formal proposition

```
theorem observation_carmichael (k : ℕ) (hk : IsCarmichael k) : 3 ≤ a k
```

`a` is the A237271 characterisation: one plus the number of consecutive
divisor pairs `(d_k, d_{k+1})` with `Odd d_{k+1}` and `d_{k+1} ≥ 2 d_k`.
`IsCarmichael` is the repository predicate
`∀ b ≥ 1, n.Coprime b → n.FermatPsp b` from
`FormalConjecturesForMathlib/NumberTheory/Carmichael.lean`.
`Nat.FermatPsp` includes compositeness.

## Source statement

Live OEIS A237271 internal format, `%I #308 Aug 13 2026 12:02:22`:

> Observation : a(A002997(n)) >= 3, at least for 1 <= n <= 10000.
> Omar E. Pol, Oct 21 2025.

A002997 is Carmichael numbers: composite `k` with `a^(k-1) ≡ 1 (mod k)`
for every `a` coprime to `k`. The Lean statement is the unrestricted
mathematical reading of that observation, not the finite range `n ≤ 10000`.

OEIS editability: public page/history retrieved; no pending-draft banner
was visible on `/internal` or `/history?seq=A237271`. Login-gated edit
status is **unknown**. No OEIS edit was made.

## Formalization history (not a prior solution of the corrected statement)

- Old hypothesis quantified Fermat over every nonzero residue of `ZMod k`.
  That predicate is unsatisfiable. Issue
  [#4974](https://github.com/google-deepmind/formal-conjectures/issues/4974)
  (closed). The old theorem is vacuously true and is a different target.
- Correction [#4987](https://github.com/google-deepmind/formal-conjectures/pull/4987),
  merged 2026-08-16 as `9ec87fd`, replaced the hypothesis by `IsCarmichael`.
  The corrected declaration remains `sorry` on frozen source and on
  DeepMind `main` as of this audit.
- Open issue
  [#5447](https://github.com/google-deepmind/formal-conjectures/issues/5447)
  (2026-09-10) records an informal proof that the claim holds for every
  odd composite, hence for Carmichael numbers, and states that there is
  no public formal proof. That issue is not an accepted Lean submission
  and does not inhabit the frozen declaration.

## Public formal results that are different targets

- Conjecture 2 (`a n = num2DenseSublists n`): AlphaProof Nexus
  [oeis_a237271_conjecture_2.lean](https://github.com/google-deepmind/alphaproof-nexus-results/blob/main/APNOutputs/OEIS/oeis_a237271_conjecture_2.lean)
  and the `formal_proof` link to
  [mo271 237271.wip.lean](https://github.com/mo271/formal-conjectures/blob/a32396489dcb8f86c3549b93aa358ac6a10a3a1f/FormalConjectures/OEIS/237271.wip.lean#L102).
  Those files prove the 2-dense characterisation, not the Carmichael
  lower bound. The repository `conjecture_2` still has `sorry`; it is
  not used.
- Conjectures 4 and 5 (parity on squares and hexagonal numbers):
  [KitaKen1/oeis-a237271-square-hexagonal-parity](https://github.com/KitaKen1/oeis-a237271-square-hexagonal-parity).
- arXiv:2605.22763 (Tsoukalas et al.) is the AlphaProof search paper.
  It is the source of the conjecture 2 artifact, not of this observation.
- Hoft’s proof of conjecture 1 is cited on A379288. It is not this target.

## Searches with no matching accepted proof of this declaration

| Source | Query / object | Result |
| --- | --- | --- |
| DeepMind formal-conjectures `main` raw file | `observation_carmichael` | still `sorry` |
| GitHub PRs on A237271 | PRs 4924, 4987 | parity marking; hypothesis fix; no proof |
| alphaproof-nexus-results | `observation_carmichael` | no hit; only conjecture 2 |
| epoch-research/LeanOpenProblems-results | A237271 / observation_carmichael | no hit; Carmichael hits are A309132 |
| Kuberwastaken/c5-k4 | A237271 | issue 4974 audit of the vacuous form |
| MathOverflow / arXiv | A237271 Carmichael 2-dense / divisor parts | no proof of `a(k)≥3` for Carmichael `k` |
| OEIS A237271 comments/links/history through #308 | observation remains an observation | Kitamura closed only conjectures 4 and 5 |

No-match here means no public kernel-checked proof of the corrected
quantified statement was found in the sources above. Issue 5447 is an
informal write-up of the same elementary argument used in this worker
file. It is recorded so that the Lean development is not presented as
the first discovery of the mathematics.

## Statement audit

- Quantifiers: `∀ k, IsCarmichael k → 3 ≤ a k`. Matches “for every
  Carmichael number”, not the finite OEIS sample.
- `IsCarmichael` uses coprime bases via `FermatPsp`, so the hypothesis
  is satisfiable (`isCarmichael_561` in `AgohGiuga.lean`). Nonvacuity holds.
- Starting index: `a` is defined for all `ℕ`. Carmichael numbers satisfy
  `1 < k` and `¬Prime k`.
- Oddness is not an extra hypothesis; it follows from `IsCarmichael`.
- The count uses `≥` and `Odd` on consecutive sorted divisors, matching
  Eldar’s formula on OEIS and the Lean `def a`.
- Boundary: primes have two divisors, so `a(p)=2` for odd primes. The
  composite conjunct of `FermatPsp` is required. The old nonzero-residue
  hypothesis had no models; the corrected one does not have that loophole.
- Stronger true statement: `3 ≤ a n` for every odd composite `n`. That
  implies the assigned theorem. Proving a loophole would not; this is a
  genuine strengthening on a nonempty class that contains all Carmichael
  numbers.

## Conclusion

Proceed with a Lean proof of the frozen corrected declaration. Do not
treat conjecture 2, the vacuous old theorem, or issue 5447’s informal
write-up as a completed formal solution.
