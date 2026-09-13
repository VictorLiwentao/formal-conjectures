# A069004 independent certificate audit: RUNNING, NOT VERIFIED

Started 2026-09-13T02:47:37.656815+00:00. Independent compilation is pending. Do not retire the candidate as independently verified until all commands pass and final exact types/axiom outputs are reviewed.

## Pins

- Candidate commit: `17170d58351d9b01d09d7fb0b803e3f978e45ce1` (`origin/cursor/b01-cursor-03-r02-4f64`).
- Frozen baseline: `a2f4a1bb12a28e04a969da78feefac7d1ce49565`.
- Frozen source `FormalConjectures/OEIS/69004.lean` SHA256: `c29abb2a5c1e48761cc6d7ebb4332bd728071b6ea6059263ffcf153800282ca2`.
- Candidate `A069004.lean` SHA256: `e759f4319aac632d277fe3b4bfdb8cd7134cf2574715e45f233423be9e2bd169`.
- Core SHA256: `c26597e76973f9114301166bf7d6e5a2586f538dec1b0940f0a2ff71c20b7be7`.
- `source-hashes.json` contains hashes of every extracted worker file. Driver verifies these before starting. Files are exact `git show` extracts, with no worker/cache oleans copied.

## Live detached job

Scratch `/Users/wentaoli/Research/cursor03-r02-a069004-audit-e2_0rjdc`.

- Persistent driver PID: **78813** (also `driver.pid`).
- Driver: `run-independent-build.py`, launched with Python `subprocess.Popen(..., start_new_session=True)` and all stdio detached.
- `build-status.json`: atomic status including current module, child PID, current command, completed count, whole-job deadline and final state.
- `driver.log`: progress summary.
- `build-events.jsonl`: completed-command exit codes, elapsed time, exact commands and log paths.
- `logs/`: full separate output per module.
- Serial `JOBS=1`, `LEAN_NUM_THREADS=2`; 12-hour total deadline and at most 30 minutes per module. Stops at the first failed or timed-out command; a timeout is incomplete, not proof failure.
- At completion expect 317 commands: frozen source, Core, 284 Pratt chunks, 26 count chunks, GlueCert, GlueCount, A069004, TypeMatch, and independent ExactTypeAudit.
- No generator or worker build script is executed. They were read to establish dependency order; the independent driver invokes the exact Lean4.33.1 binary directly.
- Fresh outputs go only to scratch `fresh-olean/` (plus frozen source olean under scratch). LEAN_PATH puts fresh outputs and scratch before compatible read-only cache1974 and Mathlib/package oleans. It never invokes `lake` or modifies the cache.

Read `build-status.json` and the recorded PID before considering a restart; do not duplicate this heavy job. A `passed` driver state means compilation finished, but the final logs still require human/agent inspection of exact-type and allowed-axiom output before recording audit PASS. A dead process with stale running state also requires investigation, not a success assumption.

## Preliminary source review (not a compile verdict)

The original source already states `conjecture2` as the negation of the full conjunction, and `conjecture2.variants.upper_bound_false` as the upper-bound negation. Candidate theorem types match these written propositions; an independent `Meta.isDefEq` type check is scheduled after fresh compilation.

Candidate lower-bounds the original `a(512720)` by 42494, and proves `Nat.primeCounting 512720 = 42493`. It does not require or prove the larger reported exact `a` value 42666. The 42494 certified square-sum witnesses must be distinct and in `[1,512720)`; Core's `okChain_sound` and `aCount_ge` enforce strict increase, positivity, range and primality, and `a_eq_aCount` is `rfl` to the original definition. Count glue covers `[0,512721)`, correctly including primes at most 512720.

Pratt/Lucas checker is supported by proofs of modular arithmetic and correctness with exponent fuel 64; certificate validation checks `p < 2^64`. The prime criterion uses Mathlib `lucas_primality`; small prime factors use a proved trial-division test. Data checks use `decide +kernel`, not native decision/compiler trust. Full dependency closure remains to be independently compiled and checked.

The known computational counterexample is attributed to j2d9w5xtjn-png, upstream PR5453, and the certificate architecture/data to the public Epoch Anthropic attempt. Original formalization credit names The Formal Conjectures Authors; new proof development names Wentao Li. Known-mathematics classification is required. Fresh public-proof/priority review remains outstanding for the final audit; no first-formalization claim is warranted from this handoff.

## Follow-up when the job finishes

1. Inspect every nonzero/timed-out command and final logs; do not infer successful closure from a partial chunk count.
2. Require both candidate theorem axioms to be subsets of exactly the allowed set `{propext, Classical.choice, Quot.sound}`; reject any `sorryAx`, native/compiler trust, or extra axiom.
3. Require both exact-type checks to pass against unchanged source declarations.
4. Refresh bounded public source/PR/Epoch-equivalence search and complete attribution review.
5. Write a final `independent-audit.md` with PASS or a precise unresolved/failure status, then have the parent coordinator update its record.

No coordinator files, worker branches, shared caches, or upstream sources were modified by this setup. No PR or publication was made.
