# cursor-07 screening (non-OEIS)

Worker: cursor-07. Branch: `cursor/b01-cursor-07-ca94`.
Frozen source: `a2f4a1bb12a28e04a969da78feefac7d1ce49565`.
Screening date: 2026-09-12. Official WOWII status from a local dump of
`http://cms.uhd.edu/faculty/delavinae/research/wowII/all.html` (live fetch timed out).

This worker may select only in
`FormalConjectures/WrittenOnTheWallII/`, `Mathoverflow/`,
`GreensOpenProblems/`, `ErdosProblems/`.
OEIS targets and mathematical equivalents of the other eight workers are
excluded: A237271, A108081, A076141, A135508, A063880, A108866 (plus
A332786/A330718), A079727, A003161/A003162, and `assignments.json` excluded IDs.

## Other workers' reserved sequences (do not touch)

See `research/batches/b01/control/assignments.json`. No selected target is an
OEIS sequence or a restatement of those sequences.

## Written on the Wall II, remaining `research open` at baseline

| ID | Lean file | Official status | Screening decision |
| --- | --- | --- | --- |
| 19 | GraphConjecture19.lean | O | **Active queue.** `b ≥ floor(avg ecc + max l)`. Follows from proved #13 when avg ecc ≤ diam−1. |
| 40 | GraphConjecture40.lean | O | Standby. `f ≥ ceil((p+b+1)/2)`. The p=1 case is noted by DeLaVina. |
| 61 | GraphConjecture61.lean | O | **Active queue.** `f ≥ residue + ceil(diam/3)`. |
| 100 | GraphConjecture100.lean | O | Standby after statement audit. Lean uses `degreeL2Norm Gᶜ`. |
| 133 | GraphConjecture133.lean | O | **Active queue.** `path ≥ rad + floor(l)^{cC4}`. The C4 case is a geodesic. |
| 141 | GraphConjecture141.lean | O in Lean, solved publicly | **Prior solution.** arXiv:2608.01396 (Ferudun) plus Lean proofs of 141/142/143. Out of scope. |
| 160 | 160.lean | O at baseline | **Later public disproof** on DeepMind main after the freeze (`c7516f9`). Out of scope. |
| 198a | GraphConjecture198a.lean | O | Unmerged PR #4597 claims a proof, file `ConditionalMain.lean`, using `b ≥ 2 rad` (WOWII #15, Fajtlowicz 1988). Do not reproduce that argument. A counterexample would still be in scope; named graphs found none. |
| 314 | GraphConjecture314.lean | O | Unmerged PRs #4455 and #4496 claim a proof. Exhaustive nauty on triangle-free P5-free graphs through n=9 found no non-WTD example. Do not reproduce those proofs. A counterexample would need n≥10. |

## MathOverflow in-repo files

| File | Decision |
| --- | --- |
| 1973 (S^6 complex structure) | Solved; Hopf problem. Out of scope. |
| 21003 (polynomial bijection Q²→Q) | Famous open. Skip. |
| 17560 (2^x, 3^x integer) | Open; hard transcendental. Skip. |
| 31809 (pretriangulated vs triangulated) | Category theory. Skip. |
| 339137 / Green 28 | Finite-support unfair convolution still open; infinite-support counterexamples do not match the Lean statement. Skip. |
| 347178 | Bounded-suprema variant open; unbounded case already solved in-repo. Skip. |
| 34145 (square tiled by 1/k×1/(k+1) rectangles) | Packing problem; not a small combinatorial search. Skip. |
| 434111 | Restricted prime-number conjecture. Skip. |
| 235893 | Connected maps R^n. Skip. |
| 486451, 507128 | Already `research solved`. Out of scope. |
| 75792 | Integer complexity `‖2^n‖=2n`; open and well-studied. Skip. |
| 10799 | Kahn–Kalai / Polymath isoperimetric. Skip. |

## Green and Erdős

Famous items (Green 1, 9, 12, 28, 44, 45, 47, 51, 53, 58, 60–63, 66, 72, 77, 81;
Erdős Ramsey, Goldbach-type, EH, etc.) were not queued. Several in-repo
Erdős files are already `research solved`. Pointer files such as Green 63/81/7/77
duplicate Erdős 424/510/342/507; still hard.

Erdős 195 has published bounds 3 ≤ k ≤ 4; determining the exact answer is not
a small-search problem. Erdős 203 has public incomplete covering-system search;
not a finished solution.

## Statement notes that affect the queue

- WOWII #13 is T (DeLaVina–Waller 2004): `b ≥ diam + max l − 1`.
- WOWII #16 is T; Waller first proved a weaker `b ≥ 2 rad + max l − 5`. If the
  Lean #16 statement is truly proved, then 19 is a corollary for self-centered
  graphs. Formalising that published chain is out of scope. A counterexample
  to 19 would also refute #16.
- WOWII #15 is R: `b ≥ 2 rad` (Fajtlowicz 1988). This is the lemma used by the
  unmerged 198a write-up.
- WOWII #49 (`f ≥ ceil(2+(1/6)length(G))`) is F, counterexample a path on 38
  vertices. That only works if `length` is the Euclidean degree-norm of the
  **complement**. Lean 100's `Gᶜ` reading matches this convention. Stars refute
  the no-overline reading of 100; that is a specification loophole, not a
  solution of the intended conjecture.
- Lean 133's `hasC4` is a (not necessarily induced) 4-cycle, matching the WOWII
  `cC4` characteristic.

## Computation so far (explicitly unverified as a resolution)

Python/networkx plus nauty helpers under `scratch/wow_search.py`.

- Named graphs and standard constructions (cycles, stars, complete
  bipartite, prisms, grids, C5 blow-ups, split/join graphs, Kneser, Paley,
  Petersen, cages, pendants on cliques): **no Lean-faithful hits** for 19, 16,
  40, 61, 100-with-complement, 133, or 198a.
- Many hits for the overline-stripped 100 (`length(G)` rather than `Gᶜ`),
  including stars and paths. Not claimed.
- Earlier triangle-free P5-free enumeration for 314: all such connected
  graphs on 4–9 vertices were well totally dominated.

## Rejected as first targets

Anything with a public exact solution, an unmerged complete proof we would
only be reproducing, a specification loophole, or no feasible finite attack
in this session.

## Coordinator update (known informal proofs)

A published informal proof was treated as in scope if no exact public Lean
proof exists. WOWII 31 was selected on that basis: Erdős–Saks–Sós Theorem
2.2, proof by Fan Chung. The frozen Lean type still has `sorry`.
Classification: `known_mathematics_formalization`. See `targets/WOWII31/`.

The 2026-09-13 literature pass missed an earlier exact Lean proof by Kenta
Kitamura (KitaKen1), DeepMind PR
[#4658](https://github.com/google-deepmind/formal-conjectures/pull/4658)
(2026-07-28). Novelty status is `prior_solution_found`. The worker file
remains a later independent implementation, not a first formalization.

## Pause (2026-09-13T01:15Z)

Coordinator: WOWII31 is under independent compile/type/axiom audit of
commit `54991f4b`. Status is `audit_pending`, not `independently_verified`.
Further target work is paused. Continuation timer cancelled. Original
deadline preserved. WOWII133 is **not** selected.

## Attribution correction (2026-09-13T01:17Z)

Coordinator candidate compilation of this branch passed. Coordinator
compilation of Kitamura’s pinned artifact is pending. No new target.
WOWII133 screening below is unchanged.

## WOWII133 screening notes (incomplete, paused)

Frozen file: `FormalConjectures/WrittenOnTheWallII/GraphConjecture133.lean`.
SHA-256: `05c03eefa92f75236bd3f1e9caa6411816fc0b88b5a739f341f6fa87d5db2cc5`.
DeepMind PR #4282 only fixed the `path` invariant and the `cC4`
characteristic; it is not a proof. No public Lean proof found on 2026-09-13.

Lean statement, connected nontrivial `G`:

`rad + ⌊l G⌋ ^ cC4 ≤ path G`,

with `cC4 = 0` if `G` has a (not necessarily induced) 4-cycle, else `1`.
In Lean, `x ^ (0 : ℕ) = 1` for `x : ℝ`, including `0 ^ 0`. So the C4 case is
`path ≥ rad + 1`. Chung (WOWII31) already gives `path ≥ 2 rad − 1`.

Informal case split, **not proved in this session**, not a candidate:

1. Has a 4-cycle: `path ≥ rad + 1`. Follows from Chung if `rad ≥ 2`. If
   `rad = 1`, a connected graph on at least two vertices has an edge, so
   `path ≥ 2`.
2. C4-free and `⌊l G⌋ ≤ 1`: same bound as the C4 case.
3. C4-free and `rad = 1`: there is a dominating vertex `v`. Then `G[N(v)]`
   is a disjoint union of cliques (an induced `P3` in `N(v)` would give a
   4-cycle with `v`). Average local independence is then `< 2`, so
   `⌊l G⌋ ≤ 1`, and `path ≥ 2`.
4. C4-free, `rad ≥ 2`, and `⌊l G⌋ ≤ rad − 1`: Chung.
5. Remaining open case: C4-free, `rad ≥ 2`, `⌊l G⌋ ≥ rad`. In particular
   `⌊l G⌋ ≥ 2`. Connected C4-free P4-free graphs are cographs, hence joins;
   both join parts of size at least 2 create a 4-cycle, so one part is a
   single vertex and `rad = 1`. Thus C4-free and `rad ≥ 2` implies
   `path ≥ 4`. Combined with Chung, `path ≥ rad + 2` holds for all C4-free
   graphs with `rad ≥ 2`. That would finish `⌊l G⌋ = 2`. Still open:
   `⌊l G⌋ ≥ 3` with `rad ≥ 2` (Petersen is a test case: `rad = 2`,
   `l = 3`, need `path ≥ 5`).

No Lean-faithful counterexample was found in the earlier named-graph search.
Nauty `133n` / construction sweeps in `scratch/wow_tight.py` were prepared
but not completed before this pause. These notes are not a proof, not a
disproof, and not a successor reservation.
