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
