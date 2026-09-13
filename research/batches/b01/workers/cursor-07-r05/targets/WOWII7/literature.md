# Literature and public Lean screen — WOWII7

Screen date: 2026-09-13 UTC. Bounded search. Not a universal absence certificate.

## Mathematical source

Ermelinda DeLaVina, Siemion Fajtlowicz, Bill Waller,
*On Some Conjectures of Griggs and Graffiti*, March 2002, revised May 2003.
https://www.uhd.edu/documents/academics/sciences/griggsngraffiti.pdf
(also archived as http://cms.dt.uh.edu/faculty/delavinae/GPC/griggsngraffiti.pdf)

The paper’s Conjecture 2 is `L ≥ n+μ−2α−1`. Lemma 1 (printed pp. 4–5) constructs
a connected dominating set of size at most `2α−μ+1` from a maximum independent
neighbourhood. The original WOWII portal
http://cms.dt.uh.edu/faculty/delavinae/research/wowII/ was not retrieved live;
the author-hosted PDF supplies the proof independently. The paper notes that a
connected dominating set is a trunk for a spanning tree in which every non-trunk
vertex is a leaf. Small graphs may have extra trunk leaves; the formal proof
uses only `≥ n-|T|` leaves.

Jerrold R. Griggs conjectured the weaker bound `L ≥ n−2α+1`. That bound is not
the assigned theorem.

## Public Lean (no exact coverage located)

- Frozen statement, still `sorry`:
  https://github.com/google-deepmind/formal-conjectures/blob/a2f4a1bb12a28e04a969da78feefac7d1ce49565/FormalConjectures/WrittenOnTheWallII/GraphConjecture7.lean
  Full-file SHA256 `b24ee6ea69c547654647cdad7102ce95e64dc8a455fbd9aa12f7214b3d3c3968`.
- DeepMind all-state `GraphConjecture7`: import-only PR
  https://github.com/google-deepmind/formal-conjectures/pull/3820
- WOWII2 public proofs are a different average-neighbourhood bound
  `Ls ≥ 2(l(G)−1)`, not `n+μ−2α−1`:
  - AlphaProof Nexus `GraphConjecture2.lean`
    https://github.com/google-deepmind/alphaproof-nexus-results/blob/0647711a71183c1ea492ad60860776617ce1ea88/APNOutputs/AICollaborator/Graphs/GraphConjecture2.lean
  - kingcharlezz
    https://github.com/kingcharlezz/formal-conjectures/blob/7d88e8b7946791ff53c322651f73de8d4df0ba53/FormalConjectures/WrittenOnTheWallII/Proofs/GraphConjecture2.lean
  - KitaKen1
    https://github.com/KitaKen1/wowii-graph-conjecture-2-lean
  Inspected declarations concern average local independence and
  `|N(u)∪N(v)|−2` leaf bounds from an edge seed. They do not imply the
  assigned `μ`/`α` inequality. Pendant attachment was reimplemented here
  rather than copied.
- WOWII1 is `n+1−2ν` with matching number, a different invariant.
- GitHub code search 2026-09-13: `GraphConjecture7` in
  `google-deepmind/alphaproof-nexus-results` and
  `epoch-research/LeanOpenProblems-results`: no hits.
  `WOWII7` language:Lean: no hits.
  `indepNeighborsCard` `indepNum` language:Lean: definition sites only
  (Independence.lean and copies), not the strengthened bound.
- Epoch review JSON in `tadamcz/fc-review-results` records statement review
  of GraphConjecture7 with `trivial_proof.attempted: false`; not a proof.
- Coordinator screen `replacement-screening-07.md` (2026-09-13) also found no
  exact public Lean. This worker’s recheck agrees.

Inaccessible: live WOWII HTML portal; GitHub code search briefly returned HTTP 429
and was retried.

Credit: DeLaVina, Fajtlowicz, Waller for the mathematics; The Formal Conjectures
Authors for the frozen Lean statement and `Ls`/`indepNeighborsCard` API;
Wentao Li only for this new Lean development and write-up.
