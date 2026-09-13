# Independently reviewed batch results

This index separates kernel verification from mathematical/formalization novelty. Working branches are public; no upstream PR or OEIS edit has been authorized. Individual audit files contain reproducible commands, source hashes, dependency checks and search limitations.

| Target | Technical result | Novelty/classification | Preserved branch and audit |
|---|---|---|---|
| A237271 corrected Carmichael observation | Exact proof independently compiled; allowed axioms only | Known informal mathematics; new Lean implementation in this batch, no earlier exact proof located in the checked sources | `cursor/b01-cursor-01-8a28`, commit `7a2f94d822d3bdef3aceaa1fafc54ed99e828b8c`; [audit](audits/cursor-01.md) |
| WOWII101 Hajnal independence-core inequality | Exact proof independently compiled; allowed axioms only | Known mathematics; no earlier exact public Lean proof found in the bounded independent search | `cursor/b01-cursor-07-r02-05fb`, commit `b42564b6f4e04abf0256355f53000056e2c2c924`; [audit](audits/cursor-07-r02.md) |
| A109074 corrected factorial-product ratio | Exact proof independently compiled, including natural-division integrality and positivity; allowed axioms only | Known mathematics; no earlier corrected exact public Lean proof found in the checked sources | `cursor/b01-cursor-01-r02-0918`, commit `5e40973bec551bd85d8749fdc3b2c6b539130720`; [audit](audits/cursor-01-r02.md) |
| A051903-C2 universal-power odd exclusion | Full negative RHS and exact answered biconditional independently compiled; allowed axioms only | Elementary consequence of known prime-power order machinery; no earlier exact public C2 Lean found in bounded searches; no mathematical priority claim | `cursor/b01-cursor-01-r03-2609`, proof `c6ba241f`, corrected documentation `e4254e79`; [audit](audits/cursor-01-r03.md) |
| Green66 known quarter-power gap bound | Exact uniform-C eventual real bound independently compiled and type-checked; allowed axioms only | Known successive-square argument; open fixed-1/10 Green66 question remains unresolved | `cursor/b01-cursor-07-r03-ceef`, commit `85c399a1`; [audit](audits/cursor-07-r03.md) |
| WOWII31 Chung induced-path bound | Batch candidate AND earlier Kitamura proof independently compiled | Already publicly formalized; not a first formalization. Worker attribution corrected | `cursor/b01-cursor-07-ca94`, corrected commit `20a7d73f546ff2a012ca56724fdc8a834537eafb`; [audit](audits/cursor-07.md), [prior proof PR4658](https://github.com/google-deepmind/formal-conjectures/pull/4658) |
| A076141 binary substring multiplicity | Earlier exact public Lean proof independently compiled | Prior public Lean result; target retired | [audit](audits/cursor-03.md), [prior proof](https://github.com/KitaKen1/oeis-a076141-binary-word/blob/b4e179767fa3041c43e019b559ee77e6737317aa/lean/OeisA76141FC.lean) |

Allowed final theorem axioms: propext, Classical.choice, Quot.sound, or a subset. Numerical evidence and compiled partial lemmas are not entries in this table. Source sorry-based defaults are not accepted proofs.

Current active attempts and exact ownership are in assignments.json and supervision-state.json.

Credit mathematical authors, original collective formalizers, earlier Lean authors if applicable, and Wentao Li's actual independent development accurately. A known-mathematics formalization must not be described as a new mathematical discovery. Search absence is bounded evidence, not universal priority certification.
