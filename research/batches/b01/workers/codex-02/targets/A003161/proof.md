# A003161: literature resolution

Status: `prior_solution_found`; independent review pending.

The exact raw integer ballot sum congruence follows from the published inputs and the explicit
algebra in [the joint derivation](../../literature-reduction.md).
No new arithmetic theorem or complete Lean proof is claimed.

The accompanying `A003161.lean` proves a conditional transfer with every missing
formal input visible as a hypothesis. It does not invoke either original
`conjecture` proof or `OeisA3162.a_is_integer`. Axiom output alone does not remove
those hypotheses. `ExactTypeAudit.lean` compares the conclusion with the complete
frozen proposition by definitional equality, without using its proof term.

The instructions require stopping a target once published results imply it.
Accordingly this handoff records the source resolution instead of reproducing
Coster's theorem in Lean as a purported new result.
