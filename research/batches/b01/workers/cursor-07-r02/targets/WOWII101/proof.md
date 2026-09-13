# WOWII101 proof

Known mathematics. This is a Lean formalization of Hajnal’s independence-core inequality, not a new theorem.

## Target

`WrittenOnTheWallII.GraphConjecture101.conjecture101`: for finite nontrivial connected simple `G`,

```
G.indepNum ≤ (Fintype.card α + (alphaCore G).card) / 2
```

Natural division is floor division. The proof establishes the equivalent form `2 * G.indepNum ≤ Fintype.card α + (alphaCore G).card`. The connectedness hypothesis is unused.

## Credits

- Mathematics: András Hajnal, *A theorem on k-saturated graphs*, Canad. J. Math. 17 (1965) 720–724.
- Independent-set form, core/corona language, and Corollary 2.4: Levit–Mandrescu, arXiv:1101.4564.
- Original Lean statement: The Formal Conjectures Authors.
- New independent Lean development and write-up: Wentao Li.
- AI assistance: Cursor Grok 4.6 Extra High, worker `cursor-07-r02`.

## Argument

1. A finite graph has a maximum independent set. The family `Ω` of all such sets is a nonempty Finset.
2. `v ∈ alphaCore G` iff deleting `v` strictly drops `indepNum` iff no maximum independent set avoids `v` iff `v` lies in every member of `Ω`. Transport uses `G.induce (univ \ {v})` and `isNClique_induce_iff` on the complement. Thus `alphaCore G` equals `∩ Ω`.
3. For any nonempty family `F` of maximum independent sets, `2α ≤ |∩F| + |∪F|`. Induct on `F`. The singleton case is `2α = |S| + |S|`. When adding `S` to a nonempty `F'` with intersection `I` and union `U`, the set `I ∪ (S ∩ U)` is independent: vertices of `I` co-occur with each vertex of `U` in some previous maximum set. Its size is at most `α = |S|`, which forces `|I \ S| ≤ |S \ U|`, so the bound is preserved.
4. Taking `F = Ω` and `|∪Ω| ≤ |V|` yields `2α ≤ |alphaCore| + n`.

This file does not use the source `sorry` theorem.
