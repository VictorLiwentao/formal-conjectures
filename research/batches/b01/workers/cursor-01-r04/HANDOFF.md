# HANDOFF — cursor-01-r04

Worker: `cursor-01-r04`
Target: `OeisA1818.conjecture1` (A001818-C1 only)
Actual branch: `cursor/b01-cursor-01-r04-6ddf`
Preferred branch name from the prompt: `codex/b01-cursor-01-r04`
Seed / baseline: `7a37b78ee539aab88ebbb77a2579f838e9fcc7a6`
Source baseline: `a2f4a1bb12a28e04a969da78feefac7d1ce49565`
Source SHA-256: `1e41db84e11a5adb981526a75330a597a13ceef8479eb4fb4ef832256496dffe`
Session start UTC: `2026-09-13T02:54:27Z`
Deadline UTC: `2026-09-13T10:54:27Z`
Follow-ups do not restart this clock.

## Reproduction

```bash
export LEAN_NUM_THREADS=2
sha256sum FormalConjectures/OEIS/1818.lean
lake env lean -DwarningAsError=true research/batches/b01/workers/cursor-01-r04/targets/A001818-C1/A001818.lean
python3 research/batches/b01/control/check_assignments.py --repo . --worker cursor-01-r04 --against 7a37b78ee539aab88ebbb77a2579f838e9fcc7a6
```

Public push: only `origin` `cursor/b01-cursor-01-r04-6ddf` on `https://github.com/VictorLiwentao/formal-conjectures.git`.
No PRs. No other branches. No subagents. No shared-control edits. No C2 / A002454 / A356041 assignment.

## Status

In progress toward an exact C1 candidate. Not independently verified. Not a solution until the frozen statement compiles with allowlisted axioms only.

Proved in worker Lean (allowlisted axioms only): `n=1` case; denominator nonvanishing; Calogero kernel sums and Fourier diagonalization; `det(calogero) = (-1)^n a n`; `per(M-J) = 2^{2n}` times the unsigned derangement sum of `(1-ζ^{σi-i})⁻¹`; signed derangement sum `= (-1)^n a n / 2^{2n}`; Guo 3.1 insertion kernel, rotate-class sum, and the sum over all listings through a fixed point (`sum_cycleEdgeWeight_ncycles`); `cycleEdgeWeight` equals a support-constant times the `(1-ζ)^{-1}` product (`cycleEdgeWeight_zeta`); listings through a fixed point are N-cycles with full support; those listings biject with `{σ | σ.IsCycle ∧ σ.support = univ}`; the `(1-ζ)^{-1}` weights of all N-cycles sum to 0 (`ncycle_inv_one_sub_sum`); lifting a cycle through `ofSubtype`; replacing one long cycle while holding a disjoint remainder fixed sums to 0 (`sum_cycleEdgeWeight_replace_cycle` and the transferred `inv_one_sub_replace_cycle`); a derangement is either a product of n transpositions or has a cycle of length at least 3; those involutions have sign `(-1)^n`; unsigned involution weights equal `(-1)^n` times signed ones; remainder of a cycle factor is supported on the complement; `σ` recovers as `ofSubtype(c.subtypePerm) * (σ * c⁻¹)`; long-cycle points of a listing times a disjoint remainder are `s ∪ longPoints τ`; sums over permutations split by `longKey`; a listing times remainder has that `longKey`; conversely a long-cycle permutation with a given `longKey` is a listing times that remainder; each `longKey` fiber of unsigned and signed `(1-ζ)^{-1}` weights vanishes; the remaining derangements are fixed-point-free involutions; the unsigned derangement sum equals `a n / 2^{2n}`; therefore `per(M-J) = a n`.

Identified `per M` with the Cayley-kernel expansion `∑_σ cayleyWeight (fun i => ζ^i) σ`, where the weight is the product over the support of `(x i + x(σ i))/(x i - x(σ i))`. Inverse permutations pick up `(-1)^{#support}`. Off-diagonal `sunMatrix` entries equal those Cayley factors.

Odd cycles of length at least 3 cancel: reversing the distinguished odd cycle (the cycle of the least odd-cycle point) is an involution that negates the Cayley weight. Hence `per M` equals the sum of Cayley weights over permutations with no odd cycle of length at least 3.

Two-point evaluation: `1 + cayleyWeight (swap a b) = -4 xa xb / (xa-xb)^2`. On `Fin 2` this is `cayleySum`. Cayley weights and odd-cycle points restrict through `ofSubtype` (`oddLongPoints_ofSubtype_nonempty_iff`, `cayleySum_ofSubtype`) and through multiplying by a disjoint transposition.

Paper Σ1/Σ2: even-cycle Cayley sums split by the cycle of a distinguished point `p`. Permutations fixing `p` match `cayleySumOn ({p}ᶜ)` (`cayleySum_sigma1`). Permutations whose cycle through `p` is a transposition equal `∑_{q ≠ p} cayleyWeight (swap p q) * cayleySumOn ({p,q}ᶜ)` (`cayleySum_sigma2`). The remainder is the sum over cycle length at least 4 (`cayleySum_eq_sigma1_add_sigma2_add`). Algebraic identity (2.4) (`cayley_triple_identity`) and Hamiltonian listing products (`cayleyWeight_formPerm`, `cayleyWeight_formPerm_cons`) are in place for Lemma 2.3.

Rotate-class insertion: after clearing the skipped edge, the weight of `p :: L.rotate k` equals `-cayleyPathWeight(L.rotate k)` minus a telescoping term in `x p`. Summing over rotations cancels the telescope (`sum_cayleyWeight_cons_rotate`). Path weights ignore `p`, so the Hamiltonian listing sum through `p` is unchanged if `x` is altered only at `p`. Parking through unused complex values therefore makes the Hamiltonian sum depend only on the type, for injective assignments on a type of cardinality at least 3 (`sum_cayleyWeight_hamiltonian_eq_of_injective`). Conjugation by a type equivalence preserves Cayley weights, so the sum depends only on cardinality (`sum_cayleyWeight_hamiltonian_eq_of_card_eq`), including on subtypes (`sum_cayleyWeight_hamiltonian_subtype_eq_fin`).

Paper (3.5) for `k ≥ 2`: cycles of support `T` match Hamiltonian cycles on the subtype (`cycleSupportEquiv`, `sum_cayleyWeight_cycles_support`). Those sums equal the cardinality constant `s_k` (`cayleyHamConst`). Counting subsets `T ∋ p` of size `2k` gives `\binom{N-1}{2k-1}` (`card_powersetCard_mem`). Therefore the `2k`-cycle sum through `p` is `\binom{N-1}{2k-1} s_k` (`sum_cayleyWeight_even_cycles_through`). Direct two-letter evaluation gives `s_1 = -1`. Summing over `k ≥ 2` gives the contribution of all even cycles of length at least 4 through `p` (`sum_cayleyWeight_long_even_cycles_through`). A single cycle has an odd long point if and only if its support has odd cardinality.

She–Sun–Xia Lemma 3.1 is proved: `per(A_n)=0` for `n≥1` (`permanent_signMatrix`), by Laplace expansion of the permanent along column 0 and pairing minors at `t` and `Fin.rev t`.

Card-2 base with a zero coordinate: `cayleySumOn {p,q} = 0` when `x p = 0` (`cayleySumOn_pair`). Conjugation by a type equivalence preserves `cayleySum` (`cayleySum_permCongr`). Even-length cycles through `p` expand as `∑_k \binom{N-1}{2k-1} s_k` when `x` is injective and `x p = 0` (`evenCycleSumThrough_eq_binom`), using `s_1 = -1` on transpositions. A permutation splits as its cycle through `p` times a disjoint remainder that fixes `p`. The even-cycle Cayley sum is `1` plus the even cycles through `p` plus complementary remainder terms (`cayleySum_eq_one_add_even_cycles_add_complementary`). On a two-point type the remainder is always `1`, so those complementary terms vanish.

Complementary terms group by remainder `τ`. If `τ p ≠ p` the fibre is empty. If `τ p = p`, permutations with that remainder are `ofSubtype u * τ` for `u` on `Fix(τ)` with `u.cycleOf ⟨p⟩ = u`, and the fibre equals `cayleyWeight τ * (1 + evenCycleSumThrough ⟨p⟩)` on the complementary subtype (`cayleySum_fibre_remainder`, `cayleySum_complementary_eq_inner`). The Cayley kernel matrix has permanent equal to `cayleySum` (`permanent_cayleyMatrix_eq_cayleySum`), and `sunMatrix` is that matrix on roots of unity.

The geometric assignment `cayleyPowZero` has a zero at index 0 and values `ε^{n-i}` off zero. For real `0<ε<1` it is injective. Its Cayley matrix tends pointwise to the transpose of the sign matrix, so on even size the Cayley sum tends to 0 (`tendsto_cayleySum_powZero`). Hamiltonian even-cycle sums transport along `permCongr` (`evenCycleSumThrough_permCongr`).

Still needed: complementary cancellation by induction plus identity (3.9), recurrence (4.8) / Theorem 1.1 matching formula, then She–Sun–Xia 1.3(i).

## Attribution

Original Lean: The Formal Conjectures Authors.
New Lean development: Wentao Li.
Mathematics: She–Sun–Xia 2022; Guo–Li–Tao–Wei 2022; Calogero–Perelomov 1979.
AI: Cursor Grok 4.6 Extra High, 2026-09-13.
