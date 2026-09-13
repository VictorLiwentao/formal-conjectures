# Proof of `Green66.green_66.variants.trivial_bound`

This is a Lean formalization of a known elementary remainder bound.
It is not a proof of Green's open question with the fixed constant
`1/10`. No optimal constant is claimed.

## Frozen proposition

There exists one real constant `C > 0` such that, for all sufficiently
large real `X`, some natural number `n = a^2 + b^2` lies in the closed
interval `[X - C X^{1/4}, X]`.

Quantifiers: a single `C` is chosen first; the eventual filter `atTop`
then quantifies over real `X`. Small and negative `X` are excluded by
that filter. The interval is `Set.Icc`, so the right endpoint `X` is
allowed. Witnesses `a, b` are natural numbers, matching
`Green66.IsSumOfTwoSquares`. The exponent is real `rpow` with exponent
`1/4`.

The candidate theorem `Green66TrivialBound.trivial_bound` has this
exact type. It does not apply the admitted source declaration.

## Route

Green's comment: subtract the greatest square `u^2` not exceeding
`X`, then the greatest square `v^2` not exceeding the remainder
`X - u^2`. Take `n = u^2 + v^2`.

For every real `X ≥ 1` the proof uses the uniform constant `C = 10`.

Write `u = ⌊√X⌋₊` and `R = X - u^2`. Then `v = ⌊√R⌋₊` and
`n = u^2 + v^2`.

## Inequalities

Let `y ≥ 0` and `m = ⌊√y⌋₊`. Then `0 ≤ m ≤ √y < m + 1`.

1. `m^2 ≤ y`.
   Square the inequality `m ≤ √y` using nonnegativity, then replace
   `(√y)^2` by `y`.

2. `y < (m + 1)^2`.
   Square `√y < m + 1` and replace `(√y)^2` by `y`.

3. `y - m^2 < 2m + 1`.
   Expand `(m + 1)^2 = m^2 + 2m + 1` and rearrange (2).

4. `y - m^2 < 2√y + 1`.
   Combine (3) with `m ≤ √y`.

Apply (1) to `y = X`: `u^2 ≤ X`, so `R ≥ 0`. Apply (1) to `y = R`:
`v^2 ≤ R`, hence `n ≤ X` as reals.

Apply (4) to `y = R`:
`X - n = R - v^2 < 2√R + 1`.

5. `R ≤ 3√X` for `X ≥ 1`.
   From (4) at `y = X`, `R < 2√X + 1`. From `1 ≤ X` one has `1 ≤ √X`,
   so `2√X + 1 ≤ 3√X`.

6. `√R ≤ √3 · √(√X)`.
   Monotonicity of `√` and `√(3√X) = √3 · √(√X)`.

7. `√3 ≤ 2`, since `3 ≤ 4` and `√4 = 2`.

8. `√(√X) = X^{1/4}`.
   `√z = z^{1/2}` and `(X^{1/2})^{1/2} = X^{1/4}` for `X ≥ 0`.

9. `1 ≤ X^{1/4}` for `X ≥ 1`.

10. `2√R + 1 ≤ 10 X^{1/4}`.
    `2√R ≤ 2√3 · √(√X) ≤ 4 X^{1/4}`, then
    `4 X^{1/4} + 1 ≤ 5 X^{1/4} ≤ 10 X^{1/4}` by (9).

Thus `X - n < 10 X^{1/4}`, so
`X - 10 X^{1/4} ≤ n ≤ X`.

The number `n` is a sum of two natural squares by construction.

## Boundary cases

- If `X` is a perfect square, then `R = 0`, `v = 0`, and `n = X`.
- If `R < 1`, then `v = 0` and `n = u^2`.
- `X < 1` and negative `X` are not required: `∀ᶠ X in atTop` is
  witnessed by the threshold `1`.
- `C = 10` does not depend on `X`.

## What is not proved

- The open statement with constant `1/10`.
- The Bambah–Chowla constant `2√2`, or any optimality claim.
- An integer-only variant as a substitute for real `X`.
