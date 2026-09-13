# An unverified route to conjectures 1 and 2

Status: **partial research, awaiting independent mathematical review and Lean
formalization**. This file records an original derivation from this session.
It is not an accepted proof or a novelty claim. All finite-field identities below
were checked by deterministic computation, but the arguments have not received
independent review. The `p^4` claim in conjecture 3 is not proved here.

Copyright 2026 Wentao Li. Apache-2.0. AI assistance: OpenAI Codex.
Conjectures: Peter Bala, 2024. Original Lean formalization: The Formal Conjectures Authors.

## Reduction to one half sum

Write `C_k = binom(2k,k)`, `c_k = C_k^3`, `h=(p-1)/2` and `N=(p^2-1)/2`.
All rational congruences below take place in the localization of the integers at
`p`. Denominators in the harmonic sums are less than `p` and are units there.

For `N<k<p^2`, adding `k` to itself in base `p` has a carry at the `p^2` place.
Consequently `p | C_k` and `c_k=0 (mod p^3)`. Thus

    a(p(p-1)) = a(N) (mod p^3).

The usual unit-factor product gives `C_(p^2)=2 (mod p^3)` for `p>=5`, so

    a(p^2) = a(N)+8 (mod p^3).

For `p=3`, the original assertions are finite direct computations. To prove
C1 and C2 for all other admissible primes, it therefore suffices to prove

    a(N) = p^2 (mod p^3).

The Lean file `Reductions.lean` develops the carry argument and the exact C2
reduction. The endpoint scaling and the argument below are not yet in Lean.

## A two-digit expansion

For `0<=i,j<=h`, a product of factorial units gives

    C_(ip+j)^3 = c_i c_j [1 + 6ip D_j + i^2 p^2 E_j] (mod p^3),

where

    D_j = H_(2j)-H_j,
    E_j = 18 D_j^2 - 6 H_(2j)^(2) + 3 H_j^(2).

Here `H_j^(r)=sum_(s=1)^j 1/s^r`, with zero for the empty sum. Indeed,

    C_(ip+j)/C_(ip) = C_j prod_(r=1)^(2j)(1+2ip/r)
                                  / prod_(r=1)^j(1+ip/r)^2.

Expanding its cube to degree two gives the displayed formula. The remaining
scaling `C_(ip)=C_i (mod p^3)` is the classical binomial scaling congruence;
only `i<=h` is needed. One direct justification is

    C_(ip)/C_i = prod_(1<=r<=ip, p does not divide r)(1+ip/r).

The reciprocal sum over these complete unit blocks vanishes modulo `p^2`
and the reciprocal-square sum modulo `p`, for `p>=5`. These follow by pairing
`r` with `p-r`, using the finite-field inverse-square sum, and translating
complete blocks. Terms of degree at least three contain `p^3`.

Every `k<=N` has the form `ip+j`. If `j>h`, the lower digit has a carry and its
cube vanishes modulo `p^3`. Thus, putting

    S = sum_(j=0)^h c_j,
    M_r = sum_(j=0)^h j^r c_j,
    D = sum_(j=0)^h c_j D_j,
    E = sum_(j=0)^h c_j E_j,

we obtain

    a(N) = S^2 + 6p M_1 D + p^2 M_2 E (mod p^3).                 (1)

Sun's published Theorem 3.2 supplies `S=0 (mod p^2)` for the assigned primes.
To finish (1), it is enough to prove

    M_1=0 (mod p), D=0 (mod p), M_2 E=1 (mod p).                (2)

The next calculation is a proposed elementary derivation of all three
identities from `S=0 (mod p)`. In particular, a separate CM harmonic-sum
result may be unnecessary.

## Finite-field differential identities

Work over `F_p` with `p>=5`. Put `theta=z d/dz`, and introduce a formal
parameter `t` with `t^3=0`. Define polynomials `f_0,f_1,f_2` of degree at most `h`
by

    sum_(j=0)^h [((1/2+t)_j/(1+t)_j)^3] z^j
        = f_0(z)+t f_1(z)+t^2 f_2(z) (mod t^3).

The denominators are units because `j<=h<p`. Explicitly their coefficients are

    [z^j]f_0 = c_j/64^j,
    [z^j]f_1 = 6 D_j c_j/64^j,
    [z^j]f_2 = E_j c_j/64^j.

Introduce a formal symbol `w` with `theta(w)=1`. The three coefficients of
`exp(tw)(f_0+t f_1+t^2 f_2)` are

    y_0=f_0,
    y_1=f_1+w f_0,
    y_2=f_2+w f_1+(w^2/2) f_0.

Each satisfies

    L y = 0,   L = theta^3 - z(theta+1/2)^3.                  (3)

Coefficient verification: the internal terms cancel by the rising-factorial
ratio. At degree zero the residual is divisible by `t^3`; at degree `h+1`
it is divisible by `(h+1/2+t)^3=t^3` in characteristic `p`. Hence both boundary
terms vanish modulo `t^3`. This is a polynomial calculation, with no analytic
logarithm or division by a supersingular value.

For any `y,zeta`, define the symmetric bilinear expression

    B(y,zeta) = (1-z)(y theta^2(zeta)+zeta theta^2(y)
                                 -theta(y)theta(zeta))
                -(z/2)(y theta(zeta)+zeta theta(y))
                -(z/4)y zeta.

Direct differentiation and (3) give `theta B(y,zeta)=0` for solutions of (3).
The parameter in the differential equation is always `z`; `zeta` denotes the
second argument of the bilinear form.

Set

    I_0 = B(f_0,f_0),
    I_1 = B(f_0,f_1)+(1-z)f_0 theta(f_0)-(z/2)f_0^2,
    I_2 = B(f_0,f_2)
          +(1-z)(2f_0 theta(f_1)-f_1 theta(f_0)+f_0^2)
          -(z/2)f_0 f_1.

Then

    I_0=0, I_1=0, I_2=1-z^p.                                (4)

Here is a degree check that avoids the false inference that a polynomial with
zero derivative in characteristic `p` is constant. All three expressions have
degree at most `2h+1=p`. Their degree-`p` coefficients are respectively

    -(h+1/2)^2 a_0^2,
    -(h+1/2)^2 a_0 a_1 -(h+1/2)a_0^2,
    -(h+1/2)^2 a_0 a_2 -(h+1/2)a_0 a_1 -a_0^2,

where `a_i=[z^h]f_i`. The first two are zero; the last is `-1`, since
`a_0=((1/2)_h/h!)^3=(-1)^(3h)` in `F_p`.

First `I_0=B(y_0,y_0)` has zero derivative and degree less than `p`, and its
constant term is zero. Next `B(y_0,y_1)=I_1+w I_0=I_1` has zero derivative,
degree less than `p`, and constant term zero. Finally
`B(y_0,y_2)=I_2+w I_1+(w^2/2)I_0=I_2` has zero derivative, constant term one,
and leading coefficient `-1`. Only degrees 0 and `p` can survive. This gives (4).

Now evaluate at `z=64` in `F_p`. Since `p` is in A003625 and `p>=5`,
`p!=7` and `64!=1` in `F_p`. Sun's result gives `f_0(64)=0`. The first
identity in (4) then gives

    (1-64)(theta f_0(64))^2=0,

so `theta f_0(64)=M_1=0`. The third identity becomes

    (1-64) f_2(64) theta^2 f_0(64)=1-64^p=1-64.

Thus `M_2 E=1`, using Fermat's little theorem and cancellation of `1-64`.
In particular `theta^2 f_0(64)` is nonzero. The second identity in (4) gives
`f_1(64)=0`, hence `D=0` because `6` is a unit. These are exactly (2).
Substituting them and the known prime-level theorem in (1) would prove the
common half-sum congruence modulo `p^3`.

## What is still missing

- Independent mathematical review of this complete-looking informal route,
  particularly the bilinear conservation calculation and the unit-block expansion.
- A more focused literature comparison of (4) with existing finite-field
  hypergeometric bilinear identities. No novelty claim is made.
- Lean proofs for the binomial expansion, polynomial identities, and the known
  Sun prime-level input. Importing a `sorry` theorem for that input is forbidden.
- A proof of the stronger modulus `p^4` in C3. The discarded carry terms have
  order `p^3` and cannot be ignored there. An ordinary-reduction theorem cannot
  be applied at these inert primes.

`polynomial_screen.py` checks all three identities (4) coefficientwise for
primes 5 through 199. `experiments.py` checks (1) for the initial assigned
primes, and C1–C3 through 503. These are computational evidence only.

## A proposed deduction of conjecture 4 from older prime-level results

The initial suspicion about the Lean syntax was false: the product has binding
precedence that leaves subtraction **outside** the product. `product_index`
and `conjecture4_parsing` in `A079727.lean` check this. The failed alternative
parse is preserved under `scratch/`.

Here is a separate route to the intended C4. It appears to follow from the
known prime-level theorem plus the known harmonic congruence; it should not be
advertised as a new prime-level result. A complete Lean derivation is missing.

Fix an admissible prime `p>=5`. For any integer `i>=0`, the same unit-product
argument, now only modulo `p^2`, gives

    C_(ip+j)^3 = C_i^3 C_j^3 (1+6ip D_j) (mod p^2), 0<=j<=h.

This does not divide by `C_i`: the exact identity has the multiplicative
factor `C_i`, with all remaining denominators prime to `p`. Thus it remains
valid when `C_i` is divisible by `p`. For `h<j<p`, the lower-digit carry makes
the cube divisible by `p^3`. Both the complete block and the first half block
therefore sum to zero modulo `p^2`, since `S=0 (mod p^2)` and `D=0 (mod p)`.
The first is Sun's Theorem 3.2; the latter is also the published CM harmonic
corollary identified in `literature.md` (or follows from the proposed identities
above).

If `m` is odd, write `(mp-1)/2 = p(m-1)/2+h`. Splitting at multiples of `p`
shows

    p^2 divides a((mp-1)/2).

For `p=3`, `h=1` and the block formula becomes, directly modulo 9,

    C_(3i)^3 + C_(3i+1)^3 = C_i^3 (1+8(1+9i)) = 0 (mod 9).

The omitted term at `3i+2` has a factor `3^3`. Binomial scaling modulo 9
holds here: the unit reciprocal sum is zero modulo 3, which suffices. Hence
the same conclusion holds for every odd `m` at `p=3`.

Now let `n` be a product of distinct admissible primes. It is positive and odd.
For each prime factor `p`, the quotient `m=n/p` is odd, so `p^2` divides
`a((n-1)/2)`. The distinct squares are pairwise coprime; their product `n^2`
divides the same value. The empty set gives `n=1` and is immediate.

This is a proposed deduction, not an independently verified or Lean-complete
resolution. Its novelty relative to existing block-congruence theorems remains
unestablished.

## A separate Legendre-polynomial route toward conjecture 3

This route is incomplete. It isolates an apparently stronger missing lemma;
experiments are not a substitute for its proof.

Put `F_n(x)=sum_(k=0)^n C_k^3 x^k`. For odd `q`, `n=(q-1)/2`, the exact
terminating Clausen identity gives

    G_n(x) := P_n(sqrt(1-64x))^2
            = sum_(k=0)^n binom(2k,k) binom(n,k) binom(n+k,k) (-16x)^k
            = sum_(k=0)^n C_k^3 x^k prod_(r=1)^k(1-q^2/(2r-1)^2).

The middle expression is a polynomial and requires no choice of square root.
For `q=p^2`, all factors with `p` not dividing `2r-1` are 1 modulo `p^4`.
For a no-carry index `k=ip+j`, `0<=i,j<=h`, the remaining factors are

    1-p^2 T_i (mod p^4), T_i=sum_(r=0)^(i-1) 1/(2r+1)^2.

Here `2r+1<p`. Carry indices already have `p^3 | C_k^3`, so their
contribution to `G_N-F_N` has valuation at least five. Combining the
first-order block expansion with the last formula would give

    G_N(x)-F_N(x)
      = -p^2 sum_(i=0)^h c_i x^(ip) T_i (S(x)+6ip D(x)) (mod p^4),

where `S(x)=sum c_j x^j` and `D(x)=sum c_j D_j x^j` over `0<=j<=h`.
Consequently the known prime-level vanishing `S(1)=0 (mod p^2)` and
`D(1)=0 (mod p)` would reduce C3 to

    G_N(1) = p^2 (mod p^4).                                  (5)

For `p>=5`, one sufficient statement would be
`P_N(sqrt(-63)) = plus or minus p (mod p^3)` in a suitable unramified
quadratic extension. The sign disappears upon squaring. No theorem proving
this precise statement was found in the sources inspected during the session.
The ordinary-prime Coster–van Hamme theorem does not supply it. A possible
approach is to adapt its formal-group coefficient argument to the degree
`p^2` multiplication-by-`-p` map at a supersingular prime; that adaptation
has not been carried out. The ordinary theorem cannot simply be invoked with
`p^2` substituted for a prime.

`legendre_screen.py --bound 101` evaluates exact integer coefficients and
checks all nonzero roots of `F_h(x)` modulo `p`, excluding `64x=1`, at the
three lifts `x`, `x+p`, and `x+2p`. All 303 cases satisfy (5), the analogous
`F_N` congruence, and their comparison. It also checks 102 rational
finite-field roots of `P_h(t)`; each has `P_N(t)+p=0 (mod p^3)`. These
bounded screens suggest that the missing statement has a wider scope than
the particular CM value, but do not establish that scope or novelty.

### Possible formal-group closure of (5): conditional and unreviewed

A coefficient argument suggests how a supersingular Jacobi multiplication map
might supply (5). The required geometric facts below have **not** been proved
in Lean or independently reviewed. This paragraph does not upgrade the target
status to a proof.

Take the Jacobi quartic `v^2=1-2t u^2+u^4`, with `t^2-1` a unit, and its
formal logarithm

    ell(u) = sum_(k>=0) P_k(t) u^(2k+1)/(2k+1).

Over an unramified extension at `p>=5`, suppose its multiplication-by-`-p`
map on the `u` coordinate has the following properties, with `q=p^2`:

1. `F(u)=A(u)/D(u)` is odd, `A,D` have integral coefficients,
   `deg A=q`, `deg D<q`, `D(0)=1`, and the coefficient of `u^q` in `A`
   is `epsilon` with `epsilon^2=1` **exactly**.
2. Supersingularity gives `A(u)=epsilon*u^q (mod p)` and `D(u)=1 (mod p)`.
3. `ell(F(u))=-p*ell(u)` as formal power series.

The first two facts are stronger than a bare assertion that the formal group
has height two. They must be checked for this coordinate and its normalization.
A possible geometric justification for the exact leading sign is the
reciprocal relation `F(1/u)=1/F(u)`, inherited from translation by two-torsion
on a Jacobi quartic. One must also justify the descent of multiplication to
this degree-two coordinate and good reduction of the resulting rational map.
The discussion of the function `S(z)` and Lemma 3.6 in Coster–van Hamme is a
useful model, but its prime-degree theorem does not itself assert these
prime-square-degree facts.

Conditional on 1–3, the remaining coefficient argument is short. Write
`A=epsilon*u^q+p*a` with `deg a<q`, and `D=1+p*d` with `d(0)=0`.
Expansion of `1/D` shows that `[u^q]F=epsilon (mod p^2)`: the order-`p`
term from `a` has degree below `q`, and the order-`p` term from `u^q*d`
has degree above it. Every coefficient of `F` in positive degrees less than
`q` is divisible by `p`. Therefore for each `3<=j<=q`, the coefficient
`[u^q]F^j` is divisible by `p^j`; each of the `j` positive-degree factors
has degree less than `q`. The coefficient of `u^q` in `ell(F)` is

    [u^q]F + sum_(3<=j<=q, j odd) P_((j-1)/2)(t)/j * [u^q]F^j.

All Legendre coefficients are integral at odd primes. For `p>=5` and
`j>=3`, `j-v_p(j)>=2`; hence the displayed sum is zero modulo `p^2`.
Comparing with `-p*ell(u)` gives

    -P_N(t)/p = epsilon (mod p^2),
    P_N(t) = -epsilon*p (mod p^3),
    P_N(t)^2 = p^2 (mod p^4).

For the target, take `t=sqrt(-63)` and use Sun's prime-level character-sum
identification to show the relevant elliptic curve is supersingular. The
identification with this precise Jacobi quartic, together with properties
1–3, remains a substantive unchecked geometric step. The experimental
`P_N(t)+p` values over `F_p` are consistent with this argument. The sign
need not be fixed for (5). The small admissible prime `p=3` is a separate
finite computation for C1–C3.

### Proposed geometric justification to examine

The following explanation sharpens the geometric gap; it remains unreviewed.
On the smooth Jacobi quartic with identity `(u,v)=(0,1)`, negation is
`(u,v)->(-u,v)`. The map `(u,v)->(1/u,-v/u^2)` preserves `du/v` and is an
involution without fixed points when `t^2!=1`, so it is translation by a
nonzero two-torsion point. The deck involution of the degree-two function
`u` is `(u,v)->(u,-v)`, of the form `T-P` for another two-torsion point `T`.
Odd multiplication commutes with both. Thus multiplication by `-p` should
descend to an odd rational function `F(u)` of degree `q=p^2`, fixing 0 and
infinity and satisfying `F(1/u)=1/F(u)`.

If `F=A/D` is in coprime integral form with `D(0)=1`, its degree and oddness
force `deg A=q`, `deg D<=q-1`. Write reciprocal polynomials with respect to
degree `q` as `A*(u)=u^q A(1/u)`, `D*(u)=u^q D(1/u)`. The reciprocal
relation and coprimality give `A*=epsilon D`, `D*=epsilon A`, and
`epsilon^2=1`. Hence the leading coefficient is an exact sign. Smooth good
reduction and the degree-two quotient (with 2 invertible) should ensure a
normalization that stays coprime modulo `p`. At a supersingular point,
`[-p]` is purely inseparable of degree `q`; its descended map is purely
inseparable of the same degree. Fixing 0 and infinity forces its reduction
to be `c*u^q`. This would give the asserted coefficient divisibilities.
A full argument must verify these assertions over the valuation ring,
including the normalization, rather than just over its fraction field.

Supersingularity can also be linked directly to the exact Jacobi coordinate:
the coefficient of `u^(p-1)` in its inverse-square-root differential is
`P_h(t)` modulo `p`, which is its Hasse invariant. The prime-level terminating
Clausen identity and Sun's result give `P_h(sqrt(-63))^2=0 (mod p)`, hence
`P_h(sqrt(-63))=0`. This avoids relying on an unspecified isomorphism to a
CM model, but still requires the Hasse-invariant criterion and the geometric
facts above. No Lean implementation of them is included.
