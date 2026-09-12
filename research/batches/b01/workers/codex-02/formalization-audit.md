# Frozen proposition audit

Both assigned source hashes match the register and the current upstream files
retrieved on 2026-09-12. No source, definition, dependency pin, or global assignment
was changed.

- Quantifiers: arbitrary natural $n,k,p$, then $n>0$, $k>0$, primality, and $p\ge5$.
  These hypotheses are simultaneously satisfiable; $(n,k,p)=(1,1,5)$ is a witness.
- All evaluated sequence arguments $N=np^k$ and $np^{k-1}$ are positive.
  Hence the natural subtraction in $2N-1$ is ordinary subtraction.
- $(2N-1)/2+1=N$, so the finite range is precisely $0,\ldots,N-1$.
- The binomial coefficient at the artificial index $-1$ is implemented by the
  explicit zero branch at $j=0$. No accidental `Nat.sub` value is used there.
- Within this range, consecutive binomial coefficients increase: for $j>0$,
  their ratio is $(2N-j)/j\ge1$. The integer difference and its cube are
  nonnegative. Thus A003161's `Int.toNat` does not truncate a negative summand.
- A003162's rational denominator is $H_N=\binom{2N-1}{N-1}>0$.
  Equation (1) of the joint derivation proves the quotient equals the integer
  $4H_N^2-3T_N$. The rational numerator in lowest terms is therefore this integer.
  This audit does not use the source's `a_is_integer` placeholder.
- Both targets have modulus $(p:\mathbb Z)^{3k}$ with ordinary integer congruence.
  Cancellation of $2$ is valid because $p\ge5$; cancellation of $H_N$ modulo
  the prime is never used. This avoids a gap when $p$ divides $H_N$ or $n$.
- Coster's theorem allows every positive dilation, including multiples of $p$.
  Its sums omit their constant term; this changes neither adjacent difference.
- At $N=1$, the reduction gives $R_N=Q_N=H_N=S_N=T_N=1$.
  For $(n,k,p)=(1,1,5)$, $R_5=204876$, $Q_5=1626$, $H_5=126$, $S_5=6376$.
  All four differences from their value at 1 are divisible by 125.

The mathematical formulations are faithful at the relevant positive odd indices.
The source attribution is a documentation mismatch: live OEIS credits Peter Bala
in March 2023, not the Sun/2019 attribution in the frozen files. This does not
provide a loophole or alter the proposition.

`ExactTypeAudit.lean` reads the original declaration types from the environment
and compares them with the full `Tower` conclusions using `Lean.Meta.isDefEq`.
It does not use the original theorem proof terms. The compiled conditional
certificates still require the identities and classical congruences as hypotheses.
