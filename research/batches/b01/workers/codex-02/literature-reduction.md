# Literature reduction for A003161 and A003162

Status: `prior_solution_found`. Published results imply both exact mathematical
statements. This deduction has been checked by the worker, not by an independent
reviewer. The Lean files certify only the final algebraic transfer under explicit
hypotheses. They are not complete formal proofs of either conjecture.

## Definitions and normalization

For $N\ge1$, write
\[
 R_N=\sum_{j=0}^{N-1}\left(\binom{2N-1}{j}-\binom{2N-1}{j-1}\right)^3,
 \quad H_N=\binom{2N-1}{N-1},
\]
where the binomial coefficient at $j=-1$ is zero. Define
\[
 S_N=\sum_{j=0}^{N-1}\binom{N-1+j}{j}^2,
 \qquad T_N=\sum_{j=N}^{2N-1}\binom jN\binom j{N-1}.
\]
The source for the needed cubic identity is Miana, Ohtsuka and Romero,
[*Sums of powers of Catalan triangle numbers*](https://arxiv.org/html/1602.04347),
Corollary 4.2(i). Their $B_{N,k}$ is our ballot term after reversing the index;
its $k=0$ term is zero. Their formula, with
$\binom{2N}{N}=2H_N$, gives
\[
 R_N=H_N(4H_N^2-3T_N). \tag{1}
\]
It follows that $R_N/H_N$ is an integer, since $H_N>0$. This proves the
integrality and normalization bridge needed before transferring to A003162.
The frozen theorem `OeisA3162.a_is_integer`, which contains `sorry`, is not used.

## The elementary telescoping step

Pascal's identity gives
\[
 \binom{j+1}{N}^2-\binom jN^2
 =2\binom jN\binom j{N-1}+\binom j{N-1}^2.
\]
Sum from $j=0$ to $2N-1$. The left side is $4H_N^2$.
The product sum is $T_N$. In the square sum, terms below $N-1$ vanish,
the last term is $H_N^2$, and reindexing the other terms gives $S_N$.
Thus
\[
 2T_N=3H_N^2-S_N. \tag{2}
\]
Let $Q_N=R_N/H_N$. Equations (1) and (2) give the exact identities
\[
 Q_N=4H_N^2-3T_N\in\mathbb Z,\qquad
 2Q_N=3S_N-H_N^2,\qquad
 2R_N=H_N(3S_N-H_N^2). \tag{3}
\]
These identities also hold at $N=1$, where $R_N=H_N=S_N=Q_N=1$ and $T_N=1$.
No division by $H_N$ in modular arithmetic is required.

## The published arithmetic theorem

Coster, [*Supercongruences*, CWI report AM-R8918 (1989)](https://ir.cwi.nl/pub/5804/5804D.pdf),
printed page 5 (PDF page 7), Theorem 4, applies for all positive $m,r$ and
primes $p\ge5$. Its generalized sum is
\[
 w_{A,B,\epsilon}(t)=\sum_{j=1}^{t}
 \binom tj^A\binom{t+j}{j}^B\epsilon^j.
\]
The shifted congruence applies when $B\ge2$; take $(A,B,\epsilon)=(0,2,1)$.
Because $S_N=1+w_{0,2,1}(N-1)$, it gives
$S_{mp^r}\equiv S_{mp^{r-1}}\pmod{p^{3r}}$.

The unshifted congruence applies when $A\ge2$; take $(2,0,1)$.
Vandermonde gives $1+w_{2,0,1}(N)=\binom{2N}{N}=2H_N$.
Since $2$ is invertible modulo $p^{3r}$, $H_N$ has the same congruence.
The printed sums start at $1$; adding the constant term changes neither
adjacent difference. There is no requirement that $p$ be coprime to $m$.
The theorem's proof is referenced there to Coster's 1988 thesis, pages 49–55;
this audit reads the published theorem, not those thesis proof pages.

## Consequences for the frozen declarations

Insert the two congruences into (3), then cancel $2$ modulo $p^{3r}$.
The result for $R_N$ is `OeisA3161.conjecture`. The result for $Q_N$ is
`OeisA3162.conjecture`: equation (1) supplies integrality, so the reduced
rational numerator is precisely $Q_N$.

This is a deduction from published theorems, not a claim that either source
explicitly names the 2023 OEIS conjectures. No novelty claim is made for the
assembly of the formulas. The 2026 public partial ballot report misses this
connection in the version inspected. Both targets are retired from this
new-result research batch; no unrelated target is substituted.

## Methods and limits

Research and write-up: Wentao Li, with OpenAI Codex AI assistance. Original Lean
formalization: The Formal Conjectures Authors. Mathematical credit belongs to
Coster for the congruence theorem and Miana, Ohtsuka and Romero for the cited
ballot identity; the conjectures are attributed by live OEIS to Peter Bala.

`experiments.py` uses exact Python integers and checks (1)–(3), integer division,
and a bounded grid of the two assigned congruences and the two classical inputs.
These checks are supplemental evidence. They do not replace the mathematical
argument, a complete Lean proof, or fresh independent review.
