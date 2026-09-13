#!/usr/bin/env python3
"""F_p coefficient of the harmonic unit sum vs Bernoulli.

Experimental only. Unverified relative to Lean.

combo = p * ((7/4)c + 2*S3 - tau) in ZMod(p^2),
where S2 = p*c is the half-range inverse squares.
"""
from __future__ import annotations

from fractions import Fraction


def is_prime(n: int) -> bool:
    if n < 2:
        return False
    if n % 2 == 0:
        return n == 2
    d = 3
    while d * d <= n:
        if n % d == 0:
            return False
        d += 2
    return True


def comb(n: int, k: int) -> int:
    if k < 0 or k > n:
        return 0
    r = 1
    for i in range(k):
        r = r * (n - i) // (i + 1)
    return r


def bernoulli(m: int) -> Fraction:
    """Bernoulli numbers B_m with B_1 = -1/2."""
    B = [Fraction(1)]
    for n in range(1, m + 1):
        tot = sum(Fraction(comb(n + 1, k)) * B[k] for k in range(n))
        B.append(-tot / (n + 1))
    return B[m]


def inv_mod(a: int, m: int) -> int:
    return pow(a, -1, m)


def zmod_inv_pow(k: int, e: int, mod: int) -> int:
    return pow(inv_mod(k, mod), e, mod)


def H_zmod(n: int, mod: int) -> int:
    s = 0
    for b in range(1, n + 1):
        s = (s + inv_mod(b, mod)) % mod
    return s


def reduce_rat(q: Fraction, p: int) -> int | None:
    if q.denominator % p == 0:
        return None
    return (q.numerator * inv_mod(q.denominator % p, p)) % p


def main() -> None:
    print("p kappa B extra=kappa+7B/8  2S3-tau  7c/4")
    for p in range(5, 80, 2):
        if not is_prime(p):
            continue
        mod = p * p
        S2 = sum(zmod_inv_pow(i + 1, 2, mod) for i in range(p // 2)) % mod
        S3 = sum(zmod_inv_pow(i + 1, 3, mod) for i in range(p // 2)) % mod
        tau = 0
        for r in range(1, p, 2):
            tau = (tau + H_zmod(r - 1, mod) * zmod_inv_pow(r, 2, mod)) % mod
        c_lift = (S2 * inv_mod(p, p) if False else S2 // p) % mod
        inv4 = inv_mod(4, mod)
        kappa = (7 * inv4 % mod * c_lift + 2 * S3 - tau) % mod
        kappa_p = kappa % p
        B = bernoulli(p - 3)
        Bmod = reduce_rat(B, p)
        inv8 = inv_mod(8, p)
        extra = None if Bmod is None else (kappa_p + (7 * Bmod * inv8) % p) % p
        print(
            f"p={p:2d} kappa={kappa_p:2d} B={Bmod} extra={extra} "
            f"2S3-tau={(2 * (S3 % p) - (tau % p)) % p} "
            f"7c/4={(7 * inv_mod(4, p) * (c_lift % p)) % p} "
            f"c={c_lift % p} S3={S3 % p} tau={tau % p}"
        )


if __name__ == "__main__":
    main()
