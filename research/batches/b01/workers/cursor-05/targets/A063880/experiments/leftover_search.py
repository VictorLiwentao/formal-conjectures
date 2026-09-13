#!/usr/bin/env python3
"""Exact leftover-ratio search for squareful kernels of A063880.

This is a deterministic Fraction search. It is evidence, not a Lean proof.
Preserve output as unverified until each claimed empty branch is proved in Lean.
"""
from fractions import Fraction
import sys

sys.stdout.reconfigure(line_buffering=True)


def is_prime(n: int) -> bool:
    if n < 2:
        return False
    if n % 2 == 0:
        return n == 2
    i = 3
    while i * i <= n:
        if n % i == 0:
            return False
        i += 2
    return True


def next_prime(n: int) -> int:
    p = n + 1
    while not is_prime(p):
        p += 1
    return p


def rho(p: int, a: int) -> Fraction:
    return Fraction(p ** (a + 1) - 1, (p - 1) * (p ** a + 1))


def last_bound(T: Fraction) -> Fraction:
    if T <= 1:
        return Fraction(0)
    return T / (T - 1)


def leftover_two_pow(a: int) -> Fraction:
    """Leftover after 2^a: 2 / rho(2^a) = 2(2^a + 1) / (2^{a+1} - 1)."""
    return Fraction(2 * (2 ** a + 1), 2 ** (a + 1) - 1)


def search(T: Fraction, pmin: int, depth: int = 0, amax: int = 40, pmax: int = 5000):
    """Return exact fills of leftover T by prime powers p^a, p >= pmin, a >= 2."""
    T = Fraction(T)
    if T == 1:
        return [[]]
    if T <= 1:
        return []
    sols = []
    p = pmin if is_prime(pmin) else next_prime(pmin - 1)
    cap_T = last_bound(T)
    seen_p = 0
    while p <= pmax:
        seen_p += 1
        r2 = rho(p, 2)
        cap_p = Fraction(p, p - 1)
        if r2 > T:
            # Larger primes have smaller rho(p^2), so they may fit later.
            if p > cap_T and rho(p, 2) > T:
                # rho(p^2) is decreasing in p for p >= 2. If it still overshoots
                # for this p > cap_T, later squares undershoot T and may become
                # last primes once rho(p^2) <= T.
                p = next_prime(p)
                continue
            p = next_prime(p)
            continue

        a = 2
        while a <= amax:
            r = rho(p, a)
            if r > T:
                break
            if r == T:
                sols.append([(p, a)])
            else:
                T2 = T / r
                lb2 = last_bound(T2)
                if lb2 > p:
                    rest = search(T2, next_prime(p), depth + 1, amax=amax, pmax=pmax)
                    for s in rest:
                        sols.append([(p, a)] + s)
            a += 1
            if cap_p <= T:
                T_lim = T / cap_p
                lb_lim = last_bound(T_lim) if T_lim > 1 else Fraction(0)
                q = next_prime(p)
                if last_bound(T / r) <= q and lb_lim <= q:
                    break
                if a == amax:
                    sols.append([("INCOMPLETE_A", p, a, str(T))])

        T_lim = T / cap_p if cap_p > 1 else T
        lb_lim = last_bound(T_lim) if T_lim > 1 else Fraction(0)
        max_lb = lb_lim if cap_p < T else last_bound(T / r2)
        if p >= cap_T and max_lb <= p and r2 <= T:
            break
        p = next_prime(p)
        if p > pmax:
            sols.append([("INCOMPLETE_P", p, str(T))])
            break
    return sols


def show(label, T, pmin=3):
    print(f"\n=== {label} T={T} pmin={pmin} last_bound={last_bound(Fraction(T))} ===")
    sols = search(Fraction(T), pmin)
    real = [s for s in sols if s and not (isinstance(s[0], tuple) and s[0] and s[0][0] == "INCOMPLETE_A" or (isinstance(s[0], tuple) and isinstance(s[0][0], str) and s[0][0].startswith("INCOMPLETE")))]
    flags = [s for s in sols if s and isinstance(s[0], tuple) and isinstance(s[0][0], str) and str(s[0][0]).startswith("INCOMPLETE")]
    # fix classification
    flags = []
    real = []
    for s in sols:
        if not s:
            real.append(s)
            continue
        head = s[0]
        if isinstance(head, tuple) and isinstance(head[0], str) and str(head[0]).startswith("INCOMPLETE"):
            flags.append(s)
        else:
            real.append(s)
    print("solutions", real)
    if flags:
        print("INCOMPLETE", flags)
    print("count", len(real))


if __name__ == "__main__":
    print("rho(4)*rho(27)", rho(2, 2) * rho(3, 3))
    print("last_bound 10/7", last_bound(Fraction(10, 7)))
    print("last_bound 100/91", last_bound(Fraction(100, 91)))
    print("last_bound 2", last_bound(Fraction(2)))
    print("last_bound 6/5", last_bound(Fraction(6, 5)))
    print("This recursive search is explicitly unverified and can be slow.")
    print("Default __main__ does not run search(); use search(T, pmin) explicitly.")
    print("done")
