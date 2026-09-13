#!/usr/bin/env python3
"""Deterministic structure scan for A135508 / OeisA135508.conjecture.

Tracks only the prime factorization of x(n), not the value of x(n).
This is an experimental witness log, not a Lean proof.
"""

import math
from collections import Counter


def sieve_primes(limit: int) -> list[int]:
    if limit < 2:
        return []
    mark = bytearray([1]) * (limit + 1)
    mark[0] = 0
    mark[1] = 0
    for i in range(2, int(limit**0.5) + 1):
        if mark[i]:
            mark[i * i : limit + 1 : i] = b"\x00" * len(range(i * i, limit + 1, i))
    return [i for i, v in enumerate(mark) if v]


def factor_small(n: int, primes: list[int]) -> Counter[int]:
    fac: Counter[int] = Counter()
    m = n
    for p in primes:
        if p * p > m:
            break
        while m % p == 0:
            fac[p] += 1
            m //= p
    if m > 1:
        fac[m] += 1
    return fac


def gcd_from_fac(n: int, xfac: Counter[int], primes: list[int]) -> int:
    g = 1
    for p, e in factor_small(n, primes).items():
        if p in xfac:
            g *= p ** min(e, xfac[p])
    return g


def is_prime(n: int) -> bool:
    if n < 2:
        return False
    if n in (2, 3):
        return True
    if n % 2 == 0 or n % 3 == 0:
        return False
    f = 5
    while f * f <= n:
        if n % f == 0 or n % (f + 2) == 0:
            return False
        f += 6
    return True


def run(max_n: int) -> dict:
    primes = sieve_primes(max_n + 5)
    prime_set = set(primes)
    xfac: Counter[int] = Counter()  # x(1) = 1
    first_entry: dict[int, int] = {}
    a_vals: dict[int, int] = {}
    failures: list[tuple[int, int, int]] = []
    remaining: list[dict] = []
    entry_via: dict[int, tuple[int, int]] = {}

    for n in range(1, max_n):
        # a(n) = (n+1) / gcd(x(n), n+1); then x(n+1) = x(n) * (a(n)+2)
        g = gcd_from_fac(n + 1, xfac, primes)
        an = (n + 1) // g
        a_vals[n] = an
        inc = 2 + an
        inc_fac = factor_small(inc, primes)
        for p, e in inc_fac.items():
            if p not in first_entry:
                first_entry[p] = n + 1  # x(n+1) first divisible by p
                entry_via[p] = (n, an)
            xfac[p] += e

    mceachen_ok = 0
    mceachen_checked = 0
    for p in primes:
        if p > max_n:
            break
        if is_prime(p - 2):
            continue
        mceachen_checked += 1
        # need a(p-1) = p, i.e. gcd(x(p-1), p) = 1
        if p - 1 not in a_vals:
            continue
        got = a_vals[p - 1]
        if got != p:
            failures.append((p, got, p - 1))
        else:
            mceachen_ok += 1
        # remaining class: p ≡ 1 (mod 3), 5 does not divide p-2
        if p >= 5 and p % 3 == 1 and (p - 2) % 5 != 0:
            q = min(factor_small(p - 2, primes))
            n0 = first_entry.get(q)
            remaining.append(
                {
                    "p": p,
                    "p_minus_2": p - 2,
                    "min_fac": q,
                    "first_entry_q": n0,
                    "need_le": p - 3,
                    "ok": n0 is not None and n0 <= p - 3,
                    "entry_via": entry_via.get(q),
                }
            )

    ratios = []
    for q in primes:
        if q == 2:
            continue
        if q not in first_entry:
            continue
        if q > 5000:
            break
        ratios.append((first_entry[q] / q, q, first_entry[q], entry_via.get(q)))
    ratios.sort(reverse=True)

    return {
        "max_n": max_n,
        "mceachen_checked": mceachen_checked,
        "mceachen_ok": mceachen_ok,
        "failures": failures,
        "first_entry_small": {q: first_entry[q] for q in primes[:40] if q in first_entry},
        "worst_ratios": ratios[:15],
        "remaining_count": len(remaining),
        "remaining_fail_entry": [r for r in remaining if not r["ok"]],
        "remaining_sample": remaining[:20],
        "first_entry_7": first_entry.get(7),
        "first_entry_11": first_entry.get(11),
        "first_entry_13": first_entry.get(13),
        "a1_a6": [a_vals.get(i) for i in range(1, 7)],
    }


def main() -> None:
    out = run(20000)
    print("a(1..6)", out["a1_a6"])
    print("McEachen checked/ok", out["mceachen_checked"], out["mceachen_ok"])
    print("failures", out["failures"])
    print("first_entry small", out["first_entry_small"])
    print("first 7,11,13", out["first_entry_7"], out["first_entry_11"], out["first_entry_13"])
    print("worst first_n/q", out["worst_ratios"][:10])
    print("remaining remaining-class", out["remaining_count"])
    print("remaining that miss entry bound", out["remaining_fail_entry"])
    print("remaining sample:")
    for row in out["remaining_sample"]:
        print(row)


if __name__ == "__main__":
    main()
