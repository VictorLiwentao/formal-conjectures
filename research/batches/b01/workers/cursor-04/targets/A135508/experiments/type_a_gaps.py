#!/usr/bin/env python3
"""Search leftover Type A/B McEachen-window injector gaps.

Experimental only; not a Lean proof. Remaining leftover means p ≡ 1 (mod 3),
p-2 composite, lpf(p-2) ≥ 157, and that least factor is not a larger twin.

Type A is p-2 < lpf^3. The cofactor (p-2)/lpf is then prime (proved in Lean as
remaining_type_A_cofactor_prime). A McEachen counterexample candidate needs no
prime injector k*r-2 with k ≤ (p-2)/r for any prime factor r of p-2.
"""

from __future__ import annotations

import sys
from math import isqrt


def miller_rabin(n: int) -> bool:
    if n < 2:
        return False
    if n < 4:
        return True
    if n % 2 == 0:
        return False
    d, s = n - 1, 0
    while d % 2 == 0:
        d //= 2
        s += 1
    for a in (2, 3, 5, 7, 11, 13, 23):
        if a % n == 0:
            continue
        x = pow(a, d, n)
        if x in (1, n - 1):
            continue
        for _ in range(s - 1):
            x = pow(x, 2, n)
            if x == n - 1:
                break
        else:
            return False
    return True


def sieve(n: int) -> bytearray:
    s = bytearray(b"\x01") * (n + 1)
    s[0:2] = b"\x00\x00"
    for i in range(2, isqrt(n) + 1):
        if s[i]:
            start = i * i
            s[start : n + 1 : i] = b"\x00" * ((n - start) // i + 1)
    return s


def min_fac(n: int, primes: list[int]) -> int:
    for p in primes:
        if p * p > n:
            return n
        if n % p == 0:
            return p
    return n


def factors(n: int, primes: list[int]) -> list[int]:
    out = []
    m = n
    for p in primes:
        if p * p > m:
            break
        if m % p == 0:
            out.append(p)
            while m % p == 0:
                m //= p
    if m > 1:
        out.append(m)
    return out


def first_injector(r: int, kmax: int) -> tuple[int, int] | None:
    if r % 3 == 2:
        k, step = 5, 6
    elif r % 3 == 1:
        k, step = 7, 6
    else:
        return None
    while k <= kmax:
        rinj = k * r - 2
        if rinj > 3 and rinj % 3 == 2 and miller_rabin(rinj):
            return k, rinj
        k += step
    return None


def main() -> None:
    n = int(sys.argv[1]) if len(sys.argv) > 1 else 2000000
    qmin = int(sys.argv[2]) if len(sys.argv) > 2 else 157
    sp = sieve(n + 10)
    primes = [i for i in range(2, isqrt(n) + 20) if sp[i]]
    leftover = 0
    type_a = 0
    type_b = 0
    lean_type_b = 0
    type_a_semiprime_fail = []
    uncovered = []
    type_b_examples = []
    seven_r = 0
    kstats = []
    worst = (0, 0, 0, 0)
    for p in range(7, n):
        if not sp[p] or p % 3 != 1:
            continue
        m = p - 2
        if sp[m]:
            continue
        q = min_fac(m, primes)
        if miller_rabin(q - 2):
            continue
        if q < qmin:
            continue
        leftover += 1
        cof = m // q
        facs = factors(m, primes)
        is_a = m < q * q * q
        lean_b = all(r % 3 == 2 for r in facs)
        if lean_b:
            lean_type_b += 1
        if is_a:
            type_a += 1
            if not miller_rabin(cof):
                type_a_semiprime_fail.append((p, q, cof, facs))
        else:
            type_b += 1
            type_b_examples.append((p, q, cof, facs, lean_b))
        hit = None
        for r in facs:
            found = first_injector(r, m // r)
            if found is not None:
                hit = (r, found[0], found[1])
                break
        if hit is None:
            uncovered.append((p, q, cof, facs, "A" if is_a else "B"))
        else:
            kstats.append(hit[1])
            if hit[1] > worst[0]:
                worst = (hit[1], p, hit[0], hit[2])
        if any(
            r % 3 == 1 and miller_rabin(7 * r - 2) and 7 <= m // r
            for r in facs
        ):
            seven_r += 1

    print(f"leftover remaining p < {n}, lpf >= {qmin}: {leftover}")
    print(f"Type A (p-2 < lpf^3): {type_a}")
    print(f"Type B (p-2 >= lpf^3): {type_b}")
    print(f"Lean Type B (all prime factors ≡ 2 mod 3): {lean_type_b}")
    print(f"Type A cofactor not prime: {len(type_a_semiprime_fail)}")
    if type_a_semiprime_fail:
        print("first Type A semiprime failures:", type_a_semiprime_fail[:10])
    print(f"some complementary 7r-2 prime: {seven_r}")
    print(f"no McEachen-window injector: {len(uncovered)}")
    if kstats:
        print(
            "covering k min/max/mean:",
            min(kstats),
            max(kstats),
            f"{sum(kstats) / len(kstats):.3f}",
        )
    print("worst covering k:", worst)
    if type_b_examples:
        print("cube-Type B examples (first 20):")
        for row in type_b_examples[:20]:
            print(row)
    if uncovered:
        print("uncovered (counterexample candidates):")
        for row in uncovered[:20]:
            print(row)


if __name__ == "__main__":
    main()
