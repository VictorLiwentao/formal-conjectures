#!/usr/bin/env python3
"""Finite check of the cofactor-seven family. Not a proof."""

def is_prime(n: int) -> bool:
    if n < 2:
        return False
    if n < 4:
        return True
    if n % 2 == 0 or n % 3 == 0:
        return n == 2 or n == 3
    d = 5
    while d * d <= n:
        if n % d == 0 or n % (d + 2) == 0:
            return False
        d += 6
    return True


def min_fac(n: int) -> int:
    if n % 2 == 0:
        return 2
    if n % 3 == 0:
        return 3
    d = 5
    while d * d <= n:
        if n % d == 0:
            return d
        if n % (d + 2) == 0:
            return d + 2
        d += 6
    return n


def is_larger_twin(q: int) -> bool:
    return q >= 13 and is_prime(q - 2)


def main() -> None:
    limit = 200000
    remaining = 0
    covered = 0
    uncovered_examples = []
    for p in range(5, limit):
        if p % 3 != 1 or not is_prime(p):
            continue
        if is_prime(p - 2):
            continue
        q = min_fac(p - 2)
        if q < 107:
            continue
        if is_larger_twin(q):
            continue
        remaining += 1
        s = (p - 2) // q
        ok = s > 1 and s % 3 == 1 and q >= 7 and is_prime(7 * s - 2)
        if ok:
            covered += 1
        elif len(uncovered_examples) < 20:
            uncovered_examples.append((p, q, s, 7 * s - 2))
    print(f"remaining McEachen primes p < {limit}: {remaining}")
    print(f"covered by 7s-2 prime: {covered}")
    print(f"uncovered: {remaining - covered}")
    print("first uncovered (p, q, s, 7s-2):")
    for row in uncovered_examples:
        print(row)


if __name__ == "__main__":
    main()
