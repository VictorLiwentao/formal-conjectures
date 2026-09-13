#!/usr/bin/env python3
"""Classify first-entry indices of primes. Experimental only; not a proof.

Checks whether q first divides x at a prime injector kq-2, a composite
coprime shift, or some other a(n) ≡ -2 (mod q).
"""

from collections import Counter

from scan_structure import factor_small, gcd_from_fac, is_prime, sieve_primes


def main() -> None:
    max_n = 30000
    primes = sieve_primes(max_n + 5)
    xfac: Counter[int] = Counter()
    first_entry: dict[int, tuple[int, int, int]] = {}
    three_div_a = []
    for n in range(1, max_n):
        g = gcd_from_fac(n + 1, xfac, primes)
        an = (n + 1) // g
        if n >= 3 and an % 3 == 0:
            three_div_a.append((n, an))
        inc = 2 + an
        for p, e in factor_small(inc, primes).items():
            if p not in first_entry:
                first_entry[p] = (n + 1, n, an)
            xfac[p] += e

    composite_coprime = []
    prime_inj = []
    other = []
    t_one = []
    for q in primes:
        if q < 11 or q > 4000:
            continue
        if q not in first_entry:
            continue
        m, n, an = first_entry[q]
        kq = n + 3
        k, r = divmod(kq, q)
        shape = {
            "q": q,
            "q_mod_3": q % 3,
            "x_index": m,
            "a_index": n,
            "a_n": an,
            "k_if_shift": None,
            "kq_minus_2_prime": None,
        }
        if r == 0 and k >= 1:
            shape["k_if_shift"] = k
            shape["kq_minus_2_prime"] = is_prime(m) if m == k * q - 2 else False
        if an == q - 2:
            t_one.append(shape)
        if m == k * q - 2 and r == 0:
            if is_prime(m):
                prime_inj.append(shape)
            else:
                composite_coprime.append(shape)
        else:
            other.append(shape)

    print("a(n) divisible by 3 for n>=3, count", len(three_div_a), "sample", three_div_a[:15])
    print("t=1 first entries a(n)=q-2", t_one[:10], "count", len(t_one))
    print("prime injectors", len(prime_inj))
    print("composite kq-2 first entries", len(composite_coprime), "sample", composite_coprime[:20])
    print("other first entries", len(other), "sample", other[:20])
    worst = sorted(prime_inj, key=lambda s: (s["k_if_shift"] or 0), reverse=True)[:10]
    print("worst k among prime injectors", worst)


if __name__ == "__main__":
    main()
