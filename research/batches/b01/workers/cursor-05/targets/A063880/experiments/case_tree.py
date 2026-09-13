#!/usr/bin/env python3
"""Exact leftover case tree for squareful kernels of A063880.

This is deterministic Fraction arithmetic. It is evidence, not a Lean proof.
Empty branches are not a resolution of the frozen theorems.
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


def primes_from(pmin: int, pmax: int):
    p = pmin if is_prime(pmin) else next_prime(pmin)
    while p <= pmax:
        yield p
        p = next_prime(p)


def rho(p: int, a: int) -> Fraction:
    return Fraction(p ** (a + 1) - 1, (p - 1) * (p ** a + 1))


def cap(p: int) -> Fraction:
    return Fraction(p, p - 1)


def last_bound(T: Fraction) -> Fraction:
    if T <= 1:
        return Fraction(0)
    return T / (T - 1)


def max_a(p: int, T: Fraction, amax: int = 80) -> int:
    """Largest a >= 2 with rho(p,a) <= T, or 1 if none."""
    if rho(p, 2) > T:
        return 1
    a = 2
    while a < amax and rho(p, a + 1) <= T:
        a += 1
    return a


def one_prime_fills(T: Fraction, pmin: int, amax: int = 80):
    out = []
    b = last_bound(T)
    if b <= 1:
        return out
    for p in primes_from(pmin, int(b)):
        for a in range(2, amax + 1):
            r = rho(p, a)
            if r == T:
                out.append((p, a))
            if r > T:
                break
    return out


def two_prime_fills(T: Fraction, pmin: int, amax: int = 40, pmax: int = 20000):
    """Complete ω=2 search: last prime is bounded by leftover after the first."""
    out = []
    incomplete = []
    p = pmin if is_prime(pmin) else next_prime(pmin)
    while p <= pmax:
        if rho(p, 2) > T:
            p = next_prime(p)
            continue
        a_hi = max_a(p, T, amax=amax)
        progressed = False
        for a in range(2, a_hi + 1):
            r = rho(p, a)
            if r >= T:
                break
            T2 = T / r
            lb = last_bound(T2)
            if lb <= p:
                continue
            progressed = True
            fills = one_prime_fills(T2, next_prime(p), amax=amax)
            for q, b in fills:
                out.append(((p, a), (q, b)))
        # If even a=2 cannot leave room for a last prime > p, larger p
        # has smaller remaining leftover when using a=2 (ρ(p^2) decreases, so
        # remaining leftover increases... wait remaining T/ρ(p^2) increases
        # toward T as p grows). So last_bound approaches last_bound(T).
        # Stop when p >= last_bound(T) and last_bound(T/ρ(p^2)) <= p.
        T2min = T / rho(p, 2)  # largest remaining after using p (min ρ)
        if last_bound(T) < p and last_bound(T2min) <= p:
            # p cannot be last, and even the most generous remaining last-bound
            # after using p^2 is <= p. Higher a shrinks remaining leftover
            # toward cap(p), last-bound of that limit is T_lim/(T_lim-1) with
            # T_lim = T/cap(p). If that is also <= p, stop.
            T_lim = T / cap(p)
            lb_lim = last_bound(T_lim) if T_lim > 1 else Fraction(0)
            if lb_lim <= p:
                break
        p = next_prime(p)
        if p > pmax:
            incomplete.append(("INCOMPLETE_P", p, str(T)))
            break
    return out, incomplete


def omega3_square_overshoot(T: Fraction, pmin: int) -> bool:
    """True if the three smallest primes >= pmin already overshoot at k=2,
    AND we also need to check large-prime undershoot separately."""
    p = pmin if is_prime(pmin) else next_prime(pmin)
    q = next_prime(p)
    r = next_prime(q)
    return rho(p, 2) * rho(q, 2) * rho(r, 2) > T


def three_cap_lt(T: Fraction, pmin: int) -> bool:
    p = pmin if is_prime(pmin) else next_prime(pmin)
    q = next_prime(p)
    r = next_prime(q)
    return cap(p) * cap(q) * cap(r) < T


def report_T(label: str, T: Fraction, pmin: int = 3):
    T = Fraction(T)
    print(f"\n==== {label} T={T} ≈ {float(T):.9f} pmin={pmin} ====")
    print("last_bound", last_bound(T))
    print("omega1", one_prime_fills(T, pmin))
    two, inc2 = two_prime_fills(T, pmin)
    print("omega2 count", len(two))
    if two[:20] != two:
        print("omega2 first 20", two[:20])
    else:
        print("omega2", two)
    if inc2:
        print("omega2 INCOMPLETE", inc2)

    p = pmin if is_prime(pmin) else next_prime(pmin)
    print("rho(pmin^2)", rho(p, 2), "cap(pmin)", cap(p))
    q = next_prime(p)
    r = next_prime(q)
    print("rho squares 3 smallest", rho(p, 2) * rho(q, 2) * rho(r, 2))
    print("caps 3 smallest", cap(p) * cap(q) * cap(r))
    print("3-squares overshoot T", rho(p, 2) * rho(q, 2) * rho(r, 2) > T)
    print("3-caps undershoot T", cap(p) * cap(q) * cap(r) < T)

    # Smallest p with rho(p^2) <= T
    pfit = p
    while rho(pfit, 2) > T:
        pfit = next_prime(pfit)
        if pfit > 5000:
            print("no p with rho(p^2)<=T below 5000")
            return
    print("smallest p with rho(p^2)<=T", pfit, "rho", rho(pfit, 2))

    # For leftover 100/91 style: check p=11 remainder
    if T == Fraction(100, 91):
        print("11^2", rho(11, 2), "remaining", T / rho(11, 2))
        print("11^3", rho(11, 3), "overshoot", rho(11, 3) > T)
        rem = T / rho(11, 2)
        print("after 11^2 last_bound", last_bound(rem))
        print("after 11^2 omega1", one_prime_fills(rem, 13))
        two_rem, inc = two_prime_fills(rem, 13, pmax=3000)
        print("after 11^2 omega2 count", len(two_rem), "incomplete", inc)
        if two_rem:
            print("after 11^2 omega2", two_rem[:10])


def leftover_after_two_pow(a: int) -> Fraction:
    return Fraction(2 * (2 ** a + 1), 2 ** (a + 1) - 1)


if __name__ == "__main__":
    print("rho(4)*rho(27)", rho(2, 2) * rho(3, 3))
    report_T("leftover 10/7 (v2=2)", Fraction(10, 7), 3)
    report_T("leftover 100/91 (v2=2,v3=2)", Fraction(100, 91), 5)
    report_T("leftover 100/91 pmin=11", Fraction(100, 91), 11)
    report_T("leftover 6/5 (v2=3)", Fraction(6, 5), 3)
    report_T("leftover 34/31 (v2=4)", Fraction(34, 31), 3)
    report_T("leftover 22/21 (v2=5)", Fraction(22, 21), 3)
    report_T("leftover 130/127 (v2=6)", leftover_after_two_pow(6), 3)
    report_T("leftover 2 (odd)", Fraction(2), 3)
    print("\ndone")
