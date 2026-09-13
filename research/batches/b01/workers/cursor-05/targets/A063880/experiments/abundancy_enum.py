#!/usr/bin/env python3
"""One- and two-prime exact fills of a leftover ratio. Fast Diophantine checks."""
from fractions import Fraction
import sys
sys.stdout.reconfigure(line_buffering=True)

def is_prime(n):
    if n < 2: return False
    if n % 2 == 0: return n == 2
    i = 3
    while i * i <= n:
        if n % i == 0: return False
        i += 2
    return True

def next_prime(n):
    p = n + 1
    while not is_prime(p):
        p += 1
    return p

def rho(p, a):
    return Fraction(p ** (a + 1) - 1, (p - 1) * (p ** a + 1))

def max_last(T: Fraction):
    if T <= 1:
        return None
    return int(T / (T - 1))

def one_prime(T: Fraction, pmin: int, amax=20):
    b = max_last(T)
    out = []
    if b is None:
        return out
    p = next_prime(pmin - 1)
    while p <= b:
        for a in range(2, amax + 1):
            r = rho(p, a)
            if r == T:
                out.append((p, a))
            if r > T:
                break
        p = next_prime(p)
    return out

def two_prime(T: Fraction, pmin: int, amax=12):
    out = []
    p = pmin if is_prime(pmin) else next_prime(pmin)
    # p as smaller prime: ρ(p^a) < T, leftover filled by one prime > p
    # bound: cap(p)*cap(next) >= T, else p too large
    while True:
        q0 = next_prime(p)
        if Fraction(p, p - 1) * Fraction(q0, q0 - 1) < T:
            break
        if rho(p, 2) > T:
            p = next_prime(p)
            continue
        for a in range(2, amax + 1):
            r = rho(p, a)
            if r >= T:
                break
            fill = one_prime(T / r, next_prime(p), amax=amax)
            for q, b in fill:
                out.append(((p, a), (q, b)))
        p = next_prime(p)
        if p > 500:
            break
    return out

print("3^3 exact leftover 1: trivial unique kernel 27")
print("3^2 leftover 100/91 one-prime >=5", one_prime(Fraction(100, 91), 5))
print("3^2 leftover 100/91 two-prime >=5", two_prime(Fraction(100, 91), 5))
print("5^3 leftover 15/13 one-prime >=7", one_prime(Fraction(15, 13), 7))
print("5^3 leftover 15/13 two-prime >=7", two_prime(Fraction(15, 13), 7))
print("13^3 leftover 157/119 one-prime >=3", one_prime(Fraction(157, 119), 3))
print("13^3 leftover 157/119 two-prime >=3", two_prime(Fraction(157, 119), 3))
print("17^3 leftover 39/29 one-prime >=3", one_prime(Fraction(39, 29), 3))
print("19^3 leftover 245/181 one-prime >=3", one_prime(Fraction(245, 181), 3))
print("31^3 leftover", Fraction(10, 7) / rho(31, 3), "one-prime >=3",
      one_prime(Fraction(10, 7) / rho(31, 3), 3))

print("\n6/5 one-prime >=3", one_prime(Fraction(6, 5), 3))
print("6/5 two-prime >=3", two_prime(Fraction(6, 5), 3))
print("34/31 one-prime >=3", one_prime(Fraction(34, 31), 3))
print("34/31 two-prime >=3", two_prime(Fraction(34, 31), 3))
print("22/21 one-prime >=3", one_prime(Fraction(22, 21), 3))
print("2 one-prime odd", one_prime(Fraction(2), 3))
print("2 two-prime odd", two_prime(Fraction(2), 3))
print("2 three? 3^a 5^b leftover then one",)
for a in range(2, 8):
    for b in range(2, 8):
        r = rho(3, a) * rho(5, b)
        if r >= 2:
            continue
        fill = one_prime(Fraction(2) / r, 7)
        if fill:
            print("  3^%d 5^%d +" % (a, b), fill)
