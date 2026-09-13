#!/usr/bin/env python3
"""Bounded structure screen for the A079727 p^4 route; not a proof.
Copyright 2026 Wentao Li. Apache-2.0. AI assistance: OpenAI Codex.
All binomial coefficients are exact integers. No random sampling.
"""
import argparse
import json
from math import comb
from experiments import primes_upto


def horner(coeffs, x, modulus):
    v = 0
    for c in reversed(coeffs):
        v = (v*x+c) % modulus
    return v


def central_coeffs(n, modulus):
    c = 1
    result = [1]
    for k in range(1, n+1):
        c = c*2*(2*k-1)//k
        result.append(pow(c, 3, modulus))
    return result


def legendre_coeffs(n, modulus):
    # P_n(t) = sum binom(n,k)binom(n+k,k)((t-1)/2)^k.
    c = 1
    result = [1]
    for k in range(1,n+1):
        c = c*(n-k+1)*(n+k)//(k*k)
        result.append(c % modulus)
    return result


def clausen_coeffs(n, modulus):
    # P_n(sqrt(1-64x))^2, using the exact terminating Clausen identity.
    c = b = power = 1
    result = [1]
    for k in range(1,n+1):
        c = c*(n-k+1)*(n+k)//(k*k)
        b = b*2*(2*k-1)//k
        power = power*(-16) % modulus
        result.append(c*b*power % modulus)
    return result


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('--bound',type=int,default=101)
    args = parser.parse_args()
    for p in primes_upto(args.bound):
        if p < 5:
            continue
        h, n, mod = (p-1)//2, (p*p-1)//2, p**4
        low = central_coeffs(h,mod)
        roots = [x for x in range(1,p) if (64*x-1)%p and horner(low,x,p)==0]
        high, square = central_coeffs(n,mod), clausen_coeffs(n,mod)
        records = []
        for x0 in roots:
            for lift in (0,1,2):
                x = x0+lift*p
                f,g = horner(high,x,mod),horner(square,x,mod)
                records.append({'x':x,'F_half_prime_mod_p2':horner(low,x,p*p),
                                'F_half_square_residual_mod_p4':(f-p*p)%mod,
                                'Clausen_square_residual_mod_p4':(g-p*p)%mod,
                                'comparison_mod_p4':(f-g)%mod})
        # This second screen requires a rational finite-field square root of 1-64x.
        l0,l1 = legendre_coeffs(h,mod),legendre_coeffs(n,mod)
        ts = [t for t in range(p) if t not in (1,p-1) and horner(l0,(t-1)*pow(2,-1,p),p)==0]
        lrecords = [{'t':t,'P_high_plus_p_mod_p3':
                     (horner(l1,(t-1)*pow(2,-1,mod),mod)+p)%(p**3)} for t in ts]
        print(json.dumps({'p':p,'hypergeometric_roots':records,'legendre_roots':lrecords}),flush=True)


if __name__ == '__main__':
    main()
