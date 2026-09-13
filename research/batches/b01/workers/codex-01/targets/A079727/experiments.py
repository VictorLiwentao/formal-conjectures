#!/usr/bin/env python3
"""Deterministic arithmetic evidence; not a formal proof.
Copyright 2026 Wentao Li. Apache-2.0.
AI assistance: OpenAI Codex.
"""
import argparse
import json
from itertools import combinations
from math import comb, isqrt, prod


def primes_upto(n):
    return [p for p in range(3, n + 1) if all(p % d for d in range(2, isqrt(p) + 1))]


def exact_a(n):
    c = total = 1
    for k in range(1, n + 1):
        c = c * 2 * (2 * k - 1) // k
        total += c ** 3
    return total


def modular_sums(p, exponent, stops):
    """Track p-adic valuation and unit of C(2k,k); only invert p-units."""
    modulus = p ** exponent
    unit = 1
    valuation = 0
    total = 1
    result = {0: 1} if 0 in stops else {}
    for k in range(1, max(stops) + 1):
        numerator, denominator = 2 * (2 * k - 1), k
        while numerator % p == 0:
            numerator //= p
            valuation += 1
        while denominator % p == 0:
            denominator //= p
            valuation -= 1
        assert valuation >= 0
        unit = unit * numerator * pow(denominator, -1, modulus) % modulus
        term = 0 if 3 * valuation >= exponent else pow(unit, 3, modulus) * p ** (3 * valuation)
        total = (total + term) % modulus
        if k in stops:
            result[k] = total
    return result


def block_expansion(p):
    """Test the proposed p^3 block reduction, with rational denominators interpreted modulo p^3."""
    modulus = p ** 3
    h = (p - 1) // 2
    cs = [comb(2*j,j)**3 % modulus for j in range(h+1)]
    harmonic = [0]
    harmonic2 = [0]
    for j in range(1,p):
        inv = pow(j, -1, modulus)
        harmonic.append((harmonic[-1]+inv) % modulus)
        harmonic2.append((harmonic2[-1]+inv*inv) % modulus)
    s0 = sum(cs) % modulus
    m1 = sum(j*c for j,c in enumerate(cs)) % modulus
    m2 = sum(j*j*c for j,c in enumerate(cs)) % modulus
    d = sum(c*(harmonic[2*j]-harmonic[j]) for j,c in enumerate(cs)) % modulus
    e = sum(c*(18*(harmonic[2*j]-harmonic[j])**2-6*harmonic2[2*j]+3*harmonic2[j]) for j,c in enumerate(cs)) % modulus
    rhs = (s0*s0 + 6*p*m1*d + p*p*m2*e) % modulus
    actual = modular_sums(p,3,{(p*p-1)//2})[(p*p-1)//2]
    return {'p':p, 'S0_mod_p2':s0%(p*p), 'D_mod_p':d%p,
            'M1_mod_p':m1%p,'M2_mod_p':m2%p,'D_over_p_mod_p':(d//p)%p if d%p==0 else None,
            'E_mod_p':e%p,'rhs_mod_p3':rhs,'actual_mod_p3':actual, 'expansion_agrees':rhs==actual}


def main():
    parser=argparse.ArgumentParser()
    parser.add_argument('--bound',type=int,default=503)
    args=parser.parse_args()
    ps=[p for p in primes_upto(args.bound) if p%7 in (3,5,6)]
    # Compare the modular recurrence with direct integer binomials before screening.
    checks=0
    for p in (3,5,7,13,17):
        values=modular_sums(p,4,set(range(0,2*p+1)))
        for n,v in values.items():
            assert v==exact_a(n)%(p**4)
            checks+=1
    print(json.dumps({'validation':'direct_integer_crosscheck','cases':checks}),flush=True)
    for p in ps:
        stops={p*p,p*(p-1),(p*p-1)//2}
        v=modular_sums(p,4,stops)
        residuals=[(v[p*p]-8-p*p)%(p**3),(v[p*(p-1)]-p*p)%(p**3),
                   (v[(p*p-1)//2]-p*p)%(p**4)]
        print(json.dumps({'p':p,'c123_residuals':residuals}),flush=True)
    for S in combinations(ps[:6],2):
        n=prod(S); idx=prod(p-1 for p in S)//2
        print(json.dumps({'c4_set':S,'rejected_parse_index':idx,'rejected_parse_residue':exact_a(idx)%(n*n),
                          'intended_index':(n-1)//2,'intended_residue':exact_a((n-1)//2)%(n*n)}),flush=True)
    for p in ps[:15]:
        if p>3:
            print(json.dumps({'block':block_expansion(p)}),flush=True)

if __name__=='__main__':
    main()
