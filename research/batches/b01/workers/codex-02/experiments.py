#!/usr/bin/env python3
"""Exact arithmetic audit of the assigned sequences and published reduction.

Copyright 2026 Wentao Li. Licensed under Apache-2.0.
AI assistance: OpenAI Codex. These finite checks are not a general proof.
"""
from functools import lru_cache
from math import comb
import json

@lru_cache(None)
def data(n):
    assert n > 0
    row = 2*n-1
    c, prev, raw = 1, 0, 0
    for j in range(n):
        assert c >= prev
        raw += (c-prev)**3
        prev, c = c, c*(row-j)//(j+1)
    h = comb(row,n-1)
    q, rem = divmod(raw,h)
    assert rem == 0
    s = sum(comb(n-1+j,j)**2 for j in range(n))
    t = sum(comb(j,n)*comb(j,n-1) for j in range(n,2*n))
    assert raw == h*(4*h*h-3*t)
    assert 2*t == 3*h*h-s
    assert 2*q == 3*s-h*h
    return raw,q,h,s

def main():
    for n in range(1,201):
        data(n)
    cases=0
    examples=[]
    for p in (5,7,11,13,17,19):
        for k in range(1,5):
            for n in range(1,51):
                hi=n*p**k
                if hi>3000:
                    continue
                lo=n*p**(k-1)
                top,bottom=data(hi),data(lo)
                modulus=p**(3*k)
                assert all((a-b)%modulus==0 for a,b in zip(top,bottom))
                cases+=1
                if n==1 and k==1 and p==5:
                    examples.append(dict(n=n,k=k,p=p,upper=top,lower=bottom,
                                         modulus=modulus))
    print(json.dumps(dict(identity_range=[1,200],tower_cases=cases,
        tower_primes=[5,7,11,13,17,19],k_range=[1,4],n_range=[1,50],
        max_upper_index=3000,all_checks_passed=True,examples=examples,
        warning="Finite checks only; not a Lean or general proof."),indent=2))

if __name__=='__main__':
    main()
