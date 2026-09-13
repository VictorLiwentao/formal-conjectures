#!/usr/bin/env python3
"""Check finite-field polynomial identities underlying a possible C1/C2 proof.
Unverified computational research, not Lean evidence.
Copyright 2026 Wentao Li. Apache-2.0. AI assistance: OpenAI Codex.
"""
from math import comb
from experiments import primes_upto
import json


def screen(p):
    h=(p-1)//2
    def add(*fs):
        z=[0]*max(map(len,fs))
        for f in fs:
            for i,c in enumerate(f):z[i]=(z[i]+c)%p
        return z
    def scale(c,f):return [c*x%p for x in f]
    def mul(f,g):
        z=[0]*(len(f)+len(g)-1)
        for i,a in enumerate(f):
            for j,b in enumerate(g):z[i+j]=(z[i+j]+a*b)%p
        return z
    def theta(f):return [i*a%p for i,a in enumerate(f)]
    def eq(f,g):return all(x%p==0 for x in add(f,scale(-1,g)))
    def B(y,z):
        return add(mul([1,-1],add(mul(y,theta(theta(z))),mul(z,theta(theta(y))),scale(-1,mul(theta(y),theta(z))))),
                   scale(-pow(2,-1,p),mul([0,1],add(mul(y,theta(z)),mul(z,theta(y))))),
                   scale(-pow(4,-1,p),mul([0,1],mul(y,z))))
    hs=[0]; h2=[0]
    for i in range(1,p):
        inv=pow(i,-1,p);hs.append((hs[-1]+inv)%p);h2.append((h2[-1]+inv*inv)%p)
    f0=[];f1=[];f2=[]
    for j in range(h+1):
        c=pow(comb(2*j,j),3,p)*pow(pow(64,j,p),-1,p)%p
        d=(hs[2*j]-hs[j])%p
        e=(18*d*d-6*h2[2*j]+3*h2[j])%p
        f0.append(c);f1.append(6*d*c%p);f2.append(e*c%p)
    b00=B(f0,f0)
    b01=add(B(f0,f1),mul([1,-1],mul(f0,theta(f0))),scale(-pow(2,-1,p),mul([0,1],mul(f0,f0))))
    b02=add(B(f0,f2),mul([1,-1],add(scale(2,mul(f0,theta(f1))),scale(-1,mul(f1,theta(f0))),mul(f0,f0))),
            scale(-pow(2,-1,p),mul([0,1],mul(f0,f1))))
    expected=[1]+[0]*(p-1)+[-1]
    vals=[eq(b00,[0]),eq(b01,[0]),eq(b02,expected)]
    return {'p':p,'B00_zero':vals[0],'B01_corrected_zero':vals[1], 'B02_corrected_eq_one_minus_Xp':vals[2]}

if __name__=='__main__':
    for p in primes_upto(199):
        if p>=5:
            r=screen(p)
            print(json.dumps(r))
            assert all(v for k,v in r.items() if k!='p')
