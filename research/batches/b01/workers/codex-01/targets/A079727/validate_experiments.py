#!/usr/bin/env python3
"""Validate the checked-in deterministic screens. This is not a mathematical proof.
Copyright 2026 Wentao Li. Apache-2.0. AI assistance: OpenAI Codex.
"""
import json
from pathlib import Path

root = Path(__file__).resolve().parent

def read(name):
    return [json.loads(s) for s in (root/name).read_text().splitlines()]

arithmetic = read('experiments.jsonl')
prime_cases = [r for r in arithmetic if 'c123_residuals' in r]
sets = [r for r in arithmetic if 'c4_set' in r]
blocks = [r['block'] for r in arithmetic if 'block' in r]
assert len(prime_cases) > 0 and prime_cases[-1]['p'] == 503
assert all(r['c123_residuals'] == [0,0,0] for r in prime_cases)
assert all(r['intended_residue'] == 0 for r in sets)
assert all(r['expansion_agrees'] for r in blocks)
assert all(r['S0_mod_p2'] == r['D_mod_p'] == r['M1_mod_p'] == 0 for r in blocks)
assert all((r['M2_mod_p']*r['E_mod_p'])%r['p'] == 1 for r in blocks)
polynomials = read('polynomial_screen.jsonl')
assert all(all(v for k,v in r.items() if k != 'p') for r in polynomials)
legendre = read('legendre_screen.jsonl')
roots = [r for p in legendre for r in p['hypergeometric_roots']]
ts = [r for p in legendre for r in p['legendre_roots']]
assert all(all(r[k] == 0 for k in ('F_half_square_residual_mod_p4',
                                  'Clausen_square_residual_mod_p4', 'comparison_mod_p4')) for r in roots)
assert all(r['P_high_plus_p_mod_p3'] == 0 for r in ts)
print(json.dumps({'result':'PASS', 'arithmetic_prime_cases':len(prime_cases),
                  'finite_set_pairs':len(sets),'block_expansions':len(blocks),
                  'polynomial_identity_primes':len(polynomials),
                  'hypergeometric_root_lifts':len(roots),'legendre_roots':len(ts)},indent=2))
