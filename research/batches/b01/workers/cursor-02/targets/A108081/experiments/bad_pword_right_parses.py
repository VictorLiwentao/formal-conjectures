#!/usr/bin/env python3
"""Shortest right-parse left factor of L(p)++[0] for last=1 penultimate≥2 PWords.

Not a proof. Records that every such p makes L(p)++[0] Xia with a right parse,
and that the length-1 parse is exactly q = (-1) :: map(lambda x: x-2, dropLast p)
when that q is Xia.
"""
from __future__ import annotations


def L(w):
    return tuple(x - 1 for x in reversed(w))


def R(w):
    return tuple(x + 1 for x in reversed(w))


def enumerate_x(max_n):
    words = {1: {(0,)}}
    for n in range(2, max_n + 1):
        nxt = set()
        for i in range(1, n):
            j = n - i
            for u in words[i]:
                lu = L(u)
                for v in words[j]:
                    nxt.add(lu + v)
            for u in words[i]:
                for v in words[j]:
                    nxt.add(u + R(v))
        words[n] = nxt
    return words


def parses(w, by_len):
    right = []
    n = len(w)
    for i in range(1, n):
        pre, suf = w[:i], w[i:]
        v = L(suf)
        if pre in by_len[i] and v in by_len[n - i]:
            right.append((pre, v, i))
    return right


def q_formula(p):
    return (-1,) + tuple(x - 2 for x in p[:-1])


def main() -> None:
    max_n = 7
    words = enumerate_x(max_n)
    P = {n: {w for w in words[n] if w.count(0) == 1} for n in range(1, max_n)}
    miss = 0
    formula_ok = 0
    formula_fail = 0
    for k in range(3, max_n):
        for p in sorted(P[k]):
            if not (p[-1] == 1 and p[-2] >= 2):
                continue
            w = L(p) + (0,)
            rp = parses(w, words)
            if not rp:
                miss += 1
                print("NO RIGHT PARSE", p, w)
                continue
            i = min(t[2] for t in rp)
            qf = q_formula(p)
            has1 = any(t[2] == 1 for t in rp)
            if has1:
                formula_ok += 1
                q1 = [t[1] for t in rp if t[2] == 1][0]
                if q1 != qf:
                    print("formula mismatch", p, q1, qf)
            else:
                formula_fail += 1
            if k <= 4:
                print(k, p, "shortest_i", i, "formula_xia", qf in words[len(qf)])
    print("no_parse", miss, "len1_ok", formula_ok, "len1_fail", formula_fail)


if __name__ == "__main__":
    main()
