#!/usr/bin/env python3
"""RightWord first-return obstruction for A108081.

Not a proof. Records that a start-with-0 unique-zero Xia word of length at
least 2 is last-1 with penultimate >= 2 exactly when its shortest right
remainder has length at least 2. For the first-factor-[0] case,
L([0] ++ R(v)) ++ [0] = v ++ [-1, 0] has a right parse whenever |v| >= 2.
That case is now a theorem. The remaining RightWord gap is |u| >= 2 with
bad remainder v.
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


def right_parses(w, by_len):
    n = len(w)
    out = []
    for i in range(1, n):
        pre, suf = w[:i], w[i:]
        v = L(suf)
        if pre in by_len[i] and v in by_len[n - i]:
            out.append((pre, v, i))
    return out


def main() -> None:
    max_n = 7
    words = enumerate_x(max_n)
    miss_char = 0
    miss_parse = 0
    for k in range(2, max_n):
        for p in sorted(w for w in words[k] if w[0] == 0 and w.count(0) == 1):
            rp = right_parses(p, words)
            if not rp:
                print("no parse", p)
                continue
            i = min(t[2] for t in rp)
            u, v, _ = [t for t in rp if t[2] == i][0]
            bad = p[-2] >= 2
            rem_long = len(v) >= 2
            if bad != rem_long:
                miss_char += 1
                print("char mismatch", p, "u", u, "v", v, "bad", bad)
            if u == (0,) and rem_long:
                w = L(p) + (0,)
                if not right_parses(w, words):
                    miss_parse += 1
                    print("no parse of L(p)++[0]", p, w)
    print("char_fail", miss_char, "cons0_no_parse", miss_parse)


if __name__ == "__main__":
    main()
