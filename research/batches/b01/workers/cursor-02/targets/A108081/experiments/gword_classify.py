#!/usr/bin/env python3
"""Classify good P-factors of I-words: Left / Right / middle, and the bad remainder."""
from __future__ import annotations

from math import comb

Word = tuple[int, ...]


def L(w: Word) -> Word:
    return tuple(x - 1 for x in reversed(w))


def R(w: Word) -> Word:
    return tuple(x + 1 for x in reversed(w))


def catalan(n: int) -> int:
    return comb(2 * n, n) // (n + 1)


def q(k: int) -> int:
    return 1 if k == 1 else 2 * catalan(k - 1)


def enumerate_x(max_n: int) -> dict[int, set[Word]]:
    words: dict[int, set[Word]] = {1: {(0,)}}
    for n in range(2, max_n + 1):
        nxt: set[Word] = set()
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
    left, right = [], []
    n = len(w)
    for i in range(1, n):
        pre, suf = w[:i], w[i:]
        u = R(pre)
        if u in by_len[i] and suf in by_len[n - i]:
            left.append((u, suf))
        v = L(suf)
        if pre in by_len[i] and v in by_len[n - i]:
            right.append((pre, v))
    return left, right


def is_pword(w: Word) -> bool:
    return w.count(0) == 1


def main() -> None:
    max_n = 7
    words = enumerate_x(max_n)
    I, P, Left, Right = {}, {}, {}, {}
    for n in range(1, max_n + 1):
        I[n] = {w for w in words[n] if not parses(w, words)[1]}
        P[n] = {w for w in words[n] if is_pword(w)}
        Right[n] = {w for w in P[n] if w[0] == 0}
        Left[n] = {w for w in P[n] if w[-1] == 0}

    print("=== G_k from L(p)++[0] I, vs L(p)++v I for all v ===")
    for k in range(1, max_n):
        G0 = {p for p in P[k] if L(p) + (0,) in I[k + 1]}
        Gall = {p for p in P[k] if all(L(p) + v in I[k + len(v)] for v in I[1])}
        # stronger: all remainders through max_n-k
        Gall2 = set(P[k])
        for n in range(k + 1, max_n + 1):
            Gall2 &= {p for p in P[k] if all(L(p) + v in I[n] for v in I[n - k])}
        print(
            f"k={k} |P|={len(P[k])} q={q(k)} |G0|={len(G0)} |Gall_v=[0]|={len(Gall)} |Gall_all|={len(Gall2)}"
        )
        extra = sorted(G0 - Left[k])
        missing_left = sorted(Left[k] - G0)
        bad = sorted(P[k] - G0)
        print(f"  extra_not_Left={extra}")
        print(f"  missing_Left={missing_left}")
        print(f"  bad={bad}")
        kinds = []
        for p in extra:
            kind = "R" if p in Right[k] else "M"
            kinds.append((kind, p))
        print(f"  extra kinds={kinds}")
        bad_kinds = []
        for p in bad:
            kind = "L" if p in Left[k] else "R" if p in Right[k] else "M"
            bad_kinds.append((kind, p))
        print(f"  bad kinds={bad_kinds}")


if __name__ == "__main__":
    main()
