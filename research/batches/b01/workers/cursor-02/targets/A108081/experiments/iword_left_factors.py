#!/usr/bin/env python3
"""Shortest-left factorization of right-irreducible Xia words.

Hypothesis: I-words of length >= 2 have unique shortest left parse w = L(u) ++ v
with v right-irreducible and u a unique-zero Xia word that either starts with 0
(RightWord) or ends with 0 (LeftWord). Together with |Right_n|=|Left_n|=C_{n-1}
this would give the generating function of A081696.
"""
from __future__ import annotations

from collections import Counter, defaultdict
from math import comb

Word = tuple[int, ...]


def L(w: Word) -> Word:
    return tuple(x - 1 for x in reversed(w))


def R(w: Word) -> Word:
    return tuple(x + 1 for x in reversed(w))


def rho(w: Word) -> Word:
    return tuple(-x for x in reversed(w))


def catalan(n: int) -> int:
    return comb(2 * n, n) // (n + 1)


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


def parses(
    w: Word, by_len: dict[int, set[Word]]
) -> tuple[list[tuple[Word, Word]], list[tuple[Word, Word]]]:
    left: list[tuple[Word, Word]] = []
    right: list[tuple[Word, Word]] = []
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


def shortest_left(w: Word, by_len: dict[int, set[Word]]) -> tuple[Word, Word] | None:
    lp, _ = parses(w, by_len)
    if not lp:
        return None
    m = min(len(u) for u, _ in lp)
    hits = [(u, v) for u, v in lp if len(u) == m]
    assert len(hits) == 1, (w, hits)
    return hits[0]


def is_pword(w: Word) -> bool:
    return w.count(0) == 1


def main() -> None:
    max_n = 8
    words = enumerate_x(max_n)
    by_len = words
    I: dict[int, set[Word]] = {}
    J: dict[int, set[Word]] = {}
    P: dict[int, set[Word]] = {}
    Right: dict[int, set[Word]] = {}
    Left: dict[int, set[Word]] = {}
    for n in range(1, max_n + 1):
        I[n] = {w for w in words[n] if not parses(w, by_len)[1]}
        J[n] = {w for w in words[n] if not parses(w, by_len)[0]}
        P[n] = {w for w in words[n] if is_pword(w)}
        Right[n] = {w for w in P[n] if w[0] == 0}
        Left[n] = {w for w in P[n] if w[-1] == 0}
        Qn = Left[n] | Right[n]
        print(
            f"n={n}: |X|={len(words[n])} |I|={len(I[n])} |J|={len(J[n])} "
            f"|P|={len(P[n])} C_n={catalan(n)} |Right|={len(Right[n])} "
            f"C_{n-1}={catalan(n-1)} |Left|={len(Left[n])} |Q|=|{len(Qn)} "
            f"Left&Right={len(Left[n] & Right[n])}"
        )

    print("\n=== shortest left factor of I-words ===")
    for n in range(2, max_n + 1):
        classes = Counter()
        not_q = []
        rem_not_I = 0
        for w in sorted(I[n]):
            hit = shortest_left(w, by_len)
            assert hit is not None, w
            u, v = hit
            in_L = u in Left[len(u)]
            in_R = u in Right[len(u)]
            in_P = u in P[len(u)]
            in_I = u in I[len(u)]
            in_J = u in J[len(u)]
            key = (
                f"len{len(u)}"
                f"{'L' if in_L else ''}"
                f"{'R' if in_R else ''}"
                f"{'P' if in_P else ''}"
                f"{'I' if in_I else ''}"
                f"{'J' if in_J else ''}"
                f" head{u[0]} last{u[-1]}"
            )
            classes[key] += 1
            if not (in_L or in_R):
                not_q.append((w, u, v))
            if v not in I[len(v)]:
                rem_not_I += 1
        print(f" n={n}: remainder-not-I={rem_not_I} not-Q={len(not_q)}")
        for k, c in sorted(classes.items()):
            print(f"    {k}: {c}")
        if not_q[:5]:
            print("    examples not Q:", not_q[:5])

    print("\n=== is L(u)++v always I for u in Q, v in I? ===")
    for n in range(2, max_n + 1):
        good = 0
        bad = []
        seen = set()
        for k in range(1, n):
            for u in Left[k] | Right[k]:
                for v in I[n - k]:
                    w = L(u) + v
                    is_x = w in words[n]
                    is_i = w in I[n]
                    good += int(is_i)
                    seen.add(w)
                    if not is_i:
                        bad.append((u, v, w, is_x))
        print(
            f" n={n}: pairs={sum(len(Left[k]|Right[k])*len(I[n-k]) for k in range(1,n))}"
            f" image-in-I={good} unique-image={len(seen)} |I|={len(I[n])}"
            f" bad={len(bad)}"
        )
        if bad[:6]:
            print("    bad examples:", bad[:6])

    print("\n=== greedy left peels of I down to [0] ===")
    for n in range(1, max_n + 1):
        factor_types = Counter()
        for w in I[n]:
            cur = w
            factors = []
            while len(cur) >= 2:
                hit = shortest_left(cur, by_len)
                assert hit is not None
                u, v = hit
                kind = (
                    "L" if u in Left[len(u)] else
                    "R" if u in Right[len(u)] else
                    "P" if u in P[len(u)] else
                    "?"
                )
                factors.append((kind, len(u), u[0], u[-1]))
                cur = v
            assert cur == (0,)
            factor_types[tuple(k for k, _, _, _ in factors)] += 1
        print(f" n={n}: peel-type { {k: c for k, c in factor_types.items()} }")

    print("\n=== I-words listed n<=5 ===")
    for n in range(1, 6):
        for w in sorted(I[n]):
            hit = shortest_left(w, by_len) if n > 1 else None
            print(f"  I_{n} {w} zeros={[i for i,x in enumerate(w) if x==0]} sl={hit}")


if __name__ == "__main__":
    main()
