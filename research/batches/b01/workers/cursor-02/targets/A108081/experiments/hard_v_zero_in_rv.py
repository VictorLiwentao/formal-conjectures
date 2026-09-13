#!/usr/bin/env python3
"""For hard v, is concat split of u++R(v) always at a 0 in r(v)?"""
Word = tuple[int, ...]


def L(w: Word) -> Word:
    return tuple(x - 1 for x in reversed(w))


def R(w: Word) -> Word:
    return tuple(x + 1 for x in reversed(w))


def enumerate_x(max_n: int) -> dict[int, set[Word]]:
    words: dict[int, set[Word]] = {1: {(0,)}}
    for n in range(2, max_n + 1):
        nxt: set[Word] = set()
        for i in range(1, n):
            for u in words[i]:
                lu = L(u)
                for v in words[n - i]:
                    nxt.add(lu + v)
                    nxt.add(u + R(v))
        words[n] = nxt
    return words


def left_parses(w, words):
    n = len(w)
    return [
        (R(w[:i]), w[i:])
        for i in range(1, n)
        if R(w[:i]) in words[i] and w[i:] in words[n - i]
    ]


def concat_splits(w, words):
    n = len(w)
    return [m for m in range(1, n) if w[:m] in words[m] and w[m:] in words[n - m]]


def main() -> None:
    max_n = 7
    words = enumerate_x(max_n)
    P = {n: {w for w in words[n] if w.count(0) == 1} for n in range(1, max_n + 1)}
    hard_v = [
        v
        for n in range(1, max_n + 1)
        for v in words[n]
        if v[0] == 0 and -1 in v and not left_parses(v, words)
    ]
    ok = fail = 0
    fails = []
    for un in range(1, max_n):
        for u in P[un]:
            for v in hard_v:
                if len(u) + len(v) > max_n:
                    continue
                w = u + R(v)
                n = len(w)
                if w not in words[n]:
                    continue
                rv = R(v)
                zeros = [j for j, x in enumerate(rv) if x == 0]
                hit = False
                hit_js = []
                for j in zeros:
                    m = len(u) + j
                    if 0 < m < n and w[:m] in words[m] and w[m:] in words[n - m]:
                        hit = True
                        hit_js.append(j)
                if hit:
                    ok += 1
                else:
                    fail += 1
                    fails.append((u, v, w, concat_splits(w, words), rv, zeros))
    print(f"ok={ok} fail={fail}")
    for f in fails[:8]:
        print(" fail", f)

    print("=== which -1 in v corresponds to a working 0 in r(v)? ===")
    from collections import Counter

    kinds = Counter()
    for un in range(1, 4):
        for u in P[un]:
            for v in hard_v:
                if len(u) + len(v) > max_n:
                    continue
                w = u + R(v)
                n = len(w)
                if w not in words[n]:
                    continue
                rv = R(v)
                for j, x in enumerate(rv):
                    if x != 0:
                        continue
                    m = len(u) + j
                    if 0 < m < n and w[:m] in words[m] and w[m:] in words[n - m]:
                        # corresponding index in v: |v|-1-j
                        iv = len(v) - 1 - j
                        kinds[
                            (
                                "first-1" if iv == v.index(-1) else "other-1",
                                "last-1"
                                if iv == len(v) - 1 - v[::-1].index(-1)
                                else "notlast",
                                v[iv],
                            )
                        ] += 1
    print(kinds)


if __name__ == "__main__":
    main()
