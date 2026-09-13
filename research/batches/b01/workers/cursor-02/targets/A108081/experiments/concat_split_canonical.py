#!/usr/bin/env python3
"""Canonical concat-split positions for multi-zero Xia words."""
from collections import Counter

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


def is_x(w, words):
    return w in words.get(len(w), set())


def main() -> None:
    max_n = 7
    words = enumerate_x(max_n)

    print("=== last-0 split (drop starts at last 0) ===")
    for n in range(2, max_n + 1):
        ok = fail = skip = 0
        fails = []
        for w in words[n]:
            if w.count(0) < 2:
                continue
            m = max(i for i, x in enumerate(w) if x == 0)
            if m == 0:
                skip += 1
                continue
            take, drop = w[:m], w[m:]
            if is_x(take, words) and is_x(drop, words):
                ok += 1
            else:
                fail += 1
                if len(fails) < 3:
                    fails.append((w, m, take, drop, is_x(take, words), is_x(drop, words)))
        print(f" n={n}: ok={ok} fail={fail} skip={skip} e.g.={fails[:2]}")

    print("=== first 0 as end of take (m = idxOf 0 + 1) ===")
    for n in range(2, max_n + 1):
        ok = fail = 0
        fails = []
        for w in words[n]:
            if w.count(0) < 2:
                continue
            m = w.index(0) + 1
            if m >= n:
                fail += 1
                continue
            take, drop = w[:m], w[m:]
            if is_x(take, words) and is_x(drop, words):
                ok += 1
            else:
                fail += 1
                if len(fails) < 2:
                    fails.append((w, take, drop, is_x(take, words), is_x(drop, words)))
        print(f" n={n}: ok={ok} fail={fail} e.g.={fails[:1]}")

    print("=== any left parse of v when v.head=0 and -1 in v? ===")
    # for Xia v start 0 with -1: left parses / right parses
    for n in range(2, max_n + 1):
        nL = nR = nBoth = nNone = 0
        none = []
        for v in words[n]:
            if v[0] != 0 or -1 not in v:
                continue
            lefts = rights = 0
            for i in range(1, n):
                pre, suf = v[:i], v[i:]
                if R(pre) in words[i] and suf in words[n - i]:
                    lefts += 1
                if pre in words[i] and L(suf) in words[n - i]:
                    rights += 1
            if lefts and rights:
                nBoth += 1
            elif lefts:
                nL += 1
            elif rights:
                nR += 1
            else:
                nNone += 1
                none.append(v)
        print(
            f" n={n}: start0_has_-1 left_only={nL} right_only={nR} both={nBoth} "
            f"none={nNone} e.g.none={none[:4]}"
        )

    print("=== if v has a left parse, u ++ R(v) concat-splits as (u++R(b)) ++ a ===")
    for n in range(2, max_n + 1):
        ok = fail = nlp = 0
        for i in range(1, n):
            for u in words[i]:
                if u.count(0) != 1:
                    continue
                for v in words[n - i]:
                    if -1 not in v:
                        continue
                    lefts = []
                    for j in range(1, len(v)):
                        pre, suf = v[:j], v[j:]
                        a = R(pre)
                        if a in words[j] and suf in words[len(v) - j]:
                            lefts.append((a, suf))
                    if not lefts:
                        nlp += 1
                        continue
                    a, b = lefts[0]
                    left = u + R(b)
                    if is_x(left, words) and is_x(a, words) and left + a == u + R(v):
                        ok += 1
                    else:
                        fail += 1
        print(f" n={n}: has_leftparse ok={ok} fail={fail} no_left_parse={nlp}")


if __name__ == "__main__":
    main()
