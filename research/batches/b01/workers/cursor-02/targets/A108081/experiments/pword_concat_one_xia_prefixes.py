#!/usr/bin/env python3
"""Classify Xia prefixes of 0::L(s) and right-parse candidates of L(s++[1])++[0]."""
from __future__ import annotations

from collections import defaultdict

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


def main() -> None:
    max_n = 8
    words = enumerate_x(max_n)
    P = {}
    I = {}
    for n in range(1, max_n + 1):
        P[n] = {w for w in words[n] if w.count(0) == 1}
        I[n] = {w for w in words[n] if not parses(w, words)[1]}

    print("Xia words starting 00:")
    for n in range(2, max_n + 1):
        zs = sorted(w for w in words[n] if w[:2] == (0, 0))
        print(f"  n={n} count={len(zs)}")
        if n <= 6:
            for w in zs:
                lp, rp = parses(w, words)
                print(f"    {w} left={lp} right={rp} I={w in I[n]}")

    xia_pref = 0
    right_cand = 0
    for k in range(1, max_n - 1):
        for s in P[k]:
            if s[-1] != 1:
                continue
            core = (0,) + L(s)
            w = core + (0,)
            n = len(w)
            if n > max_n:
                continue
            for i in range(1, n):
                pre, suf = w[:i], w[i:]
                if pre in words[i]:
                    xia_pref += 1
                    q = L(suf)
                    qxia = q in words[len(q)]
                    if qxia:
                        right_cand += 1
                        print("RIGHT PARSE", "s", s, "w", w, "pre", pre, "q", q)
                    elif suf[0] in (1, 2) and pre[-1] in (0, 1):
                        print(
                            "xia pre, rem head 1|2, q not xia",
                            "s", s, "pre", pre, "suf", suf, "q", q,
                        )
            # prefixes of core (not including final 0)
            for i in range(3, len(core) + 1):
                pre = core[:i]
                if pre[-1] not in (0, 1):
                    continue
                if pre in words[i]:
                    print("XIA CORE PREFIX", "s", s, "core", core, "pre", pre)

    print("xia_pref_of_full_w", xia_pref)
    print("actual_right_parses", right_cand)
    print(
        "all L(s++[1])++[0] in I?",
        all(
            L(s + (1,)) + (0,) in I[k + 2]
            for k in range(1, max_n - 1)
            for s in P[k]
            if k + 2 <= max_n
        ),
    )

    # How are 00-words constructed?
    print("00-word constructor stats:")
    for n in range(4, max_n + 1):
        for w in sorted(x for x in words[n] if x[:2] == (0, 0)):
            lefts = []
            rights = []
            for i in range(1, n):
                u, v = w[:i], w[i:]
                if u in words[i] and L(v) in words[n - i]:
                    # wait that's right parse
                    pass
                if R(u) in words[i] and v in words[n - i]:
                    lefts.append(i)
                if u in words[i] and L(v) in words[n - i]:
                    rights.append(i)
            print(f"  {w} left_lens={lefts} right_lens={rights}")


if __name__ == "__main__":
    main()
