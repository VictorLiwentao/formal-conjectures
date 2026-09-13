#!/usr/bin/env python3
"""Is the prefix through the first 0 of a Xia word always a LeftWord?"""
from __future__ import annotations

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


def is_pword(w):
    return w.count(0) == 1


def main() -> None:
    max_n = 8
    words = enumerate_x(max_n)
    fail = 0
    ok = 0
    for n in range(1, max_n + 1):
        for w in words[n]:
            j = w.index(0)
            pre = w[: j + 1]
            good = is_pword(pre) and pre[-1] == 0 and pre in words[len(pre)]
            if good:
                ok += 1
            else:
                fail += 1
                if fail < 8:
                    print("fail", w, "pre", pre, "inX", pre in words.get(len(pre), set()))
        print(f"n={n} ok_so_far={ok} fail={fail}")
    print("total", ok, fail)


if __name__ == "__main__":
    main()
