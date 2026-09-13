#!/usr/bin/env python3
"""Is the suffix after the last +1 of a Xia word ending in 0 always Xia?"""
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


def main() -> None:
    max_n = 8
    words = enumerate_x(max_n)
    fail = 0
    ok = 0
    skip = 0
    for n in range(1, max_n + 1):
        for u in words[n]:
            if u[-1] != 0 or 1 not in u:
                skip += 1
                continue
            j = max(i for i, x in enumerate(u) if x == 1)
            if j == n - 1:
                skip += 1
                continue
            b = u[j + 1 :]
            if b in words[len(b)]:
                ok += 1
            else:
                fail += 1
                if fail <= 10:
                    print("fail u", u, "last1", j, "b", b)
        print(f"n={n} ok={ok} fail={fail}")
    print("total", ok, fail)


if __name__ == "__main__":
    main()
