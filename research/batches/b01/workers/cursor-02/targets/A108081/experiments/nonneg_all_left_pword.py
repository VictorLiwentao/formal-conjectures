#!/usr/bin/env python3
"""Nonnegative multi-zero words whose every right-parse left factor is a PWord."""
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


def main() -> None:
    max_n = 7
    words = enumerate_x(max_n)
    for n in range(2, max_n + 1):
        found = []
        for w in words[n]:
            if -1 in w or w.count(0) < 2:
                continue
            rights = []
            for i in range(1, n):
                pre, suf = w[:i], w[i:]
                if pre in words[i] and L(suf) in words[n - i]:
                    rights.append((pre, L(suf)))
            if not rights:
                found.append(("noparse", w))
                continue
            if all(pre.count(0) == 1 for pre, _ in rights):
                found.append((w, rights))
        print(f" n={n}: all_left_PWord count={len(found)}")
        for f in found[:8]:
            print("  ", f)


if __name__ == "__main__":
    main()
