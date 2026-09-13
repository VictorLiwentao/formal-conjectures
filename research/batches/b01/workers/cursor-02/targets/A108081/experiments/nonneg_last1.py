#!/usr/bin/env python3
"""Nonnegative multi-zero, last=1, dropLast not Xia, all right-left-factors PWords?"""
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
        c = {
            "last1": 0,
            "last1_initX": 0,
            "last1_initNot": 0,
            "last1_initNot_allP": 0,
            "last0": 0,
            "last0_vhead-1": 0,
        }
        examples = []
        for w in words[n]:
            if -1 in w or w.count(0) < 2:
                continue
            if w[-1] == 0:
                c["last0"] += 1
                continue
            c["last1"] += 1
            init = w[:-1]
            if init in words[n - 1]:
                c["last1_initX"] += 1
            else:
                c["last1_initNot"] += 1
                rights = []
                for i in range(1, n):
                    pre, suf = w[:i], w[i:]
                    if pre in words[i] and L(suf) in words[n - i]:
                        rights.append((pre, L(suf)))
                if all(pre.count(0) == 1 for pre, _ in rights):
                    c["last1_initNot_allP"] += 1
                    examples.append((w, rights))
        print(f" n={n}: {c} e.g.={examples[:4]}")


if __name__ == "__main__":
    main()
