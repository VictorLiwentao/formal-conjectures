#!/usr/bin/env python3
"""List start-0 Xia words that contain -1 and have no left parse."""
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


def parses(w, words):
    n = len(w)
    lefts, rights = [], []
    for i in range(1, n):
        pre, suf = w[:i], w[i:]
        if R(pre) in words[i] and suf in words[n - i]:
            lefts.append((R(pre), suf))
        if pre in words[i] and L(suf) in words[n - i]:
            rights.append((pre, L(suf)))
    return lefts, rights


def main() -> None:
    max_n = 7
    words = enumerate_x(max_n)
    print("=== start-0 with -1, no left parse ===")
    for n in range(1, max_n + 1):
        for v in sorted(words[n]):
            if v[0] != 0 or -1 not in v:
                continue
            lefts, rights = parses(v, words)
            if not lefts:
                print(
                    f" n={n} v={v} rights={rights} zeros={v.count(0)} "
                    f"neg1={v.count(-1)}"
                )


if __name__ == "__main__":
    main()
