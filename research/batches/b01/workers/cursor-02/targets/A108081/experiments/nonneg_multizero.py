#!/usr/bin/env python3
"""Constructors of nonnegative Xia words with ≥2 zeros."""
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
    print("=== nonnegative multi-zero Xia: constructors ===")
    for n in range(2, max_n + 1):
        hard = []
        easy_neg1head = 0
        easy_u_multi = 0
        left = 0
        for w in words[n]:
            if -1 in w or w.count(0) < 2:
                continue
            rights = []
            lefts = []
            for i in range(1, n):
                pre, suf = w[:i], w[i:]
                if R(pre) in words[i] and suf in words[n - i]:
                    lefts.append((R(pre), suf))
                if pre in words[i] and L(suf) in words[n - i]:
                    rights.append((pre, L(suf)))
            if lefts:
                left += 1
            u_multi = any(pre.count(0) >= 2 for pre, _ in rights)
            hneg = any(vv[0] == -1 for _, vv in rights)
            h0_p = any(pre.count(0) == 1 and vv[0] == 0 and -1 in vv for pre, vv in rights)
            if u_multi:
                easy_u_multi += 1
            if hneg:
                easy_neg1head += 1
            if h0_p:
                hard.append((w, rights, lefts))
        print(
            f" n={n}: left_ctor={left} u_multi={easy_u_multi} vhead-1={easy_neg1head} "
            f"PWord++R(head0_with-1)={len(hard)}"
        )
        for h in hard[:6]:
            print("  HARD", h[0], "rights", h[1], "lefts", h[2])


if __name__ == "__main__":
    main()
