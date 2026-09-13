#!/usr/bin/env python3
"""Concat splits of u ++ R(v) when v is start-0, has -1, and has no left parse."""
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
    out = []
    for i in range(1, n):
        pre, suf = w[:i], w[i:]
        if R(pre) in words[i] and suf in words[n - i]:
            out.append((R(pre), suf))
    return out


def concat_splits(w, words):
    n = len(w)
    return [m for m in range(1, n) if w[:m] in words[m] and w[m:] in words[n - m]]


def main() -> None:
    max_n = 7
    words = enumerate_x(max_n)
    P = {n: {w for w in words[n] if w.count(0) == 1} for n in range(1, max_n + 1)}
    hard_v = []
    for n in range(1, max_n + 1):
        for v in words[n]:
            if v[0] == 0 and -1 in v and not left_parses(v, words):
                hard_v.append(v)

    print(f"hard |v| count={len(hard_v)}")
    print("=== u PWord ++ R(hard v): splits ===")
    shown = 0
    all_ok = True
    for u_n in range(1, 4):
        for u in sorted(P[u_n]):
            for v in hard_v:
                if len(u) + len(v) > max_n:
                    continue
                w = u + R(v)
                n = len(w)
                if w not in words[n]:
                    print("not xia", w)
                    continue
                splits = concat_splits(w, words)
                if not splits:
                    all_ok = False
                    print("NO SPLIT", u, v, w)
                elif shown < 20:
                    print(f" u={u} v={v} w={w} splits={[(m, w[:m], w[m:]) for m in splits]}")
                    shown += 1
    print("all_have_split", all_ok)

    print("=== is there always a split with drop = R(c) for some left factor c of v? ===")
    # From left parse of SOME prefix?
    # Try: v = c ++ r(d) right parse of v; then maybe another construction


if __name__ == "__main__":
    main()
