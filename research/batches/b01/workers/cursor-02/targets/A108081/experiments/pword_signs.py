#!/usr/bin/env python3
"""Sign pattern around the unique zero of P-words (one-zero Xia words)."""
from math import comb

Word = tuple[int, ...]


def L(w: Word) -> Word:
    return tuple(x - 1 for x in reversed(w))


def R(w: Word) -> Word:
    return tuple(x + 1 for x in reversed(w))


def enumerate_x(max_n: int) -> dict[int, set[Word]]:
    words = {1: {(0,)}}
    for n in range(2, max_n + 1):
        nxt = set()
        for i in range(1, n):
            for u in words[i]:
                for v in words[n - i]:
                    nxt.add(L(u) + v)
                    nxt.add(u + R(v))
        words[n] = nxt
    return words


def main() -> None:
    max_n = 7
    words = enumerate_x(max_n)
    print("=== one-zero Xia words: sign around 0 vs Catalan ===")
    for n in range(1, max_n + 1):
        one = [w for w in words[n] if w.count(0) == 1]
        bad = []
        for w in one:
            i = w.index(0)
            left = w[:i]
            right = w[i + 1 :]
            if any(x >= 0 for x in left) or any(x <= 0 for x in right):
                bad.append(w)
        print(
            f" n={n}: one-zero={len(one)} C_n={comb(2*n, n)//(n+1)} "
            f"bad_sign={len(bad)} e.g. {bad[:3]}"
        )
        # also two-zero cannot be P first peels already known

    print("=== Xia words with no -1 (for right-extension of P) ===")
    for n in range(1, max_n):
        noneg = [w for w in words[n] if -1 not in w]
        print(f" n={n}: no_-1 {len(noneg)} first { {w[0] for w in noneg} }")


if __name__ == "__main__":
    main()
