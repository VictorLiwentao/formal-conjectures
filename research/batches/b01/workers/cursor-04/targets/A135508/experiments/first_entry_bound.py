#!/usr/bin/env python3
"""Compare first_entry(q) to the McEachen-sufficient bounds q^2-1 and q(q+2)-1.

Also record how each prime first enters x (via a(n)+2) and whether that
index is a prime ≡ 2 (mod 3). Experimental only; not a proof.
"""

from __future__ import annotations

import json
from collections import Counter
from pathlib import Path

from scan_structure import factor_small, gcd_from_fac, is_prime, sieve_primes


def run(max_n: int) -> dict:
    primes = sieve_primes(max_n + 5)
    xfac: Counter[int] = Counter()
    first_entry: dict[int, int] = {}
    entry_via: dict[int, tuple[int, int, int]] = {}
    a_vals: dict[int, int] = {}

    for n in range(1, max_n):
        g = gcd_from_fac(n + 1, xfac, primes)
        an = (n + 1) // g
        a_vals[n] = an
        inc = 2 + an
        inc_fac = factor_small(inc, primes)
        for p, e in inc_fac.items():
            if p not in first_entry:
                first_entry[p] = n + 1
                entry_via[p] = (n, an, inc)
            xfac[p] += e

    bound_fail_sq: list[dict] = []
    bound_fail_qq2: list[dict] = []
    rows: list[dict] = []
    for q in primes:
        if q > 4000:
            break
        n0 = first_entry.get(q)
        if n0 is None:
            continue
        via_n, an, inc = entry_via[q]
        row = {
            "q": q,
            "q_mod3": q % 3,
            "first_entry": n0,
            "q2_minus_1": q * q - 1,
            "q_qplus2_minus_1": q * q + 2 * q - 1,
            "le_q2": n0 <= q * q - 1,
            "le_qq2": n0 <= q * q + 2 * q - 1,
            "ratio_n_over_q": n0 / q,
            "via_n": via_n,
            "via_a": an,
            "via_inc": inc,
            "via_n_prime": is_prime(via_n + 1) if False else is_prime(via_n + 1),
            "via_index_is_prime": is_prime(n0),
            "via_prime_mod3": (n0 % 3) if is_prime(n0) else None,
            "a_of_q_minus_1": a_vals.get(q - 1),
        }
        rows.append(row)
        if not row["le_q2"]:
            bound_fail_sq.append(row)
        if not row["le_qq2"]:
            bound_fail_qq2.append(row)

    # McEachen remaining-class after 3,5,7 cascade
    remaining = []
    failures = []
    for p in primes:
        if p > max_n:
            break
        if is_prime(p - 2):
            continue
        got = a_vals.get(p - 1)
        if got != p:
            failures.append({"p": p, "a": got})
        if p >= 5 and p % 3 == 1 and (p - 2) % 5 != 0 and (p - 2) % 7 != 0:
            fac = factor_small(p - 2, primes)
            q = min(fac)
            n0 = first_entry.get(q)
            remaining.append(
                {
                    "p": p,
                    "p-2": p - 2,
                    "min_fac": q,
                    "first_entry_q": n0,
                    "need_le": p - 3,
                    "ok": n0 is not None and n0 <= p - 3,
                    "entry_via": entry_via.get(q),
                    "slack": None if n0 is None else (p - 3) - n0,
                }
            )

    worst_ratio = sorted(rows, key=lambda r: r["ratio_n_over_q"], reverse=True)[:20]
    worst_slack = sorted(
        [r for r in remaining if r["ok"]], key=lambda r: r["slack"]
    )[:15]

    return {
        "max_n": max_n,
        "bound_fail_q2": bound_fail_sq,
        "bound_fail_qq2": bound_fail_qq2,
        "worst_ratio": worst_ratio,
        "mceachen_failures": failures,
        "remaining_count": len(remaining),
        "remaining_miss": [r for r in remaining if not r["ok"]],
        "tightest_remaining_slack": worst_slack,
        "sample_first_entries": rows[:25],
    }


def main() -> None:
    out = run(50000)
    print("McEachen failures", out["mceachen_failures"])
    print("fail q^2-1", [(r["q"], r["first_entry"], r["q2_minus_1"]) for r in out["bound_fail_q2"]])
    print("fail q(q+2)-1", [(r["q"], r["first_entry"], r["q_qplus2_minus_1"]) for r in out["bound_fail_qq2"]])
    print("worst first/q:")
    for r in out["worst_ratio"][:12]:
        print(r)
    print("remaining", out["remaining_count"], "miss", out["remaining_miss"])
    print("tightest slack remaining:")
    for r in out["tightest_remaining_slack"][:10]:
        print(r)
    dest = Path(__file__).with_name("first_entry_bound.json")
    dest.write_text(json.dumps({k: out[k] for k in out if k != "sample_first_entries"}, indent=2)[:200000])
    print("wrote", dest)


if __name__ == "__main__":
    main()
