#!/usr/bin/env python3
"""Deterministic WOWII invariant search for cursor-07. Unverified until a Lean audit."""

from __future__ import annotations

import itertools
import math
import subprocess
import sys
from typing import Iterable

import networkx as nx

PY = sys.executable


def g6(G: nx.Graph) -> str:
    H = nx.convert_node_labels_to_integers(G)
    return nx.to_graph6_bytes(H, header=False).decode().strip()


def adj_bits(G: nx.Graph) -> list[int]:
    n = G.number_of_nodes()
    idx = {v: i for i, v in enumerate(G.nodes())}
    adj = [0] * n
    for u, v in G.edges():
        i, j = idx[u], idx[v]
        adj[i] |= 1 << j
        adj[j] |= 1 << i
    return adj


def distances(adj: list[int]) -> list[list[int]] | None:
    n = len(adj)
    dist = [[-1] * n for _ in range(n)]
    for s in range(n):
        dist[s][s] = 0
        q = [s]
        for u in q:
            nb = adj[u]
            d = dist[s][u]
            while nb:
                v = (nb & -nb).bit_length() - 1
                nb &= nb - 1
                if dist[s][v] < 0:
                    dist[s][v] = d + 1
                    q.append(v)
        if any(x < 0 for x in dist[s]):
            return None
    return dist


def is_bip_mask(adj: list[int], mask: int) -> bool:
    color = {}
    remaining = mask
    while remaining:
        s = (remaining & -remaining).bit_length() - 1
        color[s] = 0
        q = [s]
        remaining &= remaining - 1
        for u in q:
            nb = adj[u] & mask
            while nb:
                v = (nb & -nb).bit_length() - 1
                nb &= nb - 1
                if v not in color:
                    color[v] = color[u] ^ 1
                    remaining &= ~(1 << v)
                    q.append(v)
                elif color[v] == color[u]:
                    return False
    return True


def is_forest_mask(adj: list[int], mask: int) -> bool:
    nverts = mask.bit_count()
    if nverts == 0:
        return True
    edges = 0
    seen = 0
    remaining = mask
    while remaining:
        s = (remaining & -remaining).bit_length() - 1
        stack = [s]
        seen |= 1 << s
        remaining &= remaining - 1
        parent = {s: -1}
        while stack:
            u = stack.pop()
            nb = adj[u] & mask
            while nb:
                v = (nb & -nb).bit_length() - 1
                nb &= nb - 1
                if v == parent.get(u, -1):
                    continue
                edges += 1
                if (seen >> v) & 1:
                    return False
                seen |= 1 << v
                remaining &= ~(1 << v)
                parent[v] = u
                stack.append(v)
    return edges // 2 == nverts - (bin(seen).count("1") and mask.bit_count() == seen.bit_count() or True) and True


def is_forest_mask2(adj: list[int], mask: int) -> bool:
    nverts = mask.bit_count()
    if nverts == 0:
        return True
    nedges = 0
    m = mask
    while m:
        u = (m & -m).bit_length() - 1
        m &= m - 1
        nedges += (adj[u] & mask).bit_count()
    nedges //= 2
    components = 0
    seen = 0
    remaining = mask
    while remaining:
        s = (remaining & -remaining).bit_length() - 1
        components += 1
        stack = [s]
        seen |= 1 << s
        remaining &= remaining - 1
        while stack:
            u = stack.pop()
            nb = adj[u] & mask
            while nb:
                v = (nb & -nb).bit_length() - 1
                nb &= nb - 1
                if not ((seen >> v) & 1):
                    seen |= 1 << v
                    remaining &= ~(1 << v)
                    stack.append(v)
    return nedges == nverts - components


def max_induced_bipartite(adj: list[int]) -> int:
    n = len(adj)
    best = 1 if n else 0
    for k in range(n, 1, -1):
        for S in itertools.combinations(range(n), k):
            mask = 0
            for i in S:
                mask |= 1 << i
            if is_bip_mask(adj, mask):
                return k
    return best


def max_induced_forest(adj: list[int]) -> int:
    n = len(adj)
    for k in range(n, 0, -1):
        for S in itertools.combinations(range(n), k):
            mask = 0
            for i in S:
                mask |= 1 << i
            if is_forest_mask2(adj, mask):
                return k
    return 0


def indep_num_mask(adj: list[int], mask: int) -> int:
    verts = [i for i in range(len(adj)) if (mask >> i) & 1]
    best = 0
    m = len(verts)
    for k in range(m, -1, -1):
        for S in itertools.combinations(verts, k):
            ok = True
            for a in range(k):
                for b in range(a + 1, k):
                    if (adj[S[a]] >> S[b]) & 1:
                        ok = False
                        break
                if not ok:
                    break
            if ok:
                return k
    return 0


def max_l(adj: list[int]) -> int:
    n = len(adj)
    best = 0
    for v in range(n):
        best = max(best, indep_num_mask(adj, adj[v]))
    return best


def avg_l(adj: list[int]) -> float:
    n = len(adj)
    return sum(indep_num_mask(adj, adj[v]) for v in range(n)) / n


def residue_of_degrees(degs: list[int]) -> int:
    s = sorted(degs, reverse=True)
    while s:
        if s[0] == 0:
            return len(s)
        d, rest = s[0], s[1:]
        to_dec, remaining = rest[:d], rest[d:]
        s = sorted([x - 1 for x in to_dec] + remaining, reverse=True)
        if any(x < 0 for x in s):
            return -1
    return 0


def has_c4(adj: list[int]) -> bool:
    n = len(adj)
    for a in range(n):
        for b in range(n):
            if a == b or not ((adj[a] >> b) & 1):
                continue
            for c in range(n):
                if c in (a, b) or not ((adj[b] >> c) & 1):
                    continue
                for d in range(n):
                    if d in (a, b, c):
                        continue
                    if ((adj[c] >> d) & 1) and ((adj[d] >> a) & 1):
                        return True
    return False


def max_induced_path(adj: list[int]) -> int:
    n = len(adj)
    best = 1 if n else 0

    def ok_extend(path: list[int], used: int, v: int) -> bool:
        if (used >> v) & 1:
            return False
        last = path[-1]
        if not ((adj[last] >> v) & 1):
            return False
        for u in path[:-1]:
            if (adj[u] >> v) & 1:
                return False
        return True

    def dfs(path: list[int], used: int) -> None:
        nonlocal best
        best = max(best, len(path))
        if best == n:
            return
        nb = adj[path[-1]]
        while nb:
            v = (nb & -nb).bit_length() - 1
            nb &= nb - 1
            if ok_extend(path, used, v):
                path.append(v)
                dfs(path, used | (1 << v))
                path.pop()
                if best == n:
                    return

    for s in range(n):
        dfs([s], 1 << s)
        if best == n:
            break
    return best


def has_ham_path(adj: list[int]) -> bool:
    n = len(adj)
    if n <= 1:
        return True
    N = 1 << n
    ends = [0] * N
    for i in range(n):
        ends[1 << i] = 1 << i
    for mask in range(N):
        e = ends[mask]
        while e:
            bit = e & -e
            v = bit.bit_length() - 1
            e ^= bit
            nb = adj[v] & ~mask
            while nb:
                b2 = nb & -nb
                u = b2.bit_length() - 1
                nb ^= b2
                nmask = mask | b2
                ends[nmask] |= 1 << u
    return ends[N - 1] != 0


def path_cover_number(adj: list[int]) -> int:
    n = len(adj)
    N = 1 << n
    ends = [0] * N
    for i in range(n):
        ends[1 << i] = 1 << i
    for mask in range(N):
        e = ends[mask]
        while e:
            bit = e & -e
            v = bit.bit_length() - 1
            e ^= bit
            nb = adj[v] & ~mask
            while nb:
                b2 = nb & -nb
                u = b2.bit_length() - 1
                nb ^= b2
                ends[mask | b2] |= 1 << u
    can = [mask == 0 or ends[mask] != 0 for mask in range(N)]
    INF = 99
    pc = [INF] * N
    pc[0] = 0
    for mask in range(1, N):
        lsb = mask & -mask
        sub = mask
        best = INF
        while True:
            if (sub & lsb) and can[sub]:
                best = min(best, pc[mask ^ sub] + 1)
            sub = (sub - 1) & mask
            if sub == 0:
                break
        pc[mask] = best
    return pc[N - 1]


def degree_l2(adj: list[int], complement: bool = False) -> float:
    n = len(adj)
    s = 0.0
    full = (1 << n) - 1
    for v in range(n):
        d = adj[v].bit_count()
        if complement:
            d = (n - 1) - d
        s += d * d
    return math.sqrt(s)


def analyze(G: nx.Graph, want: set[str]) -> dict:
    if not nx.is_connected(G):
        return {"connected": False}
    adj = adj_bits(G)
    n = len(adj)
    dist = distances(adj)
    assert dist is not None
    ecc = [max(row) for row in dist]
    diam = max(ecc)
    rad = min(ecc)
    avg_ecc = sum(ecc) / n
    maxL = max_l(adj)
    out = {
        "connected": True,
        "n": n,
        "g6": g6(G),
        "diam": diam,
        "rad": rad,
        "avg_ecc": avg_ecc,
        "max_l": maxL,
        "self_centered": rad == diam,
    }
    if want & {"19", "16", "198a", "40"}:
        if n > 20:
            want = want - {"19", "16", "198a", "40"}
        else:
            out["b"] = max_induced_bipartite(adj)
    if want & {"40", "61"}:
        if n > 18:
            want = want - {"40", "61"}
        else:
            out["f"] = max_induced_forest(adj)
    if want & {"61"}:
        degs = [adj[v].bit_count() for v in range(n)]
        out["res"] = residue_of_degrees(degs)
        out["rhs61"] = out["res"] + math.ceil(diam / 3)
    if want & {"19"}:
        out["rhs19"] = math.floor(avg_ecc + maxL)
    if want & {"16"}:
        out["rhs16"] = 2 * (rad - 1) + maxL
        out["rhs13"] = diam + maxL - 1
    if want & {"40"}:
        if n > 12:
            want = want - {"40"}
        else:
            out["p"] = path_cover_number(adj)
            out["rhs40"] = math.ceil((out["p"] + out["b"] + 1) / 2)
    if want & {"100"}:
        alpha = indep_num_mask(adj, (1 << n) - 1)
        out["alpha"] = alpha
        lg = degree_l2(adj, False)
        lc = degree_l2(adj, True)
        out["lenG"] = lg
        out["lenGc"] = lc
        out["rhs100G"] = math.ceil((maxL + 0.5 * lg) / 2)
        out["rhs100Gc"] = math.ceil((maxL + 0.5 * lc) / 2)
    if want & {"133"}:
        out["path"] = max_induced_path(adj)
        out["avg_l"] = avg_l(adj)
        cC4 = 0 if has_c4(adj) else 1
        out["cC4"] = cC4
        fl = math.floor(out["avg_l"])
        out["rhs133"] = rad + (fl ** cC4)
    if want & {"198a"} and "b" in out:
        out["hyp198a"] = out["b"] <= 2 + avg_ecc
        if out["hyp198a"]:
            if n > 16:
                want = want - {"198a"}
            else:
                out["ham"] = has_ham_path(adj)
    return out


def violations(info: dict, want: set[str]) -> list[str]:
    if not info.get("connected"):
        return []
    v = []
    if "19" in want and "b" in info and "rhs19" in info and info["b"] < info["rhs19"]:
        v.append(f"19: b={info['b']} < {info['rhs19']}")
    if "16" in want and "b" in info and "rhs16" in info and info["b"] < info["rhs16"]:
        v.append(f"16: b={info['b']} < {info['rhs16']}")
    if "40" in want and "f" in info and "rhs40" in info and info["f"] < info["rhs40"]:
        v.append(f"40: f={info['f']} < {info['rhs40']}")
    if "61" in want and "f" in info and "rhs61" in info and info["f"] < info["rhs61"]:
        v.append(f"61: f={info['f']} < {info['rhs61']}")
    if "100" in want and "alpha" in info and info["alpha"] > info["rhs100Gc"]:
        v.append(f"100-Lean-Gc: a={info['alpha']} > {info['rhs100Gc']}")
    if "100" in want and "alpha" in info and info["alpha"] > info["rhs100G"]:
        v.append(f"100-HTML-G: a={info['alpha']} > {info['rhs100G']}")
    if "133" in want and "path" in info and info["path"] < info["rhs133"]:
        v.append(f"133: path={info['path']} < {info['rhs133']}")
    if "198a" in want and info.get("hyp198a") and "ham" in info and not info["ham"]:
        v.append(f"198a: b={info['b']} <= {2+info['avg_ecc']:.4f} no ham path")
    return v


def named_graphs() -> Iterable[tuple[str, nx.Graph]]:
    for fname in (
        "petersen_graph",
        "chvatal_graph",
        "tutte_graph",
        "heawood_graph",
        "pappus_graph",
        "desargues_graph",
        "dodecahedral_graph",
        "icosahedral_graph",
        "octahedral_graph",
        "cubical_graph",
        "sedgewick_maze_graph",
        "moebius_kantor_graph",
        "diamond_graph",
        "bull_graph",
        "krackhardt_kite_graph",
        "house_graph",
        "house_x_graph",
        "hoffman_singleton_graph",
        "florentine_families_graph",
        "davis_southern_women_graph",
    ):
        fn = getattr(nx, fname, None)
        if fn is None:
            continue
        try:
            yield fname, fn()
        except Exception:
            continue
    for n in range(3, 16):
        yield f"C{n}", nx.cycle_graph(n)
        yield f"P{n}", nx.path_graph(n)
        yield f"K{n}", nx.complete_graph(n)
        yield f"W{n}", nx.wheel_graph(n)
        yield f"star{n}", nx.star_graph(n - 1)
        if n >= 4:
            yield f"K{n}-e", nx.complete_graph(n)
    for n in range(3, 9):
        yield f"Q{n}", nx.hypercube_graph(n)
    for a, b in itertools.product(range(1, 8), repeat=2):
        yield f"K{a},{b}", nx.complete_bipartite_graph(a, b)
    for n in range(4, 12):
        G = nx.circular_ladder_graph(n)
        yield f"prism{n}", G
    for n in range(3, 10):
        yield f"grid2x{n}", nx.grid_2d_graph(2, n)
        yield f"grid3x{n}", nx.grid_2d_graph(3, n)
    for t in range(2, 7):
        yield f"C5[K{t}]", nx.lexicographic_product(nx.cycle_graph(5), nx.complete_graph(t))
    for n in range(5, 14):
        if n % 4 == 1:
            try:
                yield f"paley{n}", nx.paley_graph(n)
            except Exception:
                continue
    if hasattr(nx, "mycielski_graph"):
        for n in range(2, 6):
            yield f"mycielski{n}", nx.mycielski_graph(n)
    # split graphs / complete joins
    for a in range(1, 8):
        for r in range(2, 8):
            G = nx.complete_graph(r)
            G = nx.disjoint_union(G, nx.empty_graph(a))
            # connect all hubs (last a) to clique
            for h in range(r, r + a):
                for c in range(r):
                    G.add_edge(h, c)
            yield f"split_a{a}_K{r}", G
    for a in range(1, 6):
        for r in range(2, 6):
            for s in range(2, 6):
                G = nx.disjoint_union(nx.complete_graph(r), nx.complete_graph(s := s))
                G = nx.disjoint_union(G, nx.empty_graph(a))
                hubs = list(range(r + s, r + s + a))
                left = range(r)
                right = range(r, r + s)
                for h in hubs:
                    for v in list(left) + list(right):
                        G.add_edge(h, v)
                yield f"join_a{a}_Kr{r}_Ks{s}", G
    # two pendants on K_n
    for n in range(3, 12):
        G = nx.complete_graph(n)
        G.add_node(n)
        G.add_node(n + 1)
        G.add_edge(0, n)
        G.add_edge(0, n + 1)
        yield f"K{n}+2pend", G
    for n in range(3, 10):
        G = nx.complete_graph(n)
        G.add_node(n)
        G.add_node(n + 1)
        G.add_node(n + 2)
        G.add_edge(0, n)
        G.add_edge(0, n + 1)
        G.add_edge(0, n + 2)
        yield f"K{n}+3pend", G
    # C5 with pendants
    for k in range(1, 6):
        G = nx.cycle_graph(5)
        for i in range(k):
            G.add_node(5 + i)
            G.add_edge(0, 5 + i)
        yield f"C5+{k}pend", G
    # barbell
    for m in range(3, 7):
        for p in range(1, 5):
            yield f"barbell{m}_{p}", nx.barbell_graph(m, p)
    # lollipop
    for m in range(3, 8):
        for p in range(2, 6):
            yield f"lollipop{m}_{p}", nx.lollipop_graph(m, p)
    # windmill / friendship
    for k in range(2, 8):
        yield f"friendship{k}", nx.windmill_graph(k, 3) if hasattr(nx, "windmill_graph") else nx.complete_graph(3)
    # complete multipartite
    for parts in [(2, 2, 2), (3, 3, 3), (2, 2, 2, 2), (1, 2, 3), (2, 3, 4), (4, 4, 4), (5, 5, 2)]:
        yield f"K{parts}", nx.complete_multipartite_graph(*parts)
    # Kneser
    for n, k in [(5, 2), (6, 2), (7, 2), (7, 3)]:
        try:
            yield f"kneser{n}_{k}", nx.kneser_graph(n, k)
        except Exception:
            continue
    # odd graphs
    if hasattr(nx, "odd_graph"):
        for k in range(3, 6):
            yield f"odd{k}", nx.odd_graph(k)


def nauty_connected(n: int):
    proc = subprocess.Popen(
        ["nauty-geng", "-c", str(n)],
        stdout=subprocess.PIPE,
        stderr=subprocess.DEVNULL,
        text=True,
    )
    assert proc.stdout is not None
    for line in proc.stdout:
        yield nx.from_graph6_bytes(line.strip().encode())
    proc.wait()


def run_named(want: set[str]) -> None:
    print("=== named/construction search ===", flush=True)
    hits = 0
    for name, G in named_graphs():
        G = nx.Graph(G)
        G.remove_edges_from(nx.selfloop_edges(G))
        if G.number_of_nodes() < 2 or not nx.is_connected(G):
            continue
        if G.number_of_nodes() > 24:
            continue
        try:
            info = analyze(G, set(want))
            vs = violations(info, want)
        except Exception as e:
            print("ERR", name, type(e).__name__, e, flush=True)
            continue
        if vs:
            hits += 1
            print(name, g6(G), vs, {k: info[k] for k in info if k != "connected"}, flush=True)
    print(f"named hits={hits}", flush=True)


def has_c4_fast(adj: list[int]) -> bool:
    n = len(adj)
    for u in range(n):
        for v in range(u + 1, n):
            if (adj[u] & adj[v]).bit_count() >= 2:
                return True
    return False


def cheap_b_lower(adj: list[int], dist: list[list[int]], ecc: list[int], maxL: int, alpha: int) -> int:
    n = len(adj)
    diam = max(ecc)
    rad = min(ecc)
    return max(alpha, maxL + 1, diam + 1, 2 * rad, 1 if n else 0)


def run_nauty(n: int, want: set[str], self_centered_only_19: bool = False) -> None:
    print(f"=== nauty n={n} ===", flush=True)
    count = 0
    hits = 0
    for G in nauty_connected(n):
        count += 1
        adj = adj_bits(G)
        dist = distances(adj)
        if dist is None:
            continue
        ecc = [max(row) for row in dist]
        diam = max(ecc)
        rad = min(ecc)
        avg_ecc = sum(ecc) / n
        maxL = max_l(adj)
        alpha = indep_num_mask(adj, (1 << n) - 1)
        blow = cheap_b_lower(adj, dist, ecc, maxL, alpha)
        need = set()
        if "19" in want:
            rhs19 = math.floor(avg_ecc + maxL)
            if blow < rhs19:
                need.add("19")
        if "16" in want:
            rhs16 = 2 * (rad - 1) + maxL
            if blow < rhs16:
                need.add("16")
        if "61" in want:
            degs = [adj[v].bit_count() for v in range(n)]
            res = residue_of_degrees(degs)
            rhs61 = res + math.ceil(diam / 3)
            if max(alpha, diam + 1) < rhs61:
                need.add("61")
        if "40" in want and n <= 8:
            need.add("40")
        if "100" in want:
            lg = degree_l2(adj, False)
            lc = degree_l2(adj, True)
            rhsG = math.ceil((maxL + 0.5 * lg) / 2)
            rhsGc = math.ceil((maxL + 0.5 * lc) / 2)
            if alpha > rhsGc or alpha > rhsG:
                info = {
                    "connected": True,
                    "n": n,
                    "g6": g6(G),
                    "alpha": alpha,
                    "max_l": maxL,
                    "rhs100G": rhsG,
                    "rhs100Gc": rhsGc,
                }
                vs = violations(info, {"100"})
                if vs:
                    hits += 1
                    print("HIT", info["g6"], vs, info, flush=True)
        if "133" in want:
            # A geodesic is an induced path, so path ≥ rad+1. If G has a C4 then
            # the Lean right-hand side is rad+1, so 133 holds without a search.
            if not has_c4_fast(adj):
                fl = math.floor(avg_l(adj))
                if max(diam + 1, 2 * rad - 1) < rad + fl:
                    need.add("133")
        if "198a" in want and n <= 12:
            # if even a lower bound on b already exceeds 2+avg_ecc, hypothesis fails
            if blow <= 2 + avg_ecc:
                need.add("198a")
        if need:
            info = analyze(G, need)
            vs = violations(info, need)
            if vs:
                hits += 1
                print("HIT", info.get("g6", g6(G)), vs, info, flush=True)
        if count % 20000 == 0:
            print(f"... scanned {count} graphs n={n} hits={hits}", flush=True)
    print(f"done n={n} scanned={count} hits={hits}", flush=True)


def main():
    want = set(sys.argv[1].split(",")) if len(sys.argv) > 1 else {"19", "16", "40", "61", "100", "133", "198a"}
    mode = sys.argv[2] if len(sys.argv) > 2 else "named"
    if mode == "named":
        run_named(want)
    elif mode.startswith("n"):
        n = int(mode[1:])
        run_nauty(n, want)
    else:
        raise SystemExit(mode)


if __name__ == "__main__":
    main()
