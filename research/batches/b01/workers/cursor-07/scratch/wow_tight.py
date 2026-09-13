#!/usr/bin/env python3
"""Tight-case searches for WOWII 40/61/133. Unverified as a resolution."""

from __future__ import annotations

import itertools
import math
import subprocess
import sys

import networkx as nx


def adj_bits(G: nx.Graph) -> list[int]:
    n = G.number_of_nodes()
    idx = {v: i for i, v in enumerate(G.nodes())}
    adj = [0] * n
    for u, v in G.edges():
        i, j = idx[u], idx[v]
        adj[i] |= 1 << j
        adj[j] |= 1 << i
    return adj


def distances(adj: list[int]):
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


def is_forest_mask(adj, mask):
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


def is_bip_mask(adj, mask):
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


def max_by_mask(adj, pred):
    n = len(adj)
    best = 0
    for mask in range(1, 1 << n):
        if pred(adj, mask):
            best = max(best, mask.bit_count())
    return best


def alpha(adj):
    n = len(adj)
    best = 0
    for mask in range(1 << n):
        ok = True
        m = mask
        verts = []
        while m:
            u = (m & -m).bit_length() - 1
            m &= m - 1
            verts.append(u)
        for i, a in enumerate(verts):
            for b in verts[i + 1 :]:
                if (adj[a] >> b) & 1:
                    ok = False
                    break
            if not ok:
                break
        if ok:
            best = max(best, len(verts))
    return best


def residue_of_degrees(degs):
    s = sorted(degs, reverse=True)
    while s:
        if s[0] == 0:
            return len(s)
        d, rest = s[0], s[1:]
        if d > len(rest):
            return -1
        to_dec, remaining = rest[:d], rest[d:]
        s = sorted([x - 1 for x in to_dec] + remaining, reverse=True)
        if any(x < 0 for x in s):
            return -1
    return 0


def path_cover_number(adj):
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


def indep_num_mask(adj, mask):
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


def avg_l(adj):
    n = len(adj)
    return sum(indep_num_mask(adj, adj[v]) for v in range(n)) / n


def has_c4_fast(adj):
    n = len(adj)
    for u in range(n):
        for v in range(u + 1, n):
            if (adj[u] & adj[v]).bit_count() >= 2:
                return True
    return False


def max_induced_path(adj):
    n = len(adj)
    best = 1 if n else 0

    def ok_extend(path, used, v):
        if (used >> v) & 1:
            return False
        last = path[-1]
        if not ((adj[last] >> v) & 1):
            return False
        for u in path[:-1]:
            if (adj[u] >> v) & 1:
                return False
        return True

    def dfs(path, used):
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


def g6(G):
    H = nx.convert_node_labels_to_integers(G)
    return nx.to_graph6_bytes(H, header=False).decode().strip()


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


def check40(adj):
    n = len(adj)
    f = max_by_mask(adj, is_forest_mask)
    b = max_by_mask(adj, is_bip_mask)
    p = path_cover_number(adj)
    rhs = math.ceil((p + b + 1) / 2)
    return f, b, p, rhs, f - rhs


def check61(adj, dist):
    n = len(adj)
    diam = max(max(row) for row in dist)
    a = alpha(adj)
    res = residue_of_degrees([adj[v].bit_count() for v in range(n)])
    rhs_strong = a + math.ceil(diam / 3)
    # cheap: f >= max(a+1 if n>=2 else a, diam+1)
    flow = max(a + (1 if n >= 2 and a < n else 0), diam + 1)
    if flow >= res + math.ceil(diam / 3):
        return a, res, diam, flow, res + math.ceil(diam / 3), True
    f = max_by_mask(adj, is_forest_mask)
    rhs = res + math.ceil(diam / 3)
    return a, res, diam, f, rhs, f >= rhs


def run_40(n: int):
    print(f"=== 40 nauty n={n} ===", flush=True)
    hits = 0
    worst = 10**9
    count = 0
    for G in nauty_connected(n):
        count += 1
        adj = adj_bits(G)
        f, b, p, rhs, gap = check40(adj)
        worst = min(worst, gap)
        if gap < 0:
            hits += 1
            print("HIT40", g6(G), f, b, p, rhs, flush=True)
        if count % 20000 == 0:
            print(f"... n={n} scanned={count} hits={hits} worst_gap={worst}", flush=True)
    print(f"done 40 n={n} scanned={count} hits={hits} worst_gap={worst}", flush=True)


def run_61(n: int):
    print(f"=== 61 tight nauty n={n} ===", flush=True)
    hits = 0
    interesting = 0
    count = 0
    worst = 10**9
    for G in nauty_connected(n):
        count += 1
        adj = adj_bits(G)
        dist = distances(adj)
        if dist is None:
            continue
        a, res, diam, f, rhs, ok = check61(adj, dist)
        if isinstance(ok, bool) and not ok:
            hits += 1
            print("HIT61", g6(G), "a", a, "res", res, "diam", diam, "f", f, "rhs", rhs, flush=True)
        gap = f - rhs
        worst = min(worst, gap)
        if diam >= 4 and f <= a + 2 and res >= a - 1:
            interesting += 1
            if interesting <= 20:
                print("TIGHT61", g6(G), "a", a, "res", res, "diam", diam, "f", f, "rhs", rhs, "gap", gap, flush=True)
        if count % 20000 == 0:
            print(f"... n={n} scanned={count} hits={hits} worst_gap={worst} tightish={interesting}", flush=True)
    print(f"done 61 n={n} scanned={count} hits={hits} worst_gap={worst} tightish={interesting}", flush=True)


def run_133(n: int):
    print(f"=== 133 C4-free nauty n={n} ===", flush=True)
    hits = 0
    c4free = 0
    count = 0
    for G in nauty_connected(n):
        count += 1
        adj = adj_bits(G)
        if has_c4_fast(adj):
            continue
        c4free += 1
        dist = distances(adj)
        if dist is None:
            continue
        ecc = [max(row) for row in dist]
        rad = min(ecc)
        fl = math.floor(avg_l(adj))
        rhs = rad + fl
        if max(max(ecc) + 1, 2 * rad - 1) >= rhs:
            continue
        path = max_induced_path(adj)
        if path < rhs:
            hits += 1
            print("HIT133", g6(G), "path", path, "rad", rad, "avg_l", avg_l(adj), "rhs", rhs, flush=True)
        if c4free % 2000 == 0:
            print(f"... n={n} scanned={count} c4free={c4free} hits={hits}", flush=True)
    print(f"done 133 n={n} scanned={count} c4free={c4free} hits={hits}", flush=True)


def constructions_40_61_133():
    print("=== constructions ===", flush=True)

    def snake_triangles(k):
        G = nx.Graph()
        for i in range(k):
            a, b, c = 2 * i, 2 * i + 1, 2 * i + 2
            G.add_edges_from([(a, b), (b, c), (c, a)])
        return G

    def path_plus_k3(m):
        G = nx.path_graph(m)
        G.add_edge(0, 2)
        return G

    def two_c4_star(m):
        G = nx.Graph()
        G.add_edges_from([(0, 1), (1, 2), (2, 3), (3, 0)])
        G.add_edges_from([(4, 5), (5, 6), (6, 7), (7, 4)])
        G.add_edge(0, 8)
        G.add_edge(4, 8)
        for i in range(m):
            G.add_edge(8, 9 + i)
        return G

    graphs = []
    for k in range(2, 8):
        graphs.append((f"snakeT{k}", snake_triangles(k)))
    for m in range(5, 16):
        graphs.append((f"P{m}+K3", path_plus_k3(m)))
    for m in range(0, 8):
        graphs.append((f"2C4star{m}", two_c4_star(m)))
    for n in range(8, 16):
        graphs.append((f"P{n}", nx.path_graph(n)))
        graphs.append((f"C{n}", nx.cycle_graph(n)))
        graphs.append((f"star{n}", nx.star_graph(n - 1)))
        graphs.append((f"double_star{n}", nx.full_rary_tree(2, n) if n >= 3 else nx.path_graph(n)))
    if hasattr(nx, "tutte_coxeter_graph"):
        graphs.append(("tutte_coxeter", nx.tutte_coxeter_graph()))
    if hasattr(nx, "mcgee_graph"):
        graphs.append(("mcgee", nx.mcgee_graph()))
    if hasattr(nx, "hoffman_singleton_graph"):
        graphs.append(("HS", nx.hoffman_singleton_graph()))
    if hasattr(nx, "petersen_graph"):
        graphs.append(("petersen", nx.petersen_graph()))
    if hasattr(nx, "heawood_graph"):
        graphs.append(("heawood", nx.heawood_graph()))
    if hasattr(nx, "app_graph"):
        pass
    for name, G in graphs:
        G = nx.Graph(G)
        G.remove_edges_from(nx.selfloop_edges(G))
        if G.number_of_nodes() < 2 or not nx.is_connected(G):
            continue
        adj = adj_bits(G)
        n = len(adj)
        dist = distances(adj)
        if dist is None:
            continue
        msg = [name, "n", n]
        if n <= 14:
            f, b, p, rhs, gap = check40(adj)
            msg += ["40", f"f={f}", f"b={b}", f"p={p}", f"rhs={rhs}", f"gap={gap}"]
            if gap < 0:
                print("HIT", *msg, flush=True)
        a, res, diam, f, rhs, ok = check61(adj, dist)
        msg += ["61", f"a={a}", f"res={res}", f"diam={diam}", f"f={f}", f"rhs={rhs}", f"ok={ok}"]
        if not ok:
            print("HIT", *msg, flush=True)
        if n <= 24 and not has_c4_fast(adj):
            ecc = [max(row) for row in dist]
            rad = min(ecc)
            al = avg_l(adj)
            rhs = rad + math.floor(al)
            path = max_induced_path(adj) if n <= 20 else -1
            if path != -1 and path < rhs:
                print("HIT133", name, "path", path, "rad", rad, "avg_l", al, "rhs", rhs, flush=True)
            elif n <= 16:
                print("ok133", name, "path", path, "rad", rad, "avg_l", f"{al:.3f}", "rhs", rhs, flush=True)
        if n <= 14:
            print("info", *msg, flush=True)


def main():
    mode = sys.argv[1] if len(sys.argv) > 1 else "cons"
    if mode == "cons":
        constructions_40_61_133()
    elif mode.startswith("40n"):
        run_40(int(mode[3:]))
    elif mode.startswith("61n"):
        run_61(int(mode[3:]))
    elif mode.startswith("133n"):
        run_133(int(mode[3:]))
    else:
        raise SystemExit(mode)


if __name__ == "__main__":
    main()
