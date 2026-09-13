#!/usr/bin/env python3
"""Gap search: f - alpha vs ceil(diam/3); self-centered 19 gap. Unverified."""
import itertools, math, subprocess, sys
import networkx as nx

def adj_bits(G):
    n = G.number_of_nodes()
    idx = {v: i for i, v in enumerate(G.nodes())}
    adj = [0] * n
    for u, v in G.edges():
        i, j = idx[u], idx[v]
        adj[i] |= 1 << j
        adj[j] |= 1 << i
    return adj

def distances(adj):
    n = len(adj)
    dist = [[-1]*n for _ in range(n)]
    for s in range(n):
        dist[s][s] = 0
        q = [s]
        for u in q:
            nb = adj[u]; d = dist[s][u]
            while nb:
                v = (nb & -nb).bit_length()-1
                nb &= nb-1
                if dist[s][v] < 0:
                    dist[s][v] = d+1
                    q.append(v)
        if any(x < 0 for x in dist[s]):
            return None
    return dist

def is_forest_mask(adj, mask):
    nverts = mask.bit_count()
    nedges = 0
    m = mask
    while m:
        u = (m & -m).bit_length()-1
        m &= m-1
        nedges += (adj[u] & mask).bit_count()
    nedges //= 2
    components = 0
    seen = 0
    remaining = mask
    while remaining:
        s = (remaining & -remaining).bit_length()-1
        components += 1
        stack = [s]
        seen |= 1 << s
        remaining &= remaining-1
        while stack:
            u = stack.pop()
            nb = adj[u] & mask
            while nb:
                v = (nb & -nb).bit_length()-1
                nb &= nb-1
                if not ((seen >> v) & 1):
                    seen |= 1 << v
                    remaining &= ~(1 << v)
                    stack.append(v)
    return nedges == nverts - components

def max_forest(adj):
    n = len(adj)
    for k in range(n, 0, -1):
        for S in itertools.combinations(range(n), k):
            mask = 0
            for i in S:
                mask |= 1 << i
            if is_forest_mask(adj, mask):
                return k
    return 0

def alpha(adj):
    n = len(adj)
    best = 1
    for k in range(n, 1, -1):
        for S in itertools.combinations(range(n), k):
            ok = True
            for a in range(k):
                for b in range(a+1, k):
                    if (adj[S[a]] >> S[b]) & 1:
                        ok = False
                        break
                if not ok:
                    break
            if ok:
                return k
    return best

def residue(degs):
    s = sorted(degs, reverse=True)
    while s:
        if s[0] == 0:
            return len(s)
        d, rest = s[0], s[1:]
        s = sorted([x-1 for x in rest[:d]] + rest[d:], reverse=True)
        if any(x < 0 for x in s):
            return -1
    return 0

def run(n):
    proc = subprocess.Popen(["nauty-geng","-c",str(n)], stdout=subprocess.PIPE, stderr=subprocess.DEVNULL, text=True)
    worst61 = 99
    worst_fa = 99
    hits61 = 0
    count = 0
    examples = []
    for line in proc.stdout:
        count += 1
        G = nx.from_graph6_bytes(line.strip().encode())
        adj = adj_bits(G)
        dist = distances(adj)
        if dist is None:
            continue
        ecc = [max(row) for row in dist]
        diam = max(ecc)
        a = alpha(adj)
        degs = [adj[v].bit_count() for v in range(n)]
        res = residue(degs)
        rhs = res + math.ceil(diam/3)
        lower = max(a, diam+1)
        if lower >= rhs:
            gap = lower - rhs
        else:
            f = max_forest(adj)
            gap = f - rhs
            if gap < 0:
                hits61 += 1
                examples.append((line.strip(), f, a, res, diam, rhs))
                print("HIT61", line.strip(), "f", f, "a", a, "res", res, "diam", diam, "rhs", rhs, flush=True)
        worst61 = min(worst61, gap if lower >= rhs else gap)
        if diam >= 3:
            # f-alpha lower via diam+1-alpha
            fa_lower = max(1, diam+1-a)
            if fa_lower < worst_fa:
                worst_fa = fa_lower
        if count % 50000 == 0:
            print("...", n, count, "worst61", worst61, "hits", hits61, flush=True)
    proc.wait()
    print("DONE", n, "scanned", count, "hits61", hits61, "worst_recorded", worst61, flush=True)
    if examples:
        print(examples[:10])

if __name__ == "__main__":
    for n in map(int, sys.argv[1:]):
        run(n)
