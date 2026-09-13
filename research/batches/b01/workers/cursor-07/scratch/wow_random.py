#!/usr/bin/env python3
"""Random and structured search for WOWII 61 / 19 / 133. Unverified."""
import itertools, math, random
import networkx as nx

from pathlib import Path
import importlib.util
spec = importlib.util.spec_from_file_location(
    "wow_search",
    "/workspace/research/batches/b01/workers/cursor-07/scratch/wow_search.py",
)
ws = importlib.util.module_from_spec(spec)
spec.loader.exec_module(ws)


def random_connected(n, p, rng):
    while True:
        G = nx.gnp_random_graph(n, p, seed=rng.randint(0, 10**9))
        if nx.is_connected(G) and G.number_of_nodes() >= 2:
            return G


def caterpillar(n, leaves_per):
    G = nx.path_graph(n)
    k = 0
    for v in range(n):
        for _ in range(leaves_per):
            G.add_edge(v, n + k)
            k += 1
    return G


def clique_path(k, m):
    """k copies of K_m, consecutive copies share one vertex."""
    G = nx.Graph()
    offset = 0
    shared = None
    for _ in range(k):
        nodes = list(range(offset, offset + m))
        if shared is not None:
            nodes[0] = shared
        G.add_nodes_from(nodes)
        G.add_edges_from(itertools.combinations(nodes, 2))
        shared = nodes[-1]
        offset = max(G.nodes()) + 1
    return G


def check(G, want):
    G = nx.Graph(G)
    G.remove_edges_from(nx.selfloop_edges(G))
    if G.number_of_nodes() < 2 or G.number_of_nodes() > 18 or not nx.is_connected(G):
        return None
    info = ws.analyze(G, want)
    vs = ws.violations(info, want)
    return vs, info


def main():
    rng = random.Random(20260912)
    want = {"19", "16", "61", "133", "198a", "100"}
    hits = 0
    tried = 0
    for n in range(8, 17):
        for p in (0.15, 0.25, 0.4, 0.6):
            for _ in range(40):
                G = random_connected(n, p, rng)
                tried += 1
                vs, info = check(G, want)
                if vs:
                    hits += 1
                    print("RAND", n, p, vs, info.get("g6"), {k: info[k] for k in ("n","diam","b","f","res","rhs61","rhs19","alpha","path") if k in info}, flush=True)
    for n in range(5, 12):
        for lp in range(1, 5):
            G = caterpillar(n, lp)
            tried += 1
            vs, info = check(G, want)
            if vs:
                hits += 1
                print("CAT", n, lp, vs, info.get("g6"), flush=True)
    for k in range(2, 8):
        for m in range(3, 7):
            G = clique_path(k, m)
            tried += 1
            vs, info = check(G, want)
            if vs:
                hits += 1
                print("CLQPATH", k, m, vs, info, flush=True)
    for n in range(6, 16):
        G = nx.cycle_graph(n)
        G.add_edges_from((i, (i+2) % n) for i in range(n))
        tried += 1
        vs, info = check(G, want)
        if vs:
            hits += 1
            print("CIRC", n, vs, info.get("g6"), flush=True)
    print("tried", tried, "hits", hits, flush=True)


if __name__ == "__main__":
    main()
