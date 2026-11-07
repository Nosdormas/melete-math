"""Frames of a vertex for μ = 1, t = λ + 1, and lifts of Kautz graphs.
"""
from __future__ import annotations

import json
import random
import statistics
import sys
import time
from collections import Counter
from itertools import combinations
from math import comb
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / "lib"))
sys.path.insert(0, str(ROOT / "lib"))


def counts(params, ins):
    v, k, t, lam, mu = params
    S = range(k + 1)
    out = [set() for _ in S]
    for y in S:
        for z in ins[y]:
            out[z].add(y)
    W = [k - len(out[o]) for o in S]
    n = [[0] * (k + 1) for _ in S]
    for o in range(1, k + 1):
        for y in S:
            if y == o:
                n[o][y] = lam + 1 - len(ins[o] & out[o])
            else:
                arc = o in ins[y]
                paths = sum(1 for z in ins[y] if z != o and o in ins[z])
                n[o][y] = 1 + (lam - 1) * arc - paths
    return n, W


def frame_ok(params, ins):
    v, k, t, lam, mu = params
    n, W = counts(params, ins)
    for o in range(1, k + 1):
        if W[o] != 0 and W[o] < lam + 1:
            return False, None, f"|W_{o}| = {W[o]} < λ + 1"
        for y in range(k + 1):
            if n[o][y] < 0 or n[o][y] > W[o]:
                return False, None, f"n({o}, {y}) = {n[o][y]} outside [0, {W[o]}]"
    a = 1 + sum(1 for o in range(1, k + 1) if W[o] == 0)
    return True, a, None


def _children(params, ins, y, choices):
    v, k, t, lam, mu = params
    good = []
    for c in choices[y]:
        ins[y] = c
        if _partial_ok(params, ins, y):
            good.append(c)
    ins[y] = None
    return good


def _partial_ok(params, ins, last):
    v, k, t, lam, mu = params
    for y2 in range(last + 1):
        iy = ins[y2]
        for o in range(1, k + 1):
            if o == y2:
                continue
            arc = o in iy
            paths = sum(1 for z in iy if z != o and z <= last and o in ins[z])
            if paths > 1 + (lam - 1) * arc:
                return False
    return True


def _choices(params):
    v, k, t, lam, mu = params
    O = range(1, k + 1)
    ch = {0: [frozenset(range(1, t + 1))]}
    for y in O:
        ch[y] = [frozenset(c) | {0} for c in combinations([z for z in O if z != y], lam)]
    return ch


def count_frames(params, choices=None, leaf=None, keep=None):
    v, k, t, lam, mu = params
    ch = choices or _choices(params)
    ins = [None] * (k + 1)
    ins[0] = ch[0][0]
    stats = Counter()

    def rec(y):
        if y > k:
            ok, a, _ = frame_ok(params, ins)
            if ok and (leaf is None or leaf(ins, a)):
                stats[a] += 1
                if keep is not None:
                    keep.append(list(ins))
            return
        for c in _children(params, ins, y, ch):
            ins[y] = c
            rec(y + 1)
        ins[y] = None

    rec(1)
    return stats, comb(k - 1, lam) ** k


def pair_choices(params):
    v, k, t, lam, mu = params
    O = range(1, k + 1)
    ch = {0: [frozenset(range(1, t + 1))], 1: [frozenset(c) | {0} for c in combinations(range(2, k + 1), lam)]}
    for y in range(2, k + 1):
        ch[y] = [frozenset(c) | {0, 1} for c in combinations([z for z in O if z not in (1, y)], lam - 1)]
    return ch


def column_pairing(ins):
    n = len(ins)
    ok = [[u != w and w in ins[u] and u in ins[w] and ins[u] - {w} == ins[w] - {u} for w in range(n)]
          for u in range(n)]

    def rec(free):
        if not free:
            return []
        u = free[0]
        for w in free[1:]:
            if ok[u][w]:
                rest = rec([z for z in free if z not in (u, w)])
                if rest is not None:
                    return [(u, w)] + rest
        return None

    return rec(list(range(n)))


def pair_leaf(ins, a):
    if a != 2 or column_pairing(ins) is None:
        return False
    return not any(u in ins[0] and u in ins[1] for u in range(2, len(ins)))


def canon(ins):
    from itertools import permutations, product
    n = len(ins)
    out = [set() for _ in range(n)]
    for y in range(n):
        for z in ins[y]:
            out[z].add(y)
    col = [0 if y == 0 else 1 for y in range(n)]
    while True:
        sig = [(col[y], tuple(sorted(col[z] for z in ins[y])), tuple(sorted(col[z] for z in out[y])))
               for y in range(n)]
        keys = sorted(set(sig))
        new = [keys.index(s) for s in sig]
        if len(set(new)) == len(set(col)):
            col = new
            break
        col = new
    cells = [[y for y in range(n) if col[y] == c] for c in sorted(set(col))]
    total = 1
    for c in cells:
        for i in range(2, len(c) + 1):
            total *= i
    if total > 10 ** 6:
        raise ValueError(f"canon: {total} permutations inside cells")
    best = None
    for perms in product(*(permutations(c) for c in cells)):
        order = [y for p in perms for y in p]
        pos = {y: i for i, y in enumerate(order)}
        key = tuple(tuple(sorted(pos[z] for z in ins[y])) for y in order)
        if best is None or key < best:
            best = key
    return best


def pair_frames(params):
    keep = []
    stats, _ = count_frames(params, pair_choices(params), pair_leaf, keep)
    classes = {}
    for ins in keep:
        classes.setdefault(canon(ins), ins)
    return sum(stats.values()), [[sorted(s) for s in ins] for ins in classes.values()]


def kautz(d):
    verts = [(u, w) for u in range(d + 1) for w in range(d + 1) if u != w]
    idx = {p: i for i, p in enumerate(verts)}
    m = len(verts)
    S = [[0] * m for _ in range(m)]
    for (u, w) in verts:
        for z in range(d + 1):
            if z != w:
                S[idx[(u, w)]][idx[(w, z)]] = 1
    return S


def lift(S, q):
    m = len(S)
    verts = [(i, a, b) for i in range(m) for a in range(q) for b in range(q)]
    n = len(verts)
    A = [[0] * n for _ in range(n)]
    for x, (i, a, b) in enumerate(verts):
        for y, (j, a2, b2) in enumerate(verts):
            if x != y and ((i == j and a == a2) or (S[i][j] and b == a2)):
                A[x][y] = 1
    return A


def lift_params(q, d):
    m = d * (d + 1)
    return (q * q * m, q - 1 + q * d, q, q - 1, 1)


# ---------- CLI ----------


