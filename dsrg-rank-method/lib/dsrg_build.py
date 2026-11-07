"""Constructions of DSRGs: flag graphs of generalized quadrangles and blow-ups.
"""
from __future__ import annotations

import itertools
import json
import sys
from pathlib import Path

import numpy as np

sys.path.insert(0, str(Path(__file__).resolve().parent))

import dsrg_graphs as dg  # noqa: E402


def clique_blowup(A, c: int) -> list[list[int]]:
    M = np.asarray(A, dtype=np.int64)
    n = len(M)
    B = np.kron(M + np.eye(n, dtype=np.int64), np.ones((c, c), dtype=np.int64))
    return (B - np.eye(n * c, dtype=np.int64)).tolist()


def gq_grid(s: int):
    pts = [(i, j) for i in range(s + 1) for j in range(s + 1)]
    lines = [frozenset((i, j) for j in range(s + 1)) for i in range(s + 1)]
    lines += [frozenset((i, j) for i in range(s + 1)) for j in range(s + 1)]
    return pts, lines


def gq_dual(pts, lines):
    new_pts = list(range(len(lines)))
    new_lines = [frozenset(i for i, L in enumerate(lines) if p in L) for p in pts]
    return new_pts, new_lines


def gq_w2():
    pts = [v for v in itertools.product((0, 1), repeat=4) if any(v)]

    def form(u, w):
        return (u[0] * w[1] + u[1] * w[0] + u[2] * w[3] + u[3] * w[2]) % 2

    lines = set()
    for u, w in itertools.combinations(pts, 2):
        if form(u, w) == 0:
            s = tuple((a + b) % 2 for a, b in zip(u, w))
            lines.add(frozenset((u, w, s)))
    return pts, sorted(lines, key=sorted)


def flag_graph(pts, lines):
    flags = [(p, i) for i, L in enumerate(lines) for p in sorted(L)]
    v = len(flags)
    A = [[1 if (a != b and flags[a][0] in lines[flags[b][1]]) else 0 for b in range(v)] for a in range(v)]
    s = len(lines[0]) - 1
    tt = sum(1 for L in lines if pts[0] in L) - 1
    k = (s + 1) * (tt + 1) - 1
    return A, (v, k, s + tt, s + tt - 1, 1)


