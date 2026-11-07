"""Exact rank, inverse and kernel over the rationals.
"""
from __future__ import annotations

import math
from collections import defaultdict
from fractions import Fraction
from itertools import combinations_with_replacement


def nullspace(M, left=False):
    if left:
        M = [list(col) for col in zip(*M)]
    A = [[Fraction(x) for x in row] for row in M]
    n, m = len(A), len(A[0])
    pivots = []
    r = 0
    for c in range(m):
        piv = next((i for i in range(r, n) if A[i][c] != 0), None)
        if piv is None:
            continue
        A[r], A[piv] = A[piv], A[r]
        p = A[r][c]
        A[r] = [x / p for x in A[r]]
        for i in range(n):
            if i != r and A[i][c] != 0:
                f = A[i][c]
                A[i] = [a - f * b for a, b in zip(A[i], A[r])]
        pivots.append(c)
        r += 1
        if r == n:
            break
    basis = []
    for fc in (c for c in range(m) if c not in pivots):
        z = [Fraction(0)] * m
        z[fc] = Fraction(1)
        for i, pc in enumerate(pivots):
            z[pc] = -A[i][fc]
        basis.append(z)
    return basis


def rank(rows) -> int:
    if not rows:
        return 0
    return len(rows[0]) - len(nullspace(rows))


def rank_int(rows) -> int:
    M = [list(r) for r in rows if any(r)]
    if not M:
        return 0
    n, m = len(M), len(M[0])
    rank, prev = 0, 1
    for c in range(m):
        piv = next((i for i in range(rank, n) if M[i][c] != 0), None)
        if piv is None:
            continue
        M[rank], M[piv] = M[piv], M[rank]
        p = M[rank][c]
        for i in range(rank + 1, n):
            a = M[i][c]
            M[i] = [(M[i][j] * p - a * M[rank][j]) // prev for j in range(m)]
        prev = p
        rank += 1
        if rank == n:
            break
    return rank


def inverse(M):
    n = len(M)
    A = [[Fraction(x) for x in row] + [Fraction(int(i == j)) for j in range(n)] for i, row in enumerate(M)]
    for c in range(n):
        p = next((r for r in range(c, n) if A[r][c] != 0), None)
        if p is None:
            return None
        A[c], A[p] = A[p], A[c]
        iv = 1 / A[c][c]
        A[c] = [x * iv for x in A[c]]
        for r in range(n):
            if r != c and A[r][c] != 0:
                f = A[r][c]
                A[r] = [a - f * b for a, b in zip(A[r], A[c])]
    return [row[n:] for row in A]


