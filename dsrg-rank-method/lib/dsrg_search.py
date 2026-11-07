"""SAT encoding of the definition of a DSRG.
"""
from __future__ import annotations

import json
import multiprocessing as mp
import queue
import random
import sys
import time
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
VERIFY = ROOT / "lib"
if str(VERIFY) not in sys.path:
    sys.path.insert(0, str(VERIFY))

import dsrg_verify  # noqa: E402


def encode(params, symmetry: bool = True, orbits: int = 0, right=None, left=None):
    from pysat.card import CardEnc, EncType
    from pysat.formula import IDPool

    v, k, t, lam, mu = params
    pool = IDPool()
    clauses: list[list[int]] = []
    if orbits:
        n = v // orbits
        false_id = pool.id(("false",))
        clauses.append([-false_id])

        def a(i, j):
            if i == j:
                return false_id
            return pool.id(("b", i // n, j // n, (j % n - i % n) % n))
        rows = [o * n for o in range(orbits)]
    else:
        def a(i, j):
            return pool.id(("a", i, j))
        rows = list(range(v))
        for i in range(v):
            clauses.append([-a(i, i)])

    def card(lits, bound, kind, guard=None):
        enc = {"eq": CardEnc.equals, "le": CardEnc.atmost, "ge": CardEnc.atleast}[kind]
        cnf = enc(lits=lits, bound=bound, vpool=pool, encoding=EncType.seqcounter)
        for cl in cnf.clauses:
            clauses.append(cl + ([guard] if guard is not None else []))

    for i in rows:
        card([a(i, j) for j in range(v) if j != i], k, "eq")
        card([a(j, i) for j in range(v) if j != i], k, "eq")
    for i in rows:
        for j in range(v):
            paths = []
            for x in range(v):
                if x in (i, j):
                    continue
                p = pool.id(("p", i, x, j))
                clauses += [[-p, a(i, x)], [-p, a(x, j)], [p, -a(i, x), -a(x, j)]]
                paths.append(p)
            if i == j:
                card(paths, t, "eq")
            else:
                card(paths, lam, "eq", guard=-a(i, j))
                card(paths, mu, "eq", guard=a(i, j))
    for vec, by_rows in ((right, True), (left, False)):
        if vec is None:
            continue
        theta, x = vec
        plus = [j for j in range(v) if x[j] > 0]
        for i in range(v):
            lits = [a(i, j) if by_rows else a(j, i) for j in plus if j != i]
            need = (k + theta * x[i]) // 2
            if need > len(lits):
                clauses.append([])
            elif lits:
                card(lits, need, "eq")
    if symmetry and not orbits and right is None and left is None:
        for j in range(1, v):
            clauses.append([a(0, j)] if j <= k else [-a(0, j)])
            clauses.append([a(j, 0)] if (j <= t or k < j <= 2 * k - t) else [-a(j, 0)])
    return pool, a, clauses


