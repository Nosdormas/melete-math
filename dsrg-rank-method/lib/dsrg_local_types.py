"""Local profiles of a vertex for λ = 1.
"""
from __future__ import annotations

import itertools
import json
import sys
from collections import Counter
from fractions import Fraction
from functools import lru_cache
from math import comb, factorial, gcd
from pathlib import Path


def profiles(k: int, t: int):
    parts = [(n, m) for n in range(2, k + 1) for m in range(0, n + 1)]

    def rec(start, k_left, t_left, acc):
        if k_left == 0:
            if t_left == 0:
                yield tuple(acc)
            return
        for idx in range(start, len(parts)):
            n, m = parts[idx]
            if n > k_left:
                break
            if m > t_left:
                continue
            acc.append((n, m))
            yield from rec(idx, k_left - n, t_left - m, acc)
            acc.pop()

    yield from rec(0, k, t, [])


