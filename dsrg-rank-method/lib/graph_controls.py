"""Graph catalogues: loading, complements and the exact check of every graph.
"""
from __future__ import annotations

import importlib.util
import json
import os
import random
import sys
import tempfile
import time
from collections import Counter
from math import gcd
from pathlib import Path

import numpy as np

import dsrg_graphs as dg

ROOT = Path(__file__).resolve().parent.parent
sys.path.insert(0, str(ROOT / "lib"))
import dsrg_verify  # noqa: E402

DATA = ROOT / "data/graphs"


class InputError(Exception):
    pass


def catalog_files() -> list[Path]:
    return [p for p in sorted(DATA.glob("*.json")) + sorted((DATA / "catalog").glob("*.json"))
            if "graphs" in json.loads(p.read_text(encoding="utf-8"))]


def load_graphs(paths, keep) -> list[dict]:
    out = []
    for path in paths:
        path = Path(path)
        if not path.is_file():
            raise InputError(f"no file {path}")
        try:
            graphs = json.loads(path.read_text(encoding="utf-8"))["graphs"]
        except (ValueError, KeyError, TypeError):
            raise InputError(f"{path}: not in the format of known-small.json") from None
        for n, g in enumerate(graphs):
            params = tuple(g["params"])
            if not keep(params):
                continue
            v = params[0]
            rows = ([[int(x) for x in row] for row in g["rows"]] if "rows" in g
                    else [[(int(mask) >> j) & 1 for j in range(v)] for mask in g["bitmasks"]])
            report = dsrg_verify.check(rows, params)
            if not report.ok:
                raise InputError(f"{path.name}#{n}: graph {params} failed the exact check: {report.violation}")
            out.append({"id": g.get("id") or f"{path.name}#{n}", "params": params, "A": np.array(rows, dtype=np.int64)})
    return out


def complement(graph: dict) -> dict:
    v, k, t, lam, mu = graph["params"]
    params = (v, v - k - 1, v - 2 * k + t - 1, v - 2 * k + mu - 2, v - 2 * k + lam)
    A = np.ones((v, v), dtype=np.int64) - np.eye(v, dtype=np.int64) - graph["A"]
    if not dsrg_verify.check(A.tolist(), params).ok:
        raise InputError(f"complement {graph['id']} failed the exact check as {params}")
    return {"id": f"{graph['id']}-complement", "params": params, "A": A}






