"""Status of a parameter set in the snapshot of the Hobart–Brouwer table.
"""
from __future__ import annotations

import json
import re
import sys
from math import gcd
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))

import brouwer_dsrg_snapshot  # noqa: E402
import dsrg_graphs as dg  # noqa: E402
from dsrg_graphs import InputError  # noqa: E402

import dsrg_conditions

DATA = dg.ROOT / "data"
SNAPSHOT = DATA / "brouwer-dsrg-v110.txt"


def load_snapshot(path: Path = SNAPSHOT) -> dict:
    if not path.is_file():
        raise InputError(f"no snapshot: {path}")
    return {tuple(p): st for p, st in brouwer_dsrg_snapshot.read_snapshot(path)}


