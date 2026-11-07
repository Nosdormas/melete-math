"""Reading graph catalogues and matrices; the exact check of a DSRG.
"""
from __future__ import annotations

import hashlib
import json
import sys
from pathlib import Path

import numpy as np

ROOT = Path(__file__).resolve().parent.parent
for _sub in (("lib",),):
    _p = str(ROOT.joinpath(*_sub))
    if _p not in sys.path:
        sys.path.insert(0, _p)

import dsrg_conditions  # noqa: E402
import dsrg_verify  # noqa: E402


class InputError(ValueError):
    pass


def complement_params(p) -> tuple[int, int, int, int, int]:
    return tuple(dsrg_conditions.complement(tuple(p)))  # type: ignore[return-value]


