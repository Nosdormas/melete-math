"""Parser of the snapshot of the Hobart–Brouwer table.
"""

import re
import sys
from pathlib import Path


def read_snapshot(path):
    result = []
    for line in Path(path).read_text(encoding="utf-8").splitlines():
        if not line or line.startswith("#"):
            continue
        head, _, rest = line.partition(":")
        for token in rest.split():
            *numbers, status = token.split(",")
            result.append(((int(head),) + tuple(map(int, numbers)), status))
    return result


