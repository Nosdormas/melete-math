
import json
import re
import sys
from dataclasses import dataclass


class InputError(ValueError):
    pass


@dataclass
class Report:
    ok: bool
    violation: dict | None = None


_DIGITS = re.compile(r"[0-9]+")
_DIGIT_CHARS = "0123456789"
_SEPARATORS = re.compile(r"[\s,]+")


def _fail(kind, row, col, expected, actual):
    return Report(False, {"kind": kind, "row": row, "col": col, "expected": expected, "actual": actual})


def check(matrix, params, undirected=False) -> Report:
    v, k, t, lam, mu = params
    if len(matrix) != v:
        return _fail("shape", None, None, v, len(matrix))
    for i, row in enumerate(matrix):
        if len(row) != v:
            return _fail("shape", i, None, v, len(row))
    for i in range(v):
        for j in range(v):
            if matrix[i][j] not in (0, 1):
                return _fail("entry", i, j, None, matrix[i][j])
    for i in range(v):
        if matrix[i][i] != 0:
            return _fail("loop", i, i, 0, matrix[i][i])
    for i in range(v):
        s = sum(matrix[i])
        if s != k:
            return _fail("out-degree", i, None, k, s)
    for j in range(v):
        s = sum(matrix[i][j] for i in range(v))
        if s != k:
            return _fail("in-degree", None, j, k, s)
    if undirected:
        for i in range(v):
            for j in range(v):
                if matrix[i][j] != matrix[j][i]:
                    return _fail("symmetry", i, j, matrix[j][i], matrix[i][j])
    for i in range(v):
        row_i = matrix[i]
        sq = [0] * v
        for m in range(v):
            if row_i[m]:
                row_m = matrix[m]
                for j in range(v):
                    sq[j] += row_m[j]
        for j in range(v):
            if i == j:
                expected = t
            elif row_i[j] == 1:
                expected = lam
            else:
                expected = mu
            if sq[j] != expected:
                return _fail("square", i, j, expected, sq[j])
    return Report(True, None)


def check_srg(matrix, v, k, lam, mu) -> Report:
    return check(matrix, (v, k, k, lam, mu), undirected=True)


def _row_values(line, lineno):
    if _SEPARATORS.search(line):
        tokens = [tok for tok in _SEPARATORS.split(line) if tok]
    else:
        tokens = list(line)
    values = []
    for tok in tokens:
        if not _DIGITS.fullmatch(tok):
            bad = next(ch for ch in tok if ch not in _DIGIT_CHARS)
            raise InputError(f"line {lineno}: invalid character {bad!r}")
        values.append(int(tok))
    return values


def read_matrix(text) -> list[list[int]]:
    rows = []
    for lineno, raw in enumerate(text.splitlines(), start=1):
        line = raw.strip()
        if not line or line.startswith("#"):
            continue
        rows.append(_row_values(line, lineno))
    if not rows:
        raise InputError("empty file: no matrix rows")
    return rows


_HELP = """usage: dsrg_verify.py --params v,k,t,λ,μ [--undirected] FILE|-

Checks an adjacency matrix as a directed strongly regular graph with parameters (v, k, t, λ, μ);
with --undirected the graph must be symmetric (for an SRG take t = k).
FILE is the path to the matrix file, «-» is standard input.

Output: one JSON line with the fields ok, params, violation.
Exit codes: 0 — the graph passes, 1 — the graph is rejected, 2 — input error (message on stderr).

  --params v,k,t,λ,μ   five integers
  --undirected         require a symmetric matrix
  -h, --help           help
"""


def _is_flag(arg):
    return arg.startswith("-") and arg != "-"


def _parse_argv(argv):
    params_text = None
    undirected = False
    positional = []
    i = 0
    while i < len(argv):
        arg = argv[i]
        if arg == "--undirected":
            undirected = True
        elif arg == "--params":
            if i + 1 >= len(argv) or _is_flag(argv[i + 1]):
                raise InputError("--params: the flag needs a set v,k,t,λ,μ")
            params_text = argv[i + 1]
            i += 1
        elif _is_flag(arg):
            raise InputError(f"unknown flag {arg}")
        else:
            positional.append(arg)
        i += 1
    if len(positional) != 1:
        raise InputError(
            f"one positional argument is needed — a file path or «-», got: {len(positional)}"
        )
    if params_text is None:
        raise InputError("--params: the set v,k,t,λ,μ is required")
    return params_text, undirected, positional[0]


def parse_params(text, label="--params"):
    parts = [p.strip() for p in text.split(",")]
    if len(parts) != 5 or not all(_DIGITS.fullmatch(p) for p in parts):
        raise InputError(f"{label}: five integers v,k,t,λ,μ are needed, got «{text}»")
    return tuple(int(p) for p in parts)


def _read_source(source):
    try:
        if source == "-":
            return sys.stdin.read()
        with open(source, encoding="utf-8") as handle:
            return handle.read()
    except OSError as exc:
        raise InputError(f"cannot read {source}: {exc.strerror}") from exc
    except UnicodeDecodeError as exc:
        raise InputError(f"{source}: the file is not UTF-8") from exc


def main(argv) -> int:
    if argv in (["-h"], ["--help"]):
        sys.stdout.write(_HELP)
        return 0
    try:
        params_text, undirected, source = _parse_argv(argv)
        params = parse_params(params_text)
        matrix = read_matrix(_read_source(source))
    except InputError as exc:
        print(f"dsrg_verify: input error: {exc}", file=sys.stderr)
        return 2
    report = check(matrix, params, undirected)
    print(json.dumps({"ok": report.ok, "params": list(params), "violation": report.violation},
                     ensure_ascii=False))
    return 0 if report.ok else 1


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
