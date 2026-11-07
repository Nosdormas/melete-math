"""LRAT certificate of the free-vertex case of (28, 6, 3, 2, 1).

    "$SOLVER_PYTHON" -X utf8 checks/dsrg28_certificate.py check [FILE.lrat.xz] [--mutate drop-step]
    "$SOLVER_PYTHON" -X utf8 checks/dsrg28_certificate.py make DIR

check - rebuilds the formula with the same program as checks/dsrg28_check.py, compares its SHA-256 with
the recorded one, unpacks certificates/free-28-6-3-2-1.lrat.xz and checks every LRAT step by unit
propagation with our checker; no solver and no drat-trim are needed (python-sat is used only for the
cardinality encodings). make - solves the formula again with CaDiCaL and writes the compressed LRAT
proof to DIR.
"""
from __future__ import annotations

import gzip
import hashlib
import lzma
import sys
import tempfile
from pathlib import Path

HERE = Path(__file__).resolve().parent
ROOT = HERE.parent
sys.path.insert(0, str(ROOT / "lib"))
sys.path.insert(0, str(ROOT / "lib"))

CELL = (28, 6, 3, 2, 1)
NAME = "free-28-6-3-2-1"
CNF_SHA = "4b59a3ff8959ed54f9a0a5ae2ca02ef07d41eb126fb759610f6732b9daf04ce3"  # recorded by checks/dsrg28_check.py
LRAT_SHA = "7771e5ec55282d9da62937af8687057900f28c8a9cef03cc166c4e7abda0ed21"
XZ = {"preset": 9 | lzma.PRESET_EXTREME}


def sha(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def sizes(label: str, data: bytes) -> None:
    print(f"  {label}: {len(data)} bytes, xz -9e {len(lzma.compress(data, **XZ))},"
          f" gzip -9 {len(gzip.compress(data, 9, mtime=0))}; SHA-256 {sha(data)}")


def make(out: Path) -> int:
    import mu_one_sat as ms
    out.mkdir(parents=True, exist_ok=True)
    with tempfile.TemporaryDirectory(prefix="cert28-") as tmp:
        rec = ms.run(CELL, "free", seconds=230, prove_dir=tmp, keep=True)
        print(f"solver: {rec.get('result')}, variables {rec.get('vars')}, clauses {rec.get('clauses')},"
              f" certify {rec.get('certify')}")
        if rec.get("result") != "UNSAT" or not rec.get("certify", {}).get("verified"):
            print("violations: 1")
            return 1
        files = {ext: (Path(tmp) / f"{NAME}.{ext}").read_bytes() for ext in ("cnf", "drat", "lrat")}
    print("sizes:")
    for ext, data in files.items():
        sizes(ext, data)
    packed = lzma.compress(files["lrat"], **XZ)
    (out / f"{NAME}.lrat.xz").write_bytes(packed)
    print(f"written: {NAME}.lrat.xz, {len(packed)} bytes, SHA-256 {sha(packed)}")
    bad = [] if sha(files["cnf"]) == CNF_SHA else ["SHA-256 of the formula differs from the recorded one"]
    print(f"violations: {len(bad)}")
    for line in bad:
        print("  " + line)
    return 1 if bad else 0


def drop_step(text: str) -> str:
    lines = text.splitlines(keepends=True)
    steps = [(i, ln.split()) for i, ln in enumerate(lines) if ln.split() and ln.split()[1] != "d"]
    ids = {tok[0] for _, tok in steps}
    for i, tok in steps:
        z1 = tok.index("0", 1)
        if any(h in ids for h in tok[z1 + 1:-1]):
            hit = next(h for h in tok[z1 + 1:-1] if h in ids)
            j = next(j for j, t in steps if t[0] == hit)
            return "".join(ln for k, ln in enumerate(lines) if k != j)
    raise SystemExit("the proof cites a missing step")


def check(path: Path, mutate: str | None) -> int:
    import mu_one_sat as ms
    import sat_certificate as sc
    bad = []
    pool, a, clauses = ms.formula(CELL, "free", None, None)
    with tempfile.TemporaryDirectory(prefix="cert28-") as tmp:
        cnf = Path(tmp) / f"{NAME}.cnf"
        cnf_sha = sc.write_dimacs(cnf, pool.top, clauses)
        cnf_bytes = cnf.read_bytes()
        print(f"formula rebuilt: variables {pool.top}, clauses {len(clauses)}, {len(cnf_bytes)} bytes,"
              f" xz -9e compressed {len(lzma.compress(cnf_bytes, **XZ))} bytes; SHA-256 {cnf_sha}")
        if cnf_sha != CNF_SHA:
            bad.append("SHA-256 of the formula differs from the recorded one")
        packed = path.read_bytes()
        text = lzma.decompress(packed)
        print(f"LRAT proof: {path.name}, {len(packed)} bytes, unpacked {len(text)} bytes;"
              f" SHA-256 of the unpacked proof {sha(text)}")
        if sha(text) != LRAT_SHA:
            bad.append("SHA-256 of the LRAT proof differs from the recorded one")
        body = text.decode("ascii")
        if mutate == "drop-step":
            body = drop_step(body)
        lrat = Path(tmp) / f"{NAME}.lrat"
        lrat.write_text(body, encoding="ascii", newline="\n")
        rep = sc.check_lrat_files(cnf, lrat)
    print(f"own LRAT check: {'accepted' if rep.ok else 'not accepted'}, steps {rep.steps}"
          + ("" if rep.ok else f"; reason: {rep.reason}"))
    if not rep.ok:
        bad.append("LRAT proof not accepted")
    print(f"violations: {len(bad)}")
    for line in bad:
        print("  " + line)
    if mutate:
        print(f"mutant {mutate}: {'caught' if bad else 'NOT caught'}")
    return 1 if bad else 0


def main(argv) -> int:
    if argv[:1] == ["make"] and len(argv) == 2:
        return make(Path(argv[1]))
    if argv[:1] == ["check"]:
        rest, mutate = argv[1:], None
        if "--mutate" in rest:
            i = rest.index("--mutate")
            mutate = rest[i + 1] if i + 1 < len(rest) else None
            if mutate != "drop-step":
                print("mutant: only drop-step", file=sys.stderr)
                return 2
            del rest[i:i + 2]
        if len(rest) > 1:
            print("check: at most one file", file=sys.stderr)
            return 2
        default = [ROOT / "certificates" / f"{NAME}.lrat.xz"]
        path = Path(rest[0]) if rest else next((p for p in default if p.is_file()), default[0])
        if not path.is_file():
            print(f"no file {path}", file=sys.stderr)
            return 2
        return check(path, mutate)
    print(__doc__.split("\n\n")[0], file=sys.stderr)
    return 2


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
