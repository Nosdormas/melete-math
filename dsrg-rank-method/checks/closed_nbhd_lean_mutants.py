"""Mutated statements of the closed-neighbourhood Lean module must be rejected by Lean.

    python -X utf8 checks/closed_nbhd_lean_mutants.py

Compiles a copy of lean/DsrgRank/ClosedNeighbourhood.lean with one statement changed at a time; exit
code 0 when the unchanged copy compiles and every mutated copy fails. Needs the Lean build.
"""
from __future__ import annotations

import subprocess
import sys
import tempfile
from pathlib import Path

HERE = Path(__file__).resolve().parent
ROOT = HERE.parent
SRC = ROOT / "lean" / "DsrgRank" / "ClosedNeighbourhood.lean"

MUTANTS = {
    "none": [],
    "bound-plus-one": [(
        "    2 * k - t ≤ (Module.finrank ℝ (eigA n A θ') : ℤ) := by",
        "    2 * k - t + 1 ≤ (Module.finrank ℝ (eigA n A θ') : ℤ) := by")],
    "r-one-strict": [(
        "    (2 * k - t) * (mu + 2) ≤ k + n - 1 := by",
        "    (2 * k - t) * (mu + 2) < k + n - 1 := by")],
    "no-clebsch": [(
        "theorem ClosedNbhd_no_50_11_7_0_3 (A : Mat) : ¬ IsDSRG 50 A 11 7 0 3 := by",
        "theorem ClosedNbhd_no_50_11_7_0_3 (A : Mat) : ¬ IsDSRG 16 A 5 5 0 2 := by")],
    "no-48": [(
        "theorem ClosedNbhd_no_50_11_7_0_3 (A : Mat) : ¬ IsDSRG 50 A 11 7 0 3 := by",
        "theorem ClosedNbhd_no_50_11_7_0_3 (A : Mat) : ¬ IsDSRG 48 A 9 5 0 2 := by")],
    "kernel-no-poly": [(
        "    (hpoly : θ ^ 3 - (t : ℝ) * θ - (mu : ℝ) * ((k : ℝ) - t) ≠ 0) {u : Fin n → ℝ}",
        "    {u : Fin n → ℝ}")],
}


def run(name: str, workdir: Path) -> tuple[int, str]:
    text = SRC.read_text(encoding="utf-8")
    for old, new in MUTANTS[name]:
        if text.count(old) != 1:
            return 2, f"mutant line not found exactly once: {old!r}"
        text = text.replace(old, new)
    copy = workdir / f"ClosedNbhd_{name.replace('-', '_')}.lean"
    copy.write_text(text, encoding="utf-8")
    proc = subprocess.run(["lake", "-d", str(ROOT / "lean"), "env", "lean", str(copy)],
                          capture_output=True, text=True, encoding="utf-8", errors="replace",
                          stdin=subprocess.DEVNULL, timeout=230)
    out = (proc.stdout + proc.stderr).strip().splitlines()
    first = next((ln for ln in out if "error" in ln), out[0] if out else "")
    first = first.replace(str(copy), copy.name)
    return proc.returncode, first


def main(argv: list[str]) -> int:
    names = argv or list(MUTANTS)
    unknown = [n for n in names if n not in MUTANTS]
    if unknown:
        print(f"error: unknown mutants {unknown}, known {sorted(MUTANTS)}", file=sys.stderr)
        return 2
    bad = 0
    with tempfile.TemporaryDirectory(prefix="closed-nbhd-") as tmp:
        for name in names:
            code, first = run(name, Path(tmp))
            want_zero = name == "none"
            ok = (code == 0) if want_zero else (code not in (0, 2))
            verdict = ("control clean" if ok else "CONTROL RED") if want_zero else \
                ("caught" if ok else "SURVIVED")
            print(f"{name}: exit {code}, {verdict}" + (f"; {first}" if first else ""))
            bad += 0 if ok else 1
    print(f"unexpected outcomes: {bad}")
    return 1 if bad else 0


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
