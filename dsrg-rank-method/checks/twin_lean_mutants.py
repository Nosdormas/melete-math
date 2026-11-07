"""Mutated statements of the Lean modules on twin classes must be rejected by Lean.

    python -X utf8 checks/twin_lean_mutants.py [--only NAME,NAME...] [--no-base]

Copies a module into a temporary folder, changes one line and compiles the copy; a mutant counts as caught
when the copy fails and the same copy without the change compiles. Needs the Lean build.
"""

from __future__ import annotations

import argparse
import os
import shutil
import subprocess
import sys
import tempfile

ROOT = os.path.abspath(os.path.join(os.path.dirname(__file__), ".."))
MU1_SRC = "lean/DsrgRank/TwinClassesMuOne.lean"
ROWS_SRC = "lean/DsrgRank/TwinClasses.lean"
EXAMPLES = "checks/twin_examples.lean"

MUTANTS = [
    ("rows-upper-minus", ROWS_SRC,
     "(htk : t < k) (x : Fin n) :\n    ((rowCl A x).card : Int) ≤ k - lam - 1 + mu := by",
     "(htk : t < k) (x : Fin n) :\n    ((rowCl A x).card : Int) ≤ k - lam - 2 + mu := by",
     "Twin_upper: a ≤ k − λ − 2 + μ (false on (16, 7, 5, 4, 2))"),
    ("rows-cond-strict", ROWS_SRC,
     "    (lam + 2 - mu) ^ 2 ≤ mu * ((n : Int) - 1 - k) := by",
     "    (lam + 2 - mu) ^ 2 < mu * ((n : Int) - 1 - k) := by",
     "Twin_cond: strict inequality (false on (8, 3, 2, 1, 1))"),
    ("rows-no-16", ROWS_SRC,
     "theorem Twin_no_80_19_13_12_2 (A : Mat) : ¬ IsDSRG 80 A 19 13 12 2 := by",
     "theorem Twin_no_80_19_13_12_2 (A : Mat) : ¬ IsDSRG 16 A 7 5 4 2 := by",
     "Twin_no_80_19_13_12_2 applied to the constructed (16, 7, 5, 4, 2)"),
    ("mu1-free-thr1", MU1_SRC,
     "    (hl : 3 ≤ lam) (x : Fin n) : 2 ≤ (rowCl A x).card := by",
     "    (hl : 1 ≤ lam) (x : Fin n) : 2 ≤ (rowCl A x).card := by",
     "TwinMuOne_free_twin: threshold λ ≥ 1 (false on (15, 4, 2, 1, 1))"),
    ("mu1-family-thr3", MU1_SRC,
     "    (hl : 4 ≤ lam) (hrow : ∀ z : Fin n, 2 ≤ (rowCl A z).card)",
     "    (hl : 3 ≤ lam) (hrow : ∀ z : Fin n, 2 ≤ (rowCl A z).card)",
     "TwinMuOne_family: threshold λ ≥ 3 (false on W(2))"),
    ("mu1-no-45", MU1_SRC,
     "theorem TwinMuOne_no_66_10_5_4_1 (A : Mat) : ¬ IsDSRG 66 A 10 5 4 1 := fun h =>",
     "theorem TwinMuOne_no_66_10_5_4_1 (A : Mat) : ¬ IsDSRG 45 A 8 4 3 1 := fun h =>",
     "TwinMuOne_no_66_10_5_4_1 applied to the constructed (45, 8, 4, 3, 1)"),
    ("mu1-class-minus", MU1_SRC,
     "      k + 1 - (rowCl A x).card ∧ ((rowCl A x).card : Int) ≤ lam + 1 := by",
     "      k - (rowCl A x).card ∧ ((rowCl A x).card : Int) ≤ lam + 1 := by",
     "TwinMuOne_class: a(λ + 2 − a) ≤ k − a (false on (8, 3, 2, 1, 1))"),
    ("example-a16", EXAMPLES,
     "theorem a16 : (rowCl A16 (0 : Fin 16)).card = 4 := by decide +kernel",
     "theorem a16 : (rowCl A16 (0 : Fin 16)).card = 3 := by decide +kernel",
     "test: false class size 3 for (16, 7, 5, 4, 2)"),
    ("example-w2-params", EXAMPLES,
     "theorem h45 : IsDSRG 45 A45 8 4 3 1 := by",
     "theorem h45 : IsDSRG 45 A45 8 4 2 1 := by",
     "test: W(2) with λ = 2 instead of 3"),
]


def compile_copy(src_rel, old, new, work):
    with open(os.path.join(ROOT, src_rel), encoding="utf8") as fh:
        text = fh.read()
    if old is not None:
        if text.count(old) != 1:
            return None, f"mutant line found {text.count(old)} times"
        text = text.replace(old, new)
    path = os.path.join(work, os.path.basename(src_rel))
    with open(path, "w", encoding="utf8") as fh:
        fh.write(text)
    r = subprocess.run(["lake", "-d", os.path.join(ROOT, "lean"), "env", "lean", path],
                       capture_output=True, text=True, encoding="utf8", cwd=ROOT, stdin=subprocess.DEVNULL)
    err = next((ln.split("error:", 1)[1].strip() for ln in r.stdout.splitlines() + r.stderr.splitlines()
                if "error:" in ln), "")
    return r.returncode, err


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--only", default=None)
    ap.add_argument("--no-base", action="store_true")
    args = ap.parse_args()
    only = set(args.only.split(",")) if args.only else None
    work = tempfile.mkdtemp(prefix="twin_mutants_")
    bad = 0
    base_done = set()
    for name, rel, old, new, what in MUTANTS:
        if only and name not in only:
            continue
        if rel not in base_done and not args.no_base:
            code, err = compile_copy(rel, None, None, work)
            print(f"copy without the change {rel}: exit {code}" + (f" — {err}" if code else ""), flush=True)
            base_done.add(rel)
            if code != 0:
                bad += 1
        code, err = compile_copy(rel, old, new, work)
        caught = code not in (0, None)
        print(f"{name}: {what} — {'caught' if caught else 'NOT CAUGHT'}, exit {code}; {err[:160]}", flush=True)
        if not caught:
            bad += 1
    shutil.rmtree(work, ignore_errors=True)
    print(f"uncaught mutants and red bases: {bad}")
    return 1 if bad else 0


if __name__ == "__main__":
    sys.exit(main())
