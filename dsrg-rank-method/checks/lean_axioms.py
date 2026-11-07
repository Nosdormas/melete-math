"""Axioms of every theorem in the Lean modules of the paper.

Run from the root of the archive after the modules are built (`lake -d lean build`):

    python -X utf8 checks/lean_axioms.py [MODULE ...] [--mutate extra-axiom]

Without module arguments all modules of the project are checked. The mutant `extra-axiom` adds to the
generated Lean file an axiom `False` and a theorem `mutant_uses_axiom` proved from it; the program must then
end with exit code 1. For each module the program lists the
public `theorem` and `lemma` declarations of its source file, writes one Lean file that imports the modules
and runs `#print axioms` on every theorem, and runs it with `lake -d lean env lean`. It prints one line
per theorem with its axioms, then a JSON line with the number of theorems per module and the theorems that
depend on an axiom outside the standard set propext, Classical.choice, Quot.sound.

Exit code: 0 - every theorem depends only on standard axioms; 1 - some theorem depends on another axiom
(for example sorryAx, or an axiom declared in the sources); 2 - Lean failed or did not answer for some theorem.
"""
from __future__ import annotations

import json
import re
import shutil
import subprocess
import sys
import tempfile
from pathlib import Path

HERE = Path(__file__).resolve().parent
LEAN_DIR = HERE.parent / "lean"
MODULES = [
    "DsrgRank.Spectral",
    "DsrgRank.KernelFrame",
    "DsrgRank.LocalRank",
    "DsrgRank.ClosedNeighbourhood",
    "DsrgRank.LeftKernel",
    "DsrgRank.SchurComplement",
    "DsrgRank.ProfileBound",
    "DsrgRank.VertexRecovery",
    "DsrgRank.TwinClassesMuOne",
    "DsrgRank.TwinClasses",
    "DsrgRank.VertexFrame",
    "DsrgRank.Complement",
]
STANDARD = ("propext", "Classical.choice", "Quot.sound")


def module_theorems(module: str) -> list[str]:
    """Full names of the public theorems of a module, in file order, with nested namespaces."""
    path = LEAN_DIR / (module.replace(".", "/") + ".lean")
    if not path.is_file():
        raise SystemExit(f"no source file for {module}: {path}")
    names, spaces = [], []
    for line in path.read_text(encoding="utf-8").splitlines():
        if m := re.match(r"\s*namespace\s+(\S+)", line):
            spaces.append(m.group(1))
        elif (m := re.match(r"\s*end\s+(\S+)\s*$", line)) and spaces and spaces[-1] == m.group(1):
            spaces.pop()
        elif m := re.match(r"\s*(?:@\[[^\]]*\]\s*)*((?:(?:private|protected|nonrec)\s+)*)(?:theorem|lemma)\s+(\S+)", line):
            if "private" not in m.group(1).split():
                names.append(".".join([*spaces, m.group(2)]))
    return names


def parse_axioms(text: str) -> dict[str, list[str]]:
    """Output of `#print axioms`: theorem name -> its axioms; the list may wrap over lines."""
    found = {}
    for m in re.finditer(r"'(\S+)' depends on axioms: \[([^\]]*)\]", text):
        found[m.group(1)] = [a.strip() for a in m.group(2).split(",") if a.strip()]
    for m in re.finditer(r"'(\S+)' does not depend on any axioms", text):
        found[m.group(1)] = []
    return found


MUTANT = ("axiom mutant_false : False\n"
          "theorem mutant_uses_axiom : (1 : Nat) = 2 := mutant_false.elim\n")


def main(argv: list[str]) -> int:
    mutate = None
    if "--mutate" in argv:
        i = argv.index("--mutate")
        mutate = argv[i + 1] if i + 1 < len(argv) else None
        if mutate != "extra-axiom":
            print("--mutate takes extra-axiom", file=sys.stderr)
            return 2
        argv = argv[:i] + argv[i + 2:]
    modules = argv or MODULES
    names = {module: module_theorems(module) for module in modules}
    if mutate:
        names["mutant"] = ["mutant_uses_axiom"]
    lake = shutil.which("lake")
    if lake is None:
        print("lake is not on PATH", file=sys.stderr)
        return 2
    source = "".join(f"import {module}\n" for module in modules) + (MUTANT if mutate else "") + "".join(
        f"#print axioms {name}\n" for theorems in names.values() for name in theorems)
    with tempfile.TemporaryDirectory() as tmp:
        source_file = Path(tmp) / "Axioms.lean"
        source_file.write_text(source, encoding="utf-8", newline="\n")
        proc = subprocess.run([lake, "-d", str(LEAN_DIR), "env", "lean", str(source_file)],
                              capture_output=True, text=True, encoding="utf-8", errors="replace")
    found = parse_axioms(proc.stdout)
    missing = [name for theorems in names.values() for name in theorems if name not in found]
    if proc.returncode != 0 or missing:
        print((proc.stdout + proc.stderr).strip()[-2000:], file=sys.stderr)
        print(f"lake env lean: exit {proc.returncode}, no answer for {len(missing)} theorems", file=sys.stderr)
        return 2
    nonstandard = {}
    for theorems in names.values():
        for name in theorems:
            axioms = found[name]
            extra = [a for a in axioms if a not in STANDARD]
            if extra:
                nonstandard[name] = extra
            print(f"{name}: {', '.join(axioms) or 'no axioms'}" + (f"  NONSTANDARD: {', '.join(extra)}" if extra else ""))
    print(json.dumps({"modules": {m: len(t) for m, t in names.items()}, "nonstandard": nonstandard}))
    return 1 if nonstandard else 0


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
