
import hashlib
import json
import subprocess
import sys
import time
from dataclasses import dataclass, field
from pathlib import Path

_HELP = """usage: sat_certificate.py lrat FORMULA.cnf PROOF.lrat
       sat_certificate.py certify FORMULA.cnf PROOF.drat --drat-trim PATH [--lrat-out FILE] [--timeout S]

Checks an unsatisfiability certificate of a DIMACS formula.
  lrat      own check of an LRAT proof: every lemma is derived by a chain of
            unit propagations along the hints, the last lemma is the empty clause
  certify   drat-trim checks the DRAT proof and writes LRAT, then the own LRAT check;
            accepted only if both checks agree

  --drat-trim PATH   drat-trim executable
  --lrat-out FILE    where drat-trim writes LRAT; by default next to the DRAT file, extension .lrat
  --timeout S        drat-trim limit in seconds, 600 by default
  -h, --help         help

Exit codes: 0 — accepted, 1 — not accepted, 2 — input error.
"""


class InputError(ValueError):
    pass


@dataclass
class Report:

    ok: bool
    steps: int = 0
    reason: str | None = None
    line: int | None = None
    extra: dict = field(default_factory=dict)


def sha256_file(path):
    digest = hashlib.sha256()
    with open(path, "rb") as fh:
        for chunk in iter(lambda: fh.read(1 << 20), b""):
            digest.update(chunk)
    return digest.hexdigest()


def write_dimacs(path, nvars, clauses):
    path = Path(path)
    with open(path, "w", encoding="ascii", newline="\n") as fh:
        fh.write(f"p cnf {nvars} {len(clauses)}\n")
        for clause in clauses:
            fh.write(" ".join(map(str, clause)))
            fh.write(" 0\n" if clause else "0\n")
    return sha256_file(path)


def write_drat(path, lines):
    path = Path(path)
    with open(path, "w", encoding="ascii", newline="\n") as fh:
        for line in lines:
            fh.write(line)
            fh.write("\n")
    return sha256_file(path)


def drat_binary_to_text(src, dst):
    out, lits, num, shift, mode, steps = [], [], 0, 0, None, 0
    while True:
        chunk = src.read(1 << 20)
        if not chunk:
            break
        for byte in chunk:
            if mode is None:
                if byte == 0x61:
                    mode = ""
                elif byte == 0x64:
                    mode = "d "
                else:
                    raise InputError(f"binary DRAT: unexpected byte {byte:#04x} at the start of a step {steps + 1}")
                continue
            num |= (byte & 0x7F) << shift
            if byte & 0x80:
                shift += 7
                continue
            if num == 0:
                out.append(mode + " ".join(lits) + (" 0\n" if lits else "0\n"))
                lits, mode = [], None
                steps += 1
            else:
                lits.append(str(-(num >> 1)) if num & 1 else str(num >> 1))
            num, shift = 0, 0
        dst.write("".join(out))
        out = []
    if mode is not None or shift:
        raise InputError(f"binary DRAT cut in the middle of a step {steps + 1}")
    return steps


def write_drat_from_binary(path, src):
    path = Path(path)
    with open(path, "w", encoding="ascii", newline="\n") as fh:
        drat_binary_to_text(src, fh)
    return sha256_file(path)


def read_dimacs(lines):
    nvars, declared, clauses, current = None, None, [], []
    for number, raw in enumerate(lines, 1):
        text = raw.strip()
        if not text or text.startswith("c"):
            continue
        if text.startswith("p"):
            parts = text.split()
            if nvars is not None or len(parts) != 4 or parts[1] != "cnf":
                raise InputError(f"DIMACS, line {number}: invalid header «{text}»")
            try:
                nvars, declared = int(parts[2]), int(parts[3])
            except ValueError:
                raise InputError(f"DIMACS, line {number}: invalid header «{text}»") from None
            continue
        if nvars is None:
            raise InputError(f"DIMACS, line {number}: clause before the header p cnf")
        for token in text.split():
            try:
                lit = int(token)
            except ValueError:
                raise InputError(f"DIMACS, line {number}: not an integer «{token}»") from None
            if lit == 0:
                clauses.append(tuple(current))
                current = []
            elif abs(lit) > nvars:
                raise InputError(f"DIMACS, line {number}: variable {abs(lit)} exceeds {nvars}")
            else:
                current.append(lit)
    if nvars is None:
        raise InputError("DIMACS: no header p cnf")
    if current:
        raise InputError("DIMACS: the last clause is not closed by zero")
    if len(clauses) != declared:
        raise InputError(f"DIMACS: declared {declared} clauses, read {len(clauses)}")
    return nvars, clauses


def _ints(tokens, number):
    try:
        return [int(t) for t in tokens]
    except ValueError:
        raise InputError(f"LRAT, line {number}: not an integer") from None


def check_lrat(clauses, lines):
    db = {i: c for i, c in enumerate(clauses, 1)}
    last = len(clauses)
    steps = 0
    for number, raw in enumerate(lines, 1):
        text = raw.strip()
        if not text or text.startswith("c"):
            continue
        tokens = text.split()
        if len(tokens) >= 2 and tokens[1] == "d":
            ids = _ints(tokens[2:], number)
            if not ids or ids[-1] != 0:
                raise InputError(f"LRAT, line {number}: deletion not closed by zero")
            for cid in ids[:-1]:
                if db.pop(cid, None) is None:
                    return Report(False, steps, f"deletion of a missing clause {cid}", number)
            continue
        nums = _ints(tokens, number)
        cid = nums[0]
        try:
            z1 = nums.index(0, 1)
            z2 = nums.index(0, z1 + 1)
        except ValueError:
            raise InputError(f"LRAT, line {number}: step not closed by two zeros") from None
        if z2 != len(nums) - 1:
            raise InputError(f"LRAT, line {number}: extra numbers after the second zero")
        lemma, hints = nums[1:z1], nums[z1 + 1:z2]
        if cid <= last:
            return Report(False, steps, f"lemma number {cid} is not greater than the previous {last}", number)
        value = {}
        for lit in lemma:
            if value.get(-lit) is False:
                value = None
                break
            value[lit] = False
            value[-lit] = True
        if value is None:
            reason = _rup_fail(lemma, hints, db, tautology=True)
        else:
            reason = _rup_fail(lemma, hints, db, value=value)
        if reason is not None:
            return Report(False, steps, reason, number)
        steps += 1
        if not lemma:
            return Report(True, steps)
        db[cid] = tuple(lemma)
        last = cid
    return Report(False, steps, "the empty clause is not derived")


def _rup_fail(lemma, hints, db, value=None, tautology=False):
    if tautology:
        return None
    for h in hints:
        if h < 0:
            return f"hint {h}: RAT steps are not supported"
        clause = db.get(h)
        if clause is None:
            return f"hint {h}: the clause is missing or deleted"
        free = None
        for lit in clause:
            val = value.get(lit)
            if val is True:
                return f"hint {h}: the clause is already satisfied"
            if val is None:
                if free is not None and free != lit:
                    return f"hint {h}: two unassigned literals in the clause"
                free = lit
        if free is None:
            return None
        value[free] = True
        value[-free] = False
    return "the hints did not lead to a conflict"


def check_lrat_files(cnf_path, lrat_path):
    with open(cnf_path, encoding="ascii") as fh:
        _, clauses = read_dimacs(fh)
    with open(lrat_path, encoding="ascii") as fh:
        return check_lrat(clauses, fh)


def run_drat_trim(binary, cnf_path, drat_path, lrat_path=None, timeout=600):
    cmd = [str(binary), str(cnf_path), str(drat_path), "-t", str(int(timeout))]
    if lrat_path is not None:
        cmd += ["-L", str(lrat_path)]
    started = time.perf_counter()
    try:
        proc = subprocess.run(cmd, capture_output=True, text=True, timeout=timeout + 30)
    except FileNotFoundError:
        raise InputError(f"drat-trim not found: {binary}") from None
    except subprocess.TimeoutExpired:
        return {"verified": False, "status": "TIMEOUT", "seconds": round(time.perf_counter() - started, 2)}
    status = [ln[2:].strip() for ln in proc.stdout.splitlines() if ln.startswith("s ")]
    return {
        "verified": status == ["VERIFIED"],
        "status": status[-1] if status else "NO-ANSWER",
        "seconds": round(time.perf_counter() - started, 2),
    }


def certify(cnf_path, drat_path, drat_trim, lrat_path=None, timeout=600):
    cnf_path, drat_path = Path(cnf_path), Path(drat_path)
    lrat_path = Path(lrat_path) if lrat_path else drat_path.with_suffix(".lrat")
    out = {
        "cnf_sha256": sha256_file(cnf_path),
        "drat_sha256": sha256_file(drat_path),
        "drat_trim": run_drat_trim(drat_trim, cnf_path, drat_path, lrat_path, timeout),
    }
    if lrat_path.exists():
        out["lrat_sha256"] = sha256_file(lrat_path)
        started = time.perf_counter()
        proc = subprocess.run(
            [sys.executable, "-X", "utf8", str(Path(__file__).resolve()), "lrat", str(cnf_path), str(lrat_path)],
            capture_output=True, text=True,
        )
        try:
            own = json.loads(proc.stdout.strip().splitlines()[-1])
        except (IndexError, json.JSONDecodeError):
            own = {"ok": False, "reason": f"LRAT check failed: {proc.stderr.strip()[-300:]}"}
        own["seconds"] = round(time.perf_counter() - started, 2)
        out["lrat"] = own
    else:
        out["lrat"] = {"ok": False, "reason": "drat-trim did not write LRAT"}
    out["verified"] = bool(out["drat_trim"]["verified"] and out["lrat"].get("ok"))
    return out


def _parse_argv(argv):
    if not argv:
        raise InputError("a command is needed: lrat or certify")
    command, rest = argv[0], argv[1:]
    if command not in ("lrat", "certify"):
        raise InputError(f"unknown command {command}")
    positional, opts = [], {"drat-trim": None, "lrat-out": None, "timeout": 600.0}
    i = 0
    while i < len(rest):
        arg = rest[i]
        if arg in ("--drat-trim", "--lrat-out", "--timeout") and command == "certify":
            if i + 1 >= len(rest) or rest[i + 1].startswith("-"):
                raise InputError(f"{arg}: the flag needs a value")
            value = rest[i + 1]
            if arg == "--timeout":
                try:
                    value = float(value)
                except ValueError:
                    value = 0.0
                if not value > 0:
                    raise InputError(f"--timeout: a positive number of seconds is needed, got «{rest[i + 1]}»")
            opts[arg[2:]] = value
            i += 2
            continue
        if arg.startswith("-"):
            raise InputError(f"unknown flag {arg}")
        positional.append(arg)
        i += 1
    if len(positional) != 2:
        raise InputError(f"two files are needed — the formula and the proof, got: {len(positional)}")
    if command == "certify" and opts["drat-trim"] is None:
        raise InputError("certify: --drat-trim PATH is needed")
    for p in positional:
        if not Path(p).is_file():
            raise InputError(f"no file {p}")
    return command, positional, opts


def main(argv):
    if argv in (["-h"], ["--help"]):
        sys.stdout.write(_HELP)
        return 0
    try:
        command, (cnf, proof), opts = _parse_argv(argv)
        if command == "lrat":
            started = time.perf_counter()
            report = check_lrat_files(cnf, proof)
            out = {"ok": report.ok, "steps": report.steps, "reason": report.reason, "line": report.line,
                   "seconds": round(time.perf_counter() - started, 2)}
            ok = report.ok
        else:
            out = certify(cnf, proof, opts["drat-trim"], opts["lrat-out"], opts["timeout"])
            ok = out["verified"]
    except InputError as exc:
        print(f"sat_certificate: input error: {exc}", file=sys.stderr)
        return 2
    print(json.dumps(out, ensure_ascii=False))
    return 0 if ok else 1


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
