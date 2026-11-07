"""SAT formulas for μ = 1, t = λ + 1: a free vertex and every vertex with twins.
"""
from __future__ import annotations

import json
import multiprocessing as mp
import os
import sys
import time
from itertools import combinations
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / "lib"))
sys.path.insert(0, str(ROOT / "lib"))
sys.path.insert(0, str(ROOT / "lib"))

import dsrg_search as ds  # noqa: E402

DRAT_TRIM = Path(os.environ.get("DRAT_TRIM") or "drat-trim")


class InputError(ValueError):
    pass


def row_free_clauses(pool, a, v):
    cl = []
    for y in range(1, v):
        diffs = []
        for j in range(1, v):
            if j == y:
                continue
            r = pool.id(("free-diff", y, j))
            cl += [[-r, a(y, j), a(0, j)], [-r, -a(y, j), -a(0, j)]]
            diffs.append(r)
        cl.append([-a(y, 0), -a(0, y)] + diffs)
    return cl


def twinned_clauses(pool, a, v, pairs=False):
    cl = []
    for kind in ("R", "C"):
        eq = {}
        for y, z in combinations(range(v), 2):
            e = pool.id(("twin", kind, y, z))
            eq[(y, z)] = eq[(z, y)] = e
            cl += [[-e, a(y, z)], [-e, a(z, y)]]
            diffs = []
            for j in range(v):
                if j in (y, z):
                    continue
                p, q = (a(y, j), a(z, j)) if kind == "R" else (a(j, y), a(j, z))
                cl += [[-e, -p, q], [-e, p, -q]]
                if pairs:
                    d = pool.id(("twin-diff", kind, y, z, j))
                    cl += [[-d, p, q], [-d, -p, -q]]
                    diffs.append(d)
            if pairs:
                cl.append([e, -a(y, z), -a(z, y)] + diffs)
        for y in range(v):
            cl.append([eq[(y, z)] for z in range(v) if z != y])
            if pairs:
                others = [z for z in range(v) if z != y]
                for z1, z2 in combinations(others, 2):
                    cl.append([-eq[(y, z1)], -eq[(y, z2)]])
    return cl


def frame_clauses(a, params, ins):
    k = params[1]
    return [[a(z, y)] if z in ins[y] else [-a(z, y)]
            for y in range(k + 1) for z in range(k + 1) if z != y]


def frame_labeling(A, x, t):
    v = len(A)
    out = [j for j in range(v) if A[x][j]]
    mutual = [j for j in out if A[j][x]]
    one_way = [j for j in out if not A[j][x]]
    ins = [j for j in range(v) if A[j][x] and not A[x][j]]
    rest = [j for j in range(v) if j != x and j not in out and j not in ins]
    if len(mutual) != t:
        raise InputError(f"vertex {x} mutual neighbours {len(mutual)}, not t = {t}")
    return [x] + mutual + one_way + ins + rest


def graph_clauses(a, A, x, t):
    order = frame_labeling(A, x, t)
    v = len(A)
    return [[a(i, j)] if A[order[i]][order[j]] else [-a(i, j)]
            for i in range(v) for j in range(v) if i != j]


def formula(params, mode, frame=None, graph=None):
    v, k, t, lam, mu = params
    if mu != 1 or t != lam + 1:
        raise InputError(f"μ = 1 and t = λ + 1 are needed, not {params}")
    pool, a, clauses = ds.encode(params, symmetry=True)
    if mode == "free":
        clauses += row_free_clauses(pool, a, v)
    elif mode in ("twinned", "pairs"):
        clauses += twinned_clauses(pool, a, v, pairs=(mode == "pairs"))
    else:
        raise InputError(f"unknown mode {mode}")
    if frame is not None:
        clauses += frame_clauses(a, params, frame)
    if graph is not None:
        clauses += graph_clauses(a, graph[0], graph[1], t)
    return pool, a, clauses


def _solve(q, params, mode, frame, graph, prove_dir, keep):
    t0 = time.time()
    pool, a, clauses = formula(params, mode, frame, graph)
    q.put({"vars": pool.top, "clauses": len(clauses)})
    if prove_dir is None:
        from pysat.solvers import Solver
        with Solver(name="cadical195", bootstrap_with=clauses) as s:
            r = s.solve()
        q.put({"result": "SAT" if r else "UNSAT", "solve_s": round(time.time() - t0, 2)})
        return
    q.put(prove(params, mode, pool, clauses, Path(prove_dir), keep))


def prove(params, mode, pool, clauses, out_dir, keep=False):
    import sat_certificate
    from solver_release import proof_solver
    out_dir = out_dir.resolve()
    out_dir.mkdir(parents=True, exist_ok=True)
    name = f"{mode}-" + "-".join(map(str, params))
    cnf, drat = out_dir / (name + ".cnf"), out_dir / (name + ".drat")
    rec = {"cnf_sha256": sat_certificate.write_dimacs(cnf, pool.top, clauses)}
    ts = time.time()
    with proof_solver("cadical195", with_proof=True) as s:
        s.append_formula(clauses)
        r = s.solve()
        rec["solve_s"] = round(time.time() - ts, 2)
        if r:
            rec["result"] = "SAT"
            return rec
        rec["result"] = "UNSAT"
        import pysolvers
        pysolvers.flushpr(s.solver.prfp)
        fh = s.solver.prfile
        fh.seek(0)
        rec["drat_sha256"] = sat_certificate.write_drat_from_binary(drat, fh)
    rec["drat_bytes"] = drat.stat().st_size
    tc = time.time()
    res = sat_certificate.certify(cnf, drat, DRAT_TRIM, timeout=3000)
    rec["certify"] = {"verified": res["verified"], "drat_trim": res["drat_trim"].get("status"),
                      "lrat_ok": res["lrat"].get("ok"), "lrat_steps": res["lrat"].get("steps")}
    rec["certify_s"] = round(time.time() - tc, 2)
    rec["files_kept"] = bool(keep or not res["verified"])
    if not rec["files_kept"]:
        for f in (cnf, drat, drat.with_suffix(".lrat")):
            if f.exists():
                f.unlink()
    return rec


def run(params, mode, seconds=200, frame=None, graph=None, prove_dir=None, keep=False):
    q = mp.Queue()
    p = mp.Process(target=_solve, args=(q, params, mode, frame, graph, prove_dir, keep))
    t0 = time.monotonic()
    p.start()
    rec = {"params": list(params), "mode": mode, "result": "TIMEOUT"}
    while time.monotonic() - t0 < seconds:
        try:
            msg = q.get(timeout=1)
        except Exception:
            if not p.is_alive():
                rec["result"] = "CRASH"
                break
            continue
        rec.update(msg)
        if "result" in msg:
            break
    if p.is_alive():
        p.kill()
    p.join()
    rec["elapsed_s"] = round(time.monotonic() - t0, 1)
    return rec


# ---------- CLI ----------


