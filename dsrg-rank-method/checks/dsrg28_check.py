"""No DSRG (28, 6, 3, 2, 1): the formulas of the free-vertex case and of the case without free
vertices, their controls on known graphs, the solver with DRAT proofs checked by drat-trim and by our
LRAT checker, and the parity case.

    "$SOLVER_PYTHON" -X utf8 checks/dsrg28_check.py [--mutate no-free|no-paths|no-twinned|block-plus] [--skip-proof]

drat-trim is taken from the environment variable DRAT_TRIM or from PATH. Exit code 0 - no violations; a
mutant must end with exit code 1.
"""
from __future__ import annotations

import argparse
import importlib.util
import json
import sys
import tempfile
import time
from pathlib import Path

HERE = Path(__file__).resolve().parent
ROOT = HERE.parent
sys.path.insert(0, str(ROOT / "lib"))
sys.path.insert(0, str(ROOT / "lib"))

import dsrg_graphs  # noqa: E402
import dsrg_verify  # noqa: E402
import mu_one_frames as mf  # noqa: E402
import mu_one_sat as ms  # noqa: E402

MUTATIONS = ("no-free", "no-twinned", "no-paths", "block-plus")
CELL = (28, 6, 3, 2, 1)


def flag_gq21():
    spec = importlib.util.spec_from_file_location("twin_mu1_check", ROOT / "checks/twin_mu1_check.py")
    mod = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(mod)
    for g in mod.built_graphs():
        if g["id"].startswith("flags GQ(2, 1)"):
            return g["A"]
    raise SystemExit("flag graph of GQ(2, 1) not built")


def verified(A, p):
    if not dsrg_verify.check(A, p).ok:
        raise SystemExit(f"control graph {p} failed verify")
    return A


def solve_here(params, mode, graph=None):
    from pysat.solvers import Solver
    pool, a, clauses = ms.formula(params, mode, None, graph)
    v = params[0]
    with Solver(name="cadical195", bootstrap_with=clauses) as s:
        if not s.solve():
            return "UNSAT", None
        model = set(x for x in s.get_model() if x > 0)
    return "SAT", [[1 if i != j and a(i, j) in model else 0 for j in range(v)] for i in range(v)]


def _no_paths(orig):
    def encode(params, symmetry=True, **kw):
        pool, a, cl = orig(params, symmetry, **kw)
        pv = {i for key, i in pool.obj2id.items() if isinstance(key, tuple) and key and key[0] == "p"}
        return pool, a, [c for c in cl if not any(abs(x) in pv for x in c)]
    return encode


def _block_plus(params, ins):
    ok, a, why = ORIG_FRAME_OK(params, ins)
    if ok:
        n, W = mf.counts(params, ins)
        if any(w and w < params[3] + 2 for w in W[1:]):
            return False, None, "block-plus"
    return ok, a, why


ORIG_FRAME_OK = mf.frame_ok


def main(args) -> int:
    if args.mutate == "no-free":
        ms.row_free_clauses = lambda pool, a, v: []
    if args.mutate == "no-twinned":
        ms.twinned_clauses = lambda pool, a, v, pairs=False: []
    if args.mutate == "no-paths":
        ms.ds.encode = _no_paths(ms.ds.encode)
    if args.mutate == "block-plus":
        mf.frame_ok = _block_plus
    p18, p54 = mf.lift_params(3, 1), mf.lift_params(3, 2)
    lift18 = verified(mf.lift(mf.kautz(1), 3), p18)
    lift54 = verified(mf.lift(mf.kautz(2), 3), p54)
    lift18t = verified([list(r) for r in zip(*lift18)], p18)
    F18 = verified(flag_gq21(), p18)
    controls = [
        ("free", p54, (lift54, 5), "SAT", "lift (54), vertex 5"),
        ("free", p18, (lift18t, 0), "UNSAT", "transposed lift (18), vertex 0"),
        ("twinned", p18, (F18, 0), "SAT", "flags GQ(2, 1), vertex 0"),
        ("twinned", p54, (lift54, 0), "UNSAT", "lift (54), vertex 0"),
        ("free", (15, 4, 2, 1, 1), None, "SAT", "without graph"),
        ("free", (24, 5, 2, 1, 1), None, "SAT", "without graph"),
    ]
    bad = []
    print("formulas:")
    for mode, p, graph, want, label in controls:
        t0 = time.time()
        got, model = solve_here(p, mode, graph)
        note = ""
        if graph is None and got == "SAT":
            rep = dsrg_verify.check(model, p)
            note = f", verify of models: {'OK' if rep.ok else rep.violation}"
            if not rep.ok:
                bad.append(f"formula {mode} {p} {label}: model is not a DSRG ({rep.violation})")
        print(f"  {mode} {p} {label}: {got} (expected {want}){note}, {time.time() - t0:.1f} s")
        if got != want:
            bad.append(f"formula {mode} {p} {label}: {got} instead of {want}")
    print("proof:")
    if args.skip_proof:
        print("  skipped (--skip-proof)")
    else:
        with tempfile.TemporaryDirectory(prefix="dsrg28-") as tmp:
            for mode in ("free", "twinned"):
                rec = ms.run(CELL, mode, seconds=230, prove_dir=tmp)
                print("  " + json.dumps(rec, ensure_ascii=False))
                if rec.get("result") != "UNSAT" or not rec.get("certify", {}).get("verified"):
                    bad.append(f"proof {mode}: {rec.get('result')}")
    print("parity:")
    K = CELL[1] + 1
    labeled, cls = mf.pair_frames(CELL)
    print(f"  K = {K}, frames under the selection of item 4 of the frame lemma: {labeled}")
    if K % 2 == 0 or labeled:
        bad.append("parity: K is even or frames under the selection of item 4 exist")
    ctl, _ = mf.pair_frames((8, 3, 2, 1, 1))
    print(f"  selection control: (8, 3, 2, 1, 1) — frames under the selection of item 4 {ctl} (expected 1)")
    if ctl != 1:
        bad.append(f"parity: the selection control (8, 3, 2, 1, 1) gave {ctl} frames instead of 1")
    comp = dsrg_graphs.complement_params(CELL)
    print(f"complement: {comp}")
    if tuple(comp) != (28, 21, 18, 15, 18):
        bad.append(f"complement {comp}")
    print(f"violations: {len(bad)}")
    for line in bad:
        print("  " + line)
    if args.mutate:
        print(f"mutant {args.mutate}: {'caught' if bad else 'NOT caught'}")
    return 1 if bad else 0


if __name__ == "__main__":
    ap = argparse.ArgumentParser()
    ap.add_argument("--mutate", choices=MUTATIONS)
    ap.add_argument("--skip-proof", action="store_true")
    sys.exit(main(ap.parse_args()))
