"""Search of the theorem on (48, 9, 5, 0, 2), second program: one SAT formula per pivot orbit.

    "$SOLVER_PYTHON" -X utf8 checks/search48_second.py cases
    "$SOLVER_PYTHON" -X utf8 checks/search48_second.py frame
    "$SOLVER_PYTHON" -X utf8 checks/search48_second.py selftest
    "$SOLVER_PYTHON" -X utf8 checks/search48_second.py control [--petersen] [--mutate pivot-sign|phi-delta|key-strict]
    "$SOLVER_PYTHON" -X utf8 checks/search48_second.py search --kind C8|2C4 [--part I/N | --orbits LIST] [--solver cadical
        [--proof-dir DIR --proof-orbits LIST|all [--discard-proofs] [--drat-timeout S]]]

cases - all 0/1 matrices Q → P of order 4 with degrees 2 and their classes C8 and 2C4; frame - the frame
of (48, 9, 5, 0, 2) in both cases; control - positive control on catalogue graphs with λ = 0, or with
--petersen on the Petersen graph, whose Schur complement at θ = 1 has rank 1 as for (48, 9, 5, 0, 2);
search - the closure, one formula per pivot orbit; with --proof-dir every listed orbit gets a DRAT
proof by CaDiCaL, checked by drat-trim and the LRAT checker, and --discard-proofs removes its files
after the check. Written without reading the first program; shares no
code with it.
"""
from __future__ import annotations

import argparse
import itertools
import os
import sys
import time
from fractions import Fraction as Fr

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))

import numpy as np  # noqa: E402

from search48_second_core import (SET48, Frame, apply_mask, cycle_structure, dsrg_params, frame_at,  # noqa: E402
                             frame_generators, frame_group, is_frame_automorphism, load_catalog_lambda0,
                             qp_case, rank, roots, two_regular_classes, type_orbits)
from search48_second_sat import Pivots, TypeTable, build_cnf, dense_ok, solve, solve_cadical  # noqa: E402
from search48_second_core import ROOT  # noqa: E402

FAIL = []


def fail(msg):
    FAIL.append(msg)
    print("VIOLATION:", msg, flush=True)


# ---------- cases ----------

def cmd_cases(args):
    total, classes = two_regular_classes()
    print(f"0/1 matrices 4 × 4 with row and column sums 2: {total}")
    for rep, size in classes:
        print(f"  class: {size} matrices, cycles of the graph Q ∪ P: {cycle_structure(rep)}")
    shapes = sorted(tuple(cycle_structure(rep)) for rep, _ in classes)
    if shapes != [(4, 4), (8,)]:
        fail(f"classes {shapes}, expected C8 and two C4")
    for kind in ("C8", "2C4"):
        cs = cycle_structure(qp_case(kind))
        print(f"  frame {kind}: cycles {cs}")
    if sum(s for _, s in classes) != total:
        fail("the classes do not cover all matrices")


# ---------- frame ----------

def phi_table(fr: Frame, u, v):
    role = lambda y: "M" if y in fr.M else ("Q" if y in fr.Q else "P")
    ru, rv = role(u), role(v)
    same = u == v
    if ru == "M":
        return {"M": 4 if same else 1, "Q": 1, "P": 2}[rv]
    if ru == "Q":
        if rv == "M":
            return 2
        if rv == "Q":
            return 5 if same else 2
        return 0 if fr.AN[u][v] else 2
    return {"M": 1, "Q": 1, "P": 5 if same else 2}[rv]


def frame48(kind, key_order="code"):
    fr = Frame(SET48, 1, qp_case(kind))
    tys = fr.all_types()
    gens, naut = frame_generators(fr)
    keys = type_orbits(fr, tys, gens)
    tt = TypeTable(fr, tys, np.array([keys[T] for T in tys], dtype=object))
    return fr, tys, gens, naut, keys, tt


def cmd_frame(args):
    for kind in ("C8", "2C4"):
        fr, tys, gens, naut, keys, tt = frame48(kind)
        print(f"== {kind}: |N'| = {fr.n - 1}, |W| = {fr.params[0] - fr.n}")
        bad = [(u, v) for u in fr.Np for v in fr.Np if fr.Phi[u][v] != phi_table(fr, u, v)]
        print(f"  Φ (A² by the equation minus paths through N) against the table of Φ: discrepancies {len(bad)}")
        if bad:
            fail(f"{kind}: Φ differs from the table of Φ in {bad[:5]}")
        outs = {r: sorted({fr.outW[y] for y in ys}) for r, ys in (("M", fr.M), ("Q", fr.Q), ("P", fr.P))}
        ins = {r: sorted({fr.inW[y] for y in ys}) for r, ys in (("M", fr.M), ("Q", fr.Q), ("P", fr.P))}
        print(f"  out-arcs to W: {outs}; in-arcs from W: {ins}")
        if outs != {"M": [8], "Q": [7], "P": [8]} or ins != {"M": [8], "Q": [8], "P": [7]}:
            fail(f"{kind}: degrees of N' in W are not as in the table of Φ")
        detD = rank(fr.D)
        print(f"  rank D = {detD} of {fr.n}; common denominator of D⁻¹ L = {fr.L}")
        Os = sorted({O for O, I in tys})
        Is = sorted({I for O, I in tys})
        qp = [(fr.Q[i], fr.P[j]) for i, j in fr.qp]
        nbad = 0
        for O in Os:
            ro = fr.row_vec(O)
            g = 1 + sum(1 for q in fr.Q if O >> q & 1)
            for I in Is:
                FL = int(sum(int(ro[y]) for y in fr.Np if I >> y & 1))
                h = 1 + sum(1 for p in fr.P if I >> p & 1)
                P2 = bin(O & I).count("1")
                P3 = sum(1 for q, p in qp if O >> q & 1 and I >> p & 1)
                if Fr(FL, fr.L) != Fr(g * h, 3) - P2 - P3:
                    nbad += 1
        print(f"  f by D⁻¹ against the formula for f on {len(Os)} × {len(Is)} pairs (O, I): discrepancies {nbad}")
        if nbad:
            fail(f"{kind}: the formula for f differs from D⁻¹")
        dvals = sorted({Fr(int(x), fr.L) for x in tt.dL})
        nonint = [d for d in dvals if (3 * d).denominator != 1]
        print(f"  types {len(tys)}; values of d: {len(dvals)} from {min(dvals)} to {max(dvals)}; 3d not an integer: {len(nonint)}")
        if nonint:
            fail(f"{kind}: 3d is not an integer")
        auts_ok = all(is_frame_automorphism(fr, g) for g in gens)
        full, _ = frame_group(fr)
        print(f"  |Aut(Q → P)| = {naut}; generators {len(gens)}, all are automorphisms of the frame: {auts_ok}; "
              f"|S_M × Aut| = {len(full)}")
        if not auts_ok:
            fail(f"{kind}: a generator is not an automorphism")
        import random
        random.seed(7)
        viol = 0
        for T in random.sample(tys, 2000):
            for g in full:
                U = (apply_mask(g, T[0]), apply_mask(g, T[1]))
                if keys.get(U) != keys[T]:
                    viol += 1
        print(f"  orbit key under the full group on 2000 types × {len(full)}: violations {viol}")
        if viol:
            fail(f"{kind}: the key is not constant on an orbit")
        orbs = {}
        for T, kk in keys.items():
            orbs.setdefault(kk, []).append(T)
        dconst = all(len({int(tt.dL[tt.index[T]]) for T in Ts}) == 1 for Ts in orbs.values())
        piv = [kk for kk, Ts in orbs.items() if tt.dL[tt.index[Ts[0]]] != 0]
        print(f"  type orbits {len(orbs)}, d constant on orbits: {dconst}; pivot orbits (d ≠ 0): {len(piv)}; "
              f"types with d = 0: {int((tt.dL == 0).sum())}")
        if not dconst:
            fail(f"{kind}: d is not constant on an orbit")


# ---------- selftest ----------

def cmd_selftest(args):
    import random
    for kind in ("C8", "2C4"):
        fr, tys, gens, naut, keys, tt = frame48(kind)
        random.seed(11 if kind == "C8" else 12)
        pivs = [i for i in range(len(tys)) if tt.dL[i] != 0]
        nb = ntest = npos = 0
        for i0 in random.sample(pivs, 6):
            pv = Pivots(tt, [i0], [[0]])
            cand = pv.candidates()
            cset = {(c[0], c[1], c[2]) for c in cand}
            sample = random.sample(sorted(cset), min(150, len(cset)))
            sample += [(random.randrange(len(tys)), (random.randint(0, 1),), (random.randint(0, 1),))
                       for _ in range(150)]
            for w, a, b in sample:
                if w == i0:
                    continue
                dn = dense_ok(tt, pv, w, a, b)
                sL = fr.L * b[0] - tt.FL(w, i0)
                tL = fr.L * a[0] - tt.FL(i0, w)
                minor = int(tt.dL[i0]) * int(tt.dL[w]) == sL * tL
                ntest += 1
                npos += (w, a, b) in cset
                if (dn and minor) != ((w, a, b) in cset):
                    nb += 1
        print(f"{kind}: candidate filter against the dense check of the subgraph N ∪ {{w0, w}} and the minor: "
              f"{ntest} triples ({npos} candidates), discrepancies {nb}")
        if nb:
            fail(f"{kind}: the filter differs from the dense check")


def assemble(pv: Pivots, cand, chosen):
    tt, fr = pv.tt, pv.tt.fr
    n, r = fr.n, pv.r
    m = n + r + len(chosen)
    A = [[0] * m for _ in range(m)]
    for i in range(n):
        for j in range(n):
            A[i][j] = fr.AN[i][j]

    def put(idx, ty):
        O, I = tt.types[ty]
        for y in fr.Np:
            A[idx][y] = O >> y & 1
            A[y][idx] = I >> y & 1

    for i in range(r):
        put(n + i, pv.piv[i])
        for j in range(r):
            A[n + i][n + j] = pv.arcs[i][j]
    for p, c in enumerate(chosen):
        w, a, b, s, t = cand[c]
        put(n + r + p, w)
        for i in range(r):
            A[n + i][n + r + p] = a[i]
            A[n + r + p][n + i] = b[i]
    adj = pv.adj
    for p, c in enumerate(chosen):
        for q, c2 in enumerate(chosen):
            if p == q:
                continue
            w, a, b, s, t = cand[c]
            w2, a2, b2, s2, t2 = cand[c2]
            num = tt.FL(w, w2) * pv.det
            if r:
                num += int(np.array(s, dtype=object).dot(adj).dot(np.array(t2, dtype=object)))
            val = Fr(num, fr.L * pv.det)
            if val not in (0, 1):
                return None
            A[n + r + p][n + r + q] = int(val)
    return A


class DsrgCheck:
    def __init__(self, pv, cand):
        self.pv, self.cand, self.nc = pv, cand, len(cand)
        self.good = 0
        self.bad = 0

    def __call__(self, model):
        chosen = [l - 1 for l in model if 0 < l <= self.nc]
        A = assemble(self.pv, self.cand, chosen)
        ok = A is not None and dsrg_params(A) == self.pv.tt.fr.params
        if ok:
            self.good += 1
            self.last = A
        else:
            self.bad += 1
        return ok


# ---------- control ----------

def petersen_graph():
    """The Petersen graph as a DSRG (10, 3, 3, 0, 1): the 2-subsets of a 5-set, arcs both ways between
    disjoint subsets. At θ = 1 the Schur complement outside N[x] has rank 1, and every outer vertex has
    d = -1/2."""
    vs = list(itertools.combinations(range(5), 2))
    A = [[int(not set(a) & set(b)) for b in vs] for a in vs]
    return [("petersen", dsrg_params(A), A)]


def exact_S(A, params, theta, order, W):
    v = len(A)
    Nn = order
    D = [[Fr(A[a][b]) - (theta if a == b else 0) for b in Nn] for a in Nn]
    from search48_second_core import inverse
    Di = inverse(D)
    B = [[A[a][w] for w in W] for a in Nn]
    C = [[A[w][a] for a in Nn] for w in W]
    CD = [[sum(C[i][z] * Di[z][j] for z in range(len(Nn))) for j in range(len(Nn))] for i in range(len(W))]
    F = [[sum(CD[i][z] * B[z][j] for z in range(len(Nn))) for j in range(len(W))] for i in range(len(W))]
    return [[Fr(A[W[i]][W[j]]) - (theta if i == j else 0) - F[i][j] for j in range(len(W))] for i in range(len(W))]


def cmd_control(args):
    mut = set(args.mutate.split(",")) if args.mutate else set()
    graphs = petersen_graph() if args.petersen else load_catalog_lambda0()
    seen = set()
    stats = dict(frames=0, types_missing=0, partners_missing=0, assembled_wrong=0, lost=0, found=0,
                 nondsrg=0, skipped=0, keyed=0)
    by_set = {}
    for name, params, A in graphs:
        key = tuple(map(tuple, A))
        if key in seen:
            continue
        seen.add(key)
        v = len(A)
        for theta in roots(params):
            for x in range(v):
                if theta == 0:
                    continue
                v_, k, t, lam, mu = params
                if theta ** 3 - t * theta - mu * (k - t) == 0:
                    continue
                fr, order, W, real = frame_at(A, params, x, theta)
                if "phi-delta" in mut:
                    thp = -mu - theta
                    for u in range(fr.n):
                        for w_ in range(fr.n):
                            fr.Phi[u][w_] += (theta - thp) * (fr.AN[u][w_] - (theta if u == w_ else 0))
                S = exact_S(A, params, theta, order, W)
                r = rank(S)
                rec = by_set.setdefault((params, theta, r), dict(frames=0, found=0))
                if r > args.max_rank:
                    stats["skipped"] += 1
                    continue
                stats["frames"] += 1
                rec["frames"] += 1
                tys = fr.all_types()
                tset = set(tys)
                miss = [T for T in real if T not in tset]
                if miss:
                    stats["types_missing"] += 1
                    stats["lost"] += 1
                    if not mut:
                        fail(f"{name} x={x} θ={theta}: types of real vertices missing from the list: {len(miss)}")
                    continue
                full, _ = frame_group(fr)
                keys = type_orbits(fr, tys, full)
                tt = TypeTable(fr, tys, np.array([keys[T] for T in tys], dtype=object))
                Wi = list(range(len(W)))
                d = [S[i][i] for i in Wi]
                g_used = None
                R = []
                key_min = None
                if r >= 1:
                    nz = [i for i in Wi if d[i] != 0]
                    i0 = min(nz, key=lambda i: (keys[real[i]], i))
                    for comb in itertools.combinations([i for i in Wi if i != i0], r - 1):
                        RR = [i0] + list(comb)
                        if rank([[S[a][b] for b in RR] for a in RR]) == r:
                            R = RR
                            break
                    if not R:
                        fail(f"{name} x={x} θ={theta}: no nonsingular principal block with a pivot")
                        continue
                    key_min = keys[real[i0]]
                    code = lambda T: (T[0] << 32) | T[1]
                    T0 = real[i0]
                    g_used = next(g for g in full if code((apply_mask(g, T0[0]), apply_mask(g, T0[1]))) == key_min)
                    stats["keyed"] += 1
                elif r == 0:
                    R = []
                gm = (lambda T: (apply_mask(g_used, T[0]), apply_mask(g_used, T[1]))) if g_used else (lambda T: T)
                realg = [gm(T) for T in real]
                if g_used is not None:
                    assert keys[realg[R[0]]] == key_min and code(realg[R[0]]) == key_min
                arcs = [[A[W[a]][W[b]] for b in R] for a in R]
                pv = Pivots(tt, [tt.index[realg[i]] for i in R], arcs)
                if not pv.ok:
                    fail(f"{name} x={x}: the pivot block fails the dense check")
                cand = pv.candidates(key_min=key_min if "no-key" not in mut else None, distinct=False)
                if "key-strict" in mut and key_min is not None:
                    cand = [c for c in cand if tt.dL[c[0]] == 0 or keys[tt.types[c[0]]] > key_min]
                partners = [i for i in Wi if i not in R]
                real_keys = [(tt.index[realg[i]], tuple(A[W[q]][W[i]] for q in R), tuple(A[W[i]][W[q]] for q in R))
                             for i in partners]
                mult = max([real_keys.count(k_) for k_ in real_keys] or [1])
                stats["max_mult"] = max(stats.get("max_mult", 1), mult)
                cand = [c for c in cand for _ in range(mult)]
                cidx = {}
                for j, c in enumerate(cand):
                    cidx.setdefault((c[0], c[1], c[2]), []).append(j)
                lits = []
                used = {}
                for k_ in real_keys:
                    js = cidx.get(k_)
                    u = used.get(k_, 0)
                    if js is None or u >= len(js):
                        lits = None
                        break
                    lits.append(js[u] + 1)
                    used[k_] = u + 1
                if lits is None:
                    stats["partners_missing"] += 1
                    stats["lost"] += 1
                    if not mut:
                        fail(f"{name} x={x} θ={theta}: a real partner failed the filter")
                    continue
                Aa = assemble(pv, cand, [l - 1 for l in lits])
                order_full = order + [W[i] for i in R] + [W[i] for i in partners]
                Areal = [[A[a][b] for b in order_full] for a in order_full]
                if g_used is not None:
                    order_new = list(order)
                    for y in fr.Np:
                        order_new[g_used[y]] = order[y]
                    order_full = order_new + [W[i] for i in R] + [W[i] for i in partners]
                    Areal = [[A[a][b] for b in order_full] for a in order_full]
                if Aa != Areal:
                    stats["assembled_wrong"] += 1
                    fail(f"{name} x={x}: assembly by the pivot formula differs from the graph")
                cl, cards, info = build_cnf(pv, cand, drop=mut, distinct=False)
                res, _ = solve(cl, cards, assumptions=lits)
                if res != "SAT":
                    stats["lost"] += 1
                    if not mut:
                        fail(f"{name} x={x} θ={theta}: the formula is unsatisfiable on the real graph")
                    continue
                chk = DsrgCheck(pv, cand)
                res2, models = solve(cl, cards, block_limit=args.block, check=chk)
                if res2 == "SAT":
                    stats["found"] += 1
                    rec["found"] += 1
                stats["nondsrg"] += chk.bad
    print("sets (set, θ, rank S): frames, DSRG solutions found")
    for (p, th, r), rec in sorted(by_set.items()):
        print(f"  {p}, θ = {th}, rank S = {r}: frames {rec['frames']}, DSRG solution found for {rec['found']}")
    print("total:", stats)
    if mut:
        if stats["lost"] == 0 and stats["types_missing"] == 0:
            fail(f"mutant {sorted(mut)} did not lose a single real graph")
        else:
            FAIL.clear()
            print(f"mutant {sorted(mut)}: real graph lost for {stats['lost']} frames — caught")
            return 1
    else:
        if stats["found"] != stats["frames"]:
            fail("not every frame has a DSRG solution")


# ---------- search ----------

def pivot_order(tt, keys, tys):
    reps = {}
    for i, T in enumerate(tys):
        c = (T[0] << 32) | T[1]
        if keys[T] == c and tt.dL[i] != 0:
            reps[c] = i
    full = {c: len(Pivots(tt, [i], [[0]]).candidates()) for c, i in reps.items()}
    order = sorted(reps, key=lambda c: (full[c], c))
    return order, reps, full


def cmd_search(args):
    drop = set(args.drop.split(",")) if args.drop else set()
    fr, tys, gens, naut, keys, tt = frame48(args.kind)
    t0 = time.time()
    import json
    ofile = os.path.join(os.path.dirname(os.path.dirname(os.path.abspath(__file__))), "data", f"search48-second-order-{args.kind}.json")
    if os.path.exists(ofile):
        saved = json.load(open(ofile, encoding="utf8"))
        reps = {}
        for i, T in enumerate(tys):
            c = (T[0] << 32) | T[1]
            if keys[T] == c and tt.dL[i] != 0:
                reps[c] = i
        order = saved["order"]
        full = {int(k): v for k, v in saved["full"].items()}
        assert sorted(order) == sorted(reps), "the order file does not match the pivot orbits"
    else:
        order, reps, full = pivot_order(tt, keys, tys)
        json.dump({"order": order, "full": {str(k): v for k, v in full.items()}}, open(ofile, "w", encoding="utf8"))
    pos = {c: p for p, c in enumerate(order)}
    tt.key = np.array([pos.get(keys[T], -1) for T in tys], dtype=object)
    print(f"{args.kind}: pivot orbits {len(order)}; order built in {time.time() - t0:.0f} s; "
          f"dropped conditions: {sorted(drop) or 'none'}", flush=True)
    part, nparts = (int(x) for x in args.part.split("/"))
    todo = [p for p in range(len(order)) if p % nparts == part]
    if args.orbits:
        todo = [int(x) for x in args.orbits.split(",")]
    if args.limit:
        todo = todo[:args.limit]
    res_count = {}
    tot_c = 0
    tmax = 0
    nroot = 0
    if args.proof_orbits == "all":
        proof_set = set(todo)
    else:
        proof_set = set(int(x) for x in args.proof_orbits.split(",")) if args.proof_orbits else set()
    for p in todo:
        c = order[p]
        i0 = reps[c]
        t1 = time.time()
        pv = Pivots(tt, [i0], [[0]])
        cand = pv.candidates(key_min=p)
        cl, cards, info = build_cnf(pv, cand, drop=drop)
        chk = DsrgCheck(pv, cand)
        root = any(len(c) == 0 for c in cl)
        nroot += root
        cert = ""
        if args.solver == "cadical":
            certify = None
            if args.proof_dir and (p in proof_set):
                def certify(cnf, drat):
                    import subprocess
                    sc = os.path.join(ROOT, "lib", "sat_certificate.py")
                    dt_ = os.environ.get("DRAT_TRIM", "drat-trim")
                    pr = subprocess.run([sys.executable, "-X", "utf8", sc, "certify", cnf, drat, "--drat-trim", dt_,
                                         "--timeout", str(args.drat_timeout)], capture_output=True, text=True, encoding="utf8")
                    last = pr.stdout.strip().splitlines()[-1] if pr.stdout.strip() else pr.stderr.strip()[-200:]
                    if pr.returncode != 0:
                        fail(f"orbit {p}: the certificate check failed with exit {pr.returncode}: {last}")
                    elif args.discard_proofs:
                        for fn in (cnf, drat, os.path.splitext(drat)[0] + ".lrat"):
                            if os.path.exists(fn):
                                os.remove(fn)
                    return f"certificate: exit {pr.returncode}, {last}"
            res, cert = solve_cadical(cl, cards, proof_dir=args.proof_dir if certify else None, certify=certify,
                                      name=f"search48-{args.kind}-orbit{p}")
            cert = f", {cert}" if cert else ""
        else:
            res, models = solve(cl, cards, block_limit=args.block, check=chk)
        dt = time.time() - t1
        tmax = max(tmax, dt)
        tot_c += len(cand)
        res_count[res] = res_count.get(res, 0) + 1
        d0 = Fr(int(tt.dL[i0]), fr.L)
        print(f"  orbit {p}: type {tys[i0]}, d0 = {d0}, candidates {len(cand)} (without key {full[c]}), "
              f"{res}{' at the root' if root else ''}, false solutions {chk.bad}, {dt:.1f} s{cert}", flush=True)
        if res == "SAT":
            print("  GRAPH FOUND:", chk.last, flush=True)
    print(f"total {args.kind} part {part}/{nparts} ({args.solver}): orbits {len(todo)}, of them closed by counting "
          f"cardinalities before the solver {nroot}, candidates in total {tot_c}, outcomes {res_count}, "
          f"longest time {tmax:.1f} s, total {time.time() - t0:.0f} s")
    if not drop and set(res_count) - {"UNSAT"}:
        fail("some orbits have an outcome other than UNSAT")


def cmd_cover_only(args):
    from pysat.solvers import Solver
    fr, tys, gens, naut, keys, tt = frame48(args.kind)
    t0 = time.time()
    nt = len(tys)
    X = lambda i: i + 1
    cards = []
    for u in fr.Np:
        for v in fr.Np:
            cards.append(([X(int(i)) for i in np.nonzero(tt.Ib[:, u] & tt.Ob[:, v])[0]], fr.Phi[u][v]))
        cards.append(([X(int(i)) for i in np.nonzero(tt.Ib[:, u])[0]], fr.outW[u]))
        cards.append(([X(int(i)) for i in np.nonzero(tt.Ob[:, u])[0]], fr.inW[u]))
    cards.append(([X(i) for i in range(nt)], fr.params[0] - fr.n))
    zero = [lits for lits, b in cards if b == 0]
    with Solver(name="minicard") as s:
        for lits, b in cards:
            if b == 0:
                for l in lits:
                    s.add_clause([-l])
            else:
                s.add_atmost(lits, b)
                s.add_atmost([-l for l in lits], len(lits) - b)
        import threading
        tm = threading.Timer(args.seconds, s.interrupt)
        tm.start()
        r = s.solve_limited(expect_interrupt=True)
        tm.cancel()
        st = s.accum_stats()
        model = s.get_model() if r else None
    print(f"{args.kind}: types {nt}, cardinality constraints {len(cards)} (zero {len(zero)}), "
          f"outcome {('SAT' if r else 'UNSAT') if r is not None else 'unsolved within ' + str(args.seconds) + ' s'}, "
          f"conflicts {st.get('conflicts')}, "
          f"{time.time() - t0:.0f} s")
    if model:
        chosen = [l - 1 for l in model if 0 < l <= nt]
        ok = len(chosen) == fr.params[0] - fr.n
        for u in fr.Np:
            for v in fr.Np:
                ok &= sum(int(tt.Ib[i, u] * tt.Ob[i, v]) for i in chosen) == fr.Phi[u][v]
            ok &= sum(int(tt.Ib[i, u]) for i in chosen) == fr.outW[u]
            ok &= sum(int(tt.Ob[i, u]) for i in chosen) == fr.inW[u]
        dsum = sum(Fr(int(tt.dL[i]), fr.L) for i in chosen)
        print(f"  cover checked by recounting: {ok}; types {len(chosen)}; Σ d = {dsum} (a graph would have −4)")
        print("  types (O, I):", [tys[i] for i in chosen])
        if not ok:
            fail("the cover solution fails the recount")


def main():
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    sub = ap.add_subparsers(dest="cmd", required=True)
    sub.add_parser("cases")
    sub.add_parser("frame")
    sub.add_parser("selftest")
    c = sub.add_parser("control")
    c.add_argument("--mutate", default="")
    c.add_argument("--max-rank", type=int, default=3)
    c.add_argument("--block", type=int, default=20)
    c.add_argument("--petersen", action="store_true",
                   help="the Petersen graph (10, 3, 3, 0, 1) instead of the catalogue")
    s = sub.add_parser("search")
    s.add_argument("--kind", required=True, choices=["C8", "2C4"])
    s.add_argument("--drop", default="")
    s.add_argument("--part", default="0/1")
    s.add_argument("--limit", type=int, default=0)
    s.add_argument("--block", type=int, default=50)
    s.add_argument("--solver", default="minicard", choices=["minicard", "cadical"])
    s.add_argument("--proof-dir", default="")
    s.add_argument("--proof-orbits", default="", help="orbits whose proofs are written and checked: numbers "
                   "separated by commas, or all")
    s.add_argument("--discard-proofs", action="store_true",
                   help="remove the CNF, DRAT and LRAT files of an orbit once drat-trim and the LRAT check "
                   "accept them; their SHA-256 stay in the output")
    s.add_argument("--drat-timeout", type=int, default=180, help="drat-trim limit per orbit, seconds")
    s.add_argument("--orbits", default="", help="orbit numbers separated by commas instead of --part")
    c2 = sub.add_parser("cover-only")
    c2.add_argument("--kind", required=True, choices=["C8", "2C4"])
    c2.add_argument("--seconds", type=float, default=180.0, help="solver limit, seconds")
    ap.add_argument("--out", default="", help="copy of the output to a file")
    args = ap.parse_args()
    if args.out:
        class Tee:
            def __init__(self, *fs):
                self.fs = fs
            def write(self, x):
                for f in self.fs:
                    f.write(x)
                    f.flush()
            def flush(self):
                for f in self.fs:
                    f.flush()
        sys.stdout = Tee(sys.stdout, open(args.out, "w", encoding="utf8"))
    rc = {"cover-only": cmd_cover_only, "cases": cmd_cases, "frame": cmd_frame, "selftest": cmd_selftest, "control": cmd_control,
          "search": cmd_search}[args.cmd](args)
    if FAIL:
        print(f"violations: {len(FAIL)}")
        sys.exit(1)
    if rc:
        sys.exit(rc)
    print("violations: 0")


if __name__ == "__main__":
    main()
