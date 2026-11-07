"""Second program for the free-vertex case of (28, 6, 3, 2, 1), written independently.

    "$SOLVER_PYTHON" -X utf8 checks/dsrg28_second.py frames [--mutate drop-frame|canon-group]
    "$SOLVER_PYTHON" -X utf8 checks/dsrg28_second.py control --only v,k,t,λ,μ [--per-graph N] [--mutate M]
    "$SOLVER_PYTHON" -X utf8 checks/dsrg28_second.py proof [--mutate cut-proof] [--drat-trim PATH]

frames - the 10⁶ labelled subgraphs on N⁺[x] and the 55 left by the cells of B² = 3B + J; control - its
formulas on known graphs (18, 5, 3, 2, 1) and (54, 8, 3, 2, 1); proof - both formulas for
(28, 6, 3, 2, 1) solved, with DRAT proofs checked by drat-trim and the LRAT checker.
"""

from __future__ import annotations

import argparse
import hashlib
import itertools
import json
import shutil
import subprocess
import sys
import tempfile
import multiprocessing as mp
import queue
import time
from pathlib import Path

import numpy as np

HERE = Path(__file__).resolve().parent
ROOT = HERE.parent
sys.path.insert(0, str(ROOT / "lib"))
sys.path.insert(0, str(ROOT / "lib"))

import dsrg_verify  # noqa: E402
from solver_release import proof_solver  # noqa: E402

TARGET = (28, 6, 3, 2, 1)
GRAPHS = HERE.parent / "data" / "dsrg28-control-graphs.json"
MUT_FRAMES = ("drop-frame", "canon-group")
MUT_CONTROL = ("lam-shift", "counter-shift", "block-swap", "sorted-strict")


def load_graphs():
    out = []
    for g in json.loads(GRAPHS.read_text(encoding="utf-8")):
        v = g["params"][0]
        A = [[int(c) for c in bin(int(h, 16))[2:].zfill(v)] for h in g["rows"]]
        out.append((g["id"], tuple(g["params"]), A))
    return out


def transpose(A):
    return [list(r) for r in zip(*A)]


def relabel(A, p, x):
    v, k, t, lam, mu = p
    outs = [y for y in range(v) if A[x][y]]
    mutual = [y for y in outs if A[y][x]]
    other = [y for y in outs if not A[y][x]]
    S = [x] + mutual + other
    Sset = set(S)
    blocks = []
    for o in S[1:]:
        blocks.append([w for w in range(v) if w not in Sset and A[o][w]])
    W = [w for b in blocks for w in b]
    if sorted(W) != sorted(set(range(v)) - Sset):
        raise ValueError("a vertex of W has not exactly one in-arc from S")
    return S + W, [len(b) for b in blocks]


def permute(A, order):
    return [[A[i][j] for j in order] for i in order]


def frame_filter(F, p, mutate=None):
    v, k, t, lam, mu = p
    K = k + 1
    B = F.astype(np.int16) + np.eye(K, dtype=np.int16)[None]
    inner = np.einsum("nsz,nzy->nsy", B, B)
    target = (lam + 1) * B + 1
    rowS = B.sum(axis=2)
    wsize = K - rowS[:, 1:]                       # |W_o| = k − |Γ⁺(o) ∩ S|
    ok = np.all(inner[:, 0, :] == target[:, 0, :], axis=1)
    diff = target[:, 1:, :] - inner[:, 1:, :]
    upper = wsize[:, :, None] - (1 if mutate == "drop-frame" else 0)
    ok &= np.all((diff >= 0) & (diff <= upper), axis=(1, 2))
    ok &= np.all(F[:, 0, 1:] == 1, axis=1) & np.all(F[:, 1:t + 1, 0] == 1, axis=1)
    ok &= np.all(F[:, t + 1:, 0] == 0, axis=1)
    free = np.all(wsize >= 1, axis=1)
    return ok, wsize, free


def gen_frames(p):
    v, k, t, lam, mu = p
    K = k + 1
    opts = []
    for o in range(1, K):
        cols = []
        for c in itertools.combinations([z for z in range(1, K) if z != o], lam):
            col = np.zeros(K, dtype=np.uint8)
            col[list(c)] = 1
            cols.append(col)
        opts.append(np.array(cols))
    sizes = [len(c) for c in opts]
    N = int(np.prod(sizes))
    if N > 3_000_000:
        raise ValueError(f"frames {N} — enumeration out of reach")
    idx = np.stack(np.unravel_index(np.arange(N), sizes), axis=1)
    F = np.zeros((N, K, K), dtype=np.uint8)
    F[:, 0, 1:] = 1
    F[:, 1:t + 1, 0] = 1
    for o in range(1, K):
        F[:, :, o] |= opts[o - 1][idx[:, o - 1]]
    return F


def brute_frames(p):
    v, k, t, lam, mu = p
    K = k + 1
    arcs = [(i, j) for i in range(1, K) for j in range(1, K) if i != j]
    N = 1 << len(arcs)
    if N > 4_000_000:
        raise ValueError("brute force out of reach")
    bits = ((np.arange(N, dtype=np.int64)[:, None] >> np.arange(len(arcs))) & 1).astype(np.uint8)
    F = np.zeros((N, K, K), dtype=np.uint8)
    F[:, 0, 1:] = 1
    F[:, 1:t + 1, 0] = 1
    for c, (i, j) in enumerate(arcs):
        F[:, i, j] = bits[:, c]
    B = F.astype(np.int16) + np.eye(K, dtype=np.int16)[None]
    row0 = np.einsum("nz,nzy->ny", B[:, 0, :], B)
    target = (lam + 1) * B[:, 0, :] + 1
    return F[np.all(row0 == target, axis=1)]


def group_perms(p, mutate=None):
    v, k, t, lam, mu = p
    if mutate == "canon-group":
        return [(0,) + q for q in itertools.permutations(range(1, k + 1))]
    out = []
    for a in itertools.permutations(range(1, t + 1)):
        for b in itertools.permutations(range(t + 1, k + 1)):
            out.append((0,) + a + b)
    return out


def codes(F):
    K = F.shape[1]
    w = (1 << np.arange(K * K, dtype=np.int64)).reshape(K, K)
    return (F.astype(np.int64) * w[None]).sum(axis=(1, 2))


def canon(F, perms):
    best = None
    for q in perms:
        q = np.array(q)
        c = codes(F[:, q][:, :, q])
        best = c if best is None else np.minimum(best, c)
    return best


def decode(code, K):
    bits = [(int(code) >> i) & 1 for i in range(K * K)]
    return np.array(bits, dtype=np.uint8).reshape(K, K)


def frame_reps(p, mutate=None, free_only=True):
    F = gen_frames(p)
    ok, wsize, free = frame_filter(F, p, mutate)
    sel = ok & free if free_only else ok
    G = F[sel]
    cc = canon(G, group_perms(p, mutate)) if len(G) else np.array([], dtype=np.int64)
    reps = sorted(set(int(c) for c in cc))
    return F, ok, free, G, reps


class Enc:
    def __init__(self):
        self.n = 0
        self.clauses = []
        self.contradiction = False

    def new(self):
        self.n += 1
        return self.n

    def add(self, clause):
        lits = []
        for x in clause:
            if x is True:
                return
            if x is False:
                continue
            lits.append(x)
        if not lits:
            self.contradiction = True
            y = self.new()
            self.clauses += [[y], [-y]]
            return
        self.clauses.append(lits)

    @staticmethod
    def neg(x):
        if x is True:
            return False
        if x is False:
            return True
        return -x

    def AND(self, a, b):
        if a is False or b is False:
            return False
        if a is True:
            return b
        if b is True:
            return a
        y = self.new()
        self.add([-y, a])
        self.add([-y, b])
        self.add([y, -a, -b])
        return y

    def counter(self, lits, R, mutate=None):
        c = sum(1 for x in lits if x is True)
        L = [x for x in lits if x is not True and x is not False]
        shift = 1 if mutate == "counter-shift" else 0
        R += shift
        prev = {0: True}
        for i, x in enumerate(L, start=1):
            cur = {0: True}
            for m in range(1, min(i, R) + 1):
                A = prev.get(m, False)
                Bv = prev.get(m - 1, False)
                if A is True:
                    cur[m] = True
                    continue
                if A is False and (Bv is False):
                    cur[m] = False
                    continue
                if A is False and Bv is True:
                    cur[m] = x
                    continue
                y = self.new()
                self.add([self.neg(A), y])
                self.add([-x, self.neg(Bv), y])
                self.add([-y, A, x])
                self.add([-y, A, Bv])
                cur[m] = y
            prev = cur
        n = len(L)

        def geq(m):
            m = m - c + shift
            if m <= 0:
                return True
            if m > n:
                return False
            if m > R:
                raise ValueError("counter truncated")
            return prev.get(m, False)
        return geq

    def exactly(self, lits, T, mutate=None):
        g = self.counter(lits, T + 1, mutate)
        self.add([g(T)])
        self.add([self.neg(g(T + 1))])

    def cond_exactly(self, cond, lits, T1, T0, mutate=None):
        g = self.counter(lits, max(T1, T0) + 1, mutate)
        nc = self.neg(cond)
        self.add([nc, g(T1)])
        self.add([nc, self.neg(g(T1 + 1))])
        self.add([cond, g(T0)])
        self.add([cond, self.neg(g(T0 + 1))])


def dsrg_constraints(enc, v, p, arc, mutate=None):
    _, k, t, lam, mu = p
    lam1 = lam + 1 if mutate == "lam-shift" else lam
    for i in range(v):
        enc.exactly([arc(i, j) for j in range(v) if j != i], k, mutate)
        enc.exactly([arc(j, i) for j in range(v) if j != i], k, mutate)
    for i in range(v):
        for j in range(v):
            if i == j:
                prods = [enc.AND(arc(i, z), arc(z, i)) for z in range(v) if z != i]
                enc.exactly(prods, t, mutate)
            else:
                prods = [enc.AND(arc(i, z), arc(z, j)) for z in range(v) if z not in (i, j)]
                enc.cond_exactly(arc(i, j), prods, lam1, mu, mutate)


def frame_formula(p, frame, mutate=None):
    v, k, t, lam, mu = p
    K = k + 1
    frame = np.asarray(frame)
    wsize = [k - int(frame[o].sum()) for o in range(1, K)]
    if mutate == "block-swap":
        wsize = wsize[::-1]
    owner = {}
    w = K
    for o, s in enumerate(wsize, start=1):
        for _ in range(s):
            owner[w] = o
            w += 1
    if w != v:
        raise ValueError(f"blocks give {w - K} vertices of W instead of {v - K}")
    enc = Enc()
    var = {}
    for i in range(K, v):
        for j in range(v):
            if i != j:
                var[(i, j)] = enc.new()

    def arc(i, j):
        if i == j:
            return False
        if i < K and j < K:
            return bool(frame[i][j])
        if i < K:
            return owner[j] == i
        return var[(i, j)]
    dsrg_constraints(enc, v, p, arc, mutate)
    return enc, var, arc


def sorted_formula(p, free=True, mutate=None):
    v, k, t, lam, mu = p
    K = k + 1
    enc = Enc()
    var = {}
    for i in range(1, v):
        for j in range(v):
            if i == j or (i <= t and j == 0) or (i > t and j == 0 and i < K):
                continue
            var[(i, j)] = enc.new()

    def arc(i, j):
        if i == j:
            return False
        if i == 0:
            return 1 <= j <= k
        if j == 0 and i < K:
            return i <= t
        return var[(i, j)]
    dsrg_constraints(enc, v, p, arc, mutate)
    for w in range(K, v - 1):
        for o in range(1, K):
            for o2 in range(1, o + (1 if mutate == "sorted-strict" else 0)):
                enc.add([-arc(o, w), -arc(o2, w + 1)])
    if free:
        for o in range(1, t + 1):
            enc.add([arc(o, w) for w in range(K, v)])
    return enc, var, arc


def assumptions_of(var, B):
    return [x if B[i][j] else -x for (i, j), x in var.items()]


def matrix_of(model, v, arc):
    pos = set(l for l in model if l > 0)
    M = [[0] * v for _ in range(v)]
    for i in range(v):
        for j in range(v):
            a = arc(i, j)
            M[i][j] = int(a is True or (a is not False and a in pos))
    return M


def _solve_child(q, clauses, solver, assumptions):
    from pysat.solvers import Solver
    with Solver(name=solver, bootstrap_with=clauses) as s:
        res = s.solve(assumptions=assumptions)
        q.put((res, s.get_model() if res else None))


def solve(enc, solver, limit, assumptions=()):
    ctx = mp.get_context("spawn")
    q = ctx.Queue()
    p = ctx.Process(target=_solve_child, args=(q, enc.clauses, solver, list(assumptions)))
    t0 = time.time()
    p.start()
    try:
        res, model = q.get(timeout=limit)
    except queue.Empty:
        res, model = None, None
    dt = time.time() - t0
    if p.is_alive():
        p.kill()
    p.join()
    return res, model, dt


def cmd_frames(args):
    bad = 0
    p = TARGET
    t0 = time.time()
    F, ok, free, G, reps = frame_reps(p, args.mutate)
    K = p[1] + 1
    a_of = 1 + (np.einsum("noy->no", F[:, 1:, :].astype(np.int16)) == K - 1).sum(axis=1)
    print(f"{p}: labelled frames {len(F)}, admissible {int(ok.sum())} "
          f"(by a: {dict(sorted(Counter_np(a_of[ok]).items()))}), free admissible {len(G)}, "
          f"classes of free frames under S_t × S_(k−t) {len(reps)} ({time.time() - t0:.1f} s)")
    for c in reps:
        Fr = decode(c, K)
        ws = [p[1] - int(Fr[o].sum()) for o in range(1, K)]
        print(f"  class {c}: blocks |W_o| = {ws}; frame by rows: "
              + " ".join("".join(map(str, r)) for r in Fr))
    for q in [(8, 3, 2, 1, 1), (15, 4, 2, 1, 1), (18, 5, 3, 2, 1), (24, 5, 2, 1, 1)]:
        try:
            Fb = brute_frames(q)
        except ValueError:
            continue
        Fg = gen_frames(q)
        sb, sg = set(map(int, codes(Fb))), set(map(int, codes(Fg)))
        same = sb == sg
        bad += not same
        print(f"generator against brute force {q}: {len(sg)} and {len(sb)} labelled frames — "
              f"{'agree' if same else 'DIFFER'}")
    stats = {}
    for gid, q, A0 in load_graphs():
        for tr, A in (("A", A0), ("Aᵀ", transpose(A0))):
            Fs, frees = [], []
            for x in range(q[0]):
                order, ws = relabel(A, q, x)
                Fs.append(np.array([r[:q[1] + 1] for r in permute(A, order)[:q[1] + 1]], dtype=np.uint8))
            Fs = np.array(Fs)
            okq, wsq, freeq = frame_filter(Fs, q, args.mutate)
            miss = int((~okq).sum())
            lost = 0
            try:
                _, _, _, Gq, repsq = frame_reps(q, args.mutate, free_only=False)
                cq = canon(Fs, group_perms(q, args.mutate))
                rs = set(repsq)
                lost = sum(1 for c in cq if int(c) not in rs)
                bad_reps = sum(1 for c in repsq if not frame_filter(decode(c, q[1] + 1)[None], q)[0][0])
                lost += bad_reps
                tag = f"classes {len(repsq)}"
            except ValueError:
                tag = "enumeration out of reach — selection only"
            bad += (miss + lost) > 0
            st = stats.setdefault(q, [0, 0, 0, 0])
            st[0] += q[0]
            st[1] += int(freeq.sum())
            st[2] += miss
            st[3] += lost
            if miss or lost:
                print(f"  {gid} {tr}: selection rejected {miss} real frames, classes missing from the list {lost}")
            del tag
    for q, (n, nf, miss, lost) in sorted(stats.items()):
        print(f"real frames {q}: vertices {n} (A and Aᵀ), free {nf}; rejected by selection {miss}, "
              f"missing from the list {lost}")
    print(f"violations: {bad}")
    if args.mutate:
        print(f"mutant {args.mutate}: {'caught' if bad else 'NOT caught'}")
    return 1 if bad else 0


def Counter_np(arr):
    vals, cnt = np.unique(arr, return_counts=True)
    return {int(a): int(b) for a, b in zip(vals, cnt)}


def control_vertices(A, p, limit):
    v = p[0]
    rows = [tuple(r[j] | (j == i) for j in range(v)) for i, r in enumerate(A)]
    cnt = {}
    for r in rows:
        cnt[r] = cnt.get(r, 0) + 1
    free = [x for x in range(v) if cnt[rows[x]] == 1]
    rest = [x for x in range(v) if cnt[rows[x]] > 1]
    return (free[:limit] + rest)[:limit], set(free)


def cmd_control(args):
    bad = 0
    lines = 0
    undecided = 0
    for gid, p, A0 in load_graphs():
        if args.only and p != tuple(int(z) for z in args.only.split(",")):
            continue
        if p not in ((18, 5, 3, 2, 1), (54, 8, 3, 2, 1)) and not args.all:
            continue
        v = p[0]
        for tr, A in (("A", A0), ("Aᵀ", transpose(A0))):
            xs, free = control_vertices(A, p, args.per_graph)
            for x in xs:
                order, _ = relabel(A, p, x)
                Bm = permute(A, order)
                K = p[1] + 1
                frame = [r[:K] for r in Bm[:K]]
                t0 = time.time()
                enc, var, arc = frame_formula(p, frame, args.mutate)
                tb = time.time() - t0
                r1, _, d1 = solve(enc, args.solver, args.time_limit, assumptions_of(var, Bm))
                r2, model, d2 = solve(enc, args.solver, args.time_limit)
                ver = None
                if r2:
                    M = matrix_of(model, v, arc)
                    ver = dsrg_verify.check(M, p).ok
                good = (r1 is True) and (r2 is not False) and (ver is not False)
                bad += not good
                undecided += r2 is None
                lines += 1
                print(f"{gid} {tr} x={x} ({'free' if x in free else 'with a twin'}): frame formula "
                      f"{enc.n} vars, {len(enc.clauses)} clauses ({tb:.1f} s); real graph — "
                      f"{fmt(r1)} ({d1:.1f} s); without graph — {fmt(r2)} ({d2:.1f} s), solver graph "
                      f"{'passes' if ver else ('does NOT pass' if ver is False else '—')} verify", flush=True)
            if v <= 54:
                x = xs[0]
                order, _ = relabel(A, p, x)
                Bm = permute(A, order)
                for fr in ((False, True) if x in free else (False,)):
                    enc, var, arc = sorted_formula(p, free=fr, mutate=args.mutate)
                    r1, _, d1 = solve(enc, args.solver, args.time_limit, assumptions_of(var, Bm))
                    good = r1 is True
                    msg = ""
                    if not fr and v <= 18:
                        r2, model, d2 = solve(enc, args.solver, args.time_limit)
                        ver = dsrg_verify.check(matrix_of(model, v, arc), p).ok if r2 else None
                        good = good and r2 is True and ver
                        msg = f"; without graph — {fmt(r2)} ({d2:.1f} s), verify {'OK' if ver else ver}"
                    bad += not good
                    print(f"{gid} {tr} x={x}: sorted formula{' with freedom' if fr else ''} "
                          f"{enc.n} vars, {len(enc.clauses)} clauses; real graph — {fmt(r1)} ({d1:.1f} s){msg}",
                          flush=True)
    print(f"violations: {bad}; frame formulas {lines}, of them without graph unsolved within the limit {undecided}")
    if args.mutate:
        print(f"mutant {args.mutate}: {'caught' if bad else 'NOT caught'}")
    return 1 if bad else 0


def fmt(r):
    return {True: "SAT", False: "UNSAT", None: "unsolved within the limit"}[r]


def cmd_close(args):
    p = TARGET
    _, _, _, _, reps = frame_reps(p)
    K = p[1] + 1
    undecided = sat = 0
    print(f"{p}: classes of frames of a free vertex {len(reps)}")
    for c in reps:
        Fr = decode(c, K)
        t0 = time.time()
        enc, var, arc = frame_formula(p, Fr)
        tb = time.time() - t0
        res, model, dt = solve(enc, args.solver, args.time_limit)
        print(f"  frame {c}: {enc.n} vars, {len(enc.clauses)} clauses ({tb:.1f} s) — {fmt(res)} in {dt:.1f} s "
              f"({args.solver})", flush=True)
        if res is None:
            undecided += 1
        if res:
            sat += 1
            M = matrix_of(model, p[0], arc)
            print("  GRAPH FOUND:", dsrg_verify.check(M, p).ok, json.dumps(M))
    t0 = time.time()
    enc, var, arc = sorted_formula(p, free=True)
    tb = time.time() - t0
    res, model, dt = solve(enc, args.solver, args.time_limit)
    print(f"sorted formula with freedom: {enc.n} vars, {len(enc.clauses)} clauses ({tb:.1f} s) — "
          f"{fmt(res)} in {dt:.1f} s ({args.solver})", flush=True)
    if res is None:
        undecided += 1
    if res:
        sat += 1
        M = matrix_of(model, p[0], arc)
        print("GRAPH FOUND:", dsrg_verify.check(M, p).ok, json.dumps(M))
    print(f"outcome: solved {len(reps) + 1 - undecided} of {len(reps) + 1}, satisfiable {sat}")
    return 0 if (undecided == 0 and sat == 0) else 1


def sha(path):
    h = hashlib.sha256()
    with open(path, "rb") as fh:
        for chunk in iter(lambda: fh.read(1 << 20), b""):
            h.update(chunk)
    return h.hexdigest()


def certify(name, enc, args, work):
    cnf = work / f"{name}.cnf"
    drat = work / f"{name}.drat"
    t0 = time.time()
    with proof_solver("cadical195", bootstrap_with=enc.clauses, with_proof=True) as s:
        res = s.solve()
        proof = s.get_proof() if not res else None
    t1 = time.time()
    if res:
        print(f"{name}: SATISFIABLE by CaDiCaL")
        return False
    if args.mutate == "cut-proof":
        proof = proof[: len(proof) // 2]
    with open(cnf, "w", encoding="ascii", newline="\n") as fh:
        fh.write(f"p cnf {enc.n} {len(enc.clauses)}\n")
        for c in enc.clauses:
            fh.write(" ".join(map(str, c)) + " 0\n")
    with open(drat, "w", encoding="ascii", newline="\n") as fh:
        for line in proof:
            fh.write(line + "\n")
    proc = subprocess.run([sys.executable, "-X", "utf8",
                           str(ROOT / "lib" / "sat_certificate.py"),
                           "certify", str(cnf), str(drat), "--drat-trim", args.drat_trim, "--timeout", "200"],
                          capture_output=True, text=True, encoding="utf-8")
    t2 = time.time()
    lrat = drat.with_suffix(".lrat")
    ok = proc.returncode == 0
    last = (proc.stdout.strip().splitlines() or [""])[-1]
    print(f"{name}: {enc.n} vars, {len(enc.clauses)} clauses; UNSAT by CaDiCaL 1.9.5 in {t1 - t0:.1f} s; "
          f"certify — {'accepted' if ok else 'NOT accepted'} (exit {proc.returncode}) in {t2 - t1:.1f} s; "
          f"SHA-256 of the formula {sha(cnf)}, DRAT {sha(drat)} ({drat.stat().st_size} bytes); {last}", flush=True)
    if not args.keep:
        for f in (cnf, drat, lrat):
            if f.exists():
                f.unlink()
    return ok


def cmd_proof(args):
    p = TARGET
    _, _, _, _, reps = frame_reps(p)
    work = Path(tempfile.mkdtemp(prefix="dsrg28_proof_"))
    bad = 0
    try:
        for c in reps:
            enc, _, _ = frame_formula(p, decode(c, p[1] + 1))
            bad += not certify(f"frame-{c}", enc, args, work)
        if not args.frames_only:
            enc, _, _ = sorted_formula(p, free=True)
            bad += not certify("sorted-free", enc, args, work)
    finally:
        if not args.keep:
            shutil.rmtree(work, ignore_errors=True)
    print(f"certificates not accepted: {bad}")
    if args.mutate:
        print(f"mutant {args.mutate}: {'caught' if bad else 'NOT caught'}")
    return 1 if bad else 0


def main():
    ap = argparse.ArgumentParser()
    sub = ap.add_subparsers(dest="cmd", required=True)
    a = sub.add_parser("frames")
    a.add_argument("--mutate", choices=MUT_FRAMES)
    a = sub.add_parser("control")
    a.add_argument("--mutate", choices=MUT_CONTROL)
    a.add_argument("--solver", default="cadical195")
    a.add_argument("--time-limit", type=float, default=60)
    a.add_argument("--per-graph", type=int, default=2)
    a.add_argument("--all", action="store_true")
    a.add_argument("--only")
    a = sub.add_parser("close")
    a.add_argument("--solver", default="cadical195")
    a.add_argument("--time-limit", type=float, default=200)
    a = sub.add_parser("proof")
    a.add_argument("--mutate", choices=("cut-proof",))
    a.add_argument("--keep", action="store_true")
    a.add_argument("--frames-only", action="store_true")
    a.add_argument("--drat-trim", default=str("drat-trim"))
    args = ap.parse_args()
    return {"frames": cmd_frames, "control": cmd_control, "close": cmd_close, "proof": cmd_proof}[args.cmd](args)


if __name__ == "__main__":
    sys.exit(main())
