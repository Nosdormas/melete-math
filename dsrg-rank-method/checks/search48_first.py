"""Search of the theorem on (48, 9, 5, 0, 2), first program: exact cover from a pivot vertex.

    python -X utf8 checks/search48_first.py selftest [--trials N] [--mutate no-exclude]
    python -X utf8 checks/search48_first.py inputs --kind C8|2C4
    python -X utf8 checks/search48_first.py run --kind C8|2C4 --from I --to J [--no-degrees]
    python -X utf8 checks/search48_first.py plant

selftest - the exact-cover engine against full enumeration on random planted instances; inputs -
partners and arcs against exact fractions through D⁻¹; run - the search over the pivot orbits I..J-1;
plant - end-to-end control on the Clebsch graph (16, 5, 5, 0, 2) at θ = 1 (S = 0) with the same engine.
"""
from __future__ import annotations

import argparse
import itertools
import random
import sys
import time
from fractions import Fraction as Fr
from pathlib import Path

import numpy as np

HERE = Path(__file__).resolve().parent
ROOT = HERE.parent
sys.path.insert(0, str(ROOT / "lib"))
sys.path.insert(0, str(HERE))
sys.path.insert(0, str(ROOT / "lib"))

import pivot_frame as dfr  # noqa: E402
from pivot_frame import (LazyRows, cells_of, degrees, exact_f, exact_pair, exact_partner,  # noqa: E402
                             partners, phi, pivot_list)
from exact_cover_pairs import Cover, bits_list, selftest, to_bits  # noqa: E402
from kernel_frame import inverse  # noqa: E402

MU = 2
NP = list(range(1, 14))
MUTATIONS = ("no-exclude", "no-saturate", "minor-off", "phi-plus")


# - search for (48, 9, 5, 0, 2)

def needs(kind, r0, c0, mutate=None):
    need = dfr.needs(kind, r0, c0)
    if mutate == "phi-plus":
        need[1] += 1
    return need


def pair_tables(R, C, Di12, k, idx, a01, a10, u, s0, rows):
    Rp, Cp = R[idx], C[idx]
    F12 = (Rp[rows] @ Di12) @ Cp.T
    X = np.outer(u[rows], s0) + k * F12            # = 12k·A(i, j)
    p2 = Rp[rows] @ Cp.T + np.outer(a10[rows], a01)
    cin = (Cp[rows] @ Cp.T > 0) | np.outer(a01[rows], a01)
    cout = (Rp[rows] @ Rp.T > 0) | np.outer(a10[rows], a10)
    one = (X == 12 * k) & (p2 == 0) & ~cin & ~cout
    zero = (X == 0) & (p2 <= MU)
    return one | zero, one


class PivotSearch48:
    def __init__(self, kind, T, R, C, Di12, d3, i0, keyrank, degrees_on=True, mutate=None, eager=False):
        self.kind, self.i0, self.T = kind, i0, T
        r0, c0 = T[i0]
        part = partners(R, C, Di12, d3, i0)
        if mutate == "minor-off":
            part = minor_off_partners(T, R, C, Di12, d3, i0)
        part = [p for p in part if d3[p[0]] == 0 or keyrank[p[0]] >= keyrank[i0]]
        self.part = part
        covers = [cells_of(*T[p[0]], p[1], p[2]) for p in part]
        need = needs(kind, r0, c0, mutate)
        self.alive = True
        m = len(part)
        trial = Cover(covers, need, [(1 << m) - 1] * m)
        st = trial.root()
        if st is None or trial.choose(st) is None:
            self.alive = False
            self.cover = trial
            self.density = 0.0
            return
        idx = np.array([p[0] for p in part], dtype=np.int64)
        a01 = np.array([p[1] for p in part], dtype=bool)
        a10 = np.array([p[2] for p in part], dtype=bool)
        u = np.array([p[3] for p in part], dtype=np.int64)
        s0 = np.array([p[4] for p in part], dtype=np.int64)
        k = 4 * int(d3[i0])
        Rp, Cp = R[idx], C[idx]
        vout = [7 - len(T[p[0]][0] & set(dfr.Q)) - p[2] for p in part] if degrees_on else None
        vin = [7 - len(T[p[0]][1] & set(dfr.P)) - p[1] for p in part] if degrees_on else None
        emut = mutate if mutate in ("no-exclude", "no-saturate") else None
        if not eager:
            lazy = LazyRows(Rp, Cp, Di12, k, idx, a01, a10, u, s0)
            self.lazy = lazy
            self.density = float("nan")
            self.cover = Cover(covers, need, lazy.view(0), lazy.view(1) if degrees_on else None,
                               lazy.view(2) if degrees_on else None, vout, vin, mutate=emut)
            return
        comp, outb, inb = [0] * m, [0] * m, [0] * m
        pairs = 0
        step = 1000
        for lo in range(0, m, step):
            rows = np.arange(lo, min(m, lo + step))
            okf, onef = pair_tables(R, C, Di12, k, idx, a01, a10, u, s0, rows)      # i → j
            F12b = (Rp @ Di12) @ Cp[rows].T
            Xb = np.outer(u, s0[rows]) + k * F12b
            p2b = Rp @ Cp[rows].T + np.outer(a10, a01[rows])
            cinb = (Cp @ Cp[rows].T > 0) | np.outer(a01, a01[rows])
            coutb = (Rp @ Rp[rows].T > 0) | np.outer(a10, a10[rows])
            oneb = (Xb == 12 * k) & (p2b == 0) & ~cinb & ~coutb
            okb = oneb | ((Xb == 0) & (p2b <= MU))
            cmp_ = okf & okb.T & (idx[rows][:, None] != idx[None, :])
            for a, i in enumerate(rows):
                cmp_[a, i] = False
                comp[i] = to_bits(cmp_[a])
                outb[i] = to_bits(onef[a] & cmp_[a])
                inb[i] = to_bits(oneb[:, a] & cmp_[a])
            pairs += int(cmp_.sum())
        self.density = pairs / max(1, m * (m - 1))
        self.cover = Cover(covers, need, comp, outb if degrees_on else None, inb if degrees_on else None,
                           vout, vin, mutate=emut)

    def graph(self, sol, Di12, R, C):
        T = self.T
        verts = [(self.i0, 0, 0, None, None)] + [self.part[i] for i in sol]
        A = np.zeros((48, 48), dtype=np.int64)
        A[:14, :14] = np.array(dfr.frame(self.kind))
        for a, (ti, a01, a10, _, _) in enumerate(verts):
            r, c = T[ti]
            w = 14 + a
            for n in r:
                A[w, n] = 1
            for n in c:
                A[n, w] = 1
            if a > 0:
                A[14, w] = a01
                A[w, 14] = a10
        d0 = Fr(-1) - Fr(int(R[self.i0] @ Di12 @ C[self.i0]), 12)
        for a in range(1, len(verts)):
            for b in range(1, len(verts)):
                if a == b:
                    continue
                ta, tb = verts[a][0], verts[b][0]
                F = Fr(int(R[ta] @ Di12 @ C[tb]), 12)
                val = F + Fr(verts[a][3], 12) * Fr(verts[b][4], 12) / d0
                A[14 + a, 14 + b] = int(val)
        return A


def minor_off_partners(T, R, C, Di12, d3, i0):
    f01 = (R[i0] @ Di12) @ C.T
    f10 = R @ (Di12 @ C[i0])
    cc = (C @ C[i0]) > 0
    rr = (R @ R[i0]) > 0
    p01 = C @ R[i0]
    p10 = R @ C[i0]
    out = []
    for a01 in (0, 1):
        ok01 = (~cc & ~rr & (p01 == 0)) if a01 else (p01 <= MU)
        for a10 in (0, 1):
            ok10 = (~cc & ~rr & (p10 == 0)) if a10 else (p10 <= MU)
            ok = ok01 & ok10
            ok[i0] = False
            for i in np.flatnonzero(ok):
                out.append((int(i), a01, a10, int(12 * a10 - f10[i]), int(12 * a01 - f01[i])))
    return out


def check_inputs(kind, pivots, pairs, seed):
    rng = random.Random(seed)
    T, R, C, Di12, d3 = dfr.type_d3(kind)
    F = exact_f(T, dfr.inverse_d(kind))

    piv, keyrank = pivot_list(kind, T, d3)
    bad = 0
    checked = 0
    for i0 in rng.sample(piv, pivots):
        part = partners(R, C, Di12, d3, i0)
        pset = {(p[0], p[1], p[2]) for p in part}

        def good(ti, a01, a10):
            return exact_partner(F, T, i0, ti, a01, a10)

        for p in rng.sample(part, min(pairs, len(part))):
            ok, s0w, sw0 = good(p[0], p[1], p[2])
            checked += 1
            if not (ok and Fr(p[3], 12) == sw0 and Fr(p[4], 12) == s0w):
                bad += 1
        for _ in range(pairs):
            ti = rng.randrange(len(T))
            a01, a10 = rng.randint(0, 1), rng.randint(0, 1)
            if ti == i0 or (ti, a01, a10) in pset:
                continue
            checked += 1
            if good(ti, a01, a10)[0]:
                bad += 1
        inst = PivotSearch48(kind, T, R, C, Di12, d3, i0, keyrank, eager=True)
        if not inst.alive:
            continue
        lazy = PivotSearch48(kind, T, R, C, Di12, d3, i0, keyrank).lazy
        for a in rng.sample(range(len(inst.part)), min(300, len(inst.part))):
            checked += 1
            if lazy.rows(a) != (inst.cover.comp[a], inst.cover.outb[a], inst.cover.inb[a]):
                bad += 1
        P = inst.part
        cv = inst.cover
        for a in rng.sample(range(len(P)), min(200, len(P))):
            for b in bits_list(cv.outb[a]):
                checked += 1
                if not (cv.inb[b] >> a) & 1 or not (cv.comp[b] >> a) & 1:
                    bad += 1
            for b in bits_list(cv.comp[a]):
                if not (cv.comp[b] >> a) & 1:
                    bad += 1
        for _ in range(pairs):
            a, b = rng.sample(range(len(P)), 2)
            want, arc = exact_pair(F, T, i0, P[a], P[b])
            got = bool((inst.cover.comp[a] >> b) & 1)
            got_arc = bool((inst.cover.outb[a] >> b) & 1)
            checked += 1
            if want != got or (want and got_arc != arc):
                bad += 1
    return checked, bad


def clebsch():
    A = np.zeros((16, 16), dtype=np.int64)
    for x in range(16):
        for g in (1, 2, 4, 8, 15):
            A[x, x ^ g] = 1
    return A


def plant():
    import dsrg_verify  # noqa: E402
    G = clebsch()
    x = 0
    Mx = [j for j in range(16) if G[x, j]]
    types = [frozenset(s) for s in itertools.combinations(range(1, 6), 2)]
    Af = np.zeros((6, 6), dtype=np.int64)
    Af[0, 1:] = 1
    Af[1:, 0] = 1
    D = Af - np.eye(6, dtype=np.int64)
    Di = inverse(D.tolist())
    ph = MU * np.ones((6, 6), dtype=np.int64) - D @ D - 4 * D
    need = [int(ph[n, m]) for n in range(1, 6) for m in range(1, 6)]
    m = len(types)
    F = [[sum(Di[i][j] for i in types[a] for j in types[b]) for b in range(m)] for a in range(m)]
    covers = [[(n - 1) * 5 + (mm - 1) for n in t for mm in t] for t in types]
    if any(F[a][a] != -1 for a in range(m)):
        return 0, 0, False
    comp_m = [[a != b and F[a][b] in (0, 1) and (F[a][b] == 0 or not (types[a] & types[b]))
               for b in range(m)] for a in range(m)]
    cov = Cover(covers, need, [to_bits(row) for row in comp_m])
    _, sols, _ = cov.search()
    good = 0
    for s in sols:
        H = np.zeros((16, 16), dtype=np.int64)
        H[:6, :6] = Af
        for a, ta in enumerate(s):
            for n in types[ta]:
                H[6 + a, n] = H[n, 6 + a] = 1
            for b, tb in enumerate(s):
                if a != b:
                    H[6 + a, 6 + b] = int(F[ta][tb])
        good += dsrg_verify.check(H.tolist(), (16, 5, 5, 0, 2)).ok
    pos = {n: i + 1 for i, n in enumerate(Mx)}
    outer = [w for w in range(16) if w != x and w not in Mx]
    true = tuple(sorted(types.index(frozenset(pos[n] for n in Mx if G[w, n])) for w in outer))
    return len(sols), good, true in [tuple(sorted(s)) for s in sols]


# ---------------------------------------------------------------- main

def main() -> int:
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("mode", choices=("selftest", "inputs", "frame", "run", "plant"))
    ap.add_argument("--kind", default="C8")
    ap.add_argument("--trials", type=int, default=300)
    ap.add_argument("--pivots", type=int, default=3)
    ap.add_argument("--pairs", type=int, default=300)
    ap.add_argument("--seed", type=int, default=1)
    ap.add_argument("--from", dest="lo", type=int, default=0)
    ap.add_argument("--to", dest="hi", type=int, default=None)
    ap.add_argument("--node-limit", type=int, default=None)
    ap.add_argument("--no-degrees", action="store_true")
    ap.add_argument("--eager", action="store_true", help="build the whole compatibility table in advance")
    ap.add_argument("--mutate", choices=MUTATIONS)
    a = ap.parse_args()
    if a.mode == "selftest":
        bad, sols = selftest(a.trials, a.mutate)
        print(f"selftest: instances {a.trials} × 2 (with and without degree counting), solutions of the full enumeration {sols}, "
              f"discrepancies {bad}{' (mutant ' + a.mutate + ')' if a.mutate else ''}")
        return 1 if bad else 0
    if a.mode == "plant":
        n, good, found = plant()
        print(f"plant (Clebsch, θ = 1, S = 0): covers {n}, of them SRG(16, 5, 0, 2) — {good}, "
              f"true cover found: {found}")
        return 0 if n and good == n and found else 1
    if a.mode == "inputs":
        checked, bad = check_inputs(a.kind, a.pivots, a.pairs, a.seed)
        print(f"inputs {a.kind}: checked {checked} partners, non-partners and pairs in fractions; discrepancies {bad}")
        return 1 if bad else 0
    T, R, C, Di12, d3 = dfr.type_d3(a.kind)
    if a.mode == "frame":
        covers = [cells_of(r, c, 0, 0) for r, c in T]
        ph = phi(a.kind)
        dout, din = degrees(a.kind)
        need = [0] * 197
        for n in NP:
            for m in NP:
                need[(n - 1) * 13 + m - 1] = int(ph[n, m])
            need[169 + n - 1] = int(dout[n])
            need[182 + n - 1] = int(din[n])
        full = (1 << len(T)) - 1
        cov = Cover(covers, need, [full ^ (1 << i) for i in range(len(T))])
        t0 = time.time()
        nodes, sols, _ = cov.search(node_limit=a.node_limit, first=True)
        print(f"frame {a.kind}: nodes {nodes}, covers found {len(sols)}"
              + (f", vertices in the cover {len(sols[0])}" if sols else "") + f", {time.time() - t0:.1f} s")
        return 0 if sols else 1
    piv, keyrank = pivot_list(a.kind, T, d3)
    hi = len(piv) if a.hi is None else min(a.hi, len(piv))
    print(f"run {a.kind}: pivot orbits with d ≠ 0 — {len(piv)}; range [{a.lo}, {hi})"
          f"{'; without degree counting' if a.no_degrees else ''}{'; mutant ' + a.mutate if a.mutate else ''}",
          flush=True)
    total, nsol, alive = 0, 0, 0
    for pi in range(a.lo, hi):
        t0 = time.time()
        inst = PivotSearch48(a.kind, T, R, C, Di12, d3, piv[pi], keyrank, not a.no_degrees, a.mutate, a.eager)
        if inst.alive:
            alive += 1
            nodes, sols, done = inst.cover.search(node_limit=a.node_limit)
        else:
            nodes, sols, done = 1, [], True
        total += nodes
        nsol += len(sols)
        print(f"  №{pi} type {piv[pi]} 3d={int(d3[piv[pi]])}: candidates {len(inst.part)}, "
              f"{'alive' if inst.alive else 'dead at the root'}, density {inst.density:.3f}, nodes {nodes}, "
              f"solutions {len(sols)}{'' if done else ', CUT'}, {time.time() - t0:.1f} s", flush=True)
        for s in sols[:3]:
            import dsrg_verify  # noqa: E402
            G = inst.graph(s, Di12, R, C)
            rep = dsrg_verify.check(G.tolist(), (48, 9, 5, 0, 2))
            print(f"  SOLUTION pivot {piv[pi]}: DSRG check {'yes' if rep.ok else 'no: ' + str(rep.violation)}")
            if rep.ok:
                print("  MATRIX", G.tolist(), flush=True)
    print(f"total run {a.kind} [{a.lo}, {hi}): live pivots {alive}, nodes {total}, solutions {nsol}")
    return 0


if __name__ == "__main__":
    sys.exit(main())
