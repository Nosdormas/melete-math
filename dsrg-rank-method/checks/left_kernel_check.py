"""Left kernel of K_1 on {x} ∪ Γ⁺(x) for λ = 1, t = 2μ, on catalogue graphs and table sets.

    python -X utf8 checks/left_kernel_check.py [--max-v 40] [--mutate plus-one|no-ell|theta-swap] [--quiet]

Part "bound": dim of the left kernel of the rows {x} ∪ Γ⁺(x) of K_θ is at least k + 1 − m'. Part
"structure": the vectors w_a and the sum equation on graphs with λ = 1, t = 2μ. Part "sets": the profile
search on every set of the snapshot with λ = 1, t = 2μ; the row of (55, 16, 12, 1, 6) reads 750 profiles,
747 excluded by item 2 and 3 by item 3. Exit code 0 - no violations; a mutant must end with exit code 1.
"""
from __future__ import annotations

import argparse
import math
import sys
from collections import Counter
from fractions import Fraction
from functools import lru_cache
from pathlib import Path

HERE = Path(__file__).resolve().parent
ROOT = HERE.parent
sys.path.insert(0, str(ROOT / "lib"))

import dsrg_cells  # noqa: E402
import graph_controls as nc  # noqa: E402
from dsrg_local_types import profiles  # noqa: E402
from kernel_frame import rank_int  # noqa: E402

MUTATIONS = ("plus-one", "no-ell", "theta-swap", "no-colsum", "gamma-sign")
EXPECTED_EXCLUDED = {(49, 15, 12, 1, 6): "n", (55, 16, 12, 1, 6): "o", (104, 27, 18, 1, 9): "n"}


def spectrum(params):
    v, k, t, lam, mu = params
    disc = (lam - mu) ** 2 + 4 * (t - mu)
    if disc <= 0:
        return None
    sq = math.isqrt(disc)
    if sq * sq != disc or (lam - mu + sq) % 2:
        return None
    r, s = (lam - mu + sq) // 2, (lam - mu - sq) // 2
    num = k + (v - 1) * r
    if num % (r - s):
        return None
    g = num // (r - s)
    return r, s, v - 1 - g, g


def nullspace(rows, ncols: int) -> list[list[Fraction]]:
    A = [[Fraction(x) for x in row] for row in rows]
    pivots, r = [], 0
    for c in range(ncols):
        piv = next((i for i in range(r, len(A)) if A[i][c] != 0), None)
        if piv is None:
            continue
        A[r], A[piv] = A[piv], A[r]
        pv = A[r][c]
        A[r] = [x / pv for x in A[r]]
        for i in range(len(A)):
            if i != r and A[i][c] != 0:
                f = A[i][c]
                A[i] = [a - f * b for a, b in zip(A[i], A[r])]
        pivots.append(c)
        r += 1
    free = [c for c in range(ncols) if c not in pivots]
    basis = []
    for fc in free:
        vec = [Fraction(0)] * ncols
        vec[fc] = Fraction(1)
        for i, pc in enumerate(pivots):
            vec[pc] = -A[i][fc]
        basis.append(vec)
    return basis


def pred_map(A, x: int, v: int):
    out = [j for j in range(v) if A[x][j]]
    pred = {}
    for y in out:
        ps = [z for z in out if A[z][y]]
        if len(ps) != 1:
            return out, None
        pred[y] = ps[0]
    return out, pred


def components(pred: dict) -> list[list[int]]:
    parent = {y: y for y in pred}

    def find(a):
        while parent[a] != a:
            parent[a] = parent[parent[a]]
            a = parent[a]
        return a

    for y, p in pred.items():
        a, b = find(y), find(p)
        if a != b:
            parent[a] = b
    comps: dict = {}
    for y in pred:
        comps.setdefault(find(y), []).append(y)
    return sorted(comps.values())


def cycles(pred: dict) -> list[list[int]]:
    seen, out = set(), []
    for start in pred:
        path, pos, y = [], {}, start
        while y not in seen and y not in pos:
            pos[y] = len(path)
            path.append(y)
            y = pred[y]
        if y in pos:
            out.append(path[pos[y]:])
        seen.update(path)
    return out


def part_bound(graphs, max_v: int, mutate) -> tuple[Counter, list[str]]:
    res, bad = Counter(), []
    extra = 1 if mutate == "plus-one" else 0
    for h in graphs:
        p = h["params"]
        v, k, t, lam, mu = p
        sp = spectrum(p)
        if not sp or not (0 < t < k < v - 1):
            continue
        r, s, f, g = sp
        A = h["A"].tolist()
        verts = range(v) if v <= max_v else range(2)
        for theta, mprime in ((r, g), (s, f)):
            K = [[v * (A[i][j] - (theta if i == j else 0)) - (k - theta) for j in range(v)] for i in range(v)]
            res["pairs"] += 1
            if v <= max_v:
                rk = rank_int(K)
                if rk != mprime:
                    bad.append(f"{h['id']} {p} θ={theta}: rank K = {rk} ≠ m' = {mprime}")
            for x in verts:
                S = [x] + [j for j in range(v) if A[x][j]]
                null = len(S) - rank_int([K[i] for i in S])
                bound = k + 1 - mprime
                res["vertices"] += 1
                if bound > 0:
                    res["positive"] += 1
                if null == bound:
                    res["tight"] += 1
                if null < bound + extra:
                    bad.append(f"{h['id']} {p} θ={theta} x={x}: left kernel of K[S, V] = {null} < {bound + extra}")
    return res, bad


def part_structure(graphs, mutate) -> tuple[Counter, list[str]]:
    res, bad = Counter(), []
    for h in graphs:
        p = h["params"]
        v, k, t, lam, mu = p
        if not (lam == 1 and t == 2 * mu and mu > 0):
            continue
        r, s, f, g = spectrum(p)
        A = h["A"].tolist()
        res["graphs"] += 1
        theta = s if mutate == "theta-swap" else 1
        K = [[v * (A[i][j] - (theta if i == j else 0)) - (k - theta) for j in range(v)] for i in range(v)]
        for x in range(v):
            out, pred = pred_map(A, x, v)
            if pred is None:
                bad.append(f"{h['id']} {p} x={x}: a vertex of Γ⁺(x) has not exactly one in-arc from Γ⁺(x)")
                continue
            res["vertices"] += 1
            inn = {i for i in range(v) if A[i][x]}
            comps = components(pred)
            c = len(comps)
            n = [len(C) for C in comps]
            m = [sum(1 for y in C if y in inn) for C in comps]
            outside = [z for z in range(v) if z != x and not A[x][z]]
            d = [k * m[i] - t * n[i] for i in range(c)]
            D = [d]
            if mutate != "no-ell":
                for z in outside:
                    ell = [sum(A[y][z] for y in C) for C in comps]
                    D.append([2 * ell[i] - m[i] for i in range(c)])
            ker = nullspace(D, c)
            if mutate != "no-ell" and c - len(ker) == 1 and any(d):
                j = next(i for i in range(c) if d[i])
                target = Fraction(k - 1, mu) * (1 if mutate == "gamma-sign" else -1)
                gs = [Fraction(row[j], d[j]) for row in D[1:]]
                off_line = any(Fraction(row[i]) != gam * d[i] for row, gam in zip(D[1:], gs) for i in range(c))
                if off_line or sum(gs) != target:
                    bad.append(f"{h['id']} {p} x={x}: 4(b) Σγ_z = {sum(gs)}, target {target}")
                res["gamma"] += 1
                res[("gamma", p)] += 1
            S = [x] + out
            null = len(S) - rank_int([K[i] for i in S])
            if len(ker) != null:
                bad.append(f"{h['id']} {p} x={x}: dim ker D = {len(ker)} ≠ left kernel of K_1[S, V] = {null}")
            for a in ker:
                w = {x: sum(a[i] * m[i] for i in range(c)) / 2}
                for i, C in enumerate(comps):
                    for y in C:
                        w[y] = a[i]
                row = [sum(w[i] * K[i][j] for i in S) for j in range(v)]
                if any(row):
                    bad.append(f"{h['id']} {p} x={x}: w_a is not in the left kernel of K[S, V]")
                    break
            if null < k + 1 - g:
                bad.append(f"{h['id']} {p} x={x}: item 2 violated: {null} < k + 1 − g = {k + 1 - g}")
            cyc = cycles(pred)
            R = [[len(C) for C in cyc]]
            for z in outside:
                R.append([sum(A[z][y] for y in C) for C in cyc])
            dimR = len(cyc) - rank_int(R)
            dimE = len(out) - rank_int([[A[i][j] - (1 if i == j else 0) for j in out] for i in range(v)])
            if dimR != dimE:
                bad.append(f"{h['id']} {p} x={x}: dim ker R = {dimR} ≠ dim E_1 ∩ ℝ^O = {dimE}")
            need = k + 1 - g if any(d) else k - g
            if dimE < need:
                bad.append(f"{h['id']} {p} x={x}: item 3 violated: {dimE} < {need}")
            res["comps"] += c
    if mutate != "no-ell" and res["gamma"] == 0:
        bad.append("control 4(b) is empty: no vertex with rank D = 1 and d ≠ 0")
    return res, bad


def gammas(prof, d) -> list[Fraction]:
    cand = None
    for (n, m), di in zip(prof, d):
        if di == 0:
            if m % 2:
                return []
            continue
        here = {Fraction(e - m, di) for e in range(0, 2 * n + 1, 2)}
        cand = here if cand is None else cand & here
        if not cand:
            return []
    return sorted(cand) if cand is not None else [Fraction(0)]


def sum_reachable(values: list[Fraction], count: int, target: Fraction) -> bool:
    if not values:
        return False
    den = 1
    for q in values + [target]:
        den = den * q.denominator // math.gcd(den, q.denominator)
    ints = sorted({int(q * den) for q in values})
    tq = target * den
    if tq.denominator != 1:
        return False
    tgt = int(tq)
    lo, hi = ints[0], ints[-1]
    if not (lo * count <= tgt <= hi * count):
        return False
    shifted = [q - lo for q in ints]
    goal = tgt - lo * count

    @lru_cache(maxsize=None)
    def can(j: int, s: int) -> bool:
        if s < 0 or s > (hi - lo) * j:
            return False
        if j == 0:
            return s == 0
        return any(can(j - 1, s - q) for q in shifted)

    return can(count, goal)


def profile_verdict(params, prof, mutate=None) -> str:
    v, k, t, lam, mu = params
    g = spectrum(params)[3]
    c = len(prof)
    base = k + 1 - g
    d = [k * m - t * n for n, m in prof]
    dz = any(d)
    if c < base + (1 if dz else 0):
        return "T0"
    if c - base != (1 if dz else 0):
        return "open"
    if not dz:
        return "open" if all(m % 2 == 0 for _, m in prof) else "T1"
    gs = gammas(prof, d)
    if not gs:
        return "T1"
    if mutate == "no-colsum":
        return "open"
    return "open" if sum_reachable(gs, v - k - 1, Fraction(-(k - 1), mu)) else "T1"


def census(params, mutate=None) -> Counter:
    v, k, t, lam, mu = params
    cnt = Counter()
    for prof in profiles(k, t):
        cnt["all"] += 1
        res = profile_verdict(params, prof, mutate)
        cnt[res] += 1
        if res == "open":
            cnt[("c", len(prof))] += 1
    return cnt


def part_sets(mutate) -> tuple[list, list[str]]:
    snap = dsrg_cells.load_snapshot()
    rows, bad, excluded = [], [], {}
    for p in sorted(q for q in snap if q[3] == 1 and q[2] == 2 * q[4] and q[4] > 0):
        if not spectrum(p):
            continue
        cnt = census(p, mutate)
        st = snap[p]
        rows.append((p, st, spectrum(p)[3], cnt))
        if cnt["open"] == 0:
            excluded[p] = st
            if st == "b":
                bad.append(f"constructed set {p} lost all profiles")
    if excluded != EXPECTED_EXCLUDED:
        bad.append(f"excluded sets {sorted(excluded)} ≠ expected {sorted(EXPECTED_EXCLUDED)}")
    return rows, bad


def main() -> int:
    graphs = []
    for g in nc.load_graphs(nc.catalog_files(), lambda p: True):
        graphs.append(g)
        graphs.append(nc.complement(g))
    mut = ARGS.mutate
    res_b, bad_b = part_bound(graphs, ARGS.max_v, mut if mut == "plus-one" else None)
    res_s, bad_s = part_structure(graphs, mut if mut in ("no-ell", "theta-swap", "gamma-sign") else None)
    rows, bad_n = part_sets(mut if mut == "no-colsum" else None)
    if not ARGS.quiet:
        print(f"bound: pairs (graph, θ) {res_b['pairs']}, vertices {res_b['vertices']}, with positive bound"
              f" {res_b['positive']}, bound exact {res_b['tight']} times")
        print(f"structure: graphs with λ = 1, t = 2μ {res_s['graphs']}, vertices {res_s['vertices']},"
              f" components {res_s['comps']}")
        per = ", ".join(f"{key[1]} {n}" for key, n in sorted(res_s.items(), key=str) if isinstance(key, tuple))
        print(f"control 4(b) Σγ_z = −(k − 1)/μ: vertices {res_s['gamma']} ({per})")
        print("snapshot sets with λ = 1, t = 2μ: set | status | g | k + 1 − g | profiles | T0 | T1 | left")
        for p, st, g, cnt in rows:
            print(f"  {p} | {st} | {g} | {p[1] + 1 - g} | {cnt['all']} | {cnt['T0']} | {cnt['T1']} | {cnt['open']}")
    bad = bad_b + bad_s + bad_n
    print(f"violations: {len(bad)} (bound {len(bad_b)}, structure {len(bad_s)}, sets {len(bad_n)})")
    for line in bad[:20]:
        print("  " + line)
    if mut:
        print(f"mutant {mut}: {'caught' if bad else 'NOT caught'}")
    return 1 if bad else 0


if __name__ == "__main__":
    ap = argparse.ArgumentParser(add_help=True)
    ap.add_argument("--mutate", choices=MUTATIONS)
    ap.add_argument("--max-v", type=int, default=40)
    ap.add_argument("--quiet", action="store_true")
    ARGS = ap.parse_args()
    sys.exit(main())
