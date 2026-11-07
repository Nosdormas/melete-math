"""Rank of A − θI on the closed neighbourhood of a vertex for λ = 0, on graphs and on the table.

    python -X utf8 checks/closed_nbhd_check.py [--mutate plus-one|det-mu|lambda-one] [--quiet]

Part "graphs": at every vertex of every catalogue matrix with λ = 0, the structure of N[x], the
determinant formula of (A − θI)[N[x]] against the exact integer determinant, and the bound
|N[x]| ≤ rank(A − θI) = 1 + m'. Part "sets": the sets of the table snapshot with λ = 0 that the bound
2k − t + 1 > m' excludes; none of them may be constructed. Exit code 0 - no violations; a mutant must
end with exit code 1.
"""
from __future__ import annotations

import argparse
import sys
from collections import Counter
from pathlib import Path

HERE = Path(__file__).resolve().parent
ROOT = HERE.parent
sys.path.insert(0, str(ROOT / "lib"))
sys.path.insert(0, str(HERE))

import dsrg_cells  # noqa: E402
import graph_controls as nc  # noqa: E402
from kernel_frame import rank_int  # noqa: E402
from kernel_frame_check import spectrum  # noqa: E402

MUTATIONS = ("plus-one", "det-mu", "lambda-one")


def det_int(M: list[list[int]]) -> int:
    M = [list(r) for r in M]
    n = len(M)
    if n == 0:
        return 1
    sign, prev = 1, 1
    for c in range(n - 1):
        piv = next((i for i in range(c, n) if M[i][c] != 0), None)
        if piv is None:
            return 0
        if piv != c:
            M[c], M[piv] = M[piv], M[c]
            sign = -sign
        for i in range(c + 1, n):
            for j in range(c + 1, n):
                M[i][j] = (M[i][j] * M[c][c] - M[i][c] * M[c][j]) // prev
            M[i][c] = 0
        prev = M[c][c]
    return sign * M[n - 1][n - 1]


def det_formula(params, theta: int, mutate=None) -> int:
    v, k, t, lam, mu = params
    tail = mu * k if mutate == "det-mu" else mu * (k - t)
    core = theta ** 3 - t * theta - tail
    e = 2 * k - t - 2
    sign = -1 if (t + 1) % 2 else 1
    if e >= 0:
        return sign * theta ** e * core
    return sign * core // theta ** (-e)


def local_structure(A, params, x: int) -> list[str]:
    v, k, t, lam, mu = params
    out = {j for j in range(v) if A[x][j]}
    inn = {i for i in range(v) if A[i][x]}
    S = {x} | out | inn
    Q, P = out - inn, inn - out
    bad = []
    if len(S) != 2 * k - t + 1:
        bad.append(f"|N[x]| = {len(S)} ≠ 2k − t + 1 = {2 * k - t + 1}")
    for i in S:
        for j in S:
            if not A[i][j]:
                continue
            ok = (i == x and j in out) or (i in inn and j == x) or (i in Q and j in P)
            if not ok:
                bad.append(f"arc {i}→{j} inside N[x] outside x→O, Γ⁻→x, Q→P")
    for q in Q:
        d = sum(A[q][p] for p in P)
        if d != mu:
            bad.append(f"q={q}: out-arcs to P {d} ≠ μ")
    for p in P:
        d = sum(A[q][p] for q in Q)
        if d != mu:
            bad.append(f"p={p}: in-arcs from Q {d} ≠ μ")
    return bad


def check_graphs(mutate) -> tuple[Counter, list[str]]:
    lam_target = 1 if mutate == "lambda-one" else 0
    graphs = nc.load_graphs(nc.catalog_files(), lambda p: True)
    items = []
    for g in graphs:
        for h in (g, nc.complement(g)):
            if h["params"][3] == lam_target:
                items.append(h)
    res = Counter()
    bad = []
    seen_sets = set()
    for h in items:
        p = h["params"]
        v, k, t, lam, mu = p
        A = h["A"].tolist()
        res["graphs"] += 1
        seen_sets.add(p)
        sp = spectrum(p)
        thetas = []
        if sp:
            r, s, f, g = sp
            thetas = [(r, g), (s, f)]
        ranks = {}
        for theta, m_prime in thetas:
            M = [[A[i][j] - (theta if i == j else 0) for j in range(v)] for i in range(v)]
            ranks[theta] = rank_int(M)
            if ranks[theta] != 1 + m_prime:
                bad.append(f"{h['id']} {p}: rank(A − {theta}I) = {ranks[theta]} ≠ 1 + m' = {1 + m_prime}")
        for x in range(v):
            res["vertices"] += 1
            for line in local_structure(A, p, x):
                bad.append(f"{h['id']} {p} x={x}: {line}")
            S = sorted({x} | {j for j in range(v) if A[x][j]} | {i for i in range(v) if A[i][x]})
            for theta, m_prime in thetas:
                sub = [[A[i][j] - (theta if i == j else 0) for j in S] for i in S]
                d = det_int(sub)
                want = det_formula(p, theta, mutate)
                res["dets"] += 1
                if d != want:
                    bad.append(f"{h['id']} {p} x={x} θ={theta}: det = {d} ≠ formula {want}")
                if d != 0:
                    res["nonsingular"] += 1
                    bound = len(S) + (1 if mutate == "plus-one" else 0)
                    if bound > ranks[theta]:
                        bad.append(f"{h['id']} {p} x={x} θ={theta}: |N[x]| = {len(S)}"
                                   f"{' + 1' if mutate == 'plus-one' else ''} > rank = {ranks[theta]}")
                    if len(S) == ranks[theta]:
                        res["tight"] += 1
    res["sets"] = len(seen_sets)
    return res, bad


def bound_verdict(params, mutate=None):
    v, k, t, lam, mu = params
    sp = spectrum(params)
    if not sp:
        return []
    r, s, f, g = sp
    out = []
    extra = 1 if mutate == "plus-one" else 0
    for theta, m_prime in ((r, g), (s, f)):
        if theta == 0 or theta ** 3 - t * theta - mu * (k - t) == 0:
            continue
        out.append((theta, m_prime, 2 * k - t + extra <= m_prime))
    return out


def check_sets(mutate) -> tuple[list, list[str]]:
    snap = dsrg_cells.load_snapshot()
    excluded, bad = [], []
    for p in sorted(snap):
        if p[3] != 0:
            continue
        verdict = bound_verdict(p, mutate)
        if all(ok for _, _, ok in verdict):
            continue
        st = snap[p]
        excluded.append((p, st, verdict))
        if st == "b":
            bad.append(f"set {p} is constructed (b), but the bound excludes it: {verdict}")
    return excluded, bad


def main() -> int:
    res, bad_g = check_graphs(ARGS.mutate)
    excluded, bad_s = check_sets(ARGS.mutate)
    if not ARGS.quiet:
        print(f"graphs with λ = {1 if ARGS.mutate == 'lambda-one' else 0}: {res['graphs']} (sets {res['sets']}),"
              f" vertices {res['vertices']}, determinants {res['dets']}, nonsingular {res['nonsingular']},"
              f" bound |N[x]| = rank attained {res['tight']} times")
        print(f"snapshot sets with λ = 0 excluded by the bound: {len(excluded)}")
        for p, st, verdict in excluded:
            ths = ", ".join(f"θ={th}: 2k−t={2 * p[1] - p[2]} {'≤' if ok else '>'} m'={mp}" for th, mp, ok in verdict)
            print(f"  {p} status {st}: {ths}")
    bad = bad_g + bad_s
    print(f"violations: {len(bad)} (graphs {len(bad_g)}, sets {len(bad_s)})")
    for line in bad[:20]:
        print("  " + line)
    if ARGS.mutate:
        print(f"mutant {ARGS.mutate}: {'caught' if bad else 'NOT caught'}")
    return 1 if bad else 0


if __name__ == "__main__":
    ap = argparse.ArgumentParser(add_help=True)
    ap.add_argument("--mutate", choices=MUTATIONS)
    ap.add_argument("--quiet", action="store_true")
    ARGS = ap.parse_args()
    sys.exit(main())
