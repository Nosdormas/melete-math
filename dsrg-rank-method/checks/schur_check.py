"""Schur complement of A − θI outside the closed neighbourhood for λ = 0, on catalogue graphs.

    python -X utf8 checks/schur_check.py [--mutate y-q|idem|rank|f-p3]

Exact check in fractions at every (vertex, root θ) with a nonsingular block. Exit code 0 - no
violations; a mutant must end with exit code 1.
"""
from __future__ import annotations

import argparse
import sys
from collections import Counter
from fractions import Fraction as Fr
from pathlib import Path

HERE = Path(__file__).resolve().parent
ROOT = HERE.parent
sys.path.insert(0, str(ROOT / "lib"))
sys.path.insert(0, str(HERE))

import graph_controls as nc  # noqa: E402
from kernel_frame import inverse  # noqa: E402
from kernel_frame_check import spectrum  # noqa: E402

MUTATIONS = ("y-q", "idem", "rank", "f-p3")


def rank(M):
    A = [[Fr(x) for x in row] for row in M]
    if not A or not A[0]:
        return 0
    n, m = len(A), len(A[0])
    r = 0
    for c in range(m):
        p = next((i for i in range(r, n) if A[i][c] != 0), None)
        if p is None:
            continue
        A[r], A[p] = A[p], A[r]
        for i in range(n):
            if i != r and A[i][c] != 0:
                f = A[i][c] / A[r][c]
                A[i] = [a - f * b for a, b in zip(A[i], A[r])]
        r += 1
        if r == n:
            break
    return r


def matmul(X, Y):
    Yt = list(zip(*Y))
    return [[sum(a * b for a, b in zip(row, col)) for col in Yt] for row in X]


def roots(params):
    sp = spectrum(params)
    if not sp:
        return []
    r, s, f, g = sp
    return [(r, s, g), (s, r, f)]


def f_formula(A, params, x, theta, w, w2, mutate=None):
    v, k, t, lam, mu = params
    out_x = {j for j in range(v) if A[x][j]}
    in_x = {i for i in range(v) if A[i][x]}
    Q = out_x - in_x
    P = in_x - out_x
    N = out_x | in_x
    beta = sum(A[p][w2] for p in P)
    gamma = sum(A[w][q] for q in Q)
    z = Fr(mu * (theta + beta), theta * t + mu * (k - t) - theta ** 3)
    p2 = sum(A[w][n] * A[n][w2] for n in N)
    p3 = 0 if mutate == "f-p3" else sum(A[w][q] * A[q][p] * A[p][w2] for q in Q for p in P)
    th = Fr(theta)
    return z * (theta + gamma) * mu / th ** 2 - p2 / th - p3 / th ** 2


def check(mutate):
    graphs = nc.load_graphs(nc.catalog_files(), lambda p: True)
    items = [h for g in graphs for h in (g, nc.complement(g)) if h["params"][3] == 0]
    res = Counter()
    gaps = Counter()
    bad = []
    for h in items:
        p = h["params"]
        v, k, t, lam, mu = p
        A = h["A"].tolist()
        res["graphs"] += 1
        for theta, theta2, m2 in roots(p):
            if theta == 0 or theta ** 3 - t * theta - mu * (k - t) == 0:
                continue
            K = [[A[i][j] - (theta if i == j else 0) for j in range(v)] for i in range(v)]
            K2 = [[A[i][j] - (theta2 if i == j else 0) for j in range(v)] for i in range(v)]
            rk = rank(K)
            if rk != 1 + m2:
                bad.append(f"{h['id']} {p} θ={theta}: rank(A − θI) = {rk} ≠ 1 + m'")
            for x in range(v):
                tag = f"{h['id']} {p} x={x} θ={theta}"
                out_x = {j for j in range(v) if A[x][j]}
                in_x = {i for i in range(v) if A[i][x]}
                Qx = out_x - in_x
                Px = in_x - out_x
                N = sorted({x} | out_x | in_x)
                W = [w for w in range(v) if w not in N]
                res["frames"] += 1
                yq = Fr(1, mu) if mutate == "y-q" else Fr(0)
                yhat = [(1 + Fr(theta, mu) if j == x else 0) + (Fr(1, mu) if j in in_x else 0)
                        + (yq if j in Qx else 0) for j in range(v)]
                Ky = [sum(K[i][j] * yhat[j] for j in range(v)) for i in range(v)]
                if any(val != 1 for val in Ky):
                    bad.append(f"{tag}: (A − θI)ŷ ≠ 1")
                D = [[K[i][j] for j in N] for i in N]
                Di = inverse(D)
                if Di is None:
                    bad.append(f"{tag}: D is singular")
                    continue
                if [sum(row) for row in Di] != [yhat[n] for n in N]:
                    bad.append(f"{tag}: D⁻¹·1 ≠ ŷ")
                zhat = [(1 + Fr(theta, mu) if n == x else 0) + (Fr(1, mu) if n in out_x else 0) for n in N]
                if [sum(Di[a][b] for a in range(len(N))) for b in range(len(N))] != zhat:
                    bad.append(f"{tag}: 1ᵀ·D⁻¹ ≠ ž")
                if not W:
                    continue
                B = [[A[n][w] for w in W] for n in N]
                C = [[A[w][n] for n in N] for w in W]
                CDB = matmul(matmul(C, Di), B)
                nW = len(W)
                S = [[K[W[a]][W[b]] - CDB[a][b] for b in range(nW)] for a in range(nW)]
                rs = rank(S)
                want = m2 - (2 * k - t) + (1 if mutate == "rank" else 0)
                gaps[(p, theta, rs)] += 1
                if rs != want:
                    bad.append(f"{tag}: rank S = {rs} ≠ m' − (2k − t) = {want}")
                if any(val != 0 for row in matmul(B, S) for val in row):
                    bad.append(f"{tag}: B·S ≠ 0")
                if any(val != 0 for row in matmul(S, C) for val in row):
                    bad.append(f"{tag}: S·C ≠ 0")
                coef = (theta - theta2) if mutate == "idem" else (theta2 - theta)
                S_sq = matmul(S, S)
                if any(S_sq[a][b] != coef * S[a][b] for a in range(nW) for b in range(nW)):
                    bad.append(f"{tag}: S² ≠ (θ' − θ)S")
                right = nW - rank([[K2[i][w] for w in W] for i in range(v)])
                left = nW - rank([[K2[w][j] for w in W] for j in range(v)])
                if right != rs or left != rs:
                    bad.append(f"{tag}: dimensions of θ'-vectors outside N {right}, {left} ≠ rank S = {rs}")
                for a, w in enumerate(W):
                    for b, w2 in enumerate(W):
                        res["entries"] += 1
                        if CDB[a][b] != f_formula(A, p, x, theta, w, w2, mutate):
                            bad.append(f"{tag}: f({w}, {w2}) ≠ formula")
                            break
                if rs == 0:
                    res["recovered"] += 1
    return res, gaps, bad


def main() -> int:
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("--mutate", choices=MUTATIONS)
    a = ap.parse_args()
    try:
        res, gaps, bad = check(a.mutate)
    except nc.InputError as e:
        print(f"input error: {e}", file=sys.stderr)
        return 2
    print(f"graphs with λ = 0: {res['graphs']}; frames (vertex, θ) with nonsingular D: {res['frames']}; "
          f"cells of the formula for f: {res['entries']}; frames with S = 0 (block outside N[x] recovered entirely): "
          f"{res['recovered']}")
    print("rank S by sets and θ — (set, θ, rank S): number of vertices")
    for key in sorted(gaps):
        print(f"  {key}: {gaps[key]}")
    for line in bad[:10]:
        print("VIOLATION", line)
    print(f"violations: {len(bad)}{' (mutant ' + a.mutate + ')' if a.mutate else ''}")
    return 1 if bad else 0


if __name__ == "__main__":
    sys.exit(main())
