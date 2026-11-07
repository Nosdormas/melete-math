"""Recovery of the graph around a vertex for λ = 0: the cover Φ, the Schur complement of the open
neighbourhood and the pivot rows of the Schur complement.

    python -X utf8 checks/vertex_recovery_check.py [--mutate phi-delta|z-qp|pivot|z-rank]

Exit code 0 - no violations; a mutant must end with exit code 1.
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

MUTATIONS = ("phi-delta", "z-qp", "pivot", "z-rank")


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


def mm(X, Y):
    Yt = list(zip(*Y))
    return [[sum(a * b for a, b in zip(row, col)) for col in Yt] for row in X]


def pivots(S, r):
    n = len(S)
    rows, cols = [], []
    for i in range(n):
        for j in range(n):
            if j in cols:
                continue
            if rank([[S[a][b] for b in cols + [j]] for a in rows + [i]]) == len(rows) + 1:
                rows.append(i)
                cols.append(j)
                break
        if len(rows) == r:
            break
    return rows, cols


def check(mutate):
    graphs = nc.load_graphs(nc.catalog_files(), lambda p: True)
    items = [h for g in graphs for h in (g, nc.complement(g)) if h["params"][3] == 0]
    res = Counter()
    ranks = Counter()
    bad = []
    for h in items:
        p = h["params"]
        v, k, t, lam, mu = p
        A = h["A"].tolist()
        res["graphs"] += 1
        sp = spectrum(p)
        if not sp:
            continue
        r_, s_, f_, g_ = sp
        for theta, theta2 in ((r_, s_), (s_, r_)):
            if theta == 0 or theta ** 3 - t * theta - mu * (k - t) == 0:
                continue
            delta = theta - theta2
            Delta = theta * t + mu * (k - t) - theta ** 3
            th = Fr(theta)
            K = [[A[i][j] - (theta if i == j else 0) for j in range(v)] for i in range(v)]
            for x in range(v):
                tag = f"{h['id']} {p} x={x} θ={theta}"
                out_x = {j for j in range(v) if A[x][j]}
                in_x = {i for i in range(v) if A[i][x]}
                Q = sorted(out_x - in_x)
                P = sorted(in_x - out_x)
                Np = sorted(out_x | in_x)
                N = [x] + Np
                W = [w for w in range(v) if w not in N]
                res["frames"] += 1
                D = [[K[i][j] for j in N] for i in N]
                Di = inverse(D)
                if Di is None:
                    bad.append(f"{tag}: D is singular")
                    continue
                B = [[A[n][w] for w in W] for n in N]
                C = [[A[w][n] for n in N] for w in W]
                D2 = mm(D, D)
                dcoef = 0 if mutate == "phi-delta" else delta
                BC = mm(B, C) if W else [[0] * len(N) for _ in N]
                for a in range(len(N)):
                    for b in range(len(N)):
                        if BC[a][b] != mu - D2[a][b] - dcoef * D[a][b]:
                            bad.append(f"{tag}: B·C ≠ μJ − D² − δD at ({N[a]}, {N[b]})")
                for a, n in enumerate(N):
                    if sum(B[a]) != k - sum(A[n][m] for m in N) or \
                            sum(C[w][a] for w in range(len(W))) != k - sum(A[m][n] for m in N):
                        bad.append(f"{tag}: degrees {n} in W")
                if not W:
                    continue
                res["frames_w"] += 1
                AQP = [[A[i][j] if (i in Q and j in P) else 0 for j in Np] for i in Np]
                if any(A[i][j] != AQP[a][b] for a, i in enumerate(Np) for b, j in enumerate(Np)):
                    bad.append(f"{tag}: inside N' not only arcs Q → P")
                if any(val for row in mm(AQP, AQP) for val in row):
                    bad.append(f"{tag}: A_QP² ≠ 0")
                Kp = [[K[i][j] for j in Np] for i in Np]
                inv_claim = [[-(th * (1 if a == b else 0) + AQP[a][b]) / th ** 2 for b in range(len(Np))]
                             for a in range(len(Np))]
                eye = mm(Kp, inv_claim)
                if any(eye[a][b] != (1 if a == b else 0) for a in range(len(Np)) for b in range(len(Np))):
                    bad.append(f"{tag}: the inverse of the block N' is not −(θI + A_QP)/θ²")
                nW = len(W)
                CDB = mm(mm(C, Di), B)
                S = [[K[W[a]][W[b]] - CDB[a][b] for b in range(nW)] for a in range(nW)]
                rs = rank(S)
                gam = [sum(A[w][q] for q in Q) for w in W]
                bet = [sum(A[q][w] for q in P) for w in W]
                Z = []
                for a, w in enumerate(W):
                    row = []
                    for b, w2 in enumerate(W):
                        p2 = sum(A[w][n] * A[n][w2] for n in Np)
                        p3 = 0 if mutate == "z-qp" else sum(A[w][q] * A[q][pp] * A[pp][w2] for q in Q for pp in P)
                        row.append(theta ** 2 * K[w][w2] + theta * p2 + p3)
                    Z.append(row)
                Cp = [[A[w][n] for n in Np] for w in W]
                Bp = [[A[n][w] for w in W] for n in Np]
                schur = mm(mm(Cp, inv_claim), Bp)
                for a in range(nW):
                    for b in range(nW):
                        if th ** 2 * (K[W[a]][W[b]] - schur[a][b]) != Z[a][b]:
                            bad.append(f"{tag}: Z ≠ θ²·Schur complement of the block N'")
                            break
                    else:
                        continue
                    break
                coef = Fr(mu * mu, Delta)
                for a in range(nW):
                    for b in range(nW):
                        if Z[a][b] != coef * (theta + gam[a]) * (theta + bet[b]) + th ** 2 * S[a][b]:
                            bad.append(f"{tag}: Z ≠ (μ²/Δ)(θ + γ)(θ + β)ᵀ + θ²S")
                            break
                    else:
                        continue
                    break
                rz = rank(Z)
                bound = rs if mutate == "z-rank" else rs + 1
                if rz > bound:
                    bad.append(f"{tag}: rank Z = {rz} > {bound}")
                rfull = rank([[K[i][j] for j in range(v) if j != x] for i in range(v) if i != x])
                if rz != rfull - len(Np):
                    bad.append(f"{tag}: rank Z = {rz} ≠ rank(A − θI)[V ∖ x] − |N'| = {rfull - len(Np)}")
                ranks[(p, theta, rs, rz)] += 1
                R_, Rc = pivots(S, rs)
                if len(R_) != rs:
                    bad.append(f"{tag}: no pivot block of order {rs}")
                    continue
                if rs:
                    Sp = [[S[a][b] for b in Rc] for a in R_]
                    Spi = inverse(Sp)
                    left = [[S[a][b] for b in Rc] for a in range(nW)]
                    right = [[S[a][b] for b in range(nW)] for a in R_]
                    S_rec = mm(mm(left, Spi), right)
                else:
                    S_rec = [[Fr(0)] * nW for _ in range(nW)]
                sign = -1 if mutate == "pivot" else 1
                for a in range(nW):
                    for b in range(nW):
                        val = theta * (1 if a == b else 0) + CDB[a][b] + sign * S_rec[a][b]
                        if val != A[W[a]][W[b]]:
                            bad.append(f"{tag}: A[W, W] not recovered from the pivots at ({W[a]}, {W[b]})")
                            break
                    else:
                        continue
                    break
                res["rebuilt"] += 1
    return res, ranks, bad


def main() -> int:
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("--mutate", choices=MUTATIONS)
    a = ap.parse_args()
    try:
        res, ranks, bad = check(a.mutate)
    except nc.InputError as e:
        print(f"input error: {e}", file=sys.stderr)
        return 2
    print(f"graphs with λ = 0: {res['graphs']}; frames (vertex, θ) with nonsingular D: {res['frames']}, "
          f"of them with W ≠ ∅: {res['frames_w']}; A[W, W] recovered from the pivot rows S: {res['rebuilt']}")
    print("(set, θ, rank S, rank Z): number of vertices")
    for key in sorted(ranks):
        print(f"  {key}: {ranks[key]}")
    for line in bad[:10]:
        print("VIOLATION", line)
    print(f"violations: {len(bad)}{' (mutant ' + a.mutate + ')' if a.mutate else ''}")
    return 1 if bad else 0


if __name__ == "__main__":
    sys.exit(main())
