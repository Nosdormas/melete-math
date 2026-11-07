"""Kernel frame of K_θ = A − θI on catalogue graphs with small multiplicity.

    python -X utf8 checks/kernel_frame_check.py [--max-m 12] [--mutate MUTANT] [--quiet]

Checks items 1-5 of the kernel-frame lemma at every vertex of every catalogue graph (and complement)
whose eigenvalue multiplicity is at most --max-m. Exit code 0 - no violations, 1 - violations or a caught
mutant.
"""
from __future__ import annotations

import math
import sys
from fractions import Fraction
from pathlib import Path

import numpy as np

HERE = Path(__file__).resolve().parent
ROOT = HERE.parent
sys.path.insert(0, str(ROOT / "lib"))

import graph_controls as nc  # noqa: E402

MUTATIONS = ("theta-swap", "scale", "rank", "frame-closed", "eigen")


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


def nullspace(M, left=False):
    if left:
        M = [list(col) for col in zip(*M)]
    A = [[Fraction(x) for x in row] for row in M]
    n, m = len(A), len(A[0])
    pivots = []
    r = 0
    for c in range(m):
        piv = next((i for i in range(r, n) if A[i][c] != 0), None)
        if piv is None:
            continue
        A[r], A[piv] = A[piv], A[r]
        p = A[r][c]
        A[r] = [x / p for x in A[r]]
        for i in range(n):
            if i != r and A[i][c] != 0:
                f = A[i][c]
                A[i] = [a - f * b for a, b in zip(A[i], A[r])]
        pivots.append(c)
        r += 1
        if r == n:
            break
    basis = []
    for fc in (c for c in range(m) if c not in pivots):
        z = [Fraction(0)] * m
        z[fc] = Fraction(1)
        for i, pc in enumerate(pivots):
            z[pc] = -A[i][fc]
        basis.append(z)
    return basis


def integral(vec):
    den = 1
    for x in vec:
        den = den * x.denominator // math.gcd(den, x.denominator)
    return np.array([int(x * den) for x in vec], dtype=object)


def inverse(M):
    n = len(M)
    A = [[Fraction(x) for x in row] + [Fraction(int(i == j)) for j in range(n)] for i, row in enumerate(M)]
    for c in range(n):
        piv = next((i for i in range(c, n) if A[i][c] != 0), None)
        if piv is None:
            return None
        A[c], A[piv] = A[piv], A[c]
        p = A[c][c]
        A[c] = [x / p for x in A[c]]
        for i in range(n):
            if i != c and A[i][c] != 0:
                f = A[i][c]
                A[i] = [a - f * b for a, b in zip(A[i], A[c])]
    return [row[n:] for row in A]


def fmat(X, Y):
    Yt = list(zip(*Y))
    return [[sum((a * b for a, b in zip(row, col)), Fraction(0)) for col in Yt] for row in X]


def frame_search(K, mult, budget=20000, samples=20000):
    import itertools
    import random
    v = len(K)
    Kf = K.astype(float)
    nodes = 0

    def ok(F):
        return np.linalg.matrix_rank(Kf[np.ix_(F, F)]) == len(F)

    def dfs(F, start):
        nonlocal nodes
        if len(F) == mult:
            return F
        for w in range(start, v - (mult - len(F)) + 1):
            nodes += 1
            if nodes > budget:
                return None
            cand = F + [w]
            if ok(cand):
                res = dfs(cand, w + 1)
                if res is not None:
                    return res
        return None

    found = dfs([], 0)
    if found is not None:
        return found
    if math.comb(v, mult) <= 200000:
        for F in itertools.combinations(range(v), mult):
            if ok(list(F)):
                return list(F)
        return None
    rng = random.Random(85)
    for _ in range(samples):
        F = sorted(rng.sample(range(v), mult))
        if ok(F):
            return F
    return None


def check_graph(g, max_m, mutate, issues):
    params = tuple(int(x) for x in g["params"])
    v, k = params[0], params[1]
    r, s, f, gm = spectrum(params)
    A = np.array(g["A"], dtype=np.int64)
    I = np.eye(v, dtype=np.int64)
    J = np.ones((v, v), dtype=np.int64)
    gid = g["id"]
    out = {"frames": 0, "kernels": 0, "recon": 0, "schur": 0}
    for theta, other, mult in ((r, s, gm), (s, r, f)):
        K = v * (A - theta * I) - (k - theta) * J
        oth = theta if mutate == "theta-swap" else other
        B = A - oth * I
        c = v * (other - theta)
        if mutate == "scale":
            c = -c
        ok1 = (np.array_equal(B @ K, 0 * K) and np.array_equal(K @ B, 0 * K)
               and np.array_equal(A @ K, other * K) and np.array_equal(K @ A, other * K)
               and np.array_equal(K @ J, 0 * K) and np.array_equal(K @ K, c * K))
        mm = mult - 1 if mutate == "rank" else mult
        ok1 = ok1 and int(np.trace(K)) == v * (other - theta) * mm
        if not ok1:
            issues.append(f"{gid} θ={theta}: item 1 fails")
        for x in range(v):
            outs = [x] + [y for y in range(v) if A[x, y]]
            ins = [x] + [y for y in range(v) if A[y, x]]
            u = B[x]
            supp_ok = all(u[j] == 0 for j in range(v) if j not in outs) and any(u[j] != 0 for j in outs)
            null_ok = not np.any(u[outs] @ K[np.ix_(outs, outs)])
            col = B[:, x]
            csupp = all(col[j] == 0 for j in range(v) if j not in ins) and any(col[j] != 0 for j in ins)
            cnull = not np.any(K[np.ix_(ins, ins)] @ col[ins])
            if not (supp_ok and null_ok and csupp and cnull):
                issues.append(f"{gid} θ={theta} x={x}: item 3 fails")
                break
            out["frames"] += 1
        xs = range(v) if v <= 40 else range(2)
        for x in xs:
            S = [x] + [y for y in range(v) if A[x, y]]
            KS = K[np.ix_(S, S)].tolist()
            eig = theta if mutate == "eigen" else other
            for z in nullspace(KS):
                zz = np.zeros(v, dtype=object)
                zz[S] = integral(z)
                phi = K.astype(object) @ zz
                if any(phi[j] != 0 for j in S) or np.any(A.astype(object) @ phi - eig * phi):
                    issues.append(f"{gid} θ={theta} x={x}: item 4: the right kernel gives no eigenvector")
                    break
                out["kernels"] += 1
            for u in nullspace(KS, left=True):
                uu = np.zeros(v, dtype=object)
                uu[S] = integral(u)
                psi = uu @ K.astype(object)
                if any(psi[j] != 0 for j in S) or np.any(psi @ A.astype(object) - eig * psi):
                    issues.append(f"{gid} θ={theta} x={x}: item 4: the left kernel gives no eigenvector")
                    break
                out["kernels"] += 1
        if mult > max_m:
            continue
        if mutate == "frame-closed":
            F = ([0] + [y for y in range(v) if A[0, y]])[:mult]
            F += [w for w in range(v) if w not in F][: mult - len(F)]
        else:
            F = frame_search(K, mult)
        if F is None:
            issues.append(f"{gid} θ={theta}: item 5: the search found no frame of {mult} vertices")
            continue
        Binv = inverse(K[np.ix_(F, F)].tolist())
        if Binv is None:
            issues.append(f"{gid} θ={theta}: item 5: the frame is singular")
            continue
        closed = any(set([x] + [y for y in range(v) if A[x, y]]) <= set(F)
                     or set([x] + [y for y in range(v) if A[y, x]]) <= set(F) for x in range(v))
        if closed:
            issues.append(f"{gid} θ={theta}: item 5: the nonsingular frame contains the closed neighbourhood")
        W = [w for w in range(v) if w not in F]
        KWF = K[np.ix_(W, F)].tolist()
        KFW = K[np.ix_(F, W)].tolist()
        rec = fmat(fmat(KWF, Binv), KFW)
        if any(rec[i][j] != K[W[i], W[j]] for i in range(len(W)) for j in range(len(W))):
            issues.append(f"{gid} θ={theta}: item 5: recovery from the frame failed")
            continue
        out["recon"] += 1
        Fh = frame_search(K, mult // 2) if v <= 40 and mult >= 2 else None
        Bh = inverse(K[np.ix_(Fh, Fh)].tolist()) if Fh is not None else None
        if Bh is not None:
            Wh = [w for w in range(v) if w not in Fh]
            corr = fmat(fmat(K[np.ix_(Wh, Fh)].tolist(), Bh), K[np.ix_(Fh, Wh)].tolist())
            Sig = [[K[Wh[i], Wh[j]] - corr[i][j] for j in range(len(Wh))] for i in range(len(Wh))]
            Sig2 = fmat(Sig, Sig)
            cs = v * (other - theta)
            ok = all(Sig2[i][j] == cs * Sig[i][j] for i in range(len(Wh)) for j in range(len(Wh)))
            ok = ok and sum(Sig[i][i] for i in range(len(Wh))) == cs * (mult - len(Fh))
            if not ok:
                issues.append(f"{gid} θ={theta}: item 5: the Schur complement is not idempotent of rank m' − |F_h|")
            else:
                out["schur"] += 1
    return out


def main(argv=None) -> int:
    argv = sys.argv[1:] if argv is None else argv
    max_m, mutate, quiet = 12, None, False
    i = 0
    while i < len(argv):
        a = argv[i]
        if a == "--max-m" and i + 1 < len(argv):
            max_m = int(argv[i + 1]); i += 2
        elif a == "--mutate" and i + 1 < len(argv):
            mutate = argv[i + 1]; i += 2
            if mutate not in MUTATIONS:
                print(f"unknown mutant {mutate}; known: {', '.join(MUTATIONS)}", file=sys.stderr)
                return 2
        elif a == "--quiet":
            quiet = True; i += 1
        else:
            print(f"unknown argument {a}", file=sys.stderr)
            return 2

    def keep(p):
        sp = spectrum(tuple(int(x) for x in p))
        return sp is not None and min(sp[2], sp[3]) <= max_m and 0 < p[2] < p[1]

    graphs = nc.load_graphs(nc.catalog_files(), keep)
    issues = []
    total = {"frames": 0, "kernels": 0, "recon": 0, "schur": 0}
    sets = set()
    for g in graphs:
        res = check_graph(g, max_m, mutate, issues)
        for key in total:
            total[key] += res[key]
        sets.add(tuple(int(x) for x in g["params"]))
        if not quiet:
            print(f"{g['id']} {tuple(int(x) for x in g['params'])}: {res}")
    has32 = (32, 9, 6, 1, 3) in sets
    print(f"mutant: {mutate or 'none'}; graphs {len(graphs)}, sets {len(sets)}, (32, 9, 6, 1, 3) among them: {has32}")
    print(f"item 3 neighbourhoods {total['frames']}; item 4 kernel vectors {total['kernels']}; "
          f"item 5 recoveries {total['recon']}, Schur complements {total['schur']}")
    if issues:
        print(f"violations: {len(issues)}; first:")
        for line in issues[:8]:
            print("  " + line)
        return 1
    if not has32:
        print("no graph (32, 9, 6, 1, 3) in the catalogues")
        return 1
    print("all items hold")
    return 0


if __name__ == "__main__":
    sys.exit(main())
