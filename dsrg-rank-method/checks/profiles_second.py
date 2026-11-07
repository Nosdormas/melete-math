"""Second program for the profile search for λ = 1, t = 2μ, written independently of the first.

    python -X utf8 checks/profiles_second.py counts [--mutate MUTANT]
    python -X utf8 checks/profiles_second.py profiles [--mutate MUTANT]

counts - its own checks C1-C11 on the catalogue graphs; profiles - the profile search on the sets of the
table snapshot with λ = 1, t = 2μ, compared with the table of item 6 of the lemma. Exit code 0 - no
discrepancies; a mutant must end with exit code 1.
"""
from __future__ import annotations

import json
import math
import sys
from collections import Counter
from fractions import Fraction
from functools import lru_cache
from pathlib import Path

import numpy as np

HERE = Path(__file__).resolve().parent
ROOT = HERE.parent
DATA = ROOT / "data" / "graphs"
SNAPSHOT = ROOT / "data" / "brouwer-dsrg-v110.txt"

MUTATIONS_COUNTS = {"k-not-k1", "in-arcs", "sign"}
MUTATIONS_PROFILES = {"no-sum", "no-t1", "slack-k", "sign"}
FIRST_PROGRAM_OUTPUT = ROOT / "data" / "left-kernel-check-output.txt"
EXPECTED_EXCLUDED = {(49, 15, 12, 1, 6), (55, 16, 12, 1, 6), (104, 27, 18, 1, 9)}
ITEM6_TABLE = {
    (44, 12, 8, 1, 4): (11, 2, 165, 124, 2),
    (55, 16, 12, 1, 6): (10, 7, 750, 0, None),
    (63, 16, 10, 1, 5): (13, 4, 1225, 198, 5),
    (64, 13, 6, 1, 3): (19, -5, 323, 323, 1),
    (75, 16, 8, 1, 4): (18, -1, 1430, 1430, 1),
    (84, 17, 8, 1, 4): (20, -2, 2253, 2253, 1),
    (95, 20, 10, 1, 5): (19, 2, 9103, 8654, 2),
    (98, 22, 12, 1, 6): (17, 6, 21619, 1840, 7),
}


def rank_q(rows) -> int:
    M = [[Fraction(x) for x in r] for r in rows]
    if not M:
        return 0
    ncols = len(M[0])
    r = 0
    for c in range(ncols):
        piv = next((i for i in range(r, len(M)) if M[i][c] != 0), None)
        if piv is None:
            continue
        M[r], M[piv] = M[piv], M[r]
        p = M[r][c]
        for i in range(len(M)):
            if i != r and M[i][c] != 0:
                f = M[i][c] / p
                M[i] = [a - f * b for a, b in zip(M[i], M[r])]
        r += 1
        if r == len(M):
            break
    return r


def load_graphs():
    out = []
    for path in sorted(DATA.rglob("*.json")):
        data = json.loads(path.read_text(encoding="utf-8"))
        graphs = data.get("graphs") if isinstance(data, dict) else None
        if not isinstance(graphs, list):
            continue
        for i, rec in enumerate(graphs):
            if "rows" in rec:
                A = [[int(ch) for ch in row] for row in rec["rows"]]
            elif "bitmasks" in rec:
                n = len(rec["bitmasks"])
                A = [[(int(m) >> j) & 1 for j in range(n)] for m in rec["bitmasks"]]
            else:
                continue
            label = f"{path.relative_to(DATA).as_posix()}#{rec.get('id', i)}"
            out.append((label, A))
            n = len(A)
            out.append((label + "~", [[int(a != b) - A[a][b] for b in range(n)] for a in range(n)]))
    return out


def params_of(A):
    M = np.asarray(A, dtype=np.int64)
    v = len(M)
    if np.any(np.diag(M)):
        return None
    k = int(M[0].sum())
    if np.any(M.sum(axis=1) != k) or np.any(M.sum(axis=0) != k):
        return None
    S = M @ M
    off = ~np.eye(v, dtype=bool)
    diag, arcs, non = set(np.diag(S).tolist()), set(S[(M == 1) & off].tolist()), set(S[(M == 0) & off].tolist())
    if len(diag) != 1 or len(arcs) > 1 or len(non) > 1:
        return None
    return (v, k, diag.pop(), arcs.pop() if arcs else 0, non.pop() if non else 0)


def vertex_data(A, x, mutate=None):
    v = len(A)
    bad = []
    O = [y for y in range(v) if A[x][y]]
    Oset = set(O)
    M = {y for y in O if A[y][x]}
    pred = {}
    for y in O:
        ins = [u for u in O if A[u][y]]
        if len(ins) != 1:
            bad.append(f"C3: vertex {y} in-arcs from O {len(ins)}")
            return None, bad
        if ins[0] == y:
            bad.append(f"C3: pred({y}) = {y}")
        pred[y] = ins[0]
    parent = {y: y for y in O}

    def find(a):
        while parent[a] != a:
            parent[a] = parent[parent[a]]
            a = parent[a]
        return a

    for y in O:
        ra, rb = find(y), find(pred[y])
        if ra != rb:
            parent[ra] = rb
    comp_of = {}
    comps = []
    for y in O:
        r = find(y)
        if r not in comp_of:
            comp_of[r] = len(comps)
            comps.append([])
        comps[comp_of[r]].append(y)
    cid = {y: comp_of[find(y)] for y in O}
    c = len(comps)
    n_i = [len(K) for K in comps]
    m_i = [sum(1 for y in K if y in M) for K in comps]
    if any(n < 2 for n in n_i):
        bad.append("C3: a component of one vertex")
    for i, K in enumerate(comps):
        into_O = sum(1 for y in K for u in range(v) if A[y][u] and u in Oset)
        into_x = sum(1 for y in K if A[y][x])
        if into_O != n_i[i] or into_x != m_i[i]:
            bad.append(f"C4: component {i}: in O {into_O} at n {n_i[i]}, in x {into_x} at m {m_i[i]}")
        if any(cid[u] != i for y in K for u in range(v) if A[y][u] and u in Oset):
            bad.append(f"C4: an arc from a component {i} into another component")
    Z = [z for z in range(v) if z != x and z not in Oset]
    cycles = [set() for _ in comps]
    for y in O:
        seen = []
        u = y
        while u not in seen:
            seen.append(u)
            u = pred[u]
        cycles[cid[u]].update(seen[seen.index(u):])
    ell = {}
    for z in Z:
        row = [0] * c
        for y in O:
            hit = A[z][y] if mutate == "in-arcs" else A[y][z]
            if hit:
                row[cid[y]] += 1
        ell[z] = row
    return {"O": O, "M": M, "S": [x] + O, "Z": Z, "c": c, "n": n_i, "m": m_i, "ell": ell,
            "cycles": cycles}, bad


def cmd_counts(mutate):
    graphs = load_graphs()
    stats = Counter()
    bad_total = []
    by_params = Counter()
    vertices_by_params = Counter()
    gamma_controls = Counter()
    zeroD_controls = Counter()
    rankD_hist = Counter()
    for label, A in graphs:
        p = params_of(A)
        if p is None:
            bad_total.append(f"{label}: the matrix is not a DSRG")
            continue
        v, k, t, lam, mu = p
        if lam != 1:
            continue
        by_params[p] += 1
        stats["graphs"] += 1
        tmu = (t == 2 * mu)
        if tmu:
            stats["graphs_tmu"] += 1
            if mu * (v - k + 1) != k * (k - 1):
                bad_total.append(f"{label}: C5 μ(v − k + 1) ≠ k(k − 1)")
            if (k + v - 1) % (mu + 1):
                bad_total.append(f"{label}: C5 g is not an integer")
            g = (k + v - 1) // (mu + 1)
        for x in range(v):
            vd, bad = vertex_data(A, x, mutate)
            stats["vertices"] += 1
            vertices_by_params[p] += 1
            for b in bad:
                bad_total.append(f"{label} x={x}: {b}")
            if vd is None:
                continue
            c, n_i, m_i, ell, Z = vd["c"], vd["n"], vd["m"], vd["ell"], vd["Z"]
            stats["components"] += c
            if sum(n_i) != k or sum(m_i) != t or len(Z) != v - k - 1:
                bad_total.append(f"{label} x={x}: C3 sums")
            coef = k if mutate == "k-not-k1" else k - 1
            for i in range(c):
                stats["C1"] += 1
                if sum(ell[z][i] for z in Z) != coef * n_i[i] - m_i[i]:
                    bad_total.append(f"{label} x={x}: C1 component {i}")
            for z in Z:
                stats["C2"] += 1
                if sum(ell[z]) != mu:
                    bad_total.append(f"{label} x={x}: C2 z={z}")
            if not tmu:
                continue
            stats["vertices_tmu"] += 1
            d = [k * m_i[i] - t * n_i[i] for i in range(c)]
            H = {z: [2 * ell[z][i] - m_i[i] for i in range(c)] for z in Z}
            target = Fraction(k - 1, mu) * (1 if mutate == "sign" else -1)
            stats["C6"] += 1
            for i in range(c):
                if Fraction(sum(H[z][i] for z in Z)) != target * d[i]:
                    bad_total.append(f"{label} x={x}: C6 coordinate {i}")
                    break
            stats["C7"] += 1
            if sum(d) != 0 or any(sum(H[z]) != 0 for z in Z):
                bad_total.append(f"{label} x={x}: C7")
            stats["profiles_real"] += 1
            if judge(p, tuple(sorted(zip(n_i, m_i), reverse=True))) is not None:
                bad_total.append(f"{label} x={x}: a real profile is excluded by test T0/T1")
            D = [d] + [H[z] for z in Z]
            rD = rank_q(D)
            rankD_hist[(c, rD, any(d))] += 1
            S = vd["S"]
            K1rows = [[v * (A[s][j] - (1 if s == j else 0)) - (k - 1) for j in range(v)] for s in S]
            rK = rank_q(K1rows)
            stats["C8"] += 1
            if c - rD != len(S) - rK:
                bad_total.append(f"{label} x={x}: C8 dim ker D {c - rD} ≠ left kernel {len(S) - rK}")
            if c - rD < k + 1 - g or rD < (1 if any(d) else 0):
                bad_total.append(f"{label} x={x}: C8 bound")
            O = vd["O"]
            pos = {y: i for i, y in enumerate(O)}
            cons = []
            for y in O:
                for z2 in O:
                    if A[y][z2]:
                        row = [0] * len(O)
                        row[pos[y]] += 1
                        row[pos[z2]] -= 1
                        cons.append(row)
            cons.append([k * A[y][x] - t for y in O])
            for z in Z:
                cons.append([2 * A[y][z] - A[y][x] for y in O])
            stats["C12"] += 1
            if len(O) - rank_q(cons) != c - rD:
                bad_total.append(f"{label} x={x}: C12 dim profSpace ≠ dim ker D")
            cyc = vd["cycles"]
            AmI_O = [[A[i][o] - (1 if i == o else 0) for o in O] for i in range(v)]
            dimE = len(O) - rank_q(AmI_O)
            Rm = [[len(C) for C in cyc]] + [[sum(1 for w in C if A[z][w]) for C in cyc] for z in Z]
            stats["C11"] += 1
            if dimE != c - rank_q(Rm):
                bad_total.append(f"{label} x={x}: C11 dim(E_1 ∩ ℝ^O) {dimE} ≠ c − rank R")
            if dimE < k + (1 if any(d) else 0) - g:
                bad_total.append(f"{label} x={x}: C11 bound of item 3")
            if rD == 1 and any(d):
                j = next(i for i in range(c) if d[i])
                gsum = Fraction(0)
                ok = True
                for z in Z:
                    gam = Fraction(H[z][j], d[j])
                    if any(Fraction(H[z][i]) != gam * d[i] for i in range(c)):
                        ok = False
                    if any(Fraction(ell[z][i]) != (m_i[i] + gam * d[i]) / 2 for i in range(c)):
                        ok = False
                    gsum += gam
                if not ok or gsum != target:
                    bad_total.append(f"{label} x={x}: C9 Σγ = {gsum}, target {target}")
                gamma_controls[p] += 1
            if rD == 0:
                zeroD_controls[p] += 1
                if any(m % 2 for m in m_i):
                    bad_total.append(f"{label} x={x}: C10 odd m with D = 0")
    print(f"catalogue graphs with complements: {len(graphs)}; with λ = 1: {stats['graphs']}, of them t = 2μ: "
          f"{stats['graphs_tmu']}")
    print(f"vertices with λ = 1: {stats['vertices']}, with t = 2μ: {stats['vertices_tmu']}; "
          f"components of pred: {stats['components']}")
    print("sets with λ = 1: graphs / vertices")
    for p in sorted(by_params):
        mark = " t = 2μ" if p[2] == 2 * p[4] else ""
        print(f"  {p} | {by_params[p]} | {vertices_by_params[p]}{mark}")
    print(f"checks: C1 {stats['C1']}, C2 {stats['C2']}, C6 {stats['C6']}, C7 {stats['C7']}, C8 {stats['C8']}, "
          f"C11 {stats['C11']}, C12 {stats['C12']}")
    print("t = 2μ: (c, rank D, d ≠ 0) — vertices")
    for key in sorted(rankD_hist):
        print(f"  {key} — {rankD_hist[key]}")
    print(f"C9, positive control of 4(b) (rank D = 1, d ≠ 0): {sum(gamma_controls.values())} vertices "
          + ", ".join(f"{p} {n}" for p, n in sorted(gamma_controls.items())))
    print(f"C10, D = 0: {sum(zeroD_controls.values())} vertices")
    print(f"real vertex profiles that passed T0 and T1: {stats['profiles_real']}")
    if mutate:
        print(f"mutant: {mutate}")
    print(f"violations: {len(bad_total)}")
    for b in bad_total[:15]:
        print(f"  {b}")
    return 1 if bad_total else 0


def snapshot_sets():
    rows = []
    for line in SNAPSHOT.read_text(encoding="utf-8").splitlines():
        if not line.strip() or line.startswith("#"):
            continue
        vtext, rest = line.split(":", 1)
        v = int(vtext)
        for item in rest.split():
            k, t, lam, mu, st = item.split(",")
            rows.append(((v, int(k), int(t), int(lam), int(mu)), st))
    return rows


def pairs_for(k, t):
    return [(n, m) for n in range(2, k + 1) for m in range(0, min(n, t) + 1)]


def enum_profiles(k, t):
    P = sorted(pairs_for(k, t), reverse=True)
    out = []

    def rec(start, kk, tt, acc):
        if kk == 0:
            if tt == 0:
                out.append(tuple(acc))
            return
        for idx in range(start, len(P)):
            n, m = P[idx]
            if n <= kk and m <= tt:
                acc.append((n, m))
                rec(idx, kk - n, tt - m, acc)
                acc.pop()

    rec(0, k, t, [])
    return out


def gf_count(k, t):
    C = [[0] * (t + 1) for _ in range(k + 1)]
    C[0][0] = 1
    for n, m in pairs_for(k, t):
        for a in range(n, k + 1):
            for b in range(m, t + 1):
                C[a][b] += C[a - n][b - m]
    return C[k][t]


@lru_cache(maxsize=None)
def sum_reachable(values: tuple, count: int, target: Fraction) -> bool:
    if not values:
        return False
    den = 1
    for q in values + (target,):
        den = den * q.denominator // math.gcd(den, q.denominator)
    ints = sorted({int(q * den) for q in values})
    tgt = target * den
    if tgt.denominator != 1:
        return False
    tgt = int(tgt)
    lo, hi = ints[0], ints[-1]
    if not (count * lo <= tgt <= count * hi):
        return False
    shifted = [a - lo for a in ints]
    goal = tgt - count * lo
    reach = {0}
    for _ in range(count):
        reach = {s + a for s in reach for a in shifted if s + a <= goal}
    return goal in reach


def gamma_set(prof, k, t):
    allowed = None
    for n, m in set(prof):
        di = k * m - t * n
        if di == 0:
            if m % 2:
                return frozenset()
            continue
        here = {Fraction(2 * l - m, di) for l in range(n + 1)}
        allowed = here if allowed is None else allowed & here
    return frozenset(allowed or ())


def judge(p, prof, mutate=None):
    v, k, t, lam, mu = p
    g = (k + v - 1) // (mu + 1)
    c = len(prof)
    dnz = any(k * m - t * n for n, m in prof)
    base = (k - g) if mutate == "slack-k" else (k + 1 - g)
    if c < base + (1 if dnz else 0):
        return "T0"
    if mutate == "no-t1":
        return None
    if c - base != (1 if dnz else 0):
        return None
    if not dnz:
        return None if all(m % 2 == 0 for _, m in prof) else "T1"
    G = gamma_set(prof, k, t)
    if not G:
        return "T1"
    if mutate == "no-sum":
        return None
    target = Fraction(k - 1, mu) * (1 if mutate == "sign" else -1)
    return None if sum_reachable(tuple(sorted(G)), v - k - 1, target) else "T1"


def cmd_profiles(mutate, sets_arg):
    rows = snapshot_sets()
    status = {p: st for p, st in rows}
    if sets_arg:
        chosen = []
        for item in sets_arg.split(";"):
            p = tuple(int(x) for x in item.split(","))
            if len(p) != 5:
                print(f"error: set {item}", file=sys.stderr)
                return 2
            chosen.append(p)
    else:
        chosen = [p for p, _ in rows if p[3] == 1 and p[2] == 2 * p[4]]
    bad = []
    excluded = []
    ours = {}
    full = {}
    print(f"sets: {len(chosen)}" + (f"; mutant: {mutate}" if mutate else ""))
    print("set | status | g | k + 1 − g | profiles (enumeration) | by GF | T0 | T1 | left | min c | "
          "of those left with slack above [d ≠ 0]")
    for p in chosen:
        v, k, t, lam, mu = p
        if (k + v - 1) % (mu + 1):
            print(f"  {p}: g is not an integer")
            continue
        g = (k + v - 1) // (mu + 1)
        profs = enum_profiles(k, t)
        gf = gf_count(k, t)
        if gf != len(profs) or len(set(profs)) != len(profs):
            bad.append(f"{p}: enumeration {len(profs)} against GF {gf}")
        verdicts = Counter(judge(p, pr, mutate) for pr in profs)
        left = [pr for pr in profs if judge(p, pr, mutate) is None]
        min_c = min((len(pr) for pr in left), default="—")
        loose = sum(1 for pr in left if len(pr) - (k + 1 - g) > (1 if any(k * m - t * n for n, m in pr) else 0))
        st = status.get(p, "?")
        print(f"  {p} | {st} | {g} | {k + 1 - g} | {len(profs)} | {gf} | {verdicts['T0']} | "
              f"{verdicts['T1']} | {len(left)} | {min_c} | {loose}")
        ours[p] = (g, k + 1 - g, len(profs), len(left), None if not left else min_c)
        full[p] = (g, k + 1 - g, len(profs), verdicts["T0"], verdicts["T1"], len(left))
        if not left:
            excluded.append((p, st))
            if st == "b":
                bad.append(f"{p}: a constructed set is excluded")
    print("excluded: " + ", ".join(f"{p} ({st})" for p, st in excluded))
    if not sets_arg:
        got = {p for p, _ in excluded}
        if got != EXPECTED_EXCLUDED:
            bad.append(f"excluded sets differ from item 6 of the lemma: {sorted(got ^ EXPECTED_EXCLUDED)}")
        for p, want in ITEM6_TABLE.items():
            if ours.get(p) != want:
                bad.append(f"{p}: table of item 6 {want}, this program {ours.get(p)}")
        print(f"table of item 6 of the lemma: {len(ITEM6_TABLE)} rows compared")
        if FIRST_PROGRAM_OUTPUT.is_file():
            diff = 0
            seen = 0
            for line in FIRST_PROGRAM_OUTPUT.read_text(encoding="utf-8").splitlines():
                parts = [x.strip() for x in line.split("|")]
                if len(parts) != 8 or not parts[0].startswith("("):
                    continue
                q = tuple(int(x) for x in parts[0].strip("()").split(","))
                nums = tuple(int(x) for x in parts[2:])
                seen += 1
                if full.get(q) != nums:
                    diff += 1
                    bad.append(f"{q}: first program record {nums}, this program {full.get(q)}")
            print(f"comparison with the output of the first program {FIRST_PROGRAM_OUTPUT.relative_to(ROOT).as_posix()}: lines {seen}, "
                  f"discrepancies {diff}")
    print(f"violations: {len(bad)}")
    for b in bad:
        print(f"  {b}")
    return 1 if bad else 0


def main(argv):
    if not argv or argv[0] not in ("counts", "profiles"):
        print(__doc__)
        return 2
    cmd, rest = argv[0], argv[1:]
    mutate = None
    sets_arg = None
    i = 0
    while i < len(rest):
        if rest[i] == "--mutate" and i + 1 < len(rest):
            mutate = rest[i + 1]
            i += 2
        elif rest[i] == "--sets" and i + 1 < len(rest) and cmd == "profiles":
            sets_arg = rest[i + 1]
            i += 2
        else:
            print(f"error: argument {rest[i]}", file=sys.stderr)
            return 2
    allowed = MUTATIONS_COUNTS if cmd == "counts" else MUTATIONS_PROFILES
    if mutate is not None and mutate not in allowed:
        print(f"error: mutant {mutate}, allowed {sorted(allowed)}", file=sys.stderr)
        return 2
    if cmd == "counts":
        return cmd_counts(mutate)
    return cmd_profiles(mutate, sets_arg)


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
