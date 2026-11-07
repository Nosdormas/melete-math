"""Twin classes of A + I for μ = 1, t = λ + 1, on graphs and on the table.

    python -X utf8 checks/twin_mu1_check.py [--mutate plus-one|rank-plus|lambda-three|free-all] [--quiet]

Exit code 0 - no violations; a mutant must end with exit code 1.
"""
from __future__ import annotations

import argparse
import sys
from collections import Counter
from fractions import Fraction
from pathlib import Path

HERE = Path(__file__).resolve().parent
ROOT = HERE.parent
sys.path.insert(0, str(ROOT / "lib"))

import dsrg_build as db  # noqa: E402
import dsrg_cells  # noqa: E402
import graph_controls as nc  # noqa: E402
import dsrg_verify
import twin_classes as tc  # noqa: E402
from kernel_frame import rank_int  # noqa: E402

MUTATIONS = ("plus-one", "rank-plus", "lambda-three", "free-all")


family = tc.family_mu_one
f_mult = tc.f_mult
classes = tc.row_classes


def admissible(params, mutate=None) -> list[int]:
    return tc.sizes_mu_one(params, low_shift=1 if mutate == "rank-plus" else 0,
                           cap_shift=-1 if mutate == "plus-one" else 0)


def excluded_by_point4(params, mutate=None) -> bool:
    return tc.mu1_twin_forced(params, 3 if mutate == "lambda-three" else 4)


def rref(rows):
    M = [[Fraction(x) for x in r] for r in rows]
    piv, r = [], 0
    m = len(M[0]) if M else 0
    for c in range(m):
        p = next((i for i in range(r, len(M)) if M[i][c] != 0), None)
        if p is None:
            continue
        M[r], M[p] = M[p], M[r]
        inv = 1 / M[r][c]
        M[r] = [a * inv for a in M[r]]
        for i in range(len(M)):
            if i != r and M[i][c] != 0:
                a = M[i][c]
                M[i] = [x - a * y for x, y in zip(M[i], M[r])]
        piv.append(c)
        r += 1
        if r == len(M):
            break
    return M[:r], piv


def null_basis(cols_matrix):
    R, piv = rref(cols_matrix)
    m = len(cols_matrix[0])
    free = [j for j in range(m) if j not in piv]
    out = []
    for fj in free:
        vec = [Fraction(0)] * m
        vec[fj] = Fraction(1)
        for row, pc in zip(R, piv):
            vec[pc] = -row[fj]
        out.append(vec)
    return out


def flag_graph(pts, lines, label):
    A, params = db.flag_graph(pts, lines)
    rep = dsrg_verify.check(A, params)
    if not rep.ok:
        raise SystemExit(f"flag graph {label} failed verify as {params}: {rep.violation}")
    return {"id": f"flags {label}", "params": params, "A": A}


def built_graphs():
    out = []
    for s in range(1, 7):
        pts, lines = db.gq_grid(s)
        out.append(flag_graph(pts, lines, f"GQ({s}, 1)"))
        dp, dl = db.gq_dual(pts, lines)
        out.append(flag_graph(dp, dl, f"GQ(1, {s})"))
    pts, lines = db.gq_w2()
    out.append(flag_graph(pts, lines, "W(2) = GQ(2, 2)"))
    return out


def catalog_graphs():
    gs = nc.load_graphs(nc.catalog_files(), family)
    seen, uniq = set(), []
    for g in gs:
        key = (g["params"], g["A"].tobytes())
        if key in seen:
            continue
        seen.add(key)
        uniq.append({"id": g["id"], "params": g["params"], "A": g["A"].tolist()})
    return uniq


def check_graph(g, mutate, stats) -> list[str]:
    p = g["params"]
    v, k, t, lam, mu = p
    A = g["A"]
    B = [[A[i][j] + (1 if i == j else 0) for j in range(v)] for i in range(v)]
    f = f_mult(p)
    bad = []
    rb = rank_int(B)
    if rb != 1 + f:
        bad.append(f"rank B = {rb} ≠ 1 + f = {1 + f}")
    cols = [[B[i][j] for i in range(v)] for j in range(v)]
    rc, cc = classes(B), classes(cols)
    rsize, csize = Counter(rc), Counter(cc)
    out = [{j for j in range(v) if B[i][j]} for i in range(v)]
    inn = [{i for i in range(v) if B[i][j]} for j in range(v)]
    members_r = {c: {i for i in range(v) if rc[i] == c} for c in rsize}
    members_c = {c: {i for i in range(v) if cc[i] == c} for c in csize}
    cap = k if mutate == "plus-one" else k + 1
    rk_extra = 1 if mutate == "rank-plus" else 0
    for x in range(v):
        stats["vertices"] += 1
        Nx = out[x]
        C, D = members_r[rc[x]], members_c[cc[x]]
        a, d = len(C), len(D)
        if any(not members_c[cc[y]] <= Nx for y in Nx):
            bad.append(f"x={x}: N⁺[x] is not a union of column classes")
        if any(not members_r[rc[y]] <= inn[x] for y in inn[x]):
            bad.append(f"x={x}: N⁻[x] is not a union of row classes")
        if len(C & D) != 1:
            bad.append(f"x={x}: |C ∩ D| = {len(C & D)}")
        if a + d > lam + 3:
            bad.append(f"x={x}: a + d = {a + d} > λ + 3")
        if a + d == lam + 3:
            stats["tight_ad"] += 1
        for u in Nx - C:
            if len(out[u] & C) > 1:
                bad.append(f"x={x}, u={u}: |N⁺[u] ∩ C| = {len(out[u] & C)} > 1")
            if len(members_r[rc[u]] & Nx) != 1:
                bad.append(f"x={x}, u={u}: |C_u ∩ N⁺[x]| ≠ 1")
        for y in C:
            if len((Nx - C) & inn[y]) != lam + 2 - a:
                bad.append(f"x={x}, y={y}: |(N⁺[x] ∖ C) ∩ N⁻[y]| ≠ λ + 2 − a")
        for size, name in ((a, "a"), (d, "d")):
            if size > lam + 1:
                bad.append(f"x={x}: {name} = {size} > λ + 1")
            if size * (lam + 3 - size) > cap:
                bad.append(f"x={x}: {name}(λ + 3 − {name}) = {size * (lam + 3 - size)} > {cap}")
            if size * (lam + 3 - size) == k + 1:
                stats["tight_class"] += 1
            if size < k + 1 - f + rk_extra:
                bad.append(f"x={x}: {name} = {size} < k + 1 − f{' + 1' if rk_extra else ''} = {k + 1 - f + rk_extra}")
            if size == k + 1 - f:
                stats["tight_rank"] += 1
    return bad


def free_vertex(g, mutate, stats) -> list[str]:
    p = g["params"]
    v, k, t, lam, mu = p
    A = g["A"]
    B = [[A[i][j] + (1 if i == j else 0) for j in range(v)] for i in range(v)]
    f = f_mult(p)
    bad = []
    rows = [tuple(r) for r in B]
    for x in range(v):
        O = [j for j in range(v) if A[x][j]]
        S = set(O) | {x}
        W = [j for j in range(v) if j not in S]
        blocks = {o: [w for w in W if A[o][w]] for o in O}
        owner = {w: o for o in O for w in blocks[o]}
        if len(owner) != len(W):
            bad.append(f"x={x}: W does not split into blocks")
            continue
        for w in W:
            for o in O:
                cnt = sum(A[y][w] for y in blocks[o])
                want = lam if o == owner[w] else 1 - A[o][owner[w]]
                if cnt != want:
                    bad.append(f"x={x}, w={w}, o={o}: in-arcs from W_o {cnt} ≠ {want}")
        stats["block_vertices"] += 1
        twin_free = all(rows[o] != rows[x] for o in O)
        if not twin_free or f != k + 1:
            continue
        stats["free"] += 1
        if mutate == "free-all" or lam >= 3:
            bad.append(f"x={x}: a vertex without a row twin at λ = {lam}"
                       f"{' (mutant free-all)' if mutate == 'free-all' else ''}")
        if any(not blocks[o] for o in O):
            bad.append(f"x={x}: an empty block at a vertex without a twin")
            continue
        M = [[A[i][j] - (lam if i == j else 0) for j in W] for i in range(v)]
        basis = null_basis(M)
        if len(basis) != 1:
            bad.append(f"x={x}: dim E_λ ∩ ℝ^W = {len(basis)} ≠ 1")
            continue
        c = basis[0]
        nz = [abs(z) for z in c if z != 0]
        c = [z / nz[0] for z in c]
        cw = {W[i]: c[i] for i in range(len(W))}
        if any(z not in (-1, 0, 1) for z in c):
            bad.append(f"x={x}: c takes values outside 0, ±1")
            continue
        r = {w: {j for j in W if B[w][j]} for w in W}
        special = []
        for o in O:
            Wo = set(blocks[o])
            pats = {frozenset(r[w] & Wo) for w in W}
            if any(0 < len(P) < len(Wo) for P in pats):
                special.append(o)
                Tpos = {frozenset(r[w] & Wo) for w in W if cw[w] == 1}
                Tneg = {frozenset(r[w] & Wo) for w in W if cw[w] == -1}
                if len(Tpos) != 1 or len(Tneg) != 1 or next(iter(Tpos)) | next(iter(Tneg)) != Wo \
                        or next(iter(Tpos)) & next(iter(Tneg)):
                    bad.append(f"x={x}, o={o}: rows ±1 do not give a partition T_o ⊔ T_o^c")
                if any(cw[w] == 0 and 0 < len(r[w] & Wo) < len(Wo) for w in W):
                    bad.append(f"x={x}, o={o}: a row with c = 0 is not constant on a block")
            pos = sum(1 for w in blocks[o] if cw[w] == 1)
            neg = sum(1 for w in blocks[o] if cw[w] == -1)
            if pos != neg:
                bad.append(f"x={x}, o={o}: the sum of c over a block ≠ 0")
            want = lam + 1 + (pos if o in special else 0)
            if len(blocks[o]) != want:
                bad.append(f"x={x}, o={o}: |W_o| = {len(blocks[o])} ≠ {want}")
        ps = [sum(1 for w in blocks[o] if cw[w] == 1) for o in special]
        if sum(ps) != lam + 1:
            bad.append(f"x={x}: Σ p_o over special blocks = {sum(ps)} ≠ λ + 1")
        if len(special) >= 2 and any(sum(1 for w in blocks[o] if cw[w] == 1) > 1 for o in O):
            bad.append(f"x={x}: |Σ| ≥ 2, but a block has p_o > 1")
        if any(len(r[w]) > k + 1 for w in W):
            bad.append(f"x={x}: |r_w| > k + 1")
        stats[f"sigma={len(special)}"] += 1
    return bad


def check_sets(mutate):
    snap = dsrg_cells.load_snapshot()
    excluded, bad = [], []
    for p in sorted(snap):
        if not family(p):
            continue
        v, k, t, lam, mu = p
        if (v - k - 1) % (lam + 1):
            continue
        adm = admissible(p, mutate)
        p4 = excluded_by_point4(p, mutate)
        if adm and not p4:
            continue
        why = []
        if not adm:
            why.append("no admissible class size (items 3, 4)")
        if p4:
            why.append("k = 2λ + 2, λ ≥ " + ("3" if mutate == "lambda-three" else "4") + " (item 4)")
        excluded.append((p, snap[p], "; ".join(why)))
        if snap[p] == "b":
            bad.append(f"set {p} is constructed (b), but the lemma excludes it: {'; '.join(why)}")
    return excluded, bad


def main() -> int:
    graphs = catalog_graphs() + built_graphs()
    stats = Counter()
    bad_g, bad_f = [], []
    for g in graphs:
        if excluded_by_point4(g["params"], ARGS.mutate):
            bad_g.append(f"{g['id']} {g['params']}: a graph exists, but item 4 excludes it")
        for line in check_graph(g, ARGS.mutate, stats):
            bad_g.append(f"{g['id']} {g['params']}: {line}")
        for line in free_vertex(g, ARGS.mutate, stats):
            bad_f.append(f"{g['id']} {g['params']}: {line}")
    excluded, bad_s = check_sets(ARGS.mutate)
    if not ARGS.quiet:
        sets = Counter(g["params"] for g in graphs)
        print(f"graphs with μ = 1, t = λ + 1: {len(graphs)} (catalogues {len(graphs) - 13}, flags GQ 13),"
              f" sets {len(sets)}, vertices {stats['vertices']}")
        print(f"  bound a(λ + 3 − a) ≤ k + 1 exact {stats['tight_class']} times (by a and d),"
              f" a + d = λ + 3 — {stats['tight_ad']}, a ≥ k + 1 − f exact {stats['tight_rank']}")
        print(f"  blocks W_o: vertices {stats['block_vertices']}; free vertices at f = k + 1: {stats['free']},"
              f" by |Σ|: {dict(sorted((k_, v_) for k_, v_ in stats.items() if k_.startswith('sigma')))}")
        print(f"snapshot sets with μ = 1, t = λ + 1 excluded by the lemma: {len(excluded)}")
        for p, st, why in excluded:
            print(f"  {p} status {st}: {why}")
    bad = bad_g + bad_f + bad_s
    print(f"violations: {len(bad)} (graphs {len(bad_g)}, free vertices {len(bad_f)}, sets {len(bad_s)})")
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
