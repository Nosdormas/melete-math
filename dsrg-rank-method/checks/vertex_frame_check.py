"""Frame of a vertex for μ = 1, t = λ + 1 on graphs, and the count of subgraphs on N⁺[x] for
(28, 6, 3, 2, 1).

    python -X utf8 checks/vertex_frame_check.py [--mutate block-plus|cf-plus|lam-plus|pairs-geq] [--quiet]

Exit code 0 - no violations; a mutant must end with exit code 1.
"""
from __future__ import annotations

import argparse
import importlib.util
import sys
from collections import Counter
from pathlib import Path

HERE = Path(__file__).resolve().parent
ROOT = HERE.parent
sys.path.insert(0, str(ROOT / "lib"))
sys.path.insert(0, str(ROOT / "lib"))

import dsrg_verify  # noqa: E402
import mu_one_frames as mf  # noqa: E402

MUTATIONS = ("lam-plus", "block-plus", "cf-plus", "pairs-geq")
LIFTS = ((3, 1), (3, 2), (4, 2), (3, 3))


def mu1_corpus():
    spec = importlib.util.spec_from_file_location("twin_mu1_check", ROOT / "checks/twin_mu1_check.py")
    mod = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(mod)
    return [(g["id"], tuple(g["params"]), g["A"]) for g in mod.catalog_graphs() + mod.built_graphs()]


def lift_graphs():
    out = []
    for q, d in LIFTS:
        A = mf.lift(mf.kautz(d), q)
        p = mf.lift_params(q, d)
        rep = dsrg_verify.check(A, p)
        if not rep.ok:
            raise SystemExit(f"lift q={q}, d={d}: verify rejected {rep.violation}")
        out.append((f"lift q={q} d={d}", p, A))
    return out


def classes(A):
    n = len(A)
    rows = [tuple(1 if (i == j or A[i][j]) else 0 for j in range(n)) for i in range(n)]
    cols = [tuple(1 if (i == j or A[i][j]) else 0 for i in range(n)) for j in range(n)]
    C = [frozenset(u for u in range(n) if rows[u] == rows[x]) for x in range(n)]
    D = [frozenset(u for u in range(n) if cols[u] == cols[x]) for x in range(n)]
    return C, D


def check_vertex(A, p, x, C, D, mutate, stats):
    v, k, t, lam, mu = p
    n = len(A)
    K = k + 1
    bad = []
    O = [j for j in range(n) if A[x][j]]
    S = set(O) | {x}
    W = [w for w in range(n) if w not in S]
    for o in O:
        block = [w for w in range(n) if A[o][w] and w not in S]
        for y in S:
            real = sum(1 for w in block if A[w][y])
            if y == o:
                want = lam + 1 - sum(1 for z in S if A[o][z] and A[z][o])
            else:
                paths = sum(1 for z in S if z not in (o, y) and A[o][z] and A[z][y])
                want = 1 + ((lam if mutate == "lam-plus" else lam - 1) * A[o][y]) - paths
            if real != want:
                bad.append(f"x={x}: item 1 n({o}, {y}) = {real}, formula {want}")
    for w in W:
        ins = [z for z in S if A[z][w]]
        if len(ins) != 1 or ins[0] == x:
            bad.append(f"x={x}: item 2 at w={w} in-arcs into S {ins}")
    empty = 0
    low = lam + 2 if mutate == "block-plus" else lam + 1
    for o in O:
        size = sum(1 for w in range(n) if A[o][w] and w not in S)
        if size != k - sum(1 for z in S if A[o][z]):
            bad.append(f"x={x}: item 2 |W_{o}| ≠ k − |Γ⁺(o) ∩ S|")
        if (size == 0) != (o in C[x]):
            bad.append(f"x={x}: item 2 block W_{o} empty {size == 0}, o ∈ C_x {o in C[x]}")
        if size == 0:
            empty += 1
        elif size < low:
            bad.append(f"x={x}: item 2 |W_{o}| = {size} < {low}")
        if size == lam + 1:
            stats["block_tight"] += 1
    if len(C[x]) != 1 + empty:
        bad.append(f"x={x}: item 2 a = {len(C[x])}, empty blocks {empty}")
    if len(C[x]) == lam + 1:
        stats["a_full"] += 1
        U = [u for u in S if u not in C[x]]
        if any(A[u][w] for u in U for w in U):
            bad.append(f"x={x}: item 3 arc inside U")
        for u in U:
            if not (D[u] - {u}) <= C[x]:
                bad.append(f"x={x}: item 3 at u={u} column twin outside C_x")
        free = sum(1 for u in U if len(D[u]) == 1)
        need = K - 2 * (lam + 1) + (1 if mutate == "cf-plus" else 0)
        if free < need:
            bad.append(f"x={x}: item 3 vertices of U with d = 1 {free} < {need}")
        if free == K - 2 * (lam + 1):
            stats["cf_tight"] += 1
    return bad


def check_pt4(p, C, D, mutate, stats):
    v, k, t, lam, mu = p
    K = k + 1
    n = len(C)
    if any(len(C[x]) == 1 or len(D[x]) == 1 for x in range(n)):
        return []
    over = K >= 2 * (lam + 1) if mutate == "pairs-geq" else K > 2 * (lam + 1)
    if not over:
        stats["pt4_boundary" if K == 2 * (lam + 1) else "pt4_below"] += 1
        return []
    stats["pt4_premise"] += 1
    bad = []
    if any(len(C[x]) > lam or len(D[x]) > lam for x in range(n)):
        bad.append("item 4: a class of size λ + 1 in a graph without free vertices")
    if lam == 2 and (any(len(C[x]) != 2 or len(D[x]) != 2 for x in range(n)) or K % 2):
        bad.append("item 4: at λ = 2 not all classes are pairs or K is odd")
    return bad


def frames_part(mutate):
    bad = []
    out = []
    for p, want_all, want_pairs in (((18, 5, 3, 2, 1), 9, 0), ((28, 6, 3, 2, 1), 55, 0),
                                    ((8, 3, 2, 1, 1), None, 1)):
        stats, before = mf.count_frames(p)
        labeled, cls = mf.pair_frames(p)
        out.append(f"  {p}: frames before items 1–2 {before}, after {sum(stats.values())} by a {dict(sorted(stats.items()))};"
                   f" under the selection of item 4 {labeled} labelled, classes {len(cls)}")
        if want_all is not None and sum(stats.values()) != want_all:
            bad.append(f"frames {p}: {sum(stats.values())} ≠ {want_all}")
        if labeled != want_pairs:
            bad.append(f"frames of item 4 {p}: {labeled} ≠ {want_pairs}")
    return out, bad


def main(args) -> int:
    graphs = mu1_corpus() + lift_graphs()
    stats = Counter()
    bad = []
    for gid, p, A in graphs:
        if p[4] != 1 or p[2] != p[3] + 1:
            continue
        stats["graphs"] += 1
        for label, M in (("A", A), ("Aᵀ", [list(r) for r in zip(*A)])):
            C, D = classes(M)
            for x in range(len(M)):
                stats["vertices"] += 1
                for line in check_vertex(M, p, x, C, D, args.mutate, stats):
                    bad.append(f"{gid} {p} {label}: {line}")
            for line in check_pt4(p, C, D, args.mutate, stats):
                bad.append(f"{gid} {p} {label}: {line}")
    lines, bad_f = frames_part(args.mutate)
    bad += bad_f
    if not args.quiet:
        print(f"graphs: {stats['graphs']} (twin-class corpus and lifts {len(LIFTS)}), vertices of A and Aᵀ {stats['vertices']}")
        print(f"  block of exactly λ + 1: {stats['block_tight']} times; vertices with a = λ + 1: {stats['a_full']},"
              f" of them the bound of item 3 is exact at {stats['cf_tight']}")
        print(f"  item 4: premise (no free vertices, K > 2(λ + 1)) at {stats['pt4_premise']} matrices;"
              f" without free vertices at K = 2(λ + 1) — {stats['pt4_boundary']}, at K < 2(λ + 1) — {stats['pt4_below']}")
        print("frames:")
        print("\n".join(lines))
    print(f"violations: {len(bad)}")
    for line in bad[:20]:
        print("  " + line)
    if args.mutate:
        print(f"mutant {args.mutate}: {'caught' if bad else 'NOT caught'}")
    return 1 if bad else 0


if __name__ == "__main__":
    ap = argparse.ArgumentParser()
    ap.add_argument("--mutate", choices=MUTATIONS)
    ap.add_argument("--quiet", action="store_true")
    sys.exit(main(ap.parse_args()))
