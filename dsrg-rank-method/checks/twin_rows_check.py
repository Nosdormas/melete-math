"""Row classes of A + I for t = λ + 1 and any μ, on graphs and on the table.

    python -X utf8 checks/twin_rows_check.py [--mutate MUTANT] [--quiet]

Mutants: lam, mu-one, class-minus, far-plus, lower-plus, upper-minus, cond-strict. Exit code 0 - no
violations; a mutant must end with exit code 1.
"""
from __future__ import annotations

import argparse
import sys
from collections import Counter
from pathlib import Path

import numpy as np

HERE = Path(__file__).resolve().parent
ROOT = HERE.parent
sys.path.insert(0, str(ROOT / "lib"))

import dsrg_build as db  # noqa: E402
import dsrg_cells  # noqa: E402
import dsrg_verify
import twin_classes as tc  # noqa: E402

MUTATIONS = ("lam", "mu-one", "class-minus", "far-plus", "lower-plus", "upper-minus", "cond-strict")


family = tc.family
comp_params = tc.complement_params
f_mult = tc.f_mult
rank_mod = tc.rank_mod


def admissible(p, mutate=None) -> list[int]:
    return tc.sizes(p, low_shift=1 if mutate == "lower-plus" else 0, lam_shift=-1 if mutate == "lam" else 0,
                    high_shift=-1 if mutate == "upper-minus" else 0, cap_shift=-1 if mutate == "class-minus" else 0)


def cond(p, mutate=None) -> bool:
    return tc.condition(p, strict=mutate == "cond-strict")


def catalog_graphs():
    return tc.family_graphs(family)


def blowups(graphs, limit=60):
    out = []
    for g in graphs:
        v, k, t, lam, mu = g["params"]
        for m in (2, 3):
            if m * v > limit:
                continue
            A = np.array(db.clique_blowup(g["A"], m), dtype=np.int64)
            p = (m * v, m * (k + 1) - 1, m * (lam + 2) - 1, m * (lam + 2) - 2, m * mu)
            rep = dsrg_verify.check(A.tolist(), p)
            if not rep.ok:
                raise SystemExit(f"blow-up {g['id']} × {m}: verify rejected {rep.violation}")
            out.append({"id": f"{g['id']}×K{m}", "params": p, "A": A})
    return out


def check_graph(g, mutate, st):
    p = g["params"]
    v, k, t, lam, mu = p
    K, q, f = k + 1, lam + 2 - mu, f_mult(p)
    one = 1 if mutate == "mu-one" else mu
    bad = []
    for side, A in (("A", g["A"]), ("Aᵀ", g["A"].T)):
        B = (A + np.eye(v, dtype=np.int64)).astype(np.int64)
        if not (B @ B == q * B + mu).all():
            bad.append(f"{side}: B² ≠ qB + μJ")
            continue
        if side == "A" and rank_mod(B) != 1 + f:
            bad.append(f"rank B ≠ 1 + f = {1 + f}")
        keys = {}
        cid = np.array([keys.setdefault(B[z].tobytes(), len(keys)) for z in range(v)])
        for x in range(v):
            st["vertices"] += 1
            r = B[x]
            Cm = cid == cid[x]
            a = int(Cm.sum())
            notC = ~Cm
            Dm = (r == 1) & notC
            if not (r[Cm] == 1).all() or not (B[Cm, x] == 1).all() or a > (lam if mutate == "lam" else lam + 1):
                bad.append(f"{side} x={x}: item 1, a = {a}")
            st["t1"] += a == lam + 1
            gamma = B @ Cm.astype(np.int64)
            cu = np.bincount(cid, weights=r, minlength=len(keys)).astype(np.int64)[cid]
            if notC.any():
                if gamma[notC].max() > one or cu[notC].max() > one:
                    bad.append(f"{side} x={x}: item 2, max γ_u = {gamma[notC].max()}, max |C_u ∩ R| = {cu[notC].max()}")
                st["t2"] += int((gamma[notC] == mu).sum())
                far = K - B @ r
                if far[notC].min() < q + (1 if mutate == "far-plus" else 0):
                    bad.append(f"{side} x={x}: item 4, min |N⁺[u] ∖ R| = {far[notC].min()} < q = {q}")
                st["t4u"] += int((far[notC] == q).sum())
            s = int(gamma[Dm].sum())
            cap = mu * (K - a) - (1 if mutate == "class-minus" else 0)
            if s != a * (lam + 2 - a) or s > cap:
                bad.append(f"{side} x={x}: item 3, Σγ = {s}, a(λ + 2 − a) = {a * (lam + 2 - a)}, μ(K − a) = {mu * (K - a)}")
            st["t3"] += s == mu * (K - a)
            if a < K - mu * f + (1 if mutate == "lower-plus" else 0):
                bad.append(f"{side} x={x}: item 4, a = {a} < K − μf = {K - mu * f}")
            st["t4"] += a == K - mu * f
            hit = Dm & (gamma >= 1)
            if hit.any() and (a - gamma[hit]).max() > k - lam - 1:
                bad.append(f"{side} x={x}: item 5, max(a − γ_u) = {(a - gamma[hit]).max()} > k − λ − 1 = {k - lam - 1}")
            high = k - lam - 1 + mu - (1 if mutate == "upper-minus" else 0)
            if a > high:
                bad.append(f"{side} x={x}: item 5, a = {a} > {high}")
            st["t5"] += a == k - lam - 1 + mu
    return bad


def check_sets(mutate):
    snap = dsrg_cells.load_snapshot()
    excluded, bad = [], []
    for p in sorted(snap):
        if not family(p) or f_mult(p) is None:
            continue
        adm = admissible(p, mutate)
        c = cond(p, mutate)
        if adm and c:
            continue
        why = []
        if not c:
            why.append("item 6: λ + 2 − μ > μf" if mutate != "cond-strict" else "item 6 (strict): λ + 2 − μ ≥ μf")
        if not adm:
            why.append("no admissible class size")
        excluded.append((p, snap[p], "; ".join(why)))
        if snap[p] == "b":
            bad.append(f"set {p} is constructed (b), but the lemma excludes it: {'; '.join(why)}")
    return excluded, bad


def main() -> int:
    cat = catalog_graphs()
    blow = blowups(cat)
    graphs = cat + blow
    st = Counter()
    bad_g = []
    for g in graphs:
        for line in check_graph(g, ARGS.mutate, st):
            bad_g.append(f"{g['id']} {g['params']}: {line}")
    excluded, bad_s = check_sets(ARGS.mutate)
    if not ARGS.quiet:
        mus = Counter(g["params"][4] for g in graphs)
        print(f"graphs with t = λ + 1: {len(graphs)} (catalogues and complements {len(cat)}, blow-ups by cliques {len(blow)}),"
              f" sets {len({g['params'] for g in graphs})}, vertices by A and Aᵀ {st['vertices']};"
              f" μ = 1: {mus[1]}, μ = 2: {mus[2]}, μ ≥ 3: {sum(c for m, c in mus.items() if m >= 3)}")
        print(f"  equalities: a = λ + 1 — {st['t1']}, γ_u = μ — {st['t2']}, Σγ = μ(K − a) — {st['t3']},"
              f" |N⁺[u] ∖ R| = q — {st['t4u']}, a = K − μf — {st['t4']}, a = k − λ − 1 + μ — {st['t5']}")
        print(f"snapshot sets with t = λ + 1 and integer f excluded by the lemma: {len(excluded)}")
        for p, s, why in excluded:
            print(f"  {p} status {s}: {why}")
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
