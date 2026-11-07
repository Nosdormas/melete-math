"""SAT formulas and solver calls of the second program for (48, 9, 5, 0, 2).
"""
from __future__ import annotations

import itertools
from fractions import Fraction as Fr

import numpy as np

from search48_second_core import Frame


class TypeTable:

    def __init__(self, fr: Frame, types, keys=None):
        self.fr = fr
        self.types = types
        self.index = {T: i for i, T in enumerate(types)}
        n = fr.n
        self.Ob = np.array([[O >> y & 1 for y in range(n)] for O, I in types], dtype=np.int64).reshape(-1, n)
        self.Ib = np.array([[I >> y & 1 for y in range(n)] for O, I in types], dtype=np.int64).reshape(-1, n)
        succ = np.array([[fr.AN[y][z] if (y > 0 and z > 0) else 0 for z in range(n)] for y in range(n)],
                        dtype=np.int64)
        self.cin = self.Ib @ succ.T
        self.cout = self.Ob @ succ
        self.RO = self.Ob @ fr.DI        # L·r_O·D⁻¹
        self.dL = -fr.theta * fr.L - (self.RO * self.Ib).sum(axis=1)
        self.eps = (self.Ob * self.Ib).sum(axis=1)
        self.key = keys
        self.Phi = np.array(fr.Phi, dtype=np.int64)

    def FL(self, i, j) -> int:
        return int(self.RO[i] @ self.Ib[j])


def det_adj(M):
    r = len(M)
    if r == 0:
        return 1, []
    def det(A):
        A = [[Fr(x) for x in row] for row in A]
        n = len(A)
        d = Fr(1)
        for c in range(n):
            p = next((i for i in range(c, n) if A[i][c] != 0), None)
            if p is None:
                return Fr(0)
            if p != c:
                A[c], A[p] = A[p], A[c]
                d = -d
            d *= A[c][c]
            for i in range(c + 1, n):
                f = A[i][c] / A[c][c]
                A[i] = [x - f * y for x, y in zip(A[i], A[c])]
        return d
    D = det(M)
    adj = [[0] * r for _ in range(r)]
    for i in range(r):
        for j in range(r):
            minor = [[M[a][b] for b in range(r) if b != i] for a in range(r) if a != j]
            adj[i][j] = int((-1) ** (i + j) * det(minor)) if r > 1 else 1
    assert D.denominator == 1
    return int(D), adj


class Pivots:

    def __init__(self, tt: TypeTable, piv, arcs):
        self.tt, self.piv, self.arcs = tt, list(piv), arcs
        fr = tt.fr
        r = self.r = len(piv)
        L = fr.L
        SL = [[int(tt.dL[piv[i]]) if i == j else L * arcs[i][j] - tt.FL(piv[i], piv[j]) for j in range(r)]
              for i in range(r)]
        self.SL = SL
        self.det, adj = det_adj(SL)
        assert self.det != 0, "the block S[R, R] is singular"
        self.adj = np.array(adj, dtype=object).reshape(r, r)
        self.ok = self._pivots_ok()

    def _pivots_ok(self) -> bool:
        return dense_ok(self.tt, self, None, (), ())

    def candidates(self, key_min=None, exclude_types=(), distinct=True):
        tt, fr, piv, r = self.tt, self.tt.fr, self.piv, self.r
        mu, t, L, det = fr.mu, fr.t, fr.L, self.det
        adj = self.adj
        Ntypes = len(tt.types)
        base = np.ones(Ntypes, dtype=bool)
        if distinct:
            for i in piv:
                base[i] = False
        for i in exclude_types:
            base[i] = False
        if key_min is not None:
            base &= np.array([(tt.dL[i] == 0) or (tt.key[i] >= key_min) for i in range(Ntypes)])
        Ob, Ib = tt.Ob, tt.Ib
        PO = [Ob[i] for i in piv]
        PI = [Ib[i] for i in piv]
        R = tt.Phi - sum((np.outer(PI[i], PO[i]) for i in range(r)), np.zeros_like(tt.Phi))
        assert (R[1:, 1:] >= 0).all()
        Z = (R <= 0).astype(np.int64)
        Z[0, :] = 0
        Z[:, 0] = 0
        base &= ~(((Ib @ Z) * Ob).sum(axis=1) > 0)
        A_RR = self.arcs
        FwR = np.stack([tt.RO @ PI[i] for i in range(r)], axis=1) if r else np.zeros((Ntypes, 0), dtype=np.int64)
        FRw = np.stack([Ib @ tt.RO[piv[i]] for i in range(r)], axis=1) if r else np.zeros((Ntypes, 0), dtype=np.int64)
        P2_Rw = [Ib @ PO[i] for i in range(r)]      # |O_i ∩ I_w|
        P2_wR = [Ob @ PI[i] for i in range(r)]      # |O_w ∩ I_i|
        eps_R = [int(tt.eps[piv[i]]) + sum(A_RR[i][j] * A_RR[j][i] for j in range(r)) for i in range(r)]
        out = []
        for a in itertools.product((0, 1), repeat=r):
            for b in itertools.product((0, 1), repeat=r):
                ok = base.copy()
                av, bv = np.array(a, dtype=np.int64), np.array(b, dtype=np.int64)
                for i in range(r):
                    via = sum(A_RR[i][j] * a[j] for j in range(r))
                    ok &= P2_Rw[i] + via <= mu * (1 - a[i])
                    # (w, w_i)
                    via = sum(b[j] * A_RR[j][i] for j in range(r))
                    ok &= P2_wR[i] + via <= mu * (1 - b[i])
                    if eps_R[i] + a[i] * b[i] > t:
                        ok &= False
                    for j in range(r):
                        if i != j:
                            base_ij = int(PO[i] @ PI[j]) + sum(A_RR[i][l] * A_RR[l][j] for l in range(r))
                            if base_ij + a[i] * b[j] > mu * (1 - A_RR[i][j]):
                                ok &= False
                ok &= tt.eps + int(av @ bv) <= t
                inR = sum((a[i] * PI[i] for i in range(r)), np.zeros(fr.n, dtype=np.int64))
                outR = sum((b[i] * PO[i] for i in range(r)), np.zeros(fr.n, dtype=np.int64))
                ok &= (tt.cin + inR[None, :] <= mu * (1 - Ib)).all(axis=1)
                ok &= (tt.cout + outR[None, :] <= mu * (1 - Ob)).all(axis=1)
                for i in range(r):
                    cin_i = tt.cin[piv[i]] + sum((PI[j] * A_RR[j][i] for j in range(r) if j != i),
                                                 np.zeros(fr.n, dtype=np.int64))
                    cout_i = tt.cout[piv[i]] + sum((A_RR[i][j] * PO[j] for j in range(r) if j != i),
                                                   np.zeros(fr.n, dtype=np.int64))
                    ok &= (cin_i[None, :] + b[i] * Ib <= mu * (1 - PI[i][None, :])).all(axis=1)
                    ok &= (cout_i[None, :] + a[i] * Ob <= mu * (1 - PO[i][None, :])).all(axis=1)
                sL = L * bv[None, :] - FwR
                tL = L * av[None, :] - FRw
                if r:
                    lhs = det * tt.dL
                    rhs = np.array([int(sL[w] @ adj @ tL[w]) for w in range(Ntypes)], dtype=object) \
                        if r > 1 else sL[:, 0] * tL[:, 0] * int(adj[0][0])
                    ok &= np.array(lhs == rhs, dtype=bool)
                else:
                    ok &= tt.dL == 0
                for w in np.nonzero(ok)[0]:
                    out.append((int(w), a, b, tuple(int(x) for x in sL[w]), tuple(int(x) for x in tL[w])))
        return out


def dense_ok(tt: TypeTable, pv: Pivots, w, a, b) -> bool:
    fr = tt.fr
    n, r = fr.n, pv.r
    verts = list(range(n)) + [("R", i) for i in range(r)] + ([("w",)] if w is not None else [])
    m = len(verts)
    A = [[0] * m for _ in range(m)]
    for i in range(n):
        for j in range(n):
            A[i][j] = fr.AN[i][j]
    def put(idx, ty):
        O, I = tt.types[ty]
        for y in fr.Np:
            A[idx][y] = O >> y & 1
            A[y][idx] = I >> y & 1
    for i in range(r):
        put(n + i, pv.piv[i])
        for j in range(r):
            A[n + i][n + j] = pv.arcs[i][j]
    if w is not None:
        put(n + r, w)
        for i in range(r):
            A[n + i][n + r] = a[i]
            A[n + r][n + i] = b[i]
    for i in range(m):
        for j in range(m):
            p = sum(A[i][z] * A[z][j] for z in range(m))
            if i == j:
                tgt = fr.t
            else:
                tgt = fr.mu * (1 - A[i][j])
            if p > tgt:
                return False
    return True


def pair_table(pv: Pivots, cand, mutate=()):
    tt, fr = pv.tt, pv.tt.fr
    L, mu, det, r = fr.L, fr.mu, pv.det, pv.r
    rhos, sigmas, rho_of, sig_of, rf, sf = {}, {}, [], [], [], []
    for (i, a, b, s, t) in cand:
        key = (tt.types[i][0], b)
        if key not in rhos:
            rhos[key] = len(rhos)
            rf.append((i, b, s))
        assert rf[rhos[key]][2] == s
        rho_of.append(rhos[key])
        key = (tt.types[i][1], a)
        if key not in sigmas:
            sigmas[key] = len(sigmas)
            sf.append((i, a, t))
        assert sf[sigmas[key]][2] == t
        sig_of.append(sigmas[key])
    nR, nS = len(rf), len(sf)
    RO = np.array([tt.RO[i] for i, _, _ in rf], dtype=np.int64).reshape(nR, fr.n)
    Ob = np.array([tt.Ob[i] for i, _, _ in rf], dtype=np.int64).reshape(nR, fr.n)
    Ib = np.array([tt.Ib[i] for i, _, _ in sf], dtype=np.int64).reshape(nS, fr.n)
    Bm = np.array([b for _, b, _ in rf], dtype=np.int64).reshape(nR, r)
    Am = np.array([a for _, a, _ in sf], dtype=np.int64).reshape(nS, r)
    Sm = np.array([s for _, _, s in rf], dtype=object).reshape(nR, r)
    Tm = np.array([t for _, _, t in sf], dtype=object).reshape(nS, r)
    sign = -1 if "pivot-sign" in mutate else 1
    num = (RO @ Ib.T).astype(object) * det
    if r:
        num = num + sign * (Sm.dot(pv.adj)).dot(Tm.T)
    is0 = num == 0
    is1 = num == L * det
    paths = Ob @ Ib.T + Bm @ Am.T
    if "no-paths" in mutate:
        paths = paths * 0
    good = (is0 & (paths <= mu)) | (is1 & (paths == 0))
    return nR, nS, np.argwhere(~np.asarray(good, dtype=bool)), rho_of, sig_of


def build_cnf(pv: Pivots, cand, drop=(), distinct=True):
    from pysat.formula import IDPool
    tt, fr, r = pv.tt, pv.tt.fr, pv.r
    nc = len(cand)
    pool = IDPool(start_from=nc + 1)
    X = lambda c: c + 1
    clauses, cards = [], []
    by_type = {}
    for c, (i, a, b, s, t) in enumerate(cand):
        by_type.setdefault(i, []).append(c)
    if distinct:
        for cs in by_type.values():
            for p in range(len(cs)):
                for q in range(p + 1, len(cs)):
                    clauses.append([-X(cs[p]), -X(cs[q])])
    else:
        prev = {}
        for c, cc in enumerate(cand):
            key = (cc[0], cc[1], cc[2])
            if key in prev:
                clauses.append([-X(c), X(prev[key])])
            prev[key] = c
    info = {"candidates": nc}
    if "compat" not in drop:
        nr, ns, bad, rho_of, sig_of = pair_table(pv, cand, mutate=drop)
        Y = [pool.id(("Y", q)) for q in range(nr)]
        Zv = [pool.id(("Z", q)) for q in range(ns)]
        rm = [[] for _ in range(nr)]
        sm = [[] for _ in range(ns)]
        diag = {}
        for c in range(nc):
            clauses.append([-X(c), Y[rho_of[c]]])
            clauses.append([-X(c), Zv[sig_of[c]]])
            rm[rho_of[c]].append(c)
            sm[sig_of[c]].append(c)
            diag.setdefault((rho_of[c], sig_of[c]), []).append(c)
        for p, q in bad:
            p, q = int(p), int(q)
            ds = diag.get((p, q))
            if ds is None:
                clauses.append([-Y[p], -Zv[q]])
            else:
                dset = set(ds)
                clauses.extend([-X(c), -Zv[q]] for c in rm[p] if c not in dset)
                for cs in ds:
                    clauses.extend([-X(cs), -X(c)] for c in sm[q] if c != cs)
        info["bad pairs (ρ,σ)"] = len(bad)

    def card(lits, bound):
        if bound < 0 or bound > len(lits):
            clauses.append([])
        elif bound == 0:
            clauses.extend([[-l] for l in lits])
        elif bound == len(lits):
            clauses.extend([[l] for l in lits])
        else:
            cards.append((lits, bound))

    Ob = np.array([tt.Ob[i] for i, *_ in cand], dtype=np.int64).reshape(nc, fr.n)
    Ib = np.array([tt.Ib[i] for i, *_ in cand], dtype=np.int64).reshape(nc, fr.n)
    PO = [tt.Ob[i] for i in pv.piv]
    PI = [tt.Ib[i] for i in pv.piv]
    if "cover" not in drop:
        for u in fr.Np:
            for v in fr.Np:
                card([X(int(c)) for c in np.nonzero(Ib[:, u] & Ob[:, v])[0]],
                     fr.Phi[u][v] - sum(int(PI[i][u] * PO[i][v]) for i in range(r)))
    if "degree" not in drop:
        for u in fr.Np:
            card([X(int(c)) for c in np.nonzero(Ib[:, u])[0]], fr.outW[u] - sum(int(PI[i][u]) for i in range(r)))
            card([X(int(c)) for c in np.nonzero(Ob[:, u])[0]], fr.inW[u] - sum(int(PO[i][u]) for i in range(r)))
        A_RR = pv.arcs
        for i in range(r):
            card([X(c) for c, cc in enumerate(cand) if cc[1][i]],
                 fr.k - int(PO[i].sum()) - sum(A_RR[i]))
            card([X(c) for c, cc in enumerate(cand) if cc[2][i]],
                 fr.k - int(PI[i].sum()) - sum(A_RR[j][i] for j in range(r)))
            card([X(c) for c, cc in enumerate(cand) if cc[1][i] and cc[2][i]],
                 fr.t - int((PO[i] * PI[i]).sum()) - sum(A_RR[i][j] * A_RR[j][i] for j in range(r)))
    card([X(c) for c in range(nc)], fr.params[0] - fr.n - r)
    info["clauses"] = len(clauses)
    info["cardinalities"] = len(cards)
    return clauses, cards, info


def encode_cards(clauses, cards):
    from pysat.card import CardEnc, EncType
    from pysat.formula import IDPool
    top = max([abs(l) for c in clauses for l in c] + [abs(l) for lits, b in cards for l in lits] + [0])
    pool = IDPool(start_from=top + 1)
    out = list(clauses)
    for lits, b in cards:
        out.extend(CardEnc.equals(lits=lits, bound=b, vpool=pool, encoding=EncType.seqcounter).clauses)
    return out


def solve_cadical(clauses, cards, proof_dir=None, certify=None, name="search48_second"):
    """CaDiCaL with a DRAT proof. With proof_dir, the CNF, DRAT and LRAT files of an UNSAT formula stay in
    proof_dir under the given name, and certify(cnf, drat) checks them."""
    import os
    import sys
    sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), os.pardir, "lib"))
    import time
    from solver_release import proof_solver
    full = encode_cards(clauses, cards)
    if any(len(c) == 0 for c in full):
        return "UNSAT", "empty clause"
    with proof_solver("cadical195", bootstrap_with=full, with_proof=proof_dir is not None) as s:
        t_solve = time.time()
        r = s.solve()
        t_solve = time.time() - t_solve
        proof = s.get_proof() if (proof_dir is not None and not r) else None
    if r:
        return "SAT", None
    cert = None
    if proof is not None:
        cnf = os.path.join(proof_dir, f"{name}.cnf")
        drat = os.path.join(proof_dir, f"{name}.drat")
        nv = max(abs(l) for c in full for l in c)
        with open(cnf, "w") as f:
            f.write(f"p cnf {nv} {len(full)}\n")
            for c in full:
                f.write(" ".join(map(str, c)) + " 0\n")
        with open(drat, "w") as f:
            for line in proof:
                f.write(line + "\n")
        cert = f"solver {t_solve:.1f} s, " + certify(cnf, drat)
    return "UNSAT", cert


def solve(clauses, cards, assumptions=(), block_limit=0, check=None):
    from pysat.solvers import Solver
    with Solver(name="minicard", bootstrap_with=clauses) as s:
        for lits, b in cards:
            s.add_atmost(lits, b)
            s.add_atmost([-l for l in lits], len(lits) - b)
        found = []
        for _ in range(block_limit + 1):
            if not s.solve(assumptions=list(assumptions)):
                return "UNSAT", found
            m = s.get_model()
            found.append(m)
            if check is None or check(m):
                return "SAT", found
            s.add_clause([-l for l in m if l > 0 and l <= check.nc])
        return "LIMIT", found
