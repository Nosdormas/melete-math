"""Frame, types, Φ and orbit keys of the second program for (48, 9, 5, 0, 2).
"""
from __future__ import annotations

import itertools
import json
import glob
import os
from fractions import Fraction as Fr
from math import lcm

import numpy as np

ROOT = os.path.abspath(os.path.join(os.path.dirname(__file__), os.pardir))


def popcount(x: int) -> int:
    return bin(x).count("1")


def inverse(M):
    n = len(M)
    a = [[Fr(v) for v in row] + [Fr(int(i == j)) for j in range(n)] for i, row in enumerate(M)]
    for c in range(n):
        p = next(r for r in range(c, n) if a[r][c] != 0)
        a[c], a[p] = a[p], a[c]
        inv = 1 / a[c][c]
        a[c] = [v * inv for v in a[c]]
        for r in range(n):
            if r != c and a[r][c] != 0:
                f = a[r][c]
                a[r] = [vr - f * vc for vr, vc in zip(a[r], a[c])]
    return [row[n:] for row in a]


def rank(M) -> int:
    a = [[Fr(v) for v in row] for row in M]
    if not a:
        return 0
    r = 0
    cols = len(a[0])
    for c in range(cols):
        p = next((i for i in range(r, len(a)) if a[i][c] != 0), None)
        if p is None:
            continue
        a[r], a[p] = a[p], a[r]
        for i in range(len(a)):
            if i != r and a[i][c] != 0:
                f = a[i][c] / a[r][c]
                a[i] = [vi - f * vr for vi, vr in zip(a[i], a[r])]
        r += 1
    return r


def roots(params):
    v, k, t, lam, mu = params
    disc = mu * mu + 4 * (t - mu)
    s = int(round(disc ** 0.5))
    assert s * s == disc, params
    r1, r2 = (-mu + s) // 2, (-mu - s) // 2
    assert r1 * r1 + mu * r1 - (t - mu) == 0 and r2 * r2 + mu * r2 - (t - mu) == 0
    return r1, r2


class Frame:
    def __init__(self, params, theta, qp_arcs):
        v, k, t, lam, mu = params
        assert lam == 0
        self.params, self.theta = params, theta
        self.k, self.t, self.mu = k, t, mu
        h = k - t
        self.M = list(range(1, t + 1))
        self.Q = list(range(t + 1, t + 1 + h))
        self.P = list(range(t + 1 + h, t + 1 + 2 * h))
        self.n = 2 * k - t + 1
        self.Np = list(range(1, self.n))
        n = self.n
        A = [[0] * n for _ in range(n)]
        for y in self.M + self.Q:
            A[0][y] = 1
        for y in self.M + self.P:
            A[y][0] = 1
        self.qp = sorted(qp_arcs)
        for i, j in self.qp:
            A[self.Q[i]][self.P[j]] = 1
        self.AN = A
        self.mask = lambda vs: sum(1 << y for y in vs)
        self.mOut = self.mask(self.M + self.Q)   # Γ⁺(x)
        self.mIn = self.mask(self.M + self.P)    # Γ⁻(x)
        self.mQ, self.mP, self.mM = self.mask(self.Q), self.mask(self.P), self.mask(self.M)
        th = theta
        thp = -mu - th
        A2 = [[sum(A[i][z] * A[z][j] for z in range(n)) for j in range(n)] for i in range(n)]
        tgt = [[t if i == j else mu * (1 - A[i][j]) for j in range(n)] for i in range(n)]
        self.Phi = [[tgt[i][j] - A2[i][j] for j in range(n)] for i in range(n)]
        D = [[Fr(A[i][j]) - (th if i == j else 0) for j in range(n)] for i in range(n)]
        D2 = [[sum(D[i][z] * D[z][j] for z in range(n)) for j in range(n)] for i in range(n)]
        delta = th - thp
        Phi2 = [[mu - D2[i][j] - delta * D[i][j] for j in range(n)] for i in range(n)]
        assert all(Phi2[i][j] == self.Phi[i][j] for i in range(n) for j in range(n)), "Φ: the formulas differ"
        assert all(self.Phi[0][j] == 0 and self.Phi[j][0] == 0 for j in range(n)), "Φ at x is not zero"
        self.outW = {y: k - sum(A[y]) for y in self.Np}
        self.inW = {y: k - sum(A[z][y] for z in range(n)) for y in self.Np}
        self.D = D
        Dinv = inverse(D)
        self.L = lcm(*[x.denominator for row in Dinv for x in row])
        self.DI = np.array([[int(x * self.L) for x in row] for row in Dinv], dtype=np.int64)
        self.Dinv = Dinv
        self.succ = {y: self.mask([z for z in self.Np if A[y][z]]) for y in self.Np}
        self.pred = {y: self.mask([z for z in self.Np if A[z][y]]) for y in self.Np}

    def row_vec(self, Omask):
        idx = [y for y in self.Np if Omask >> y & 1]
        return self.DI[idx].sum(axis=0) if idx else np.zeros(self.n, dtype=np.int64)

    def F_scaled(self, Omask, Imask) -> int:
        r = self.row_vec(Omask)
        return int(sum(int(r[y]) for y in self.Np if Imask >> y & 1))

    def _o_ok(self, O) -> bool:
        if popcount(O & self.mIn) != self.mu or popcount(O) > self.k:
            return False
        return all(popcount(O & self.pred[y]) <= self.mu * (1 - (O >> y & 1)) for y in self.Np)

    def _i_ok(self, I) -> bool:
        if popcount(I & self.mOut) != self.mu or popcount(I) > self.k:
            return False
        return all(popcount(self.succ[y] & I) <= self.mu * (1 - (I >> y & 1)) for y in self.Np)

    def _bad_in(self, O) -> int:
        m = 0
        for v in self.Np:
            if O >> v & 1:
                for u in self.Np:
                    if self.Phi[u][v] < 1:
                        m |= 1 << u
        return m

    def type_ok(self, O, I) -> bool:
        return (self._o_ok(O) and self._i_ok(I) and popcount(O & I) <= self.t
                and I & self._bad_in(O) == 0)

    def all_types(self):
        mu = self.mu
        outs = []
        for MP in itertools.combinations(self.M + self.P, mu):
            for r in range(len(self.Q) + 1):
                for Qs in itertools.combinations(self.Q, r):
                    O = self.mask(MP) | self.mask(Qs)
                    if self._o_ok(O):
                        outs.append(O)
        ins = []
        for MQ in itertools.combinations(self.M + self.Q, mu):
            for r in range(len(self.P) + 1):
                for Ps in itertools.combinations(self.P, r):
                    I = self.mask(MQ) | self.mask(Ps)
                    if self._i_ok(I):
                        ins.append(I)
        res = []
        for O in outs:
            bad = self._bad_in(O)
            for I in ins:
                if I & bad == 0 and popcount(O & I) <= self.t:
                    res.append((O, I))
        return res

    def d_scaled(self, O, I) -> int:
        """L·d_w, d_w = S_ww = −θ − f(w, w)."""
        return -self.theta * self.L - self.F_scaled(O, I)


# ---------- (48, 9, 5, 0, 2) ----------

SET48 = (48, 9, 5, 0, 2)


def qp_case(kind):
    if kind == "C8":
        return {(i, i) for i in range(4)} | {(i, (i + 1) % 4) for i in range(4)}
    if kind == "2C4":
        return {(i, j) for i in (0, 1) for j in (0, 1)} | {(i, j) for i in (2, 3) for j in (2, 3)}
    raise ValueError(kind)


def two_regular_classes(h=4, deg=2):
    rows = [c for c in itertools.combinations(range(h), deg)]
    mats = []
    for choice in itertools.product(rows, repeat=h):
        col = [0] * h
        for r in choice:
            for j in r:
                col[j] += 1
        if all(c == deg for c in col):
            mats.append(frozenset((i, j) for i, r in enumerate(choice) for j in r))
    perms = list(itertools.permutations(range(h)))
    seen, classes = set(), []
    for m in mats:
        if m in seen:
            continue
        orb = {frozenset((a[i], b[j]) for i, j in m) for a in perms for b in perms}
        seen |= orb
        classes.append((m, len(orb)))
    return len(mats), classes


def cycle_structure(arcs, h=4):
    adj = {("q", i): [] for i in range(h)} | {("p", j): [] for j in range(h)}
    for i, j in arcs:
        adj[("q", i)].append(("p", j))
        adj[("p", j)].append(("q", i))
    seen, lens = set(), []
    for s in adj:
        if s in seen:
            continue
        stack, comp = [s], 0
        seen.add(s)
        while stack:
            u = stack.pop()
            comp += 1
            for w in adj[u]:
                if w not in seen:
                    seen.add(w)
                    stack.append(w)
        lens.append(comp)
    return sorted(lens)


def frame_group(fr: Frame):
    h = len(fr.Q)
    qp = set(fr.qp)
    aut = [(a, b) for a in itertools.permutations(range(h)) for b in itertools.permutations(range(h))
           if {(a[i], b[j]) for i, j in qp} == qp]
    group = []
    for pm in itertools.permutations(range(len(fr.M))):
        for a, b in aut:
            g = {fr.M[i]: fr.M[pm[i]] for i in range(len(fr.M))}
            g.update({fr.Q[i]: fr.Q[a[i]] for i in range(h)})
            g.update({fr.P[j]: fr.P[b[j]] for j in range(h)})
            group.append(g)
    return group, len(aut)


def is_frame_automorphism(fr: Frame, g) -> bool:
    gg = dict(g)
    gg[0] = 0
    n = fr.n
    return all(fr.AN[i][j] == fr.AN[gg[i]][gg[j]] for i in range(n) for j in range(n))


def apply_mask(g, m):
    r = 0
    for y, z in g.items():
        if m >> y & 1:
            r |= 1 << z
    return r


def mask_tables(g, bits=16):
    lo = [apply_mask(g, m) for m in range(256)]
    hi = [apply_mask(g, m << 8) for m in range(1 << (bits - 8))]
    return lo, hi


def frame_generators(fr: Frame):
    group_qp = []
    h = len(fr.Q)
    qp = set(fr.qp)
    for a in itertools.permutations(range(h)):
        for b in itertools.permutations(range(h)):
            if {(a[i], b[j]) for i, j in qp} == qp:
                g = {y: y for y in fr.M}
                g.update({fr.Q[i]: fr.Q[a[i]] for i in range(h)})
                g.update({fr.P[j]: fr.P[b[j]] for j in range(h)})
                group_qp.append(g)
    ident_qp = {y: y for y in fr.Q + fr.P}
    gens = []
    t = len(fr.M)
    if t >= 2:
        sw = {fr.M[i]: fr.M[i] for i in range(t)}
        sw[fr.M[0]], sw[fr.M[1]] = fr.M[1], fr.M[0]
        cyc = {fr.M[i]: fr.M[(i + 1) % t] for i in range(t)}
        for g in (sw, cyc):
            gg = dict(g)
            gg.update(ident_qp)
            gens.append(gg)
    gens += group_qp
    return gens, len(group_qp)


def type_orbits(fr: Frame, types, gens):
    idx = {T: i for i, T in enumerate(types)}
    parent = list(range(len(types)))

    def find(a):
        while parent[a] != a:
            parent[a] = parent[parent[a]]
            a = parent[a]
        return a

    tabs = [mask_tables(g) for g in gens]
    for T, i in idx.items():
        O, I = T
        for lo, hi in tabs:
            U = (lo[O & 255] | hi[O >> 8], lo[I & 255] | hi[I >> 8])
            j = idx.get(U)
            assert j is not None, "the set of types is not closed under the symmetry of the frame"
            ra, rb = find(i), find(j)
            if ra != rb:
                parent[ra] = rb
    code = lambda T: (T[0] << 32) | T[1]
    best = {}
    for T, i in idx.items():
        r = find(i)
        c = code(T)
        if r not in best or c < best[r]:
            best[r] = c
    return {T: best[find(i)] for T, i in idx.items()}


def load_catalog_lambda0():
    files = sorted(glob.glob(os.path.join(ROOT, "data", "graphs", "*.json")))
    files += sorted(glob.glob(os.path.join(ROOT, "data", "graphs", "catalog", "*.json")))
    out = []
    for f in files:
        d = json.load(open(f, encoding="utf8"))
        gs = d.get("graphs")
        if not gs:
            continue
        for gi, e in enumerate(gs):
            if "rows" in e:
                A = [[int(c) for c in r] for r in e["rows"]]
            elif "bitmasks" in e:
                v = len(e["bitmasks"])
                A = [[m >> j & 1 for j in range(v)] for m in e["bitmasks"]]
            else:
                continue
            name = f"{os.path.basename(f)}:{e.get('id', gi)}"
            for comp in (False, True):
                B = [[(0 if i == j else 1 - A[i][j]) for j in range(len(A))] for i in range(len(A))] if comp else A
                p = dsrg_params(B)
                if p and p[3] == 0:
                    out.append((name + (":complement" if comp else ""), p, B))
    return out


def dsrg_params(A):
    v = len(A)
    if any(A[i][i] for i in range(v)):
        return None
    k = sum(A[0])
    if any(sum(r) != k for r in A) or any(sum(A[i][j] for i in range(v)) != k for j in range(v)):
        return None
    A2 = [[sum(A[i][z] * A[z][j] for z in range(v) if A[i][z]) for j in range(v)] for i in range(v)]
    t = A2[0][0]
    lam = mu = None
    for i in range(v):
        if A2[i][i] != t:
            return None
        for j in range(v):
            if i == j:
                continue
            if A[i][j]:
                if lam is None:
                    lam = A2[i][j]
                elif A2[i][j] != lam:
                    return None
            else:
                if mu is None:
                    mu = A2[i][j]
                elif A2[i][j] != mu:
                    return None
    if lam is None or mu is None:
        return None
    return (v, k, t, lam, mu)


def frame_at(A, params, x, theta):
    v = len(A)
    out = [y for y in range(v) if A[x][y]]
    inn = [y for y in range(v) if A[y][x]]
    M = [y for y in out if A[y][x]]
    Q = [y for y in out if not A[y][x]]
    P = [y for y in inn if not A[x][y]]
    order = [x] + M + Q + P
    arcs = {(i, j) for i, q in enumerate(Q) for j, p in enumerate(P) if A[q][p]}
    fr = Frame(params, theta, arcs)
    for i, a in enumerate(order):
        for j, b in enumerate(order):
            assert A[a][b] == fr.AN[i][j], "the structure of N[x] is not as in the closed neighbourhood lemma"
    W = [y for y in range(v) if y not in set(order)]
    pos = {a: i for i, a in enumerate(order)}
    tys = []
    for w in W:
        O = sum(1 << pos[y] for y in order[1:] if A[w][y])
        I = sum(1 << pos[y] for y in order[1:] if A[y][w])
        tys.append((O, I))
    return fr, order, W, tys
