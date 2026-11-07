"""Frame of a vertex for λ = 0 with a pivot: types of outer vertices, D⁻¹, Φ and the cover data.
"""
from __future__ import annotations

from collections import Counter
from fractions import Fraction as Fr
from itertools import combinations, permutations, product

import numpy as np

from exact_cover_pairs import to_bits
from kernel_frame import inverse

X, M, Q, P = 0, list(range(1, 6)), list(range(6, 10)), list(range(10, 14))
NN = 14
MU = 2


def qp_arcs(kind):
    if kind == "C8":
        return [(Q[i], P[i]) for i in range(4)] + [(Q[i], P[(i + 1) % 4]) for i in range(4)]
    if kind == "2C4":
        return [(Q[0], P[0]), (Q[0], P[1]), (Q[1], P[0]), (Q[1], P[1]),
                (Q[2], P[2]), (Q[2], P[3]), (Q[3], P[2]), (Q[3], P[3])]
    raise ValueError(f"graph Q → P: C8 or 2C4, not {kind}")


def frame(kind):
    A = [[0] * NN for _ in range(NN)]
    for o in M + Q:
        A[X][o] = 1
    for i in M + P:
        A[i][X] = 1
    for q, p in qp_arcs(kind):
        A[q][p] = 1
    return A


def qp_aut(kind):
    arcs = set(qp_arcs(kind))
    return [(pq, pp) for pq in permutations(range(4)) for pp in permutations(range(4))
            if {(Q[pq[q - 6]], P[pp[p - 10]]) for q, p in arcs} == arcs]


def types(kind):
    arcs = qp_arcs(kind)
    out = []
    for cin in combinations(M + Q, 2):
        for cp in product((0, 1), repeat=4):
            c = set(cin) | {P[i] for i in range(4) if cp[i]}
            for rout in combinations(M + P, 2):
                for rq in product((0, 1), repeat=4):
                    r = set(rout) | {Q[i] for i in range(4) if rq[i]}
                    if any((q in c and p in r) or (q in r and p in r) or (q in c and p in c)
                           for q, p in arcs):
                        continue
                    out.append((frozenset(r), frozenset(c)))
    return out


def _key(r, c, aut):
    mk = tuple(sorted((m in r, m in c) for m in M))
    best = min((tuple(Q[pq[i]] in r for i in range(4)) + tuple(Q[pq[i]] in c for i in range(4)),
                tuple(P[pp[i]] in r for i in range(4)) + tuple(P[pp[i]] in c for i in range(4)))
               for pq, pp in aut)
    return mk, best


def canon(r, c, aut):
    return _key(r, c, aut)


def inverse_d(kind):
    A = frame(kind)
    D = [[A[i][j] - (1 if i == j else 0) for j in range(NN)] for i in range(NN)]
    return inverse(D)


def inverse12(kind):
    Di = inverse_d(kind)
    if any((12 * x).denominator != 1 for row in Di for x in row):
        raise ArithmeticError("12·D⁻¹ is not integer")
    return np.array([[int(12 * x) for x in row] for row in Di], dtype=np.int64)


def _rows(T):
    n = len(T)
    R = np.zeros((n, NN), dtype=np.int64)
    C = np.zeros((n, NN), dtype=np.int64)
    for i, (r, c) in enumerate(T):
        R[i, list(r)] = 1
        C[i, list(c)] = 1
    return R, C


def type_d3(kind):
    Di12 = inverse12(kind)
    T = types(kind)
    R, C = _rows(T)
    d12 = -12 - np.einsum("ij,jk,ik->i", R, Di12, C)
    if np.any(d12 % 4):
        raise ArithmeticError("3d is not an integer")
    return T, R, C, Di12, d12 // 4


DELTA = 4
K = 9
NP = list(range(1, NN))
NCELL = 197


def phi(kind):
    A = np.array(frame(kind), dtype=np.int64)
    D = A - np.eye(NN, dtype=np.int64)
    return MU * np.ones((NN, NN), dtype=np.int64) - D @ D - DELTA * D


def degrees(kind):
    A = np.array(frame(kind), dtype=np.int64)
    return K - A.sum(axis=1), K - A.sum(axis=0)


def pivot_list(kind, T, d3):
    aut = qp_aut(kind)
    keys = [canon(r, c, aut) for r, c in T]
    order = sorted(set(keys))
    rank_of = {k: i for i, k in enumerate(order)}
    keyrank = np.array([rank_of[k] for k in keys])
    rep = {}
    for i, k in enumerate(keys):
        rep.setdefault(k, i)
    return [rep[k] for k in order if d3[rep[k]] != 0], keyrank


def partners(R, C, Di12, d3, i0):
    f01 = (R[i0] @ Di12) @ C.T          # 12 F(w0, w')
    f10 = R @ (Di12 @ C[i0])            # 12 F(w', w0)
    cc = (C @ C[i0]) > 0
    rr = (R @ R[i0]) > 0
    p01 = C @ R[i0]
    p10 = R @ C[i0]
    out = []
    for a01 in (0, 1):
        ok01 = (~cc & ~rr & (p01 == 0)) if a01 else (p01 <= MU)
        for a10 in (0, 1):
            ok10 = (~cc & ~rr & (p10 == 0)) if a10 else (p10 <= MU)
            ok = ok01 & ok10
            ok[i0] = False
            s0 = 12 * a01 - f01         # 12 S(w0, w')
            u = 12 * a10 - f10          # 12 S(w', w0)
            ok &= (16 * d3[i0] * d3 == s0 * u)
            idx = np.flatnonzero(ok)
            for i in idx:
                out.append((int(i), a01, a10, int(u[i]), int(s0[i])))
    return out


def cells_of(r, c, a01, a10):
    out = [(n - 1) * 13 + (m - 1) for n in c for m in r]
    out += [169 + n - 1 for n in c]
    out += [182 + m - 1 for m in r]
    if a01:
        out.append(195)
    if a10:
        out.append(196)
    return out


def needs(kind, r0, c0):
    ph = phi(kind)
    dout, din = degrees(kind)
    need = [0] * NCELL
    for n in NP:
        for m in NP:
            need[(n - 1) * 13 + m - 1] = int(ph[n, m])
        need[169 + n - 1] = int(dout[n])
        need[182 + n - 1] = int(din[n])
    need[195] = 7 - len(r0 & set(Q))
    need[196] = 7 - len(c0 & set(P))
    for c in cells_of(r0, c0, 0, 0):
        need[c] -= 1
    return need


class LazyRows:

    def __init__(self, Rp, Cp, Di12, k, idx, a01, a10, u, s0):
        self.RD = Rp @ Di12
        self.DC = Di12 @ Cp.T
        self.Rp, self.Cp, self.k, self.idx = Rp, Cp, k, idx
        self.a01, self.a10, self.u, self.s0 = a01, a10, u, s0
        self.cache = {}

    def rows(self, i):
        if i in self.cache:
            return self.cache[i]
        Rp, Cp, k = self.Rp, self.Cp, self.k
        a01, a10, u, s0 = self.a01, self.a10, self.u, self.s0
        # i → j
        X = u[i] * s0 + k * (self.RD[i] @ Cp.T)
        p2 = Rp[i] @ Cp.T + (a10[i] & a01)
        cin = (Cp @ Cp[i] > 0) | (a01[i] & a01)
        cout = (Rp @ Rp[i] > 0) | (a10[i] & a10)
        onef = (X == 12 * k) & (p2 == 0) & ~cin & ~cout
        okf = onef | ((X == 0) & (p2 <= MU))
        # j → i
        Xb = u * s0[i] + k * (self.RD @ Cp[i])
        p2b = Rp @ Cp[i] + (a10 & a01[i])
        cinb = (Cp @ Cp[i] > 0) | (a01 & a01[i])
        coutb = (Rp @ Rp[i] > 0) | (a10 & a10[i])
        oneb = (Xb == 12 * k) & (p2b == 0) & ~cinb & ~coutb
        okb = oneb | ((Xb == 0) & (p2b <= MU))
        cmp_ = okf & okb & (self.idx != self.idx[i])
        cmp_[i] = False
        out = (to_bits(cmp_), to_bits(onef & cmp_), to_bits(oneb & cmp_))
        self.cache[i] = out
        return out

    def view(self, which):
        lazy = self

        class _V:
            def __getitem__(self, i):
                return lazy.rows(i)[which]
        return _V()


def exact_f(T, Di):
    def F(ta, tb):
        r, _ = T[ta]
        _, c = T[tb]
        return sum(Di[i][j] for i in r for j in c)
    return F


def admissible(arc, r_from, c_to, c_from, r_to, via_from, via_to, in_both, out_both):
    paths = len(r_from & c_to) + (1 if via_from and via_to else 0)
    if arc:
        return paths == 0 and not (c_from & c_to) and not in_both and not (r_from & r_to) and not out_both
    return paths <= MU


def exact_partner(F, T, i0, ti, a01, a10):
    r0, c0 = T[i0]
    r, c = T[ti]
    d0 = -1 - F(i0, i0)
    s0w = a01 - F(i0, ti)
    sw0 = a10 - F(ti, i0)
    dw = -1 - F(ti, ti)
    ok = d0 * dw == s0w * sw0
    ok &= admissible(a01, r0, c, c0, r, False, False, False, False)
    ok &= admissible(a10, r, c0, c, r0, False, False, False, False)
    return ok, s0w, sw0


def exact_pair(F, T, i0, pa, pb):
    (ta, x01a, x10a, _, _), (tb, x01b, x10b, _, _) = pa, pb
    ra, ca = T[ta]
    rb, cb = T[tb]
    d0 = -1 - F(i0, i0)
    val = F(ta, tb) + (x10a - F(ta, i0)) * (x01b - F(i0, tb)) / d0
    val2 = F(tb, ta) + (x10b - F(tb, i0)) * (x01a - F(i0, ta)) / d0
    both_out, both_in = bool(x01a and x01b), bool(x10a and x10b)
    ok1 = val in (0, 1) and admissible(val == 1, ra, cb, ca, rb, x10a, x01b, both_out, both_in)
    ok2 = val2 in (0, 1) and admissible(val2 == 1, rb, ca, cb, ra, x10b, x01a, both_out, both_in)
    return bool(ok1 and ok2 and ta != tb), val == 1
