"""Row and column classes of A + I.
"""
from __future__ import annotations

import numpy as np

import graph_controls as nc

PRIME = 2_147_483_629


def family(p, mu_min: int = 1) -> bool:
    v, k, t, lam, mu = p
    return t == lam + 1 and mu >= mu_min and 0 < t < k < v - 1 and lam + 2 - mu > 0


def family_mu_one(p) -> bool:
    v, k, t, lam, mu = p
    return mu == 1 and t == lam + 1 and 0 < t < k < v - 1


def complement_params(p):
    v, k, t, lam, mu = p
    return (v, v - k - 1, v - 2 * k + t - 1, v - 2 * k + mu - 2, v - 2 * k + lam)


def f_mult(p):
    v, k, t, lam, mu = p
    q = lam + 2 - mu
    if q <= 0:
        return None
    f, r = divmod(v - k - 1, q)
    return f if r == 0 else None


def family_graphs(keep):
    raw = nc.load_graphs(nc.catalog_files(), lambda p: keep(p) or keep(complement_params(p)))
    out, seen = [], set()
    for g in raw:
        cand = [g] if keep(g["params"]) else []
        if keep(complement_params(g["params"])):
            cand.append(nc.complement(g))
        for h in cand:
            key = (h["params"], h["A"].tobytes())
            if key not in seen:
                seen.add(key)
                out.append(h)
    out.sort(key=lambda h: h["params"])
    return out


def rank_mod(M, p: int = PRIME) -> int:
    M = np.array(M, dtype=np.int64) % p
    n, m = M.shape
    r = 0
    for c in range(m):
        nz = np.nonzero(M[r:, c])[0]
        if not len(nz):
            continue
        piv = r + nz[0]
        if piv != r:
            M[[r, piv]] = M[[piv, r]]
        M[r] = (M[r] * pow(int(M[r, c]), p - 2, p)) % p
        col = M[:, c].copy()
        col[r] = 0
        rows = np.nonzero(col)[0]
        if len(rows):
            M[rows] = (M[rows] - np.outer(col[rows], M[r]) % p) % p
        r += 1
        if r == n:
            break
    return r


def row_classes(rows) -> list[int]:
    idx, out = {}, []
    for r in rows:
        out.append(idx.setdefault(tuple(int(x) for x in r), len(idx)))
    return out


def sizes_mu_one(p, low_shift: int = 0, cap_shift: int = 0) -> list[int]:
    v, k, t, lam, mu = p
    f = (v - k - 1) // (lam + 1)
    low = max(1, k + 1 - f + low_shift)
    cap = k + 1 + cap_shift
    return [a for a in range(low, lam + 2) if a * (lam + 3 - a) <= cap]


def mu1_twin_forced(p, threshold: int = 4) -> bool:
    v, k, t, lam, mu = p
    return k == 2 * lam + 2 and lam >= threshold


def sizes(p, low_shift: int = 0, lam_shift: int = 0, high_shift: int = 0, cap_shift: int = 0) -> list[int]:
    v, k, t, lam, mu = p
    K, f = k + 1, f_mult(p)
    low = max(1, K - mu * f + low_shift)
    high = min(lam + 1 + lam_shift, k - lam - 1 + mu + high_shift)
    return [a for a in range(low, high + 1) if a * (lam + 2 - a) <= mu * (K - a) + cap_shift]


def condition(p, strict: bool = False) -> bool:
    v, k, t, lam, mu = p
    q, f = lam + 2 - mu, f_mult(p)
    return q < mu * f if strict else q <= mu * f
