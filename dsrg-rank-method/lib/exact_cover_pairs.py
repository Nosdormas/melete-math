"""Exact cover with pairwise compatibility and degree counting.
"""
from __future__ import annotations

import itertools
import random

import numpy as np

MUTATIONS = ("no-exclude", "no-saturate")


def to_bits(rowbool):
    by = np.packbits(np.asarray(rowbool, dtype=np.uint8), bitorder="little")
    return int.from_bytes(by.tobytes(), "little")


def bits_list(mask):
    out = []
    while mask:
        low = mask & -mask
        out.append(low.bit_length() - 1)
        mask ^= low
    return out


class Cover:

    def __init__(self, covers, need, comp, outb=None, inb=None, vout=None, vin=None, mutate=None,
                 cellmask=None):
        if mutate is not None and mutate not in MUTATIONS:
            raise ValueError(f"engine mutant: {', '.join(MUTATIONS)}, not {mutate}")
        self.m = len(covers)
        self.covers, self.need0, self.comp = covers, list(need), comp
        self.outb, self.inb, self.vout, self.vin = outb, inb, vout, vin
        self.deg = vout is not None
        self.mutate = mutate
        if cellmask is not None:
            if len(cellmask) != len(need):
                raise ValueError("cellmask and need differ in length")
            self.cellmask = list(cellmask)
            return
        self.cellmask = [0] * len(need)
        for i, cs in enumerate(covers):
            for c in cs:
                self.cellmask[c] |= 1 << i

    def root(self):
        if any(x < 0 for x in self.need0):
            return None
        cand = (1 << self.m) - 1
        for c, nd in enumerate(self.need0):
            if nd == 0:
                cand &= ~self.cellmask[c]
        return (tuple(self.need0), cand, (), {}, {})

    def choose(self, st):
        need, cand, chosen, vo, vi = st
        best = None
        pending = False
        for c, nd in enumerate(need):
            if nd <= 0:
                continue
            pending = True
            mk = cand & self.cellmask[c]
            cnt = mk.bit_count()
            if cnt < nd:
                return None
            if best is None or cnt < best[1]:
                best = (mk, cnt)
        if self.deg:
            for rel, d in ((self.outb, vo), (self.inb, vi)):
                for w, rem in d.items():
                    if rem > 0:
                        pending = True
                        mk = cand & rel[w]
                        cnt = mk.bit_count()
                        if cnt < rem:
                            return None
                        if best is None or cnt < best[1]:
                            best = (mk, cnt)
        if not pending:
            return "leaf"
        return best

    def take(self, st, i, excl):
        need, cand, chosen, vo, vi = st
        need = list(need)
        for c in self.covers[i]:
            need[c] -= 1
            if need[c] < 0:
                return None
        cand = cand & self.comp[i] & ~excl
        if self.mutate != "no-saturate":
            for c in self.covers[i]:
                if need[c] == 0:
                    cand &= ~self.cellmask[c]
        if self.deg:
            vo, vi = dict(vo), dict(vi)
            ro, ri = self.vout[i], self.vin[i]
            for w in chosen:
                if (self.outb[w] >> i) & 1:
                    vo[w] -= 1
                    ri -= 1
                if (self.inb[w] >> i) & 1:
                    vi[w] -= 1
                    ro -= 1
            if ro < 0 or ri < 0 or any(x < 0 for x in vo.values()) or any(x < 0 for x in vi.values()):
                return None
            vo[i], vi[i] = ro, ri
            for w, rem in vo.items():
                if rem == 0:
                    cand &= ~self.outb[w]
            for w, rem in vi.items():
                if rem == 0:
                    cand &= ~self.inb[w]
        return (tuple(need), cand, chosen + (i,), vo, vi)

    def search(self, node_limit=None, first=False):
        st0 = self.root()
        if st0 is None:
            return 0, [], True
        nodes, sols, stack = 0, [], [st0]
        while stack:
            st = stack.pop()
            nodes += 1
            if node_limit and nodes > node_limit:
                return nodes, sols, False
            ch = self.choose(st)
            if ch is None:
                continue
            if ch == "leaf":
                sols.append(st[2])
                if first:
                    return nodes, sols, False
                continue
            mk, _ = ch
            excl = 0
            for o in bits_list(mk):
                nxt = self.take(st, o, excl)
                if self.mutate != "no-exclude":
                    excl |= 1 << o
                if nxt is not None:
                    stack.append(nxt)
        return nodes, sols, True


def brute(covers, need, comp, outb, inb, vout, vin):
    m = len(covers)
    out = []
    for size in range(m + 1):
        for X in itertools.combinations(range(m), size):
            if any(not (comp[i] >> j) & 1 for i in X for j in X if i != j):
                continue
            cnt = [0] * len(need)
            for i in X:
                for c in covers[i]:
                    cnt[c] += 1
            if cnt != list(need):
                continue
            if vout is not None and any(
                    sum((outb[i] >> j) & 1 for j in X) != vout[i] or sum((inb[i] >> j) & 1 for j in X) != vin[i]
                    for i in X):
                continue
            out.append(tuple(sorted(X)))
    return sorted(out)


def random_instance(rng, m, ncell):
    X = sorted(rng.sample(range(m), rng.randint(2, min(6, m))))
    covers = [sorted(rng.sample(range(ncell), rng.randint(1, 3))) for _ in range(m)]
    comp_m = [[False] * m for _ in range(m)]
    arc = [[False] * m for _ in range(m)]
    for i in range(m):
        for j in range(i + 1, m):
            ok = (i in X and j in X) or rng.random() < 0.6
            comp_m[i][j] = comp_m[j][i] = ok
    for i in range(m):
        for j in range(m):
            if i != j and comp_m[i][j] and rng.random() < 0.4:
                arc[i][j] = True
    need = [0] * ncell
    for i in X:
        for c in covers[i]:
            need[c] += 1
    vout = [sum(arc[i][j] for j in X) if i in X else rng.randint(0, 2) for i in range(m)]
    vin = [sum(arc[j][i] for j in X) if i in X else rng.randint(0, 2) for i in range(m)]
    comp = [to_bits(comp_m[i]) for i in range(m)]
    outb = [to_bits(arc[i]) for i in range(m)]
    inb = [to_bits([arc[j][i] for j in range(m)]) for i in range(m)]
    return covers, need, comp, outb, inb, vout, vin, tuple(X)


def selftest(trials, mutate=None, seed=7):
    rng = random.Random(seed)
    bad = 0
    sols_total = 0
    for _ in range(trials):
        m = rng.randint(4, 13)
        inst = random_instance(rng, m, rng.randint(3, 6))
        covers, need, comp, outb, inb, vout, vin, X = inst
        for deg in (True, False):
            args = (covers, need, comp, outb, inb, vout, vin) if deg else (covers, need, comp, None, None, None, None)
            want = brute(*args)
            eng = Cover(*args, mutate=mutate)
            _, sols, _ = eng.search()
            got = sorted(tuple(sorted(s)) for s in sols)
            sols_total += len(want)
            if got != want or (deg and X not in want):
                bad += 1
    return bad, sols_total
