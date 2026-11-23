"""GF(2) feasibility of independent row and column phase tables.

An off-diagonal rectangle imposes a parity equation on two entries from
each table. Exchanging one pair of corners changes which entries belong
to each table and hence supplies a distinct equation.
"""
from __future__ import annotations

from collections import Counter
from itertools import product
from random import Random


def constraints(q):
    for d in range(1, q):
        for x, y in product(range(q), repeat=2):
            # Translating both x and y by d exchanges each pair within its table.
            if x < x ^ d:
                yield x, y, d


def entries(q, r):
    x, y, d = r
    offset = q * q
    return (x*q+y, (x^d)*q+(y^d), offset+x*q+(y^d), offset+(x^d)*q+y)


def solve(q, rows):
    pivots = {}
    best = None
    for i, r in enumerate(rows):
        support = sum(1 << j for j in entries(q, r))
        history = 1 << i
        while support:
            p = support.bit_length()-1
            if p not in pivots:
                pivots[p] = (support, history)
                break
            other, chain = pivots[p]
            support ^= other
            history ^= chain
        if not support and history.bit_count() % 2:
            if best is None or history.bit_count() < best.bit_count():
                best = history
    if best is not None:
        return len(pivots), None, [r for i,r in enumerate(rows) if best >> i & 1]
    table = 0
    for p in sorted(pivots):
        support, history = pivots[p]
        if ((support & table).bit_count() ^ history.bit_count()) & 1:
            table |= 1 << p
    assert all(sum(table >> j & 1 for j in entries(q,r)) % 2 for r in rows)
    return len(pivots), table, None


def verify(q, witness):
    assert len(witness) % 2 == 1
    assert all(0 <= x < q and 0 <= y < q and 0 < d < q for x,y,d in witness)
    counts = Counter(j for r in witness for j in entries(q,r))
    assert all(n % 2 == 0 for n in counts.values())
    return len(counts)


def search():
    for q in [2,4,8,16]:
        rows = list(constraints(q))
        rank, table, best = solve(q, rows)
        if best is None:
            print(f"q={q}: {len(rows)} rows, rank {rank}, exactly 2^{2*q*q-rank} solutions")
            continue
        # Prefer rectangles supported on small sets of row indices and
        # XOR fibers. This brings sparse dependencies to the pivots early.
        rng = Random(1)
        row_order, fiber_order = list(range(q)), list(range(q))
        rng.shuffle(row_order)
        rng.shuffle(fiber_order)
        rng.shuffle(rows)
        def order(rectangle):
            x, y, d = rectangle
            return max(row_order[x], row_order[x^d], fiber_order[x^y], fiber_order[x^y^d])
        rows.sort(key=order)
        _, _, candidate = solve(q, rows)
        best = min(best, candidate, key=len)
        count = verify(q,best)
        print(f"q={q}: {len(rows)} rows, rank {rank}, inconsistent")
        print(f"{len(best)} rectangles, {count} distinct table entries:")
        print(sorted(best))
        return sorted(best)


if __name__ == "__main__":
    search()
