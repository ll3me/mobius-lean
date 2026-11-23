"""Search all binary sign tables implicitly, using exact elimination over F₂.

Each row encodes the four phase entries of a nonzero equal-XOR rectangle.
A dependency of odd cardinality certifies impossibility for *every* sign
table. The search never assumes bilinearity or a monomial ansatz.
"""
from __future__ import annotations

from itertools import product
from random import Random


def constraints(q):
    for direction in range(1, q):
        for x, y in product(range(q), repeat=2):
            if x < x ^ direction and y < y ^ direction:
                yield x, y, direction


def cells(q, rectangle):
    x, y, d = rectangle
    return (q*x+y, q*(x^d)+y, q*x+(y^d), q*(x^d)+(y^d))


def row_mask(q, rectangle):
    return sum(1 << i for i in cells(q, rectangle))


def eliminate(q, rows):
    # Every RHS is 1, so the XOR of RHSs is the parity of the provenance.
    pivots = {}
    bad = []
    for i, rectangle in enumerate(rows):
        row, provenance = row_mask(q, rectangle), 1 << i
        while row:
            pivot = row.bit_length()-1
            if pivot not in pivots:
                pivots[pivot] = (row, provenance)
                break
            other, history = pivots[pivot]
            row ^= other
            provenance ^= history
        if row == 0 and provenance.bit_count() % 2:
            bad.append(provenance)
    if bad:
        witness = min(bad, key=int.bit_count)
        return len(pivots), None, [r for i,r in enumerate(rows) if (witness >> i) & 1]
    table = 0
    for pivot in sorted(pivots):
        row, history = pivots[pivot]
        if ((row & table).bit_count() ^ history.bit_count()) & 1:
            table |= 1 << pivot
    assert all((row_mask(q,r) & table).bit_count() % 2 for r in rows)
    return len(pivots), table, None


def check_obstruction(q, witness):
    residual = 0
    for r in witness:
        assert r in set(constraints(q))
        residual ^= row_mask(q,r)
    return residual == 0 and len(witness) % 2 == 1


def search():
    for q in [2,4,8,16]:
        rows = list(constraints(q))
        rank, table, bad = eliminate(q, rows)
        if table is not None:
            print(f"q={q}: {len(rows)} rectangles, rank {rank}, exactly 2^{q*q-rank} sign tables")
        else:
            assert bad is not None and check_obstruction(q, bad)
            seed = Random(4117)
            for _ in range(40):
                seed.shuffle(rows)
                _, _, other = eliminate(q, rows)
                if len(other) < len(bad):
                    bad = other
            assert check_obstruction(q, bad)
            print(f"q={q}: {len(rows)} rectangles, rank {rank}, inconsistent; {len(bad)}-rectangle certificate")
            print(sorted(bad))
            return sorted(bad)


if __name__ == "__main__":
    search()
