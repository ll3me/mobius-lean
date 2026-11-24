"""Simultaneous optima on common-core boards with the three core directions good."""
from collections import Counter, defaultdict
from functools import lru_cache
from itertools import combinations, product

from axis_relations import solve
from free_direction_coloring import bridge, coloring, costs_on_one_world, lines3, span_points
from port_k4 import phase3


def line(a, b):
    assert a and b and a != b
    return tuple(sorted((a, b, a ^ b)))


def equality_lines(a, b, t, f, j):
    d = a ^ b
    removed = line(d, f)
    return [line(x, y) for x, y in bridge(a, b, t)] + [
        row for row in lines3((d, f, j)) if row != removed]


def color_network(n, edges):
    """Each occurrence has its own quotient point. Only equality links join copies."""
    if n < 0 or len(set(edges)) != len(edges) or any(not 0 <= u < v < n for u, v in edges):
        raise ValueError('expected a simple graph with ordered endpoints')
    groups = [[(v, c) for c in range(3)] for v in range(n)]
    for u, v in edges:
        for c in range(3):
            groups.append([(u, c), (v, c), None])  # private slack point

    # Bits zero and one span the common two-dimensional physical core.
    next_bit = 2
    copies = defaultdict(list)
    rows = []
    for group in groups:
        a, b = 1 << next_bit, 2 << next_bit
        next_bit += 2
        rows.append(line(a, b))
        for variable, point in zip(group, (a, b, a ^ b)):
            if variable is not None:
                copies[variable].append(point)
    forced = {}
    for points in copies.values():
        for a, b in zip(points, points[1:]):
            rows.extend(equality_lines(a, b, 1 << next_bit, 2 << next_bit, 4 << next_bit))
            next_bit += 3
            forced[a ^ b] = 1  # selected by the six retained Fano lines alone
    assert len(rows) == len(set(rows)) == n + 57 * len(edges)
    assert all(len(row) == 3 and row[0] ^ row[1] == row[2] for row in rows)
    assert all(k <= 3 for k in Counter(p for row in rows for p in row).values())
    return rows, forced


def check_equality():
    rows = equality_lines(1, 2, 4, 8, 16)
    points = sorted(set().union(*rows))
    counts = Counter()
    for values in product((0, 1), repeat=len(points)):
        marks = dict(zip(points, values))
        if all(sum(marks[p] for p in row) == 1 for row in rows):
            counts[marks[1], marks[2], marks[3]] += 1
    assert counts == {(0, 0, 1): 1, (1, 1, 1): 1}
    print(f'equality link: {len(rows)} actual quotient lines, {2**len(points)} full assignments')


def check_matching():
    # Exhaust both the matching description and all point choices on a small geometry.
    fano = lines3((4, 8, 16))
    checked = 0
    for mask in range(1 << len(fano)):
        rows = [row for i, row in enumerate(fano) if mask >> i & 1]
        incident = defaultdict(list)
        for i, row in enumerate(rows):
            for point in row:
                incident[point].append(i)
        if any(len(v) > 2 for v in incident.values()):
            continue
        singles = {v[0] for v in incident.values() if len(v) == 1}
        pairs = {tuple(v) for v in incident.values() if len(v) == 2}

        @lru_cache(None)
        def can_match(active):
            if not active:
                return True
            i = min(active)
            rest = active - {i}
            return ((i in singles and can_match(rest)) or
                    any((i, j) in pairs and can_match(rest - {j}) for j in rest))

        assert can_match(frozenset(range(len(rows))))
        assert solve([(r, ()) for r in rows]) is not None
        checked += 1
    print(f'matching criterion: {checked} degree-at-most-two Fano subfamilies')


def check_realizations():
    """Complete a subcubic overlap graph by private ports to one boundary vertex."""
    total = realized = 0
    for n in range(1, 6):
        possible = list(combinations(range(n), 2))
        for mask in range(1 << len(possible)):
            edges = [edge for i, edge in enumerate(possible) if mask >> i & 1]
            degrees = Counter(i for edge in edges for i in edge)
            if any(d > 3 for d in degrees.values()):
                continue
            for v in range(n):
                edges.extend([(v, n)] * (3-degrees[v]))
            stars = [sum(1 << e for e, ends in enumerate(edges) if v in ends) for v in range(n)]
            # The star of the boundary is already the xor of the other stars.
            cuts, basis = {0}, {}
            for row in stars:
                cuts |= {x ^ row for x in cuts}
                v = row
                for pivot in sorted(basis, reverse=True):
                    if v >> pivot & 1:
                        v ^= basis[pivot]
                if v:
                    basis[v.bit_length()-1] = v
            labels = []
            for i in range(len(edges)):
                v = 1 << i
                for pivot in sorted(basis, reverse=True):
                    if v >> pivot & 1:
                        v ^= basis[pivot]
                labels.append(v)
            faithful = 0 not in labels and len(set(labels)) == len(labels)
            assert faithful == all(cut.bit_count() >= 3 for cut in cuts if cut)
            if faithful:
                rows = [tuple(labels[e] for e in range(len(edges)) if star >> e & 1) for star in stars]
                assert all(a ^ b == c for a, b, c in rows)
                assert len({frozenset(row) for row in rows}) == len(rows)
                realized += 1
            total += 1
    print(f'cographic realization: {realized} faithful placements out of {total} incidence systems')


def check_face_tables():
    a, b, c = 4, 8, 16
    lines = [line(a, b), line(b, c), line(c, a)]
    clauses = [(row, ()) for row in lines]
    assert solve(clauses, {a: 1, b: 1}) is None
    marks = solve(clauses, {a: 1, b: 0})
    assert marks is not None
    charts = [(1, 2, p, q) for p, q, _ in lines]

    def phase_coordinate(x):
        # Shear sends the prescribed bad direction a+3 to the pure direction a.
        u = (x & 3) ^ (3 if x & a else 0)
        p = x & ~3
        return u | (4 if p and not marks[p] else 0)

    def base(x, y):
        return phase3(phase_coordinate(x), phase_coordinate(y))

    # Prescribe all tagged entries on two independent quotient faces. The
    # shared core correction is nonzero and the two face corrections differ.
    boundary = {}
    def core_delta(tag, x, y):
        return int((x & 3) == 2) ^ tag
    for p in (a, b):
        face = span_points((1, 2, p))
        for tag, x, y in product(range(2), face, face):
            sx, sy = int(bool(x & p)), int(bool(y & p))
            local = sx * (sy ^ tag) if p == a else int((x & 3) == 1 and sx)
            bit = base(x, y) ^ core_delta(tag, x, y) ^ local
            assert boundary.setdefault((tag, x, y), bit) == bit

    def patched(tag, x, y):
        result = base(x, y) ^ core_delta(tag, x, y)
        for p in (a, b):
            xx, yy = x & (3 | p), y & (3 | p)
            result ^= boundary[tag, xx, yy] ^ base(xx, yy) ^ core_delta(tag, xx, yy)
        return result

    assert all(patched(*key) == value for key, value in boundary.items())
    _, costs = costs_on_one_world([(charts, patched)])
    assert costs == [128] * len(lines)
    print(f'two prescribed independent faces: {len(boundary)} distinct tagged cells extend')


def check_graph(n, edges, physical=False):
    rows, forced = color_network(n, edges)
    result = solve([(row, ()) for row in rows], forced)
    assert (result is not None) == (coloring(n, edges) is not None)
    if not physical or result is None:
        return
    charts = [(1, 2, a, b) for a, b, _ in rows]

    def image(x):
        p = x & ~3
        return (x & 3) | (4 if p and not result[p] else 0)

    def table(tag, x, y):
        return phase3(image(x), image(y))

    for direction in (1, 2, 3):
        assert table(0, 0, 0) ^ table(0, direction, direction) ^ (
            table(1, 0, direction) ^ table(1, direction, 0))
    _, costs = costs_on_one_world([(charts, table)])
    assert costs == [128] * len(rows)
    print(f'{len(rows)} full boards: three core squares good and each board has 128 failures')


if __name__ == '__main__':
    check_equality()
    check_matching()
    check_realizations()
    check_face_tables()
    edges = list(combinations(range(4), 2))
    for mask in range(1 << len(edges)):
        check_graph(4, [edge for i, edge in enumerate(edges) if mask >> i & 1], mask == 31)
    print('all 64 labelled four-vertex graphs agree with direct coloring')
