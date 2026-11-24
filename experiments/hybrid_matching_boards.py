"""Matching as an exact physical boundary relation; finite checks for the hybrid bound."""
from collections import Counter
from itertools import combinations, product

from axis_relations import solve
from common_core_signatures import canonical, station_map
from free_direction_coloring import costs_on_one_world, span_points
from overlap_fibers import Span, cell, ground, read_decoder


def board_network(vertex_count, edges):
    incident = [[] for _ in range(vertex_count)]
    if len(set(edges)) != len(edges) or any(not 0 <= u < v < vertex_count for u, v in edges):
        raise ValueError('expected a simple graph with ordered edge endpoints')
    ports = [1 << (2+i) for i in range(len(edges))]
    for (u, v), port in zip(edges, ports):
        incident[u].append(port)
        incident[v].append(port)
    if any(len(row) != 3 for row in incident):
        raise ValueError('expected three edges at every vertex')
    lines, clear = [], []
    for v, (a, b, c) in enumerate(incident):
        private = 1 << (2+len(ports)+v)
        p, q = a ^ b, c ^ private
        lines.extend([(a, b, p), (c, private, q), (p, q, p ^ q)])
        clear.append(p ^ q)
    assert len({tuple(sorted(row)) for row in lines}) == len(lines)
    assert max(Counter(port for row in lines for port in row).values()) == 2
    return lines, ports, clear


def completions():
    decoder = read_decoder()
    completed = []
    for selected in range(3):
        reference = ground(4*(selected+1)+1)
        equations = Span()
        for i, port in enumerate((4, 8, 12)):
            raw = canonical(1 if selected == i else None)
            for j, site in enumerate(station_map(port)):
                rhs = ((raw >> j) & 1) ^ reference[site]
                equations.add((decoder[site] << 1) | rhs)
        assert 0 not in equations.rows
        solution = 1
        for pivot, row in sorted(equations.rows.items()):
            if (row & solution).bit_count() % 2:
                solution |= 1 << pivot
        coeff = solution >> 1
        completed.append(tuple(bit ^ ((mask & coeff).bit_count() % 2)
                               for bit, mask in zip(reference, decoder)))
    return completed


def check_physical(lines, selected, tables):
    charts, world = [], {}
    for line in lines:
        a, b, _ = line
        basis = (1, 2, a, b)
        coords = span_points(basis)
        charts.append(basis)
        table = tables[next(i for i, p in enumerate(line) if selected[p])]
        for tag, x, y in product(range(2), range(16), range(16)):
            value = table[cell(tag, x, y)]
            assert world.setdefault((tag, coords[x], coords[y]), value) == value
    for port, mark in selected.items():
        coords = span_points((1, 2, port))
        target = canonical(1 if mark else None)
        for tag, x, y in product(range(2), range(8), range(8)):
            assert world[tag, coords[x], coords[y]] == (target >> (tag*64+x*8+y) & 1)
        pins = ((0, 0, 0), (0, 0, port), (0, port, 0), (0, port, port),
                (1, 0, port), (1, port, 0))
        assert tuple(world[key] for key in pins) == (0, 0, 0, 1, 0, 0)
    for d in (1, 2, 3):
        assert world[0, 0, 0] ^ world[0, d, d] ^ world[1, 0, d] ^ world[1, d, 0]
    _, costs = costs_on_one_world([(charts, lambda t, x, y: world[t, x, y])])
    assert costs == [128] * len(charts)


def check_graph(vertex_count, edges, tables):
    lines, ports, clear = board_network(vertex_count, edges)
    clauses = [(row, ()) for row in lines]
    accepted = []
    for mask in range(1 << len(ports)):
        fixed = dict.fromkeys(clear, 0)
        fixed.update((p, (mask >> i) & 1) for i, p in enumerate(ports))
        result = solve(clauses, fixed)
        endpoints = [v for i, e in enumerate(edges) if mask >> i & 1 for v in e]
        assert (result is not None) == (len(endpoints) == len(set(endpoints)))
        if result is not None:
            check_physical(lines, result, tables)
            accepted.append(mask)
    print(f'{len(lines)} boards, {1 << len(ports)} boundary words, {len(accepted)} physical witnesses')
    return accepted


def check_small_cover(edges, accepted):
    # For K4 exhaust every balanced cut and every possible left leg. The largest
    # compatible right leg suffices. Weights are from independent candidate-edge coins.
    legal = set(accepted)
    n = len(edges)
    full = (1 << n) - 1
    neighbors = [sum(1 << j for j, other in enumerate(edges)
                     if i != j and set(edge).intersection(other)) for i, edge in enumerate(edges)]
    weights = Counter()
    for coins in range(1 << n):
        matching = sum(1 << i for i in range(n) if coins >> i & 1 and not (coins & neighbors[i]))
        weights[matching] += 1
    assert weights.keys() == legal
    largest = 0
    for cut in range(1 << n):
        if not n <= 3*cut.bit_count() <= 2*n:
            continue
        left = sorted({word & cut for word in legal})
        right = {word & (full ^ cut) for word in legal}
        for subset in range(1, 1 << len(left)):
            leg = [x for i, x in enumerate(left) if subset >> i & 1]
            compatible = [y for y in right if all((x | y) in legal for x in leg)]
            largest = max(largest, sum(weights[x | y] for x in leg for y in compatible))
    affine = 0
    for mask in range(1, 1 << len(accepted)):
        flats = [x for i, x in enumerate(accepted) if mask >> i & 1]
        if len(flats) == 1 << len(Span(x ^ flats[0] for x in flats)):
            affine = max(affine, sum(weights[x] for x in flats))
    assert max(largest, affine) < 1 << n
    print(f'K4: max balanced rectangle {largest}/{1<<n}; max full-scope affine leaf {affine}/{1<<n}')


if __name__ == '__main__':
    tables = completions()
    k4 = list(combinations(range(4), 2))
    check_small_cover(k4, check_graph(4, k4, tables))
    check_graph(6, [(i, j) for i in range(3) for j in range(3, 6)], tables)
