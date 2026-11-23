"""Embed a graph cut in one pair of geometric signing tables.

Input JSON has "edges" (distinct unordered nonnegative vertex pairs) and
"cut_at_least". Each edge emits thirteen unweighted squares. Isolated
vertices do not affect either optimum. With no file, run finite checks.
"""
import argparse
from collections import Counter, deque
from itertools import combinations, product
import json
from pathlib import Path

from one_in_three_geometry import ENDS, Space, SquareSet, corners, syndromes, wire


def compile_cut(edges):
    if not isinstance(edges, (list, tuple)) or any(
        not isinstance(e, (list, tuple)) or len(e) != 2 or e[0] == e[1] or
        any(type(x) is not int or x < 0 for x in e) for e in edges
    ):
        raise ValueError('expected a simple graph given by pairs of distinct nonnegative integers')
    edges = [tuple(sorted(e)) for e in edges]
    if len(set(edges)) != len(edges):
        raise ValueError('parallel edges are not supported')
    degrees = Counter(v for e in edges for v in e)
    space = Space()
    ports = {v: space.port() for v in sorted(degrees)}
    target = SquareSet()
    for u, v in edges:
        target.select(wire(ports[u], ports[v]), ENDS)
    width, rows, project = target.compressed(space.width)
    projected_ports = {v: project(p) for v, p in ports.items()}
    reads = Counter(c for sq in rows for c in corners(sq))
    assert len(rows) == 13 * len(edges)
    for v, p in projected_ports.items():
        assert all(reads[c] == degrees[v] for c in corners(p))
    assert max(reads.values(), default=0) <= max(2, max(degrees.values(), default=0))
    return width, rows, projected_ports


def syndrome_distances(columns):
    """The shortest path to a syndrome is the fewest individual failed rows."""
    moves = set(columns) - {0}
    distance = {0: 0}
    queue = deque([0])
    while queue:
        old = queue.popleft()
        for move in moves:
            new = old ^ move
            if new not in distance:
                distance[new] = distance[old] + 1
                queue.append(new)
    return distance


def check(name, edges, expected):
    width, rows, ports = compile_cut(edges)
    raw, columns, _ = syndromes(rows)
    physical_optimum = syndrome_distances(columns)[raw]
    assert physical_optimum == expected
    target, columns, _ = syndromes(rows + list(ports.values()))
    distances = syndrome_distances(columns[:len(rows)])
    for bits in product((0, 1), repeat=len(ports)):
        rhs = target
        color = dict(zip(ports, bits))
        for i, bit in enumerate(bits, len(rows)):
            if bit:
                rhs ^= columns[i]
        cost = sum(color[a] == color[b] for a, b in edges)
        assert distances[rhs] == cost
    print(f'{name}: {len(rows)} geometric squares, width {width}, exact minimum {physical_optimum}.')


def self_check():
    check('empty graph', [], 0)
    check('one edge', [(0, 1)], 0)
    for n in (3, 4, 5, 6):
        check(f'cycle of length {n}', [(i, (i + 1) % n) for i in range(n)], n % 2)
    check('tetrahedron K4', list(combinations(range(4), 2)), 2)
    check('bipartite cubic K3,3', [(u, v) for u in range(3) for v in range(3, 6)], 0)
    check('two disjoint triangles', [(0,1),(1,2),(2,0),(3,4),(4,5),(5,3)], 2)


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('graph', nargs='?', type=Path)
    args = parser.parse_args()
    if args.graph is None:
        self_check()
    else:
        graph = json.loads(args.graph.read_text())
        width, squares, _ = compile_cut(graph['edges'])
        k = graph['cut_at_least']
        if type(k) is not int or not 0 <= k <= len(graph['edges']):
            raise ValueError('cut_at_least must lie between zero and the number of edges')
        print(json.dumps(dict(width=width, squares=squares, threshold=len(graph['edges']) - k)))
