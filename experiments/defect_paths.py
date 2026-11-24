"""Contract arbitrary directed segments to erase repeated witness edges."""
from collections import Counter
from fractions import Fraction
from itertools import combinations, permutations
from math import comb, factorial, inf

from cycle_cover_queries import original, tour_count
from paired_contraction import Circuit, held_karp


def segments(order, cuts):
    n = len(order)
    paths = []
    for last in cuts:
        j = (last+1) % n
        path = [order[j]]
        while j not in cuts:
            j = (j+1) % n
            path.append(order[j])
        paths.append(tuple(path))
    return tuple(sorted(paths))


def restrict(dag, out, paths):
    small = Circuit(len(paths))
    mapping = {edge: 1 for path in paths for edge in zip(path, path[1:])}
    for i, path in enumerate(paths):
        for j, other in enumerate(paths):
            if i != j:
                mapping[path[-1], other[0]] = small.inputs[i, j]
    return small, dag.replay(small, mapping)[out]


def witness_length(dag, out, rows, counted_edge=None):
    lengths = [inf, 0]
    for u, v in dag.edges:
        cost = int(counted_edge is None or counted_edge == (u, v))
        lengths.append(cost if rows[u] & (1 << v) else inf)
    for op, a, b in dag.nodes[len(lengths):]:
        lengths.append(lengths[a]+lengths[b] if op == 'and' else min(lengths[a], lengths[b]))
    return lengths[out]


def check(n, small_n, repeats):
    assert 2 <= small_n <= n-repeats
    # A proof for a tour repeats exactly the outgoing edges of these designated tails.
    big = Circuit(n)
    out = held_karp(big, n)
    for u in range(repeats):
        guard = big.fold('or', (big.inputs[u, v] for v in range(n) if u != v))
        out = big.gate('and', out, guard)
    counts = Counter()
    clean = Counter()
    for tail in permutations(range(1, n)):
        order = (0,) + tail
        full = [0]*n
        for u, v in zip(order, order[1:]+order[:1]):
            full[u] |= 1 << v
        assert witness_length(big, out, full) == n+repeats
        for chosen in combinations(range(n), small_n):
            cuts = set(chosen)
            paths = segments(order, cuts)
            counts[paths] += 1
            if all(order[j] >= repeats for j in cuts):
                clean[paths] += 1
    assert set(counts.values()) == {factorial(small_n-1)}
    density = Fraction(sum(clean.values()), sum(counts.values()))
    assert density == Fraction(comb(n-repeats, small_n), comb(n, small_n))
    template = original(small_n)
    examples = (min(counts, key=lambda p: clean[p]), max(counts, key=lambda p: clean[p]))
    for paths in examples:
        dag, root = restrict(big, out, paths)
        clean_tours = 0
        for mask in range(1 << len(dag.edges)):
            rows = template.graph(mask)
            length = witness_length(dag, root, rows)
            assert (length != inf) == bool(tour_count(rows))
            if mask.bit_count() == small_n and length == small_n:
                clean_tours += 1
        assert clean_tours >= clean[paths]
    print(f'{n} to {small_n}, {repeats} repeated tails: {len(counts)} path partitions, '
          f'{counts[examples[0]]} tours each, clean density {density}')


def check_all_tails_guard(n):
    dag = Circuit(n)
    original_out = held_karp(dag, n)
    outgoing = [dag.fold('or', (dag.inputs[u, v] for v in range(n) if v != u)) for u in range(n)]
    guarded_out = dag.gate('and', original_out, dag.fold('and', outgoing))
    assert dag.size(guarded_out) <= dag.size(original_out) + n*(n-1)
    for tail in permutations(range(1, n)):
        order = (0,) + tail
        edges = tuple(zip(order, order[1:] + order[:1]))
        rows = [0]*n
        for u, v in edges:
            rows[u] = 1 << v
        for edge in edges:
            assert witness_length(dag, original_out, rows, edge) == 1
            assert witness_length(dag, guarded_out, rows, edge) == 2
    print(f'{n} cities: every tour edge must occur twice with the all-outgoing guard')


if __name__ == '__main__':
    for parameters in ((5, 3, 1), (6, 2, 2), (6, 3, 2), (6, 4, 1)):
        check(*parameters)
    for n in (4, 6):
        check_all_tails_guard(n)
    for n in range(4, 100):
        for d in range((n-2)//2+1):
            k = n-2*d
            assert Fraction(comb(n-d, k), comb(n, k)) == Fraction(comb(2*d, d), comb(n, d))
