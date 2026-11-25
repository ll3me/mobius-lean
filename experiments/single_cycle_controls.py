"""Check a Hamiltonian INDEX restriction and the forced-arc control on adjacency inputs."""
from collections import Counter
from itertools import permutations

from cycle_cover_queries import cover_index, original, tour_count
from hamiltonian_boards import arcs, cycle_masks
from paired_contraction import lift_graph, pairings, strongly_connected


def directed_cycle(vertices):
    return set(zip(vertices, vertices[1:] + vertices[:1]))


def rows_of(n, edges):
    rows = [0] * n
    for u, v in edges:
        rows[u] |= 1 << v
    return rows


def check_selector(n):
    m = n // 2
    left, right, hub = tuple(range(m)), tuple(range(m, n-1)), n-1
    data = [(u, v) for u in left for v in right]
    edge_bit = {e: 1 << i for i, e in enumerate(arcs(n))}
    data_mask = sum(edge_bit[e] for e in data)
    tours = cycle_masks(n)
    for i, a in enumerate(left):
        for j, b in enumerate(right):
            fixed = directed_cycle(left) | directed_cycle(right) | {
                (hub, left[(i+1) % len(left)]), (a, hub), (hub, b), (right[j-1], hub)}
            rows = rows_of(n, fixed)
            assert strongly_connected(rows) and cover_index(rows)[1] > 0
            allowed = data_mask | sum(edge_bit[e] for e in fixed)
            intersections = {t & data_mask for t in tours if (t & allowed) == t}
            assert intersections == {edge_bit[a, b]}
    # A negative completion for the all-one data mask. The hub is locked in a 2-cycle.
    v = left[0]
    all_one = set(data) | set(permutations(left, 2)) | directed_cycle(right)
    all_one.update(((hub, v), (v, hub), (right[0], v)))
    rows = rows_of(n, all_one)
    assert strongly_connected(rows) and cover_index(rows)[1] > 0 and tour_count(rows) == 0
    print(f'{n}-vertex selector: {len(data)} addresses valid on all {1 << len(data)} masks')


def forced_arcs(rows):
    n = len(rows)
    unique_head = 0
    for v in range(n):
        if sum(bool(row & (1 << v)) for row in rows) == 1:
            unique_head |= 1 << v
    return [row if row.bit_count() == 1 else row & unique_head for row in rows]


def forced_tour(rows):
    forced = forced_arcs(rows)
    if any(row.bit_count() != 1 for row in forced) or len(set(forced)) != len(rows):
        return False
    successor = [row.bit_length() - 1 for row in forced]
    successor[0] = 0
    for _ in range((len(rows)-1).bit_length()):
        successor = [successor[j] for j in successor]
    return all(v == 0 for v in successor)


def check_forced_arcs(m):
    graph = original(m)
    pair_list = list(pairings(m)) if m <= 3 else [tuple((i, i+m) for i in range(m))]
    for mask in range(1 << len(graph.labels)):
        rows = graph.graph(mask)
        k = forced_tour(rows)
        h = tour_count(rows) > 0
        assert not k or h
        if mask.bit_count() <= m:
            assert k == h
        for pairs in pair_list:
            larger = lift_graph(rows, pairs)
            assert forced_arcs(larger) == lift_graph(forced_arcs(rows), pairs)
            assert forced_tour(larger) == k
    print(f'{m} vertices: {len(pair_list) * (1 << len(graph.labels))} forced-arc pairing tests')


def check_unique_covers(m):
    checked = 0
    for perm in permutations(range(m)):
        if any(v == mate for v, mate in enumerate(perm)):
            continue
        arcs_out = set(permutations(range(m), 2))
        arcs_out.update((i, m+i) for i in range(m))
        arcs_out.update((m+i, perm[i]) for i in range(m))
        rows = rows_of(2*m, arcs_out)
        assert strongly_connected(rows) and cover_index(rows)[1] == 1
        assert forced_tour(rows) == (tour_count(rows) > 0)
        checked += 1
    return checked


def check_low_support_slice(n):
    """Square one arc in a tour DNF and recover the HC layer by reducing only that arc."""
    terms = [tuple(i for i in range(n*(n-1)) if tour & (1 << i)) for tour in cycle_masks(n)]
    poly = Counter({(): 1})
    for tour in terms:
        term = tour + ((0,) if 0 in tour else ())
        for monomial, coefficient in list(poly.items()):
            poly[tuple(sorted(monomial + term))] -= coefficient
    poly = {monomial: -coefficient for monomial, coefficient in poly.items()
            if monomial and coefficient}
    repeated = {i for monomial in poly for i in set(monomial) if monomial.count(i) > 1}
    low = {i for monomial in poly if len(set(monomial)) <= n
           for i in set(monomial) if monomial.count(i) > 1}
    assert low == {0}
    layer = Counter()
    for monomial, coefficient in poly.items():
        reduced = tuple(sorted([i for i in monomial if i not in low] + list(set(monomial) & low)))
        if len(reduced) == n:
            layer[reduced] += coefficient
    assert layer == Counter(terms)
    print(f'{n}-vertex HC slice: {len(low)} low-support repeated arc, {len(repeated)} overall')


if __name__ == '__main__':
    for n in (6, 8):
        check_selector(n)
    for m in (2, 3, 4):
        check_forced_arcs(m)
    print(f'{sum(check_unique_covers(m) for m in range(2, 7))} strongly connected unique covers')
    check_low_support_slice(4)
