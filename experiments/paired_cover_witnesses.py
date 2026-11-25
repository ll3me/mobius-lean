"""Count pairings containing a graph and check Hamiltonicity on two-cover inputs."""
from collections import Counter
from itertools import combinations, permutations

from cycle_cover_queries import cover_index, original, set_bits
from joint_pair_support import small_negative_words
from paired_contraction import allowed, lift_graph, pairings, strongly_connected


def pairing_multiplicity(rows):
    """Count unordered collections of oriented pairs whose entire image contains rows."""
    n = len(rows)
    incoming = [sum(1 << u for u, row in enumerate(rows) if row >> v & 1) for v in range(n)]
    if any(rows[u] & incoming[u] for u in range(n)):
        return 0  # Opposite open arcs would include a forbidden return to the partner.
    side = {}
    answer = 1
    for root in range(n):
        if root in side:
            continue
        side[root] = 0
        component = [root]
        for u in component:
            for v in set_bits(rows[u] | incoming[u]):
                if v not in side:
                    side[v] = 1 - side[u]
                    component.append(v)
                elif side[v] == side[u]:
                    return 0
        orientations = sum(all((rows[u] if side[u] == entry else incoming[u]).bit_count() == 1
                               for u in component) for entry in (0, 1))
        answer *= orientations
        if not answer:
            return 0
    return answer


def check_fibers(m):
    graph = original(m)
    small = [graph.graph(mask) for mask in range(1 << len(graph.labels))]
    counts = Counter(tuple(lift_graph(rows, pairs)) for pairs in pairings(m) for rows in small)
    assert all(pairing_multiplicity(rows) == count for rows, count in counts.items())
    if m == 2:
        big = original(4)
        for mask in range(1 << len(big.labels)):
            rows = tuple(big.graph(mask))
            assert pairing_multiplicity(rows) == counts[rows]
    return dict(sorted(Counter(counts.values()).items()))


def check_four_cycle_components():
    disjoint_cycles = {(4*k+i, 4*k+(i+1) % 4) for k in range(2) for i in range(4)}
    for edges, expected in ((disjoint_cycles, 4), (disjoint_cycles | {(0, 4)}, 1),
                            (disjoint_cycles | {(1, 0)}, 0)):
        rows = [sum(1 << v for u, v in edges if u == i) for i in range(8)]
        compatible = sum(required <= edges <= required | free for required, free in
                         (allowed(pairs) for pairs in pairings(4)))
        assert compatible == pairing_multiplicity(rows) == expected


def cycles(successor):
    lengths = []
    seen = set()
    for u in range(len(successor)):
        if u in seen:
            continue
        v = u
        length = 0
        while v not in seen:
            seen.add(v)
            length += 1
            v = successor[v]
        assert v == u
        lengths.append(length)
    return tuple(sorted(lengths))


def union_rows(sigma, tau):
    assert sorted(sigma) == sorted(tau) == list(range(len(sigma)))
    return [(1 << a) | (1 << b) for a, b in zip(sigma, tau, strict=True)]


def extend_vertex(rows, vertex, extra):
    """Replace one vertex by a forced path, keeping its old label as the entry."""
    result = list(rows) + [0]*extra
    end = vertex
    for new in range(len(rows), len(result)):
        result[end] = 1 << new
        end = new
    result[end] = rows[vertex]
    return result


def six_vertex_family():
    """All loopless 2-in/2-out digraphs on six vertices with exactly two covers."""
    covers = [p for p in permutations(range(6)) if all(u != v for u, v in enumerate(p))]
    for sigma, tau in combinations(covers, 2):
        relative = [sigma.index(v) for v in tau]
        if cycles(relative) == (6,):
            yield union_rows(sigma, tau), (cycles(sigma) == (6,) or cycles(tau) == (6,))


def check_six_vertex_controls():
    four = original(4)
    negatives = small_negative_words(4)
    assert len(negatives) == 144
    assert all(cover_index(four.graph(mask))[1] == 1 for mask in negatives)
    classified = Counter()
    for rows, answer in six_vertex_family():
        assert strongly_connected(rows) and cover_index(rows)[1] == 2
        classified[answer] += 1
    assert classified == {False: 480, True: 4320}
    tau = (2, 3, 4, 5, 0, 1)
    for sigma, expected in [((1, 0, 3, 2, 5, 4), [(2, 2, 2), (3, 3)]),
                            ((1, 2, 3, 4, 5, 0), [(3, 3), (6,)])]:
        rows = union_rows(sigma, tau)
        covers = [p for p in permutations(range(6)) if all(rows[u] >> v & 1 for u, v in enumerate(p))]
        assert strongly_connected(rows) and set(covers) == {sigma, tau}
        assert sorted(cycles(p) for p in covers) == expected
        for _ in range(2):
            rows = lift_graph(rows, tuple((2*i, 2*i+1) for i in range(len(rows))))
            assert strongly_connected(rows) and cover_index(rows)[1] == 2
            assert pairing_multiplicity(rows) == 1


def inner_product_covers(k, x, y):
    """Return two permutations on 4 lanes and 4k layers (numbered cyclically)."""
    p, q = (1, 0, 2, 3), (2, 3, 0, 1)
    layers = 4*k
    sigma, shift = [], []
    for layer in range(layers):
        switch = p if layer % 2 == 0 else q
        enabled = ((x if layer % 2 == 0 else y) >> (layer // 4)) & 1
        for lane in range(4):
            dest = switch[lane] if enabled else lane
            next_layer = (layer+1) % layers
            wrap = int(next_layer == 0)
            sigma.append(4*next_layer + (dest+wrap) % 4)
            shift.append(4*next_layer + (lane+wrap) % 4)
    assert cycles(shift) == (4*layers,)
    return sigma, [sigma[v] for v in shift]


def check_product(k):
    n = 16*k
    edge_columns = [0] * (n*n)
    answers = [0] * (1 << k)
    for x in range(1 << k):
        for y in range(1 << k):
            sigma, tau = inner_product_covers(k, x, y)
            rows = union_rows(sigma, tau)
            assert strongly_connected(rows)
            assert all(row.bit_count() == 2 and not row >> i & 1 for i, row in enumerate(rows))
            assert cover_index(rows)[1] == 2
            assert len(cycles(tau)) >= 2
            yes = cycles(sigma) == (n,)
            assert yes == ((x & y).bit_count() % 2 == 0)
            answers[x] |= yes << y
            assert (len(cycles(sigma)) - len(cycles(tau))) % 2 == 1
            bit = 1 << ((x << k) | y)
            for u, row in enumerate(rows):
                for v in set_bits(row):
                    edge_columns[u*n+v] |= bit
    ones = (1 << (1 << (2*k)))-1
    literals = {0, ones}
    for i in range(2*k):
        literal = sum(1 << w for w in range(1 << (2*k)) if w >> i & 1)
        literals.update((literal, literal ^ ones))
    assert set(edge_columns) <= literals
    assert len(set(answers)) == 1 << k
    for left, right in combinations(answers[1:], 2):
        assert (left & ~right).bit_count() == (right & ~left).bit_count() == (1 << k)//4


if __name__ == '__main__':
    for m in (2, 3):
        print(f'{2*m} vertices: graphs by pairing multiplicity {check_fibers(m)}')
    check_four_cycle_components()
    check_six_vertex_controls()
    for k in (1, 2, 3):
        check_product(k)
    print('144 four-vertex controls, 4800 six-vertex two-cover graphs, both specified lifts, '
          'and 84 even-inner-product graphs checked')
