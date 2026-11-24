"""Hamiltonicity projections and adaptive joint cycle-cover queries on actual digraphs."""
from dataclasses import dataclass
from functools import lru_cache
from itertools import combinations
from math import factorial
from random import Random

from hamiltonian_boards import BoardFamily, arcs, cycle_masks


FIXED = -1


@dataclass
class Template:
    order: int
    # Absent arcs have no entry. A present entry is FIXED or a source bit index.
    labels: dict

    def graph(self, word):
        rows = [0] * self.order
        for (u, v), label in self.labels.items():
            if label == FIXED or (word >> label) & 1:
                rows[u] |= 1 << v
        return rows


def original(m):
    return Template(m, {e: i for i, e in enumerate(arcs(m))})


def split_cities(inner):
    n = inner.order
    edges = {(2*u, 2*u+1): FIXED for u in range(n)}
    edges.update({(2*u+1, 2*u): FIXED for u in range(n)})
    edges.update({(2*u, 2*v): FIXED for u, v in arcs(n)})
    edges.update({(2*u+1, 2*v): label for (u, v), label in inner.labels.items()})
    return Template(2*n, edges)


def with_hubs(source, k):
    if k < 1:
        raise ValueError('at least one hub is required')
    m = source.order
    # Vertex 0 is the start. Move incoming arcs of 0 to the new end m.
    edges = {(u, m if v == 0 else v): label for (u, v), label in source.labels.items()}
    first_hub = m+k  # between the path instance and the hubs lie k-1 isolated vertices
    size = m+2*k
    edges.update({(u, v): FIXED for u, v in arcs(size) if max(u, v) >= first_hub})
    return Template(size, edges)


def query_bits(inner, request):
    """On the padded graph, None means impossible; otherwise AND these source bits."""
    tails, heads, bits = set(), set(), set()
    for a, b in set(request):
        if not (0 <= a < 2*inner.order and 0 <= b < 2*inner.order):
            raise ValueError('requested vertex outside the outer graph')
        if a % 2 == 0:
            if b == a+1:
                continue
            return None
        if b % 2 or a//2 in tails or b//2 in heads:
            return None
        u, v = a//2, b//2
        tails.add(u)
        heads.add(v)
        if u != v:
            if (u, v) not in inner.labels:
                return None
            label = inner.labels[u, v]
            if label != FIXED:
                bits.add(label)
    return frozenset(bits)


def evaluate(bits, word):
    return bits is not None and all((word >> i) & 1 for i in bits)


def set_bits(mask):
    while mask:
        bit = mask & -mask
        yield bit.bit_length()-1
        mask ^= bit


def cover_index(rows):
    """Generic exact enumeration by the left/right permutation constraints.

    The bitset for an arc indexes all concrete covers containing it. Intersect
    these bitsets to query for a *single* cover containing the whole request.
    """
    n = len(rows)
    columns = [sum(1 << u for u in range(n) if (rows[u] >> v) & 1) for v in range(n)]
    index = {(u, v): 0 for u, v in arcs(n)}
    count = 0
    chosen = []

    def visit(left, right):
        nonlocal count
        if not left:
            for arc in chosen:
                index[arc] |= 1 << count
            count += 1
            return
        options = [(rows[u] & right, u, False) for u in set_bits(left)]
        options.extend((columns[v] & left, v, True) for v in set_bits(right))
        candidates, fixed, column = min(options, key=lambda item: item[0].bit_count())
        for other in set_bits(candidates):
            u, v = (other, fixed) if column else (fixed, other)
            chosen.append((u, v))
            visit(left ^ (1 << u), right ^ (1 << v))
            chosen.pop()

    visit((1 << n)-1, (1 << n)-1)
    return index, count


def tour_count(rows):
    """Independent Hamiltonian path DP, starting at 0 in the actual graph."""
    @lru_cache(None)
    def finish(u, remaining):
        if not remaining:
            return rows[u] & 1
        return sum(finish(v, remaining ^ (1 << v)) for v in set_bits(rows[u] & remaining))
    return finish(0, (1 << len(rows))-2)


def root_on_cycle(rows):
    seen = 0
    frontier = rows[0]
    while frontier:
        if frontier & 1:
            return True
        seen |= frontier
        following = 0
        for v in set_bits(frontier):
            following |= rows[v]
        frontier = following & ~seen
    return False


def check_two_layers(m):
    source = original(m)
    inner = split_cities(source)
    outer = split_cities(inner)
    tests = {arc: query_bits(inner, [arc]) for arc in arcs(outer.order)}
    count = 0
    for word in range(1 << len(source.labels)):
        raw = source.graph(word)
        exact, _ = cover_index(outer.graph(word))
        assert tour_count(outer.graph(word)) == tour_count(raw)
        assert all(bool(exact[e]) == evaluate(f, word) for e, f in tests.items())
        for i, j in arcs(m):
            # Outer crossings representing inner a_j -> a_i and a_i -> b_i.
            first = (4*j+1, 4*i)
            second = (4*i+1, 4*i+2)
            assert exact[first] and exact[second]
            assert bool(exact[first] & exact[second]) == bool(raw[i])
            count += 1
    print(f'Gamma^2 on m={m}: {len(tests)*(1 << len(source.labels))} single-arc and '
          f'{count} joint row-OR answers')


def check_padded(m, k, exhaustive_pairs):
    source = original(m)
    inner = with_hubs(source, k)
    outer = split_cities(inner)
    assert outer.order == 2*m+4*k
    assert sorted(v for v in outer.labels.values() if v != FIXED) == list(range(m*(m-1)))
    edges = arcs(outer.order)
    requests = [()] + [(e,) for e in edges]
    if k >= 2:
        requests.extend((e, e) for e in edges)
    if exhaustive_pairs:
        requests.extend(combinations(edges, 2))
    if k >= 3:
        # Full Cartesian set of compatible directed options is exercised for
        # pairs below. For triples, cover all triples of *potentially usable*
        # b-to-a arcs (including loops in the inner permutation).
        options = [(2*u+1, 2*v) for u in range(inner.order) for v in range(inner.order)
                   if u == v or (u, v) in inner.labels]
        requests.extend(combinations(options, 3))
        rng = Random(401)
        requests.extend(tuple(rng.sample(edges, k)) for _ in range(250))
    formulas = [(req, query_bits(inner, req)) for req in requests]
    # Fix t -> h -> s, with each other hub already using its loop.
    first_hub = m+k
    beyond = [(2*m+1, 2*first_hub), (2*first_hub+1, 0)]
    beyond.extend((2*h+1, 2*h) for h in range(first_hub+1, first_hub+k))
    sources = cycle_masks(m)
    comparisons = 0
    for word in range(1 << len(source.labels)):
        rows = outer.graph(word)
        assert tour_count(rows) == factorial(k)*factorial(k-1)*sum(word & s == s for s in sources)
        index, count = cover_index(rows)
        assert count
        full = (1 << count)-1
        for request, expected in formulas:
            common = full
            for edge in request:
                common &= index[edge]
            assert bool(common) == evaluate(expected, word), (m, k, word, request)
        joint = full
        for edge in beyond:
            joint &= index[edge]
        assert bool(joint) == root_on_cycle(source.graph(word))
        for drop in beyond:
            partial = full
            for edge in beyond:
                if edge != drop:
                    partial &= index[edge]
            assert partial
        comparisons += len(formulas)
    print(f'padded m={m}, k={k}, {outer.order} vertices: {comparisons} common-cover answers, '
          f'width {k+1} reads a cycle through 0')


def check_board_positions():
    # At this size the actual dense board word fits comfortably in memory.
    source = original(2)
    inner = split_cities(source)
    board = BoardFamily(inner.order)
    positions = board.bit_positions()
    at = {e: i for i, e in enumerate(board.edges)}
    live = {label: positions[at[e]] for e, label in inner.labels.items() if label != FIXED}

    def payload(word):
        rows = inner.graph(word)
        mask = sum(1 << i for i, (u, v) in enumerate(board.edges) if (rows[u] >> v) & 1)
        return board.pack(mask)

    base = payload(0)
    for word in range(4):
        expected = bytearray(base)
        for i, pos in live.items():
            if (word >> i) & 1:
                expected[pos // 8] ^= 1 << (pos % 8)
        assert expected == payload(word)
    print(f'{len(board.boards(0))} physical boards: both source bits retain their own position')


if __name__ == '__main__':
    check_two_layers(2)
    check_two_layers(3)
    check_padded(2, 1, False)
    check_padded(2, 2, True)
    check_padded(3, 2, True)
    check_padded(2, 3, True)
    check_board_positions()
