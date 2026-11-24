"""Common paired restrictions and local assignments inside strongly connected non-Hamiltonian covers."""
from collections import defaultdict
from itertools import combinations, product
from math import comb
from random import Random

from cycle_cover_queries import original, tour_count
from hamiltonian_boards import arcs
from paired_contraction import allowed, pairings, strong_with_cover


def rows_to_fix(marked):
    """Outside these rows the marked cells form a partial permutation."""
    rows = defaultdict(list)
    for u, v in marked:
        rows[u].append(v)
    kept = set()
    claimed_heads = set()
    for u, heads in sorted(rows.items()):
        if len(heads) == 1 and heads[0] not in claimed_heads:
            kept.add(u)
            claimed_heads.add(heads[0])
    return set(rows)-kept


def pairing_fixing(n, marked):
    m = n//2
    vertices = set(range(n))
    rows = rows_to_fix(marked)
    cols = rows_to_fix([(v, u) for u, v in marked])
    assert len(rows)+len(cols) <= len(marked)
    chosen = rows if len(rows) <= len(cols) else cols
    assert len(chosen) <= m
    side = chosen | set(sorted(vertices-chosen)[:m-len(chosen)])
    entries = side if len(rows) <= len(cols) else vertices-side
    exits = vertices-entries
    cross = [(v, u) for u, v in marked if u in exits and v in entries]
    remaining_left = entries-{a for a, _ in cross}
    remaining_right = exits-{b for _, b in cross}
    assert len(remaining_left) == len(remaining_right) == m-len(cross)
    pairs = tuple(sorted(cross + list(zip(sorted(remaining_left), sorted(remaining_right)))))
    assert len(pairs) == m and set(marked).isdisjoint(allowed(pairs)[1])
    return pairs


def negative_completion(n, marked, values):
    """Realize all prescribed bits. A leaf and its sole neighbor form a forced 2-cycle."""
    assert n >= 5 and len(marked) <= n-2
    opened = {e for e, bit in zip(marked, values) if bit}
    closed = set(marked)-opened
    incident = {v: {e for e in marked if v in e} for v in range(n)}
    if len(closed) == n-2:
        leaf = max(incident, key=lambda v: len(incident[v]))
        assert len(incident[leaf]) >= 2
    elif len(closed) == n-3:
        leaf = next(v for v, edges in incident.items() if edges & closed and not edges & opened)
    else:
        leaf = min(incident, key=lambda v: len(incident[v]))
        assert len(incident[leaf]) <= 1

    forced = incident[leaf] & opened
    if forced:
        other, = set(next(iter(forced)))-{leaf}
    else:
        other = next(v for v in range(n) if v != leaf and not {(v, leaf), (leaf, v)} & closed)
    graph = [0]*n
    for u, v in arcs(n):
        if (u, v) not in closed and (leaf not in (u, v) or other in (u, v)):
            graph[u] |= 1 << v
    assert all((graph[u] >> v & 1) == bit for (u, v), bit in zip(marked, values))
    return graph


def check_fixing(n):
    m = n//2
    edges = arcs(n)
    pool = list(pairings(m))
    fixed = {e: 0 for e in edges}
    for i, pairing in enumerate(pool):
        _, free = allowed(pairing)
        for e in fixed.keys()-free:
            fixed[e] |= 1 << i
    first, *others = edges
    if n <= 6:
        # Relabel one marked arc to 'first'. All smaller supports are subsets of these.
        for tail in combinations(others, n):
            candidates = fixed[first]
            for edge in tail:
                candidates &= fixed[edge]
            assert candidates != 0
        print(f'{n} vertices: independently checked all {comb(len(others), n)} supports '
              f'of size {n+1} containing a normalized first arc')
    critical = [edge for v in range(1, m+2) for edge in ((0, v), (v, 0))]
    candidates = (1 << len(pool))-1
    for edge in critical:
        candidates &= fixed[edge]
    assert not candidates
    for omit in critical:
        pairing_fixing(n, [e for e in critical if e != omit])
    rng = Random(n)
    for _ in range(200):
        pairing_fixing(n, rng.sample(edges, n+1))
    print(f'{n} vertices: every pairing hits the {n+2}-arc free-coordinate obstruction, '
          'every one-arc deletion admits simultaneous fixing')


def check_negative_completions(n):
    first, *others = arcs(n)
    count = 0
    for rest in combinations(others, n-3):
        marked = (first,)+rest
        for bits in product((0, 1), repeat=n-2):
            graph = negative_completion(n, marked, bits)
            assert strong_with_cover(graph) and not tour_count(graph)
            count += 1
    print(f'{n} vertices: {count} signed local assignments checked after relabeling one arc')


def small_negative_words(m):
    template = original(m)
    words = []
    for w in range(1 << len(template.labels)):
        rows = template.graph(w)
        if strong_with_cover(rows) and not tour_count(rows):
            words.append(w)
    return words


def negative_single_flip(n, edge):
    u, v = edge
    leaf, bridge, *_ = (w for w in range(n) if w not in edge)
    core = [w for w in range(n) if w not in (u, leaf)]
    rows = [0]*n
    for a, b in zip(core, core[1:]+core[:1]):
        rows[a] |= 1 << b
    rows[u] = (1 << leaf) | (1 << bridge)
    rows[leaf] = 1 << u
    rows[bridge] |= 1 << u
    assert rows[u] & (1 << v) == 0
    other = rows.copy()
    other[u] |= 1 << v
    assert all(strong_with_cover(g) and not tour_count(g) for g in (rows, other))
    return rows, other


def check_sharp_signal(n):
    from paired_contraction import Circuit

    m = n//2
    dag = Circuit(n)
    parity = 0
    for v in range(1, m+2):
        for edge in ((0, v), (v, 0)):
            x = dag.inputs[edge]
            both = dag.gate('and', parity, x)
            parity = dag.gate('and', dag.gate('or', parity, x), dag.neg(both))
    examples = {e: negative_single_flip(m, e) for e in arcs(m)}
    support = {(u, v) for u, v in dag.edges if 0 in (u, v) and max(u, v) <= m+1}
    for pairs in pairings(m):
        small, image = dag.contract(pairs)
        edge = next((i, j) for i, (_, b) in enumerate(pairs) for j, (a, _) in enumerate(pairs)
                    if i != j and (b, a) in support)
        low, high = examples[edge]
        assert small.values(low)[image[parity]] != small.values(high)[image[parity]]
    print(f'{n}-vertex parity on {n+2} inputs distinguishes two retained negatives in every pairing')


if __name__ == '__main__':
    for n in (4, 6, 8):
        check_fixing(n)
    for n in (5, 6):
        check_negative_completions(n)
    check_sharp_signal(8)
