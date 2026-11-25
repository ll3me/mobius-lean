"""Check the single-cycle probes, alternating-circuit bound premises and same-pair gate cut."""
from itertools import combinations, permutations

from boolean_sweep import affine_rebuild, live_gates, make_gate, rewrite_windows, xor_gate
from hamiltonian_boards import arcs, cycle_masks
from paired_contraction import Circuit, held_karp, pairings
from paired_matrix_tests import check_all_graphs


def edge_mask(index, edges):
    return sum(1 << index[e] for e in edges)


def subcube_masks(bits):
    masks = [0]
    for bit in bits:
        masks.extend([mask | bit for mask in masks])
    return masks


def internal_probe(m, left, right):
    """Keep the cross edges of a tour with exactly the two designated internal steps."""
    blocks = []
    for side, pair in enumerate((left, right)):
        singletons = [(v,) for v in range(side, 2*m, 2) if v not in pair]
        blocks.append([pair, *singletons])
    tour = [u for block_pair in zip(*blocks) for block in block_pair for u in block]
    return [(u, v) for u, v in zip(tour, tour[1:]+tour[:1]) if u % 2 != v % 2]


def check_internal_probes(m):
    index = {e: i for i, e in enumerate(arcs(2*m))}
    sides = [[(u, v) for u, v in index if u % 2 == v % 2 == side] for side in (0, 1)]
    masks = [subcube_masks(1 << index[e] for e in side) for side in sides]
    # A mask in a single outgoing or incoming star can contribute at most one
    # internal edge to any tour, even if all its switches are on.
    stars = []
    for side, side_masks in zip(sides, masks):
        star_masks = [edge_mask(index, (e for e in side if e[position] == v))
                      for position in (0, 1) for v in range(2*m)]
        stars.append([mask for mask in side_masks if any(mask & star == mask for star in star_masks)])
    tests = [(a, b) for a in masks[0] for b in masks[1] if a in stars[0] or b in stars[1]]
    tours = cycle_masks(2*m)
    total = 0
    for e in sides[0]:
        for f in sides[1]:
            cross = edge_mask(index, internal_probe(m, e, f))
            needed = edge_mask(index, [e, f])
            # Examine independent Hamiltonian masks on the original vertices.
            internal = edge_mask(index, sides[0]+sides[1])
            compatible = [t & internal for t in tours if t & (cross | internal) == t]
            for a, b in tests:
                active = a | b
                assert any(active & t == t for t in compatible) == (active & needed == needed)
            total += len(tests)
    print(f'{2*m} vertices: {total:,} probe graphs, all paired switch answers correct')


def check_saturated_backgrounds(m):
    raw = arcs(2*m)
    index = {e: i for i, e in enumerate(raw)}
    internal = [(u, v) for u, v in raw if u % 2 == v % 2]
    cross = [e for e in raw if e not in internal]
    all_tours = cycle_masks(2*m)
    inside = edge_mask(index, internal)
    alternating = [t for t in all_tours if not t & inside]
    free = subcube_masks(1 << index[e] for e in cross)
    buckets = [edge_mask(index, [(2*i, 2*j), (2*i+1, 2*j+1)]) for i, j in arcs(m)]
    valid = []
    for background in subcube_masks(1 << index[e] for e in internal):
        if all(background & bucket for bucket in buckets) and all(
                any(t & (word | background) == t for t in all_tours)
                == any(t & word == t for t in alternating) for word in free):
            valid.append(background)
    assert set(valid) == {edge_mask(index, (e for e in internal if e[0] % 2 == side))
                          for side in (0, 1)}
    print(f'{2*m} vertices: exactly two saturated backgrounds preserve every alternating answer')


def check_robust_arcs(m):
    """By relabeling within sides and interchanging sides, the marked arc can be (0,0)."""
    cells = [(i, j) for i in range(m) for j in range(m)]
    index = {e: i for i, e in enumerate(cells)}
    matchings = [(p, edge_mask(index, enumerate(p))) for p in permutations(range(m))]
    marked = 1 << index[0, 0]

    def one_cycle(p, q):
        seen = set()
        v = 0
        while v not in seen:
            seen.add(v)
            v = q[p[v]]
        return len(seen) == m

    completions = {mask: [other for q, other in matchings if one_cycle(p, q)]
                   for p, mask in matchings if mask & marked}
    opposite_sets = [edge_mask(index, group) for group in combinations(cells, m-2)]
    count = 0
    for group in combinations(cells[1:], m-2):
        same = edge_mask(index, group)
        valid = next(mask for _, mask in matchings
                     if mask & marked and not mask & same
                     and not any(other & ((mask ^ marked) | same) == other for _, other in matchings))
        for opposite in opposite_sets:
            assert any(not closing & opposite for closing in completions[valid])
            count += 1
    print(f'{m}+{m} alternating vertices: {count:,} maximal pairs of marked sets checked')


def check_cross_matrix_probe(m):
    k = (m-1)//2
    left, right = list(range(1, k+1)), list(range(k+1, m))
    cells = [(i, j) for i in left for j in right]
    index = {e: i for i, e in enumerate(arcs(2*m))}
    parked = [(2*i, 2*i+1) for i in range(m)] + [(0, 2*i+1) for i in left] + [(2*j, 1) for j in right]
    switches = [1 << index[2*i, 2*j+1] for i, j in cells]
    words = subcube_masks(switches)
    # Enumerate alternating tours directly, with the first left vertex fixed.
    tours = []
    for tail in permutations(range(1, m)):
        for other in permutations(range(m)):
            route = [v for i, j in zip((0, *tail), other) for v in (2*i, 2*j+1)]
            tours.append(edge_mask(index, zip(route, route[1:]+route[:1])))
    for (i, j), bit in zip(cells, switches):
        rest = [v for v in range(m) if v not in (i, j)]
        back = [(2*i+1, 2*i), (2*j+1, 2*j)]
        back.extend((2*u+1, 2*v) for u, v in zip(rest, rest[1:]+rest[:1]))
        base = edge_mask(index, parked+back)
        active = sum(switches)
        compatible = [t & active for t in tours if t & (base | active) == t]
        assert compatible == [bit]
        assert all(any(w & t == t for t in compatible) == bool(w & bit) for w in words)
    print(f'{m}+{m} alternating vertices: {len(words)*len(cells):,} three-cycle address tests')


def source_circuit(m, encoding):
    small = Circuit(2*m)
    tour = held_karp(small, 2*m)
    if encoding == 'Held-Karp':
        return small, tour, set()
    if encoding == 'unrestricted correction':
        alternate = small.replay(small, {e: w for e, w in small.inputs.items()
                                         if e[0] % 2 != e[1] % 2})[tour]
        sides = [small.fold('or', (w for (u, v), w in small.inputs.items() if u % 2 == v % 2 == side))
                 for side in (0, 1)]
        correction = small.gate('and', small.gate('and', *sides), tour)
        return small, small.gate('or', alternate, correction), {correction}
    big = Circuit(2*m)
    view = dict(big.inputs)
    a, b = (0, 2), (1, 3)
    x, y = view[a], view[b]
    if encoding == 'cross XOR':
        a, b = (0, 3), (2, 5)
        x, y = view[a], view[b]
        p = xor_gate(big, x, y)
        view[a] = xor_gate(big, p, y)
        ports = set()
    elif encoding == 'mixed XOR':
        p = xor_gate(big, x, y)
        view[a] = xor_gate(big, p, y)
        ports = {p}
    else:
        assert encoding in ('controlled swap', 'cross controlled swap')
        if encoding == 'cross controlled swap':
            a, b = (0, 3), (2, 5)
            x, y = view[a], view[b]
            c = big.inputs[1, 2]
        else:
            c = big.inputs[0, 1]
        def switch(u, v):
            return big.gate('or', big.gate('and', big.neg(c), u), big.gate('and', c, v))
        p, q = switch(x, y), switch(y, x)
        view[a], view[b] = switch(p, q), switch(q, p)
        ports = {p, q}
    return big, small.replay(big, view)[tour], ports


def pure_signals(dag, live, side):
    pure = {w for (u, v), w in dag.inputs.items() if side[u] == side[v]}
    for g in live:
        if all(w in pure for w in dag.nodes[g][1:]):
            pure.add(g)
    return pure.intersection(live)


def cut_graph(dag, root, selected):
    paid, ports, raw = set(), set(), set()
    pending = [root]
    while pending:
        g = pending.pop()
        if g in selected:
            ports.add(g)
        elif dag.nodes[g][0] == 'input':
            raw.add(g)
        elif g >= 2 and g not in paid:
            paid.add(g)
            pending.extend(dag.nodes[g][1:])
    return paid, ports, raw


def check_cut(dag, root, live, small, image, selected, fixed, final, views=None):
    paid, ports, raw = cut_graph(dag, root, selected)
    removed = set(live)-paid
    # The intermediate circuit has no live within-side inputs.
    source_raw = {w for v in live for w in dag.nodes[v][1:] if dag.nodes[w][0] == 'input'}
    hidden = source_raw-raw
    g, a, b = len(removed), len(ports), len(hidden)
    assert all(image[w] < 2 for w in ports | hidden)

    # Replace every selected output at once and replay only the residual DAG.
    rebuilt = {w: image[w] for w in ports | raw | {0, 1}}
    for v in sorted(paid):
        op, *args = dag.nodes[v]
        rebuilt[v] = make_gate(small, op, [rebuilt[w] for w in args])
    assert rebuilt[root] == image[root]
    internal = removed | hidden
    incoming = sum(w not in internal for v in removed for w in dag.nodes[v][1:])
    unary = sum(dag.nodes[v][0] == 'not' for v in removed)
    credit = g+a-b
    assert b <= g and 2*credit >= b+incoming+unary
    assert 3*credit >= g+a+incoming+unary
    if views is not None:
        assert b <= 2*views*a and 2*views*credit >= g
        assert (3*views-1)*credit >= views*g
    assert len(live)-final >= fixed+credit
    return (g, a, b), credit


def check_second_cut(dag, root, pairs, standard, full_size, fixed, m, mixed):
    live = live_gates(dag, root)
    entries = {u for u, _ in pairs}
    forward = {w for (u, v), w in dag.inputs.items() if u in entries and v not in entries}
    known = set(forward)
    for g in live:
        if all(w in known for w in dag.nodes[g][1:]):
            known.add(g)
    selected = known.intersection(live) | mixed
    views = 2 if mixed else 1
    small, image = dag.contract(pairs)
    assert small.size(image[root]) == standard
    count, credit = check_cut(dag, root, live, small, image, selected, m*m+m, standard)
    g, a, b = count
    _, _, remaining = cut_graph(dag, root, selected)
    backward = {w for (u, v), w in dag.inputs.items() if u not in entries and v in entries}
    hidden_backward = len(backward - remaining)
    assert hidden_backward <= m
    k = (m-1)//2
    area = k*(m-1-k)
    assert area*(b-hidden_backward) <= views*m*m*a
    assert views*m*m*g <= (3*views*m*m-2*area)*credit + area*hidden_backward
    assert full_size-standard >= fixed+credit
    return credit


def check_ledger(m, encoding):
    dag, root, encoded = source_circuit(m, encoding)
    live = live_gates(dag, root)
    domains = list(pairings(m)) if m == 3 and not encoded else [[(2*i, 2*i+1) for i in range(m)]]
    largest = largest_all = largest_second = 0
    for pairs in domains:
        entries = {u for u, _ in pairs}
        side = [v in entries for v in range(2*m)]
        pure = pure_signals(dag, live, side)
        cross_controlled = encoding == 'cross controlled swap'
        selected = pure if cross_controlled else (encoded or pure)
        cross_only = Circuit(2*m)
        cross_wires = {e: cross_only.inputs[e] for e in dag.edges if side[e[0]] != side[e[1]]}
        first = dag.replay(cross_only, cross_wires)
        interim = cross_only.size(first[root])
        residual, image = dag.contract(pairs)
        assert all(image[wire] == first[wire] < 2 for wire in selected)
        check_all_graphs(residual, image[root])
        window, wr = rewrite_windows(residual, image[root])
        affine, ar = affine_rebuild(window, wr)
        final = min(residual.size(image[root]), window.size(wr), affine.size(ar))
        fixed = len(dag.edges)-m*(m-1)
        mixed = {first[w] for w in encoded} if cross_controlled else set()
        second_credit = check_second_cut(cross_only, first[root], pairs,
                                         residual.size(image[root]), len(live), fixed, m, mixed)
        first_counts, first_credit = check_cut(dag, root, live, cross_only, first, selected,
                                              2*m*(m-1), interim)
        assert len(live)-final >= fixed+first_credit+second_credit
        views = {'Held-Karp': 1, 'mixed XOR': 1, 'cross XOR': 1,
                 'controlled swap': 2, 'cross controlled swap': 1}.get(encoding)
        counts, credit = check_cut(dag, root, live, residual, image, selected, fixed, final, views)
        assert counts == first_counts and credit == first_credit
        if encoding == 'unrestricted correction':
            assert counts[1:] == (1, 2*m*(m-1))
        all_constants = {g for g in live if image[g] < 2}
        (all_removed, _, _), all_credit = check_cut(
            dag, root, live, residual, image, all_constants, fixed, final)
        assert credit <= all_credit
        kept, frozen_ports, remaining = cut_graph(dag, root, all_constants)
        fixed_wires = frozen_ports | {w for w in remaining if image[w] < 2}
        neutral_uses = []
        for v in kept:
            pinned = [w for w in dag.nodes[v][1:] if w in fixed_wires]
            if pinned:
                assert len(pinned) == 1 and dag.nodes[v][0] in ('and', 'or')
                assert image[pinned[0]] == int(dag.nodes[v][0] == 'and')
                neutral_uses.append(v)
        assert len(live)-final >= all_removed+len(neutral_uses) >= fixed+all_credit
        assert 2*interim >= 6*m*m+m-5
        assert interim-final >= m*m+m
        largest = max(largest, credit)
        largest_all = max(largest_all, all_credit)
        largest_second = max(largest_second, second_credit)
    print(f'{encoding}, {2*m} vertices, {len(domains)} pairings: best certified extra {largest}; '
          f'all-constant cut best extra {largest_all}; second cut best {largest_second}; '
          f'last (g,a,b)={counts}, '
          f'{len(live)} -> {interim} -> {final} gates')


if __name__ == '__main__':
    check_saturated_backgrounds(2)
    check_internal_probes(3)
    for order in (3, 4):
        check_robust_arcs(order)
        check_ledger(order, 'Held-Karp')
    for order in (4, 5, 6):
        check_cross_matrix_probe(order)
    for variant in ('mixed XOR', 'cross XOR', 'controlled swap', 'cross controlled swap',
                    'unrestricted correction'):
        check_ledger(4, variant)
