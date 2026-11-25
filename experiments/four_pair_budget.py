"""Count four paired domains, decode them with a shared core, and audit actual R+ costs."""
from collections import Counter
from itertools import combinations, combinations_with_replacement, permutations, product
from math import comb, factorial

from boolean_sweep import affine_rebuild, live_gates, rewrite_windows
from cycle_cover_queries import cover_index, tour_count
from paired_contraction import Circuit, allowed, held_karp, lift_graph, strongly_connected
from paired_matrix_tests import check_all_graphs


def check_fixed_groups(m):
    small = Circuit(m)
    target = held_karp(small, m)
    big = Circuit(2*m)
    groups = [(2*i, 2*i+1) for i in range(m)]
    decoded = {(i, j): big.fold('or', (big.inputs[u, v] for u in groups[i] for v in groups[j]))
               for i, j in small.edges}
    root = small.replay(big, decoded)[target]
    assert big.size(root) == small.size(target) + 3*m*(m-1)
    for flips in product((0, 1), repeat=m):
        pairs = [group[::-1] if flip else group for group, flip in zip(groups, flips)]
        result, image = big.contract(pairs)
        assert all(image[wire] == result.inputs[edge] for edge, wire in decoded.items())
        assert result.size(image[root]) == small.size(target)
        check_all_graphs(result, image[root])
    print(f'{m} fixed groups: all {2**m} orientations, {big.size(root)} -> {small.size(target)} gates')


def check_longer_paths():
    first, second = tuple(range(4)), tuple(range(4, 8))
    tested = 0
    for left, right in product(permutations(first), permutations(second)):
        for forward, backward in product((0, 1), repeat=2):
            rows = [0]*8
            for path in (left, right):
                for u, v in zip(path, path[1:]):
                    rows[u] |= 1 << v
            rows[left[-1]] |= forward << right[0]
            rows[right[-1]] |= backward << left[0]
            assert tour_count(rows) == (forward & backward)
            tested += 1
    print(f'Two four-vertex paths: {tested} orders and switch settings')


def check_partner_swap(m):
    """Two strong graphs have the same grouped adjacencies and number of covers."""
    j = m//2
    swap = list(range(m))
    swap[0], swap[j] = j, 0
    successor = [(v+1) % m for v in swap]
    hidden = [0]*m
    connector = []
    for root in (0, j):
        cycle = [root]
        while successor[cycle[-1]] != root:
            cycle.append(successor[cycle[-1]])
        members = sum(1 << i for i in cycle)
        for i in cycle:
            hidden[i] = members ^ (1 << i)
        hidden[cycle[-1]] = 1 << root
        connector.append(cycle[1])
    u, v = connector
    hidden[u] |= 1 << v
    hidden[v] |= 1 << u
    visible = [hidden[i] for i in swap]
    visible[0] |= 1 << j
    visible[j] |= 1
    usual = [(2*i, 2*i+1) for i in range(m)]
    other = [(2*i, 2*swap[i]+1) for i in range(m)]
    positive, negative = lift_graph(visible, usual), lift_graph(hidden, other)
    result = []
    for graph in (positive, negative):
        recovered = [0]*m
        for a, b in permutations(range(m), 2):
            if any(graph[x] & (1 << y) for x in usual[a] for y in usual[b]):
                recovered[a] |= 1 << b
        assert recovered == visible and strongly_connected(graph)
        result.append((tour_count(graph), cover_index(graph)[1]))
    assert result[0][0] > 0 and result[1][0] == 0
    assert result[0][1] == result[1][1] >= factorial(j-2)*factorial(m-j-2)
    print(f'{2*m} vertices, one partner swap, (tours, covers): {result}')


def check_free_summary(m):
    """Give the second computation all first-stage quotient signals for free."""
    small = Circuit(m)
    target = held_karp(small, m)
    big = Circuit(2*m)
    pairs = [(2*i, 2*i+1) for i in range(m)]
    decoded = {e: big.fold('or', (big.inputs[u, v] for u in pairs[e[0]] for v in pairs[e[1]]))
               for e in small.edges}
    image = small.replay(big, decoded)
    summaries = set(decoded.values()) | {image[g] for g in live_gates(small, target)}
    # This explicit full-graph control exposes a quotient subcircuit on the standard slice.
    core = image[target]
    matched, free = allowed(pairs)
    required = big.fold('and', (big.inputs[e] for e in sorted(matched)))
    admissible = matched | free
    foreign = big.fold('or', (big.inputs[e] for e in big.edges if e not in admissible))
    inside = big.gate('and', required, big.neg(foreign))
    ordinary = held_karp(big, 2*m)
    root = big.gate('or', big.gate('and', inside, core),
                    big.gate('and', big.neg(inside), ordinary))
    paid, ports, raw = set(), set(), set()
    stack = [root]
    while stack:
        g = stack.pop()
        if g in summaries:
            ports.add(g)
        elif big.nodes[g][0] == 'input':
            raw.add(g)
        elif g >= 2 and g not in paid:
            paid.add(g)
            stack.extend(big.nodes[g][1:])
    assert raw == set(big.inputs.values())

    wiring = {e: 1 for e in matched}
    for i, j in small.edges:
        wiring[2*i, 2*j] = 1
        wiring[2*i+1, 2*j] = small.inputs[i, j]
    filled = big.replay(small, wiring)
    assert all(filled[g] == 1 for g in decoded.values())
    assert all(filled[g] < 2 for g in summaries)
    check_all_graphs(small, filled[root])
    fixed_raw = len(big.edges)-len(small.edges)
    assert len(paid) >= small.size(filled[root])+fixed_raw+len(ports)
    print(f'{2*m} vertices: {len(summaries)} quotient-only gates, {len(ports)} live boundary wires, '
          f'{len(paid)} remaining gates, {fixed_raw} fixed raw inputs, '
          f'{small.size(filled[root])} gates after fixing the complete quotient')

    def quotient(rows):
        return tuple(any(rows[u] & (1 << v) for u in pairs[i] for v in pairs[j])
                     for i, j in small.edges)

    for u, v in big.edges:
        path = [u, v]
        if u//2 != v//2:
            path.extend((u ^ 1, v ^ 1))
        path += [w for w in range(2*m) if w not in path]
        rows = [0]*(2*m)
        for a, b in zip(path, path[1:]+path[:1]):
            rows[a] = 1 << b
        before = quotient(rows)
        assert tour_count(rows) == 1
        rows[u] = 0
        assert quotient(rows) == before and tour_count(rows) == 0


def class_sizes(m):
    quotient, remainder = divmod(m, 3)
    return [quotient + int(i < remainder) for i in range(3)]


def extremal_quartet(m):
    if m < 6:
        raise ValueError('each pair of complementary classes needs two different matchings')
    group = {}
    masks = []
    for mask, width in zip((3, 5, 9), class_sizes(m)):
        for kind in (mask, 15 ^ mask):
            group[kind] = list(range(len(masks), len(masks)+width))
            masks.extend([kind]*width)
    domains = []
    for row in range(4):
        pairs = []
        for kind, exits in group.items():
            if not (kind >> row) & 1:
                continue
            entries = group[15 ^ kind]
            shift = int((kind & -kind) != (1 << row))
            pairs.extend((a, exits[(j+shift) % len(exits)]) for j, a in enumerate(entries))
        domains.append(sorted(pairs))
    return domains, masks


def check_chain_coefficients():
    chains = []
    for order in permutations(range(4)):
        chain = [0]
        for bit in order:
            chain.append(chain[-1] | (1 << bit))
        chains.append(chain)
    for left in range(16):
        weight = comb(4, left.bit_count())
        assert weight*sum(left in chain for chain in chains) == len(chains)
        for right in range(16):
            if left == right or left & right != left:
                continue
            hits = sum(left in chain and right in chain for chain in chains)
            assert 2*weight*comb(4, right.bit_count())*hits <= 4*len(chains)


def check_small_cuts(m):
    vertices = range(2*m)
    cuts = [sum(1 << (u*2*m+v) for u in side for v in vertices if v not in side)
            for side in combinations(vertices, m)]
    # Relabel the first cut. Enumerate the remaining three, up to their order.
    maximum = max((cuts[0] | a | b | c).bit_count()
                  for a, b, c in combinations_with_replacement(cuts, 3))
    assert maximum == (2*m)**2 - 2*sum(c*c for c in class_sizes(m))
    print(f'{2*m} vertices: all balanced cut quartets up to relabeling the first, '
          f'maximum directed cut union {maximum} before removing the partners')


def check_decoder(m):
    domains, masks = extremal_quartet(m)
    allowed_arcs = [allowed(pairs) for pairs in domains]
    free_counts = Counter(e for _, free in allowed_arcs for e in free)
    missing = 2*sum(c*c for c in class_sizes(m))
    assert len(free_counts) == 4*m*m-missing and max(free_counts.values()) <= 2
    dag = Circuit(2*m)
    signs = [[] for _ in domains]
    for r, s in combinations(range(4), 2):
        selector = min(allowed_arcs[r][0] - (allowed_arcs[s][0] | allowed_arcs[s][1]))
        wire = dag.inputs[selector]
        signs[r].append(wire)
        signs[s].append(dag.neg(wire))
    selected = [dag.fold('and', literals) for literals in signs]
    decoded = {}
    masked_uses = 0
    for i, j in permutations(range(m), 2):
        alternatives = []
        for r, pairs in enumerate(domains):
            u, v = pairs[i][1], pairs[j][0]
            wire = dag.inputs[u, v]
            if (masks[u] ^ masks[v]) == 15:
                wire = dag.gate('and', selected[r], wire)
                masked_uses += 1
            alternatives.append(wire)
        decoded[i, j] = dag.fold('or', alternatives)
    assert masked_uses == 2*missing-4*m
    size = len(set().union(*(live_gates(dag, output) for output in decoded.values())))
    bound = 3*m*(m-1) + masked_uses + 14
    assert size <= bound
    for r, pairs in enumerate(domains):
        small, image = dag.contract(pairs)
        assert [image[w] for w in selected] == [int(j == r) for j in range(4)]
        assert all(image[w] == small.inputs[e] for e, w in decoded.items())
    print(f'{2*m} vertices: {len(free_counts)} distinct free arcs, '
          f'{size} shared decoder gates (bound {bound}); all four projections checked')


def check_quarter_average():
    m = 6
    domains, _ = extremal_quartet(m)
    big = Circuit(2*m)
    output = held_karp(big, 2*m)
    live = live_gates(big, output)
    multiplicities = Counter()
    actual = []
    extra_deleted = 0
    for pairs in domains:
        small, image = big.contract(pairs)
        root = image[output]
        reached = set(live_gates(small, root))
        origins = {}
        for g in live:
            if image[g] in reached:
                origins.setdefault(image[g], g)
        assert len(origins) == len(reached)
        multiplicities.update(origins.values())
        windows, wr = rewrite_windows(small, root)
        affine, ar = affine_rebuild(windows, wr)
        residual, last = min(((small, root), (windows, wr), (affine, ar)),
                             key=lambda candidate: candidate[0].size(candidate[1]))
        check_all_graphs(residual, last)
        actual.append(residual.size(last))
        extra_deleted += len(reached)-actual[-1]
    unused = len(live)-len(multiplicities)
    repeated = sum(uses-1 for uses in multiplicities.values())
    assert sum(actual) == len(live)-unused+repeated-extra_deleted
    print(f'Held-Karp {len(live)} gates, R+ residues {actual}, unused {unused}, '
          f'repeated {repeated}, additional R+ deletions {extra_deleted}')


if __name__ == '__main__':
    for size in (2, 3, 4):
        check_fixed_groups(size)
    check_longer_paths()
    for size in (6, 8, 10):
        check_partner_swap(size)
    for size in (3, 4):
        check_free_summary(size)
    check_chain_coefficients()
    for size in (3, 4):
        check_small_cuts(size)
    for size in (6, 7, 8, 11, 20):
        check_decoder(size)
    check_quarter_average()
