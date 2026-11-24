"""Sensitivity of a tour edge and actual wire loss under paired restrictions."""
from collections import Counter
from itertools import combinations, permutations
from math import comb

from cycle_cover_queries import original, set_bits, split_cities, tour_count
from hamiltonian_boards import arcs, cycle_masks
from paired_contraction import Circuit, held_karp, lift_graph, pairings, strongly_connected


def sensitive_tour(n, opened):
    """Build a tour whose edge 0->1 stays essential with all specified edges open."""
    # Contract 0->1 to the symbol 1. Succeeding each tail in tails with a
    # vertex outside heads reserves the predecessors needed to block a cover.
    tails = {u for u, _ in opened if u != 0}
    heads = {v for u, v in opened if u == 0}
    both = sorted(tails & heads)
    unused = sorted(set(range(1, n)) - tails - heads)
    assert len(unused) > len(both)
    order = sorted(heads - tails) + sorted(tails - heads)
    for i, vertex in enumerate(both):
        order.extend((unused[i], vertex))
    order.extend(unused[len(both):])
    order.insert(order.index(1), 0)
    return list(zip(order, order[1:] + order[:1]))


def isolating_tour(n, marked):
    """Leave 0->1 decisive for every setting of the same marked arcs."""
    assert (0, 1) not in marked and len(marked) <= n-3
    targets_from_zero = {v for u, v in marked if u == 0}
    forbidden = {}
    for u, v in marked:
        if u != 0:
            # Token 1 represents the path 0->1. Its entering vertex is 0.
            forbidden.setdefault(u, set()).add(1 if v == 0 else v)
    paths = [[u] for u in range(1, n)]
    for tail, heads in sorted(forbidden.items()):
        current = next(path for path in paths if path[-1] == tail)
        blocked = targets_from_zero | heads
        following = next(path for path in paths if path is not current and path[0] not in blocked)
        current.extend(following)
        paths.remove(following)
    order = [u for path in paths for u in path]
    order.insert(order.index(1), 0)
    return list(zip(order, order[1:] + order[:1]))


def check_sensitivity(n):
    edges = arcs(n)
    bits = {edge: 1 << i for i, edge in enumerate(edges)}
    pivot = bits[0, 1]
    other = [e for e in edges if e != (0, 1)]
    tours = {t for t in cycle_masks(n) if t & pivot}
    covers = [sum(bits[u, v] for u, v in enumerate(p))
              for p in permutations(range(n)) if all(u != v for u, v in enumerate(p))]
    count = isolated_count = 0
    for k in range(n-1):
        for marked in combinations(other, k):
            mask = sum(bits[e] for e in marked)
            if k <= n-3:
                isolated = sum(bits[e] for e in isolating_tour(n, marked))
                assert isolated in tours and (isolated & mask) == 0
                maximal_negative = (isolated ^ pivot) | mask
                assert not any(cover & maximal_negative == cover for cover in covers)
                isolated_count += 1
            tour = sum(bits[e] for e in sensitive_tour(n, marked))
            assert tour in tours
            without = (tour | mask) ^ pivot
            assert not any(cover & without == cover for cover in covers)
            count += 1
    cut = sum(bits[1, v] for v in range(2, n))
    assert all(t & cut for t in tours)
    print(f'{n} vertices: {count} open sets checked; {isolated_count} sets admit all pin values '
          'on one completion')


def live_wires(dag, out):
    uses = Counter()
    gates = set()
    todo = [out]
    while todo:
        node = todo.pop()
        op, *children = dag.nodes[node]
        if op == 'input' or node in gates:
            continue
        assert op in ('and', 'or', 'not')
        gates.add(node)
        uses.update(children)
        todo.extend(children)
    return gates, uses


def wire_loss(dag, out, small, image):
    gates, uses = live_wires(dag, out)
    assert len(uses) == len(gates) - 1 + len(dag.inputs) and image[out] >= 2
    fixed = [v for v in dag.inputs.values() if image[v] < 2]
    constants = [g for g in gates if image[g] < 2]
    absorbing = 0
    constant_nots = 0
    eliminated = 0
    for g in gates:
        op, *operands = dag.nodes[g]
        if op == 'not':
            if image[operands[0]] < 2:
                constant_nots += 1
                eliminated += 1
            continue
        left, right = operands
        a, b = image[left] < 2, image[right] < 2
        eliminated += a or b
        absorbing += (a != b) and image[g] < 2
    raw_surplus = sum(uses[v] - 1 for v in fixed)
    gate_surplus = sum(uses[g] - 1 for g in constants)
    assert eliminated == len(fixed) + raw_surplus + gate_surplus + absorbing + constant_nots
    loss = len(gates) - small.size(image[out])
    assert loss >= eliminated
    return len(fixed), raw_surplus, gate_surplus, absorbing, loss


def guarded_inputs(base, out):
    dest = Circuit(base.order)
    guard = dest.fold('or', (w for (u, _), w in dest.inputs.items() if u == 0))
    aliases = {edge: dest.gate('and', w, guard) for edge, w in dest.inputs.items()}
    return dest, base.replay(dest, aliases)[out]


def path_labels(rows):
    """All realizable nonempty (visited set excluding root, endpoint) pairs."""
    labels = set()
    todo = [(0, 0)]
    while todo:
        mask, end = todo.pop()
        for v in set_bits(rows[end] & ~(mask | 1)):
            state = (mask | (1 << v), v)
            if state not in labels:
                labels.add(state)
                todo.append(state)
    return labels


def check_pairings(m):
    n = 2*m
    q = n-1
    base = Circuit(n)
    tour = held_karp(base, n)
    rows = base.fold('and', (base.fold('or', (base.inputs[u, v] for v in range(n) if v != u))
                             for u in range(n)))
    guarded, masked = guarded_inputs(base, tour)
    _, uses = live_wires(guarded, masked)
    assert all(uses[wire] == 1 + (u == 0) for (u, _), wire in guarded.inputs.items())
    if m == 2:
        source = original(n)
        for word in range(1 << len(base.edges)):
            graph = source.graph(word)
            assert guarded.values(graph)[masked] == base.values(graph)[tour]
    best_fixed_reuse = 0
    hk_internal = []
    seen_labels = Counter()
    complete_small = [(1 << m)-1 ^ (1 << i) for i in range(m)]
    count = 0
    for pairs in pairings(m):
        small, image = base.contract(pairs)
        fixed, raw, internal, absorbing, loss = wire_loss(base, rows, small, image)
        assert fixed == 3*m*m-m and raw == internal == absorbing == 0 and loss == fixed
        _, _, internal, _, _ = wire_loss(base, tour, small, image)
        hk_internal.append(internal)
        labels = path_labels(lift_graph(complete_small, pairs))
        assert len(labels) <= q * 2**m + (m-1) * 2**(m-1)
        seen_labels.update(labels)
        live_surplus = sum(max(0, q-mask.bit_count()-1) for mask, _ in labels
                           if mask.bit_count() >= 2)
        total_surplus = q*(q-3)*(2**(q-2)-1)
        assert internal == total_surplus - live_surplus
        small_guarded, guard_image = guarded.contract(pairs)
        _, raw, _, _, _ = wire_loss(guarded, masked, small_guarded, guard_image)
        best_fixed_reuse = max(best_fixed_reuse, raw)
        count += 1
    assert best_fixed_reuse == n-1
    for s in range(1, q+1):
        counts = [frequency for (mask, _), frequency in seen_labels.items() if mask.bit_count() == s]
        # Across all pairings, every such label has the same survival frequency.
        assert len(counts) == s*comb(q, s) and len(set(counts)) == 1
    print(f'{count} pairings on {n} vertices: wire identity checked on three DAGs; '
          f'{n-1} raw inputs used twice in guarded circuit; '
          f'Held-Karp internal surplus {min(hk_internal)}..{max(hk_internal)}')


def check_outer_graph():
    source = original(4)
    outer = split_cities(source)
    inner = original(2)
    count = 0
    for pairs in pairings(2):
        for word in range(4):
            rows = lift_graph(inner.graph(word), pairs)
            mask = sum(1 << i for (u, v), i in source.labels.items() if rows[u] >> v & 1)
            graph = outer.graph(mask)
            assert strongly_connected(graph)
            assert all(row & (1 << (u ^ 1)) for u, row in enumerate(graph))
            assert bool(tour_count(graph)) == bool(tour_count(inner.graph(word)))
            count += 1
    print(f'{count} outer graphs: fixed cover, strongly connected, correct single-cycle bit')


def check_two_rings(r):
    # Left ring 0->1->0. On the right ring local indices 0 and r+1 give
    # always-open crossings in opposite directions with incompatible labels.
    width = r+2
    internal = [2, 1] + [1 << (2+(i+1) % width) for i in range(width)]
    for x in range(1 << r):
        for y in range(1 << r):
            rows = internal.copy()
            forward = (x << 1) | 1
            backward = (y << 1) | (1 << (width-1))
            for i in range(width):
                if forward >> i & 1:
                    rows[0] |= 1 << (2+i)
                if backward >> i & 1:
                    predecessor = 2+(i-1) % width
                    rows[predecessor] |= 1 << 1
            assert strongly_connected(rows)
            assert tour_count(rows) == (x & y).bit_count()
    print(f'two rings, {r} free labels: {4**r} masks, tour counts equal common labels')


if __name__ == '__main__':
    for order in (4, 5, 6):
        check_sensitivity(order)
    for half in (2, 3, 4):
        check_pairings(half)
    check_outer_graph()
    for labels in (2, 3, 4):
        check_two_rings(labels)
