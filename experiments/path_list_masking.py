"""Check a shared monotone circuit whose true gates evade fixed path lists."""
from collections import Counter
from random import Random

from cycle_cover_queries import original
from paired_contraction import Circuit, held_karp, lift_graph, pairings
from paired_fanout import live_wires, path_labels


def tour_edges(order):
    return tuple(zip(order, order[1:] + order[:1]))


def sample(m, count):
    """Find count maximal graphs, with no balanced label common to three."""
    rng = Random(21)
    candidates = list(pairings(m))
    rng.shuffle(candidates)
    q = 2*m-1
    full = [((1 << m)-1) ^ (1 << i) for i in range(m)]
    frequencies = Counter()
    prefixes = set()
    result = []
    for pairs in candidates:
        rows = lift_graph(full, pairs)
        labels = {label for label in path_labels(rows) if q <= 3*label[0].bit_count() <= 2*q}
        if any(frequencies[label] >= 2 for label in labels):
            continue
        shuffled = list(pairs)
        rng.shuffle(shuffled)
        order = tuple(v for pair in shuffled for v in pair)
        root = order.index(0)
        order = order[root:] + order[:root]
        if order[1:3] in prefixes:
            continue
        edges = tour_edges(order)
        assert all(rows[u] & (1 << v) for u, v in edges)
        prefixes.add(order[1:3])
        frequencies.update(labels)
        result.append((rows, edges))
        if len(result) == count:
            break
    assert len(result) == count and max(frequencies.values()) <= 2
    return result


def check_mask(m, count):
    witnesses = sample(m, count)
    plain = Circuit(2*m)
    tour = held_karp(plain, 2*m)
    masked = Circuit(2*m)
    guard = masked.fold('or', (masked.fold('and', (masked.inputs[e] for e in edges))
                               for _, edges in witnesses))
    replacements = {e: masked.gate('or', wire, guard) for e, wire in masked.inputs.items()}
    out = plain.replay(masked, replacements)[tour]

    gates, uses = live_wires(masked, out)
    shared = [g for g in gates if uses[g] >= 2]
    assert shared
    for rows, _ in witnesses:
        value = masked.values(rows)
        assert value[guard] and all(value[g] for g in shared)
    if m == 2:
        source = original(4)
        for word in range(1 << len(source.labels)):
            rows = source.graph(word)
            assert plain.values(rows)[tour] == masked.values(rows)[out]

    exceptions = 0
    total = 0
    full = [((1 << m)-1) ^ (1 << i) for i in range(m)]
    for pairs in pairings(m):
        rows = lift_graph(full, pairs)
        possible = any(all(rows[u] & (1 << v) for u, v in edges) for _, edges in witnesses)
        restricted, image = masked.contract(pairs)
        assert (image[guard] != 0) == possible
        if possible:
            exceptions += 1
        else:
            reference, plain_image = plain.contract(pairs)
            replay = restricted.replay(reference, reference.inputs)
            assert replay[image[out]] == plain_image[tour]
        total += 1
    assert count <= exceptions <= 2*count
    print(f'{2*m} vertices, {count} witnesses: every balanced label hits at most 2; '
          f'all {len(shared)} shared gates true on every witness; '
          f'original residual expression on {total-exceptions}/{total} pairings')


if __name__ == '__main__':
    for half, count in ((2, 3), (3, 5), (4, 7)):
        check_mask(half, count)
