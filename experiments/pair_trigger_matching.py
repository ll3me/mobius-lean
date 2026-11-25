"""Check which shared-gate uses are paid by a single prescribed partner pair."""
from collections import Counter
from fractions import Fraction
from functools import cache
from itertools import permutations
from math import ceil, factorial

from joint_pair_support import pairing_fixing
from negative_gate_loss import path_columns, weights_and_triggers
from oriented_contraction import de_morgan_circuit, propagate_pin_values, zero_pin_values
from pair_certificate import tables
from paired_contraction import Circuit, held_karp, pairings
from signed_tour_sweep import signed_tour_circuit
from staged_contraction import protect_inputs


def partner_pins(dag):
    """Bit i imposes the forced one and all zeros implied by ordered partner pair i."""
    universe = (1 << len(dag.edges)) - 1
    zero, one = [universe, 0], [0, universe]
    for u, v in dag.edges:
        fixed_zero = fixed_one = 0
        for i, (entry, exit_vertex) in enumerate(dag.edges):
            if (u, v) == (entry, exit_vertex):
                fixed_one |= 1 << i
            elif u == entry or v == exit_vertex or (v, u) == (entry, exit_vertex):
                fixed_zero |= 1 << i
        zero.append(fixed_zero)
        one.append(fixed_one)
    return propagate_pin_values(dag, zero, one)


def assignments_avoiding(rows):
    """Permanent of a zero-one matrix. A set bit is an allowed column."""
    @cache
    def count(free):
        if not free:
            return 1
        choices = rows[len(rows) - free.bit_count()] & free
        total = 0
        while choices:
            bit = choices & -choices
            total += count(free ^ bit)
            choices ^= bit
        return total
    return count((1 << len(rows)) - 1)


def undirected_matching_count(neighbors):
    """Enumerate perfect matchings of a simple graph, choosing the next vertex once."""
    @cache
    def count(free):
        if not free:
            return 1
        first = free & -free
        remaining = free ^ first
        choices = neighbors[first.bit_length() - 1] & remaining
        total = 0
        while choices:
            mate = choices & -choices
            total += count(remaining ^ mate)
            choices ^= mate
        return total
    return count((1 << len(neighbors)) - 1)


def avoidance_graph(n, allowed):
    """Each allowed orientation gets a private three-edge path between its two endpoints."""
    neighbors = [0] * (n + 2*len(allowed))
    for i, (a, b) in enumerate(allowed):
        middle = n + 2*i
        for u, v in ((a, middle), (middle, middle+1), (middle+1, b)):
            neighbors[u] |= 1 << v
            neighbors[v] |= 1 << u
    return neighbors


def check_avoidance_graph():
    dag = Circuit(4)
    bits = {e: 1 << i for i, e in enumerate(dag.edges)}
    full_pairings = [sum(bits[e] for e in pairs) for pairs in pairings(2)]
    for mask in range(1 << len(bits)):
        allowed = [e for e in dag.edges if bits[e] & mask]
        expected = sum((mask & pair) == pair for pair in full_pairings)
        assert undirected_matching_count(avoidance_graph(4, allowed)) == expected
    print('4 vertices: simple-graph matching count verified for all 4096 allowed-orientation masks')


def conditional_charge(tokens, pair_bit, prefix, left, right):
    count = factorial(len(left))
    forced = sum(pair_bit[e] for e in prefix)
    certain = total = 0
    for triggers, copies in tokens.items():
        misses = 0
        if not (triggers & forced):
            rows = [sum(1 << j for j, b in enumerate(right)
                        if not (triggers & pair_bit[a, b])) for a in left]
            misses = assignments_avoiding(rows)
        certain += copies * (misses == 0)
        total += copies * (count - misses)
    return certain, Fraction(total, count)


def check_circuit(dag, out, label, varies):
    n = dag.order
    m = n // 2
    size = dag.size(out)
    width = len(dag.edges)
    single_mask = (1 << width) - 1
    single = zero_pin_values(dag)
    partner = partner_pins(dag)
    both = [[a | (b << width) for a, b in zip(left_pins, right_pins)]
            for left_pins, right_pins in zip(single, partner)]
    raw, _, joint = weights_and_triggers(dag, out, varies, both,
                                         lambda mask: (mask & single_mask).bit_count())
    old_tokens, new_tokens, raw_tokens = Counter(), Counter(), Counter()
    for mask, copies in joint.items():
        raw_pins = mask & single_mask
        old = 0
        for i, edge in enumerate(dag.edges):
            if raw_pins & (1 << i):
                old |= partner[0][dag.inputs[edge]]
        new = mask >> width
        assert old & new == old
        old_tokens[old] += copies
        new_tokens[new] += copies
    for wire, weight in raw.items():
        raw_tokens[partner[0][wire] | partner[1][wire]] += weight
    pair_bit = {e: 1 << i for i, e in enumerate(dag.edges)}
    marked = sorted((e for e in dag.edges if raw[dag.inputs[e]] > 0),
                    key=lambda e: (-raw[dag.inputs[e]], e))[:n-2]
    fixed_pairing = pairing_fixing(n, marked)
    entries = {a for a, _ in fixed_pairing}
    exits = {b for _, b in fixed_pairing}
    prefix = {(v, u) for u, v in marked if u in exits and v in entries}
    left = sorted(entries - {a for a, _ in prefix})
    right = sorted(exits - {b for _, b in prefix})
    certain, mean = conditional_charge(new_tokens, pair_bit, prefix, left, right)
    _, old_mean = conditional_charge(old_tokens, pair_bit, prefix, left, right)
    always_raw, mean_raw = conditional_charge(raw_tokens, pair_bit, prefix, left, right)
    fixed_inputs = 3*m*m - m
    assert always_raw >= sum(raw[dag.inputs[e]] for e in marked)
    observed_charges = []
    raw_total = old_total = 0
    paired_best = 0
    for mates in permutations(right):
        pairs = tuple(sorted(prefix | set(zip(left, mates))))
        used = sum(pair_bit[e] for e in pairs)
        paid = sum(copies for triggers, copies in new_tokens.items() if triggers & used)
        small, image = dag.contract(pairs)
        assert all(image[dag.inputs[e]] < 2 for e in marked)
        literal = sum(weight for w, weight in raw.items() if image[w] < 2)
        assert literal >= always_raw
        raw_total += literal
        old_total += sum(copies for triggers, copies in old_tokens.items() if triggers & used)
        actual = size - small.size(image[out])
        assert actual >= fixed_inputs + literal + paid
        observed_charges.append(paid)
        paired_best = max(paired_best, actual)
    assert sum(observed_charges) == len(observed_charges) * mean
    assert raw_total == len(observed_charges) * mean_raw
    assert old_total == len(observed_charges) * old_mean
    assert certain <= min(observed_charges)
    print(f'{label}: {size} gates, {len(observed_charges)} compatible pairings, '
          f'mean raw extras {mean_raw}, certain partner charges {certain}, '
          f'mean shared {old_mean} -> {mean}, '
          f'certified deletions {fixed_inputs + ceil(mean_raw + old_mean)} -> '
          f'{fixed_inputs + ceil(mean_raw + mean)}, best actual deletions {paired_best}')


def two_or_more(dag, inputs):
    some = multiple = 0
    for wire in inputs:
        multiple = dag.gate('or', multiple, dag.gate('and', some, wire))
        some = dag.gate('or', some, wire)
    return multiple


def check_degree_signal(n):
    dag = Circuit(n)
    outgoing = two_or_more(dag, (dag.inputs[0, v] for v in range(1, n)))
    incoming = two_or_more(dag, (dag.inputs[v, 0] for v in range(1, n)))
    g = dag.gate('and', outgoing, incoming)
    zero, one = zero_pin_values(dag)
    assert zero[g] == one[g] == 0
    zero, _ = partner_pins(dag)
    incident = sum(1 << i for i, e in enumerate(dag.edges) if 0 in e)
    assert zero[g] & incident == incident
    count = 0
    for pairs in pairings(n//2):
        _, image = dag.contract(pairs)
        assert image[g] == 0
        count += 1
    ones, cols = path_columns(dag)
    assert 0 < tables(dag, ones, cols)[g] < ones
    print(f'{n}-vertex degree signal: no single zero pin, forced to zero on all {count} pairings')


def check_reciprocal_pairs(n):
    dag = Circuit(n)
    edges = ((0, 1), (2, 3), (4, 5))
    out = dag.fold('and', (dag.gate('or', dag.inputs[a, b], dag.inputs[b, a]) for a, b in edges))
    zero, one = zero_pin_values(dag)
    assert not (zero[out] | one[out]) and dag.size(out) == 5
    counts = Counter()
    for pairs in pairings(n//2):
        small, image = dag.contract(pairs)
        counts[small.size(image[out])] += 1
    m = n // 2
    split = Fraction(m*(m-1)*(m-2), (2*m-1)*(2*m-3)*(2*m-5))
    expected = split * (2 - Fraction(3, m) + Fraction(1, m*(m-1)*(m-2)))
    assert Fraction(sum(k*v for k, v in counts.items()), sum(counts.values())) == expected
    print(f'{n}-vertex reciprocal pairs: {sum(counts.values())} pairings, mean {expected} of 5 gates')


if __name__ == '__main__':
    check_avoidance_graph()
    for order in (4, 6, 8):
        check_degree_signal(order)
    for order in (8, 10):
        check_reciprocal_pairs(order)
    n = 8
    core = Circuit(n)
    source, root = de_morgan_circuit(core, held_karp(core, n))
    guarded, _, mapping = protect_inputs(source)
    signed, signed_root = signed_tour_circuit(6)
    path_inputs = {n: path_columns(source), 6: path_columns(signed)}
    for network, output, label in ((source, root, 'Held–Karp dual'),
                                   (guarded, mapping[root], 'with identity input gates'),
                                   (signed, signed_root, 'six-vertex signed inclusion–exclusion')):
        ones, cols = path_inputs[network.order]
        path_values = tables(network, ones, cols)
        check_circuit(network, output, label, [0 < x < ones for x in path_values])
