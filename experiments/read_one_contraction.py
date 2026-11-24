"""Typed products, completion families and actual R0 loss for read-1 witnesses."""
from collections import Counter, defaultdict
from fractions import Fraction
from itertools import combinations
from math import comb, factorial

from hamiltonian_boards import cycle_masks
from paired_contraction import Circuit, held_karp, pairings
from paired_fanout import live_wires


def type_probability(m, k, overlap):
    """Randomly choose entries, then a bijection from entries to exits."""
    n = 2*m
    one_side = k-overlap
    outside = n-2*k+overlap
    probability = Fraction(0)
    for both in range(overlap+1):
        for only_tail in range(one_side+1):
            only_head = k-2*both-only_tail
            neither = m-both-only_tail-only_head
            if not (0 <= only_head <= one_side and 0 <= neither <= outside):
                continue
            choices = (comb(overlap, both)*comb(one_side, only_tail)
                       *comb(one_side, only_head)*comb(outside, neither))
            probability += Fraction(choices, comb(n, m)*comb(m, both+only_tail))
    return probability


def check_types(m, exhaustive=False):
    n = 2*m
    all_pairs = list(pairings(m)) if exhaustive else []
    for k in range(1, n):
        r = min(k, n-k)
        probes = min((r+1)//2, n//8)
        for overlap in range(max(0, 2*k-n), k+1):
            p = type_probability(m, k, overlap)
            assert p <= Fraction(2, 3)**probes
            if exhaustive:
                tails = set(range(k))
                heads = set(range(overlap)) | set(range(k, 2*k-overlap))
                live = sum(all((a in tails) == (b in heads) for a, b in pairs)
                           for pairs in all_pairs)
                assert p == Fraction(live, len(all_pairs))


def fixed_pool(n):
    """Cover the directed shifts +1 and +2 by at most five oriented pairings."""
    pool = []
    for step in (1, 2):
        colors = [[], [], []]
        unseen = set(range(n))
        while unseen:
            v = min(unseen)
            cycle = []
            while v in unseen:
                unseen.remove(v)
                cycle.append(v)
                v = (v+step) % n
            for i, u in enumerate(cycle):
                j = (i+1) % len(cycle)
                color = 2 if j == 0 and len(cycle) % 2 else i % 2
                colors[color].append((u, cycle[j]))
        for edges in colors:
            if edges:
                used = [v for e in edges for v in e]
                assert len(used) == len(set(used))
                rest = sorted(set(range(n))-set(used))
                pool.append(tuple(sorted(edges + list(zip(rest[::2], rest[1::2])))))
    assert len(pool) <= 5
    combined = {e for pairs in pool for e in pairs}
    assert all((i, (i+j) % n) in combined for i in range(n) for j in (1, 2))
    return pool


def check_fixed_pool(n):
    pool = fixed_pool(n)
    for k in range(1, n):
        masks = [sum(1 << x for x in subset) for subset in combinations(range(n), k)]
        for u in masks:
            for v in masks:
                assert any(any((u >> a & 1) != (v >> b & 1) for a, b in pairs) for pairs in pool)
    print(f'{n} vertices: {len(pool)} fixed pairings separate all nontrivial types')


def multiply(left, right):
    assert all(a & b == 0 for a in left for b in right)
    return {a | b for a in left for b in right}


def formal_support(dag, out):
    """Only used on homogeneous circuits for which every product is multilinear."""
    gates, _ = live_wires(dag, out)
    table = {node: {1 << i} for i, node in enumerate(dag.inputs.values())}
    types = {wire: (1 << u, 1 << v) for (u, v), wire in dag.inputs.items()}
    for g in sorted(gates):
        op, a, b = dag.nodes[g]
        at, ah = types[a]
        bt, bh = types[b]
        if op == 'and':
            assert (at & bt) == 0 and (ah & bh) == 0
            types[g] = at | bt, ah | bh
            table[g] = multiply(table[a], table[b])
        else:
            assert op == 'or' and types[a] == types[b]
            types[g] = types[a]
            table[g] = table[a] | table[b]
    return gates, types, table


def upper_band(dag, out, radius):
    gates, types, table = formal_support(dag, out)
    n = dag.order
    assert table[out] == set(cycle_masks(n))
    high = {g for g in gates if types[g][0].bit_count() > n-radius}
    middle = {g for g in gates-high if types[g][0].bit_count() >= radius}
    low = gates-high-middle
    extensions, unions, entries = set(), set(), set()
    contexts = defaultdict(set)
    contexts[out].add(0)
    high_uses = Counter()
    for g in sorted(high, reverse=True):
        op, a, b = dag.nodes[g]
        high_uses.update(v for v in (a, b) if v in high)
        if op == 'or':
            assert a in high and b in high
            unions.add(g)
            contexts[a].update(contexts[g])
            contexts[b].update(contexts[g])
        elif a in high or b in high:
            assert (a in high) != (b in high)
            h, other = (a, b) if a in high else (b, a)
            extensions.add(g)
            contexts[h].update(multiply(contexts[g], table[other]))
        else:
            entries.add(g)
            if 3*radius <= n:
                assert a in middle or b in middle
    excess = sum(high_uses[g]-1 for g in high if g != out)
    assert excess == len(unions)-len(entries)+1
    groups = defaultdict(list)
    for g in sorted(entries):
        tail, head = types[g]
        missing = n-tail.bit_count()
        assert len(contexts[g]) <= factorial(missing)
        for mask in contexts[g]:
            edges = [e for i, e in enumerate(dag.edges) if mask >> i & 1]
            assert len(edges) == missing
            assert {u for u, _ in edges} == {u for u in range(n) if not tail >> u & 1}
            assert {v for _, v in edges} == {v for v in range(n) if not head >> v & 1}
        groups[frozenset(contexts[g])].append(g)
    return low, middle, entries, extensions, unions, excess, groups


def regroup(dag, data):
    low, middle, entries, _, _, _, groups = data
    dest = Circuit(dag.order)
    image = {wire: dest.inputs[e] for e, wire in dag.inputs.items()}
    for g in sorted(low | middle | entries):
        op, a, b = dag.nodes[g]
        image[g] = dest.gate(op, image[a], image[b])
    pieces = []
    for contexts, entry_gates in groups.items():
        value = dest.fold('or', (image[g] for g in entry_gates))
        terms = (dest.fold('and', (dest.inputs[e] for i, e in enumerate(dest.edges) if mask >> i & 1))
                 for mask in sorted(contexts))
        pieces.append(dest.gate('and', value, dest.fold('or', terms)))
    return dest, dest.fold('or', pieces)


def check_band(dag, out, radius):
    data = upper_band(dag, out, radius)
    low, middle, entries, extensions, unions, excess, groups = data
    new, new_out = regroup(dag, data)
    _, _, table = formal_support(new, new_out)
    assert table[new_out] == set(cycle_masks(dag.order))
    # All low/middle/entry producers may be kept. Only the part above the entries is replaced.
    allowance = len(entries)-1 + len(groups)*(1+radius*factorial(radius))
    assert new.size(new_out) <= len(low | middle | entries) + allowance
    for pairs in pairings(dag.order//2):
        small, image = dag.contract(pairs)
        live_entries = sum(image[g] != 0 for g in entries)
        live_middle = sum(image[g] != 0 for g in middle)
        two = sum(all(image[v] != 0 for v in dag.nodes[g][1:]) for g in unions)
        assert two <= live_entries-1+excess
        assert small.size(image[out]) <= len(low)+live_middle+2*live_entries+len(extensions)+excess
    return len(entries), len(groups), len(extensions), excess, new.size(new_out)


def add_repeated_tour(dag, out):
    """Two ways of filling the same pair of missing edges after a shared prefix."""
    n = dag.order
    edges = [dag.inputs[v, (v+1) % n] for v in range(n)]
    prefix = dag.fold('and', edges[:-2])
    a, b = edges[-2:]
    ab = dag.gate('and', dag.gate('and', prefix, a), b)
    ba = dag.gate('and', dag.gate('and', prefix, b), a)
    return dag.gate('or', out, dag.gate('or', ab, ba))


if __name__ == '__main__':
    for half in range(2, 17):
        check_types(half, exhaustive=(half <= 4))
    for n in (4, 6, 8):
        check_fixed_pool(n)
    for n, radius in ((4, 1), (6, 2), (6, 3), (8, 2)):
        dag = Circuit(n)
        tour = held_karp(dag, n)
        print(f'{n} vertices, radius {radius}: entry/group/extension/surplus/rebuilt',
              check_band(dag, tour, radius))
        if n == 6:
            redundant = add_repeated_tour(dag, tour)
            print('extra full-tour terms:', check_band(dag, redundant, radius))
    tours = cycle_masks(4)
    assert len(tours) == 6 and all((a & b).bit_count() <= 1 for a, b in combinations(tours, 2))
    assert all(sum(mask >> i & 1 for mask in tours) == 2 for i in range(12))
    dag = Circuit(4)
    out = held_karp(dag, 4)
    gates, _, _ = formal_support(dag, out)
    assert Counter(dag.nodes[g][0] for g in gates) == {'and': 15, 'or': 5}
    for pairs in pairings(2):
        small, image = dag.contract(pairs)
        assert small.size(image[out]) == 1
    print('4 vertices: 15 AND + 5 OR; 12 pairings, each leaves 1 gate')
