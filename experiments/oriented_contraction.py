"""Choose orientations of prescribed pairs in AND/OR circuits with paid NOT."""
from collections import Counter
from fractions import Fraction

from cycle_cover_queries import original, tour_count
from hamiltonian_boards import cycle_masks
from paired_contraction import Circuit, allowed, held_karp, pairings
from paired_fanout import live_wires, wire_loss


def matchings(vertices):
    if not vertices:
        yield ()
        return
    u, *rest = vertices
    for i, v in enumerate(rest):
        for tail in matchings(rest[:i] + rest[i+1:]):
            yield ((u, v),) + tail


def one_pair(dag, a, b):
    """Force a->b. Keep the contracted city in the earlier of the two slots."""
    merged = min(a, b)
    removed = max(a, b)
    remaining = [v for v in range(dag.order) if v != removed]
    slots = {v: i for i, v in enumerate(remaining)}
    slots[removed] = slots[merged]
    dest = Circuit(dag.order-1)
    mapping = {(a, b): 1}
    for u, v in dag.edges:
        if u != a and v != b and slots[u] != slots[v]:
            mapping[u, v] = dest.inputs[slots[u], slots[v]]
    return dest, dag.replay(dest, mapping), slots


def check_cofactors(n):
    tours = cycle_masks(n)
    tour_set = set(tours)
    indices = range(n*(n-1))
    for pivot in indices:
        for other in indices:
            if other == pivot:
                continue
            # Only 'other' is flipped. Both settings of 'pivot' preserve its influence.
            e, f = 1 << pivot, 1 << other
            t = next(t for t in tours if t & f and not t & e)
            assert (t ^ f) not in tour_set and ((t ^ f) | e) not in tour_set
            assert ((t ^ f) | e).bit_count() == n
    dag = Circuit(n)
    pivot = (0, 1)
    for other in dag.edges:
        if other == pivot:
            continue
        a, b = pivot[0], other[1]
        if a == b:
            a, b = other[0], pivot[1]
        if a == b:  # Opposite arcs in the same pair.
            a, b = pivot
        _, image, _ = one_pair(dag, a, b)
        assert image[dag.inputs[pivot]] < 2 and image[dag.inputs[other]] < 2
        assert sum(image[w] < 2 for w in dag.inputs.values()) == 2*(n-1)


def de_morgan_circuit(source, out):
    dest = Circuit(source.order)
    opposite = [1, 0] + [dest.neg(dest.inputs[e]) for e in source.edges]
    for op, a, b in source.nodes[len(opposite):]:
        opposite.append(dest.gate({'and': 'or', 'or': 'and'}[op], opposite[a], opposite[b]))
    return dest, dest.neg(opposite[out])


def check_arc_pairs(m):
    n = 2*m
    pivot = (0, 1)
    counts = Counter()
    total = 0
    for pairs in pairings(m):
        mandatory, free = allowed(pairs)
        available = mandatory | free
        if pivot in available:
            counts.update(available - {pivot})
        total += 1
    for u, v in Circuit(n).edges:
        if (u, v) == pivot:
            continue
        if (u, v) == (1, 0):
            probability = 0
        elif u == 0 or v == 1:
            probability = Fraction(m-2, 4*(2*m-1))
        elif u == 1 or v == 0:
            probability = Fraction(1, 2*(2*m-1))
        else:
            probability = Fraction(m*(m-1), 4*(2*m-1)*(2*m-3))
        assert Fraction(counts[u, v], total) == probability <= Fraction(1, 6)
    print(f'{n} vertices: two-arc probabilities verified on all {total} pairings')


def zero_pin_values(dag):
    """For each wire, record which single zero pins force each Boolean value."""
    all_pins = (1 << len(dag.edges))-1
    zero = [all_pins, 0] + [1 << i for i in range(len(dag.edges))]
    one = [0, all_pins] + [0]*len(dag.edges)
    for op, *args in dag.nodes[len(zero):]:
        a = args[0]
        if op == 'not':
            z, o = one[a], zero[a]
        elif op == 'and':
            b = args[1]
            z, o = zero[a] | zero[b], one[a] & one[b]
        else:
            assert op == 'or'
            b = args[1]
            z, o = zero[a] & zero[b], one[a] | one[b]
        zero.append(z)
        one.append(o)
    return zero, one


def zero_pin_certificates(dag):
    zero, one = zero_pin_values(dag)
    return [z | o for z, o in zip(zero, one)]


def charge_weights(dag, out, eligible_zero_pins):
    gates, uses = live_wires(dag, out)
    weight = {w: uses[w]-1 for w in dag.inputs.values()}
    for g in gates:
        op, *args = dag.nodes[g]
        if op == 'not' and args[0] in weight:
            # One paid negation plus every use beyond the first of its output.
            weight[args[0]] += uses[g]
    pins = zero_pin_certificates(dag)
    deep = {g: max(0, uses[g]-1)+int(dag.nodes[g][0] == 'not')
            for g in gates if (pins[g] & eligible_zero_pins).bit_count() >= 2}
    return weight, deep, pins


def check_signed_charges(dag, out):
    weight, deep, pins = charge_weights(dag, out, (1 << len(dag.edges))-1)
    count = total_charge = total_deep = 0
    m = dag.order//2
    for pairs in pairings(m):
        small, image = dag.contract(pairs)
        fixed, _, _, _, loss = wire_loss(dag, out, small, image)
        charge = sum(wgt for w, wgt in weight.items() if image[w] < 2)
        zero_mask = sum(1 << i for i, e in enumerate(dag.edges) if image[dag.inputs[e]] == 0)
        killed = [g for g in deep if pins[g] & zero_mask]
        assert all(image[g] < 2 for g in killed)
        deep_charge = sum(deep[g] for g in killed)
        assert fixed == 3*m*m-m and loss >= fixed+charge+deep_charge
        total_charge += charge
        total_deep += deep_charge
        count += 1
    assert total_charge*len(weight) == count*(3*m*m-m)*sum(weight.values())
    assert 6*total_deep >= 5*count*sum(deep.values())
    print(f'{dag.order} vertices: literal weight {sum(weight.values())}, internal weight '
          f'{sum(deep.values())}, all {count} oriented pairings checked')
    return sum(deep.values())


def two_tour_mask(source, out):
    dag = Circuit(source.order)
    n = dag.order
    tours = [dag.fold('and', (dag.inputs[i, (i+step) % n] for i in range(n))) for step in (1, -1)]
    guard = dag.gate('or', *tours)
    mapping = {e: dag.gate('or', w, guard) for e, w in dag.inputs.items()}
    root = source.replay(dag, mapping)[out]
    assert dag.size(root) <= source.size(out)+len(dag.edges)+2*n-1
    return dag, root, guard


def orient(dag, out, pairs):
    start, start_out = dag, out
    locations = list(range(dag.order))
    chosen = []
    readers = Counter()
    for u, v in pairs:
        k = dag.order
        i, j = locations[u], locations[v]
        pivot = dag.inputs[i, j]
        live, _ = live_wires(dag, out)
        reader = next(g for g in sorted(live) if pivot in dag.nodes[g][1:])
        op = dag.nodes[reader][0]
        readers[op] += 1
        value = int(op != 'and')
        first = Circuit(k)
        mapping = dict(first.inputs)
        mapping[i, j] = value
        first_image = dag.replay(first, mapping)
        assert first_image[reader] < 2
        assert dag.size(out)-first.size(first_image[out]) >= 2
        _, first_uses = live_wires(first, first_image[out])
        assert all(first_uses[w] > 0 for e, w in first.inputs.items() if e != (i, j))

        a, b = (i, j) if value else (j, i)
        small, image, slots = one_pair(dag, a, b)
        assert dag.size(out)-small.size(image[out]) >= 2*k-1
        chosen.append((u, v) if value else (v, u))
        locations = [slots[x] for x in locations]
        dag, out = small, image[out]

    batch, image = start.contract(chosen)
    # Compare expressions in the same hash-consed DAG, including NOT nodes.
    assert batch.replay(dag, dag.inputs)[image[start_out]] == out
    assert start.size(start_out)-dag.size(out) >= 3*len(pairs)**2
    return readers


def check_orientations(m):
    n = 2*m
    base = Circuit(n)
    tour = held_karp(base, n)
    dual, dual_out = de_morgan_circuit(base, tour)
    guarded = Circuit(n)
    rows = guarded.fold('and', (guarded.fold('or', (guarded.inputs[u, v] for v in range(n) if u != v))
                                for u in range(n)))
    masked = guarded.gate('and', rows, base.replay(guarded, guarded.inputs)[tour])
    source = original(n)
    tour_mask = cycle_masks(n)[0]
    short_cover = sum(1 << source.labels[u, u ^ 1] for u in range(n))
    for word in (0, tour_mask, tour_mask & (tour_mask-1), short_cover, (1 << len(base.edges))-1):
        g = source.graph(word)
        expected = bool(tour_count(g))
        assert all(dag.values(g)[out] == expected for dag, out in
                   ((base, tour), (dual, dual_out), (guarded, masked)))
    if m == 3:
        assert check_signed_charges(base, tour) > 0
        assert check_signed_charges(dual, dual_out) > 0
        left, right = (guarded.inputs[e] for e in ((0, 1), (1, 2)))
        term = guarded.gate('and', left, right)
        tautology = guarded.gate('or', term, guarded.neg(term))
        check_signed_charges(guarded, guarded.gate('and', masked, tautology))
        hidden, hidden_out, guard = two_tour_mask(dual, dual_out)
        assert check_signed_charges(hidden, hidden_out) == 0
        exceptions = 0
        for pairs in pairings(m):
            small, image = hidden.contract(pairs)
            if image[guard] != 0:
                exceptions += 1
                continue
            ref, ref_image = dual.contract(pairs)
            assert small.replay(ref, ref.inputs)[image[hidden_out]] == ref_image[dual_out]
        assert exceptions == 4
        print(f'{n} vertices: only {exceptions} pairings keep the two-tour guard')
        for word in (0, tour_mask, short_cover, (1 << len(base.edges))-1):
            graph = source.graph(word)
            assert hidden.values(graph)[hidden_out] == base.values(graph)[tour]
    kinds = Counter()
    cases = 0
    for pairs in matchings(list(range(n))):
        for dag, out in ((base, tour), (dual, dual_out), (guarded, masked)):
            kinds.update(orient(dag, out, pairs))
        cases += 1
    assert set(kinds) == {'and', 'or', 'not'}
    print(f'{n} to {m}: {cases} unordered matchings on three DAGs, '
          f'all orientations verified against one-shot R0; live reader types {sorted(kinds)}')


if __name__ == '__main__':
    for order in range(4, 9):
        check_cofactors(order)
    for half in (2, 3, 4):
        check_arc_pairs(half)
    for half in (3, 4):
        check_orientations(half)
