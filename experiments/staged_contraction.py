"""A conditional gate-loss bound and an input encoding that survives every R0 pairing."""
from fractions import Fraction
from itertools import combinations, product
from math import factorial

from cycle_cover_queries import original
from oriented_contraction import charge_weights, de_morgan_circuit, two_tour_mask
from pair_certificate import all_inputs, tables
from paired_contraction import Circuit, held_karp, incident_guard, pairings
from paired_fanout import live_wires


def prefix_blocks(n, prefix):
    used = {v for pair in prefix for v in pair}
    return tuple(prefix) + tuple((v, v) for v in range(n) if v not in used)


def check_tour_prefixes(n):
    m = n//2
    dag = Circuit(n)
    tours = [frozenset((u, (u+step) % n) for u in range(n)) for step in (1, -1)]
    terms = [dag.fold('and', (dag.inputs[e] for e in sorted(tour))) for tour in tours]
    guard = dag.gate('or', *terms)
    partial = [set() for _ in range(m+1)]
    for pairs in pairings(m):
        for t in range(m+1):
            partial[t].update(combinations(pairs, t))
    counts = []
    for t, prefixes in enumerate(partial):
        kept_tour = kept_guard = 0
        for prefix in prefixes:
            _, image = dag.contract(prefix_blocks(n, prefix))
            for tour, term in zip(tours, terms):
                assert (image[term] != 0) == tour.issuperset(prefix)
            kept_tour += image[terms[0]] != 0
            kept_guard += image[guard] != 0
        prob = Fraction(factorial(n-t-1), factorial(n-1))
        assert Fraction(kept_tour, len(prefixes)) == prob
        assert Fraction(kept_guard, len(prefixes)) == (2*prob if t else 1)
        counts.append((kept_guard, len(prefixes)))
    print(f'{n} vertices: two-tour guard survives prefixes (surviving, total) {counts}')


def check_prefix_ledger(dag, out, label):
    """Fix one pair, then average over all completions of that particular prefix."""
    n = dag.order
    m = n//2
    r = m-1
    s = dag.size(out)
    certified = 0
    positive_deep = 0
    for first in dag.edges:
        blocks = prefix_blocks(n, (first,))
        residual, first_image = dag.contract(blocks)
        root = first_image[out]
        first_loss = s-residual.size(root)
        fresh = sum(1 << i for i, (u, v) in enumerate(residual.edges) if u > 0 and v > 0)
        literal, deep, pins = charge_weights(residual, root, fresh)
        inside = sum(literal[w] for (u, v), w in residual.inputs.items() if u > 0 and v > 0)
        boundary = sum(literal.values())-inside  # There is just one previously merged city.
        mean_literal = Fraction(3*r-1, 4*r-2)*inside + Fraction(boundary, 2)
        fixed = len(residual.inputs)-m*(m-1)
        bound = first_loss+fixed+mean_literal+Fraction(5, 6)*sum(deep.values())
        certified += 4*bound >= 3*s
        positive_deep += sum(deep.values()) > 0

        count = total_loss = total_literal = total_deep = 0
        for rest in pairings(r):
            last = ((0, 0),) + tuple((u+1, v+1) for u, v in rest)
            small, image = residual.contract(last)
            joint = (first,) + tuple((blocks[u+1][0], blocks[v+1][0]) for u, v in rest)
            batch, direct = dag.contract(joint)
            assert batch.replay(small, small.inputs)[direct[out]] == image[root]
            zero = sum(1 << i for i, e in enumerate(residual.edges) if image[residual.inputs[e]] == 0)
            raw_charge = sum(weight for w, weight in literal.items() if image[w] < 2)
            deep_charge = sum(weight for g, weight in deep.items() if pins[g] & fresh & zero)
            loss = s-small.size(image[root])
            assert loss >= first_loss+fixed+raw_charge+deep_charge
            total_literal += raw_charge
            total_deep += deep_charge
            total_loss += loss
            count += 1
        assert total_literal == count*mean_literal
        assert 6*total_deep >= 5*count*sum(deep.values())
        assert total_loss >= count*bound
    print(f'{label}: all {len(dag.edges)} first pairs checked, {positive_deep} expose '
          f'internal weight and {certified} certify a quarter by the conditional bound')


def protect_inputs(source):
    n = source.order
    dag = Circuit(n)
    anchor = incident_guard(dag, 0)
    opposite = dag.neg(anchor)
    false_by_head = [dag.gate('and', anchor, opposite)]
    true_by_tail = [dag.gate('or', anchor, opposite)]
    for _ in range(1, n):
        false_by_head.append(dag.gate('and', false_by_head[-1], anchor))
        true_by_tail.append(dag.gate('or', true_by_tail[-1], anchor))
    proxies = {(u, v): dag.gate('and', dag.gate('or', raw, false_by_head[v]), true_by_tail[u])
               for (u, v), raw in dag.inputs.items()}
    return dag, proxies, source.replay(dag, proxies)


def check_decoding(dag, proxies):
    """No proxy equals a tree with an old gate at its root and proxies at its leaves."""
    labels = set(proxies)
    assert len(labels) == len(proxies)
    contains_proxy = [False]*(2+len(dag.edges))
    assert all(w >= len(contains_proxy) for w in labels)
    for w, (op, *children) in enumerate(dag.nodes[len(contains_proxy):], start=len(contains_proxy)):
        if w in labels:
            assert op in ('and', 'or') and any(not contains_proxy[c] for c in children)
        contains_proxy.append(w in labels or any(contains_proxy[c] for c in children))


def check_protection(source, out, label):
    n = source.order
    gates, _ = live_wires(source, out)
    s = len(gates)
    dag, proxies, embedded = protect_inputs(source)
    out_embedded = embedded[out]
    size = dag.size(out_embedded)
    assert size <= s+2*n*(n-1)+8*n
    # Check both truth values of the protected wires on the full input space at n=4.
    graph = original(n)
    words = range(1 << len(dag.edges)) if n == 4 else (0, 1, (1 << len(dag.edges))-1)
    for word in words:
        rows = graph.graph(word)
        values = dag.values(rows)
        assert all(values[proxies[e]] == values[w] for e, w in dag.inputs.items())
        assert values[out_embedded] == source.values(rows)[out]

    sizes = []
    for pairs in pairings(n//2):
        small, image = dag.contract(pairs)
        check_decoding(small, [image[w] for w in proxies.values()])
        old_images = [image[w] for w in embedded]
        live, _ = live_wires(small, old_images[out])
        distinct = {old_images[g] for g in gates}
        assert len(distinct) == s and distinct <= live
        for g in gates:
            op, *args = source.nodes[g]
            children = sorted(old_images[a] for a in args)
            assert small.nodes[old_images[g]] == (op, *children)
        sizes.append(len(live))
    print(f'{label}: {s} distinct original gates survive each of {len(sizes)} pairings; '
          f'{size} gates before, {min(sizes)}..{max(sizes)} after')


def check_cut_replacement():
    dag = Circuit(4)
    x = list(dag.inputs.values())
    frontier = (dag.gate('and', x[0], x[1]), dag.gate('or', x[2], x[3]), dag.neg(x[4]))
    local = dag.gate('and', x[5], dag.neg(x[6]))

    def select(flag, yes, no):
        return dag.gate('or', dag.gate('and', flag, yes), dag.gate('and', dag.neg(flag), no))

    def differs(cut):
        positive = dag.fold('or', (g for g, bit in cut.items() if bit == 0))
        negative = dag.fold('and', (g for g, bit in cut.items() if bit == 1))
        return dag.gate('or', positive, dag.neg(negative))

    def replace(root, cut):
        active, uses = live_wires(dag, root)
        image = list(range(2+len(dag.inputs)))
        removed = 0
        for w, (op, *args) in enumerate(dag.nodes[len(image):root+1], start=len(image)):
            if w in cut:
                image.append(cut[w])
                continue
            children = [image[a] for a in args]
            removed += w in active and any(a < 2 for a in children)
            image.append(dag.neg(children[0]) if op == 'not' else dag.gate(op, *children))
        forced = image[root]
        slots = sum(uses[w] for w in cut)
        assert removed >= slots-int(forced < 2)
        flag = differs(cut)
        rebuilt = select(flag, local, forced)
        extra = 3+int(any(cut.values()))
        assert dag.size(rebuilt) <= len(active)-(slots-len(cut))+dag.size(local)+extra
        return forced, flag, rebuilt

    checked = []
    root_types = set()
    for pattern in product((0, 1), repeat=len(frontier)):
        pins = dict(zip(frontier, pattern))
        some = differs(pins)
        a, b, c = (dag.neg(g) if bit else g for g, bit in pins.items())
        together = dag.gate('or', dag.gate('and', a, c), dag.gate('and', b, c))
        for default in (together, dag.neg(together), dag.gate('or', together, x[7])):
            root = select(some, local, default)
            for width in range(1, len(frontier)+1):
                for subset in combinations(frontier, width):
                    forced, flag, rebuilt = replace(root, {g: pins[g] for g in subset})
                    root_types.add(forced if forced < 2 else 'signal')
                    checked.append((root, flag, rebuilt))
    assert root_types == {0, 1, 'signal'}
    ones, columns = all_inputs(dag)
    truth = tables(dag, ones, columns)
    for root, flag, rebuilt in checked:
        assert truth[flag] & (truth[root] ^ truth[local]) == 0
        assert truth[root] == truth[rebuilt]
    print(f'{len(checked)} cut replacements preserve all {1 << len(dag.edges)} assignments, '
          'including shared consumers and both constant-output cases')


if __name__ == '__main__':
    check_cut_replacement()
    for order in (4, 6, 8):
        check_tour_prefixes(order)
        base = Circuit(order)
        tour = held_karp(base, order)
        dual, dual_out = de_morgan_circuit(base, tour)
        if order == 6:
            check_prefix_ledger(dual, dual_out, 'six-vertex De Morgan circuit')
            masked, masked_out, _ = two_tour_mask(dual, dual_out)
            check_prefix_ledger(masked, masked_out, 'same circuit with two-tour guard')
        if order <= 6:
            check_protection(base, tour, f'{order}-vertex Held-Karp')
        check_protection(dual, dual_out, f'{order}-vertex De Morgan')
