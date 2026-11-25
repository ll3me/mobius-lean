"""Audit the saved internal uses on a prescribed balanced cut and two-step zero certificates."""
from dataclasses import dataclass
from fractions import Fraction
from itertools import combinations, permutations, product

from absorbing_readers import ReaderProfile, masked_circuit
from cycle_cover_queries import cover_index, original, tour_count
from oriented_contraction import de_morgan_circuit, propagate_pin_values
from pair_trigger_matching import assignments_avoiding
from paired_contraction import Circuit, allowed, held_karp, pairings, strongly_connected
from single_cycle_controls import rows_of
from staged_contraction import protect_inputs


@dataclass(frozen=True)
class Unit:
    source: int
    # Each source uses the same reserved reader for all its extra positions.
    # A paid internal NOT instead requires only the gate itself to stay live.
    required: tuple


def units_certified_by_cut(profile, side):
    dag = profile.dag
    zero = [1, 0] + [int((a in side) == (b in side)) for a, b in dag.edges]
    one = [0, 1] + [0]*len(dag.edges)
    zero, one = propagate_pin_values(dag, zero, one)
    inputs = set(dag.inputs.values())
    units = []
    for g in sorted(profile.gates):
        op, *args = dag.nodes[g]
        if op == 'not' and args[0] in inputs:
            continue
        constant = zero[g] or one[g]
        if op == 'not' and constant:
            units.append(Unit(g, (g,)))
        readers = profile.reads[g]
        for reader in readers[1:]:
            node = dag.nodes[reader]
            absorbed = False
            if node[0] != 'not':
                sibling = node[2] if node[1] == g else node[1]
                absorbed = zero[sibling] if node[0] == 'and' else one[sibling]
            if constant or absorbed:
                units.append(Unit(g, (readers[0], reader)))
    return units


def check_joint_ledger(dag, out, name):
    profile = ReaderProfile(dag, out)
    m = dag.order // 2
    vertices = set(range(dag.order))
    u = 3*m*m - m
    beta = Fraction(1, 2*m)
    rows = []
    for tail in combinations(range(1, dag.order), m-1):
        side = {0, *tail}
        units = units_certified_by_cut(profile, side)
        trials = lost_units = total_loss = 0
        for entries in (side, vertices-side):
            left = sorted(entries)
            for right in permutations(sorted(vertices-entries)):
                pairs = list(zip(left, right))
                matching, free = allowed(pairs)
                fixed = set(dag.edges) - free
                small, image = dag.contract(pairs)
                loss = len(profile.gates) - small.size(image[out])
                fees = sum(profile.fees[e] for e in fixed)
                for other in permutations(right):
                    if any(b == c for b, c in zip(right, other)):
                        continue
                    zero_matching = set(zip(left, other))
                    heads = {h for e, h in profile.head.items()
                             if e in (matching if dag.nodes[h][0] == 'or' else zero_matching)}
                    active, _ = profile.reachable_after_cut(heads)
                    pruned = profile.gates - active - heads
                    lost_raw = sum(e in fixed and g in pruned for e, g in profile.repeated_tickets)
                    paid = 0
                    for unit in units:
                        if all(h in active for h in unit.required):
                            assert unit.source in active or unit.source in heads
                            paid += 1
                        else:
                            assert any(profile.first_head[h] in heads for h in unit.required)
                    assert loss >= u + fees + len(heads) + len(pruned) - lost_raw + paid
                    trials += 1
                    lost_units += len(units) - paid
                    total_loss += loss
        k = len(units)
        assert lost_units <= trials * 2*beta*k
        bound = u + m + (1-(m+1)*beta)*profile.total_fee + (1-2*beta)*k
        assert total_loss >= trials*bound
        rows.append((k, lost_units))
    counts = [k for k, _ in rows]
    print(f'{name}: {len(rows)} unordered balanced cuts, {min(counts)}..{max(counts)} prepaid '
          f'internal positions, {sum(lost for _, lost in rows)} vetoes across completions')
    return rows


def check_full_petals(m):
    n = 2*m
    vertices = set(range(n))
    failures = count = 0
    for pairs in pairings(m):
        matching, free = allowed(pairs)
        allowed_ones = matching | free
        for u, v in permutations(range(n), 2):
            triggered = any((u, w) not in allowed_ones and (w, v) not in allowed_ones
                            for w in vertices-{u, v})
            assert triggered == ((v, u) not in matching)
            failures += not triggered
            count += 1
    assert Fraction(failures, count) == Fraction(1, 4*m-2)
    print(f'{n} vertices: {count} ordered-core/pairing tests, exceptional fraction {Fraction(failures, count)}')


def check_induced_index(m):
    inside = tuple(range(m))
    data = set(permutations(inside, 2))
    outside = tuple(range(m+1, 2*m))
    a = m
    for u, v in sorted(data):
        left = (v,) + tuple(w for w in inside if w not in (u, v))
        path = tuple(vertex for pair in zip(left, outside) for vertex in pair)
        fixed = set(zip(path, path[1:])) | {
            (a, u), (u, a), (path[-1], v), (path[-1], a), (a, path[2])}
        rows = rows_of(2*m, fixed)
        max_rows = rows_of(2*m, fixed | data)
        assert strongly_connected(rows) and cover_index(rows)[1] == 1 and tour_count(rows) == 0
        assert cover_index(max_rows)[1] == 2 and tour_count(max_rows) == 1
        assert tour_count(rows_of(2*m, fixed | {(u, v)})) == 1
        assert tour_count(rows_of(2*m, fixed | (data-{(u, v)}))) == 0
    print(f'{2*m} vertices: induced-side INDEX checked for {len(data)} addresses on all {1 << len(data)} masks')


def zero_completions(side, other, prefix, zero_arcs):
    """Count completions of a partial partner bijection which pin every specified arc to zero."""
    required = set(prefix) | {(v, u) for u, v in zero_arcs if u in other and v in side}
    forbidden = {(u, v) for u, v in zero_arcs if u in side and v in other}
    left_used = {a for a, _ in required}
    right_used = {b for _, b in required}
    if required & forbidden or len(required) != len(left_used) or len(required) != len(right_used):
        return 0
    free_right = sorted(other - right_used)
    rows = [sum(1 << j for j, b in enumerate(free_right) if (a, b) not in forbidden)
            for a in sorted(side-left_used)]
    return assignments_avoiding(rows)


def iid_probability(flowers, core):
    result = Fraction(0)
    for values in product((0, 1), repeat=len(core)):
        colors = dict(zip(core, values))
        missed = Fraction(1)
        for arcs in flowers:
            private = sorted({v for arc in arcs for v in arc} - set(core))
            good = 0
            for bits in product((0, 1), repeat=len(private)):
                colors.update(zip(private, bits))
                good += all(colors[u] <= colors[v] for u, v in arcs)
            missed *= 1 - Fraction(good, 2**len(private))
        result += 1 - missed
    return result / 2**len(core)


def check_sparse_cores():
    petals = (3, 4, 5)
    examples = [
        ((0, 1), [{(0, w), (1, w)} for w in petals], Fraction(29, 32), Fraction(13, 14)),
        ((0, 1), [{(0, w), (w, 1)} for w in petals], Fraction(11, 16), Fraction(121, 140)),
        ((0, 1, 2), [{(0, w), (w, 1), (w, 2)} for w in petals], Fraction(9, 16), Fraction(101, 140)),
    ]
    vertices = set(range(8))
    for core, flowers, expected_iid, expected_paired in examples:
        assert iid_probability(flowers, core) == expected_iid
        total = hits = 0
        for entries in combinations(range(8), 4):
            side, other = set(entries), vertices-set(entries)
            for prefix in ((), ((entries[0], min(other)),)):
                inc_exc = sum((-1)**(k+1) * zero_completions(side, other, prefix, set.union(*sub))
                              for k in range(1, len(flowers)+1) for sub in combinations(flowers, k))
                brute = 0
                for mates in permutations(other):
                    pairs = set(zip(entries, mates))
                    if not pairs.issuperset(prefix):
                        continue
                    fixed_one, free = allowed(pairs)
                    triggered = any(z.isdisjoint(fixed_one | free) for z in flowers)
                    brute += triggered
                    if not prefix:
                        total += 1
                        hits += triggered
                assert brute == inc_exc
        assert Fraction(hits, total) == expected_paired
        print(f'core {len(core)}, three petals: independent colors {expected_iid}, eight-vertex pairing {expected_paired}')


def check_eight_vertex_coverage():
    base = Circuit(8)
    dual, root = de_morgan_circuit(base, held_karp(base, 8))
    guarded, _, mapping = protect_inputs(dual)
    for dag, out, label in ((dual, root, 'De Morgan'), (guarded, mapping[root], 'with identity inputs')):
        profile = ReaderProfile(dag, out)
        size = len(profile.gates)
        delta = profile.total_fee - 6
        internal = size - 56 + 1 - profile.total_fee
        gap = size - size//4 - 50
        counts = [len(units_certified_by_cut(profile, {0, *side})) for side in combinations(range(1, 8), 3)]
        print(f'8 vertices, {label}: delta={delta}, G={gap}, I={internal}, '
              f'same-side charges {min(counts)}..{max(counts)} on all {len(counts)} cuts')


def pure_side(profile, side):
    dag = profile.dag
    raw = {w for (u, v), w in dag.inputs.items() if u in side and v in side}
    inside = set(raw)
    outgoing = paid_nots = 0
    for g in sorted(profile.gates):
        op, *args = dag.nodes[g]
        if all(w in inside for w in args):
            inside.add(g)
            paid_nots += op == 'not'
        else:
            outgoing += sum(w in inside for w in args)
    gate_count = len(inside) - len(raw)
    assert outgoing >= len(raw) and profile.out not in inside
    weight = sum(len(profile.reads[w])-1 for w in inside) + paid_nots
    assert weight == gate_count + outgoing - len(raw)
    return gate_count


def check_two_pure_sides(dag, out):
    profile = ReaderProfile(dag, out)
    m = dag.order//2
    pure_counts = {}
    for pairs in pairings(m):
        side = frozenset(a for a, _ in pairs)
        if side not in pure_counts:
            other = frozenset(range(dag.order)) - side
            value = pure_side(profile, side) + pure_side(profile, other)
            pure_counts[side] = pure_counts[other] = value
        small, image = dag.contract(pairs)
        assert len(profile.gates) - small.size(image[out]) >= 3*m*m-m + pure_counts[side]
    print(f'{dag.order} vertices: {min(pure_counts.values())}..{max(pure_counts.values())} '
          'pure-side gates charged above the fixed-input count')


def check_sibling_degree():
    n = 4
    graph = original(n)
    for word in range(1 << len(graph.labels)):
        rows = graph.graph(word)
        # Arc 0->1 can only be used if vertex 1 can leave for a vertex other than 0.
        if not (rows[1] & ~1):
            reduced = list(rows)
            reduced[0] &= ~(1 << 1)
            assert tour_count(rows) == tour_count(reduced)
    print('4 vertices: OR sibling of degree n-2 preserves H on all 4096 masks')


if __name__ == '__main__':
    check_sparse_cores()
    check_sibling_degree()
    for m in (3, 4):
        check_full_petals(m)
        check_induced_index(m)
    base = Circuit(6)
    dual, root = de_morgan_circuit(base, held_karp(base, 6))
    check_joint_ledger(dual, root, 'six-vertex De Morgan')
    check_two_pure_sides(dual, root)
    guarded, output = masked_circuit(6, False)
    rows = check_joint_ledger(guarded, output, 'three distinct guards')
    assert any(lost for _, lost in rows)
    check_eight_vertex_coverage()
