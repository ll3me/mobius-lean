"""Check flexible entry-side pins, the size ledger, and the sharp standalone guard."""
from fractions import Fraction
from itertools import combinations, permutations, product
from math import factorial

from absorbing_readers import ReaderProfile
from boolean_sweep import live_gates
from cycle_cover_queries import tour_count
from hamiltonian_boards import arcs
from pair_certificate import all_inputs, tables
from paired_contraction import Circuit, allowed, held_karp, pairings
from paired_matrix_tests import check_all_graphs
from private_reader_forest import guarded_circuit, row_circuit
from signed_tour_sweep import expected_decisions
from simultaneous_zero_pins import and_readers, partial_pins, pivotal_tour
from single_cycle_controls import directed_cycle, rows_of


def entry_pins(pairs):
    entries = {a for a, _ in pairs}
    _, marked = partial_pins(pairs)
    flexible = {e for e in marked if e[0] in entries and e[1] in entries}
    return flexible, marked - flexible


def check_pivots(m):
    pairs = tuple((2*i, 2*i+1) for i in range(m))
    flexible, zero = entry_pins(pairs)
    assert len(flexible) == m*(m-1)-1
    assert len(zero) == 2*m*m-3*m-1
    for e in arcs(2*m):
        tour = pivotal_tour(pairs, e)
        assert e in tour and not (tour-{e}) & (flexible | zero)
        assert tour_count(rows_of(2*m, tour)) == 1
        assert tour_count(rows_of(2*m, (tour | flexible)-{e})) == 0
    print(f'{2*m} vertices, {len(flexible)} flexible and {len(zero)} zero positions, '
          f'all {2*m*(2*m-1)} pivotal arcs checked')


def check_ledger(dag, out):
    profile = ReaderProfile(dag, out)
    m = dag.order//2
    variables = len(dag.edges)
    fixed_count = 3*m*m-m
    alpha = Fraction(3*m*m-4*m-2, variables)
    beta = Fraction(m*(m-1)-1, variables)
    heads_and = {e for e, g in profile.head.items() if dag.nodes[g][0] == 'and'}
    heads_or = set(profile.head)-heads_and
    formula = (variables-1 + (Fraction(fixed_count, variables)-alpha-beta)*profile.total_fee
               + (alpha-beta)*len(heads_and))
    check = Circuit(m)
    full, columns = all_inputs(check)
    truth, _ = expected_decisions(check)
    samples = hits = flexible_hits = total = 0
    for pairs in pairings(m):
        matching, free = allowed(pairs)
        fixed = set(dag.edges)-free
        for ordered in permutations(pairs):
            flexible, zero = entry_pins(ordered)
            opened = heads_or & flexible
            selected = opened | (heads_and & (flexible | zero))
            small = Circuit(m)
            wiring = {e: 1 for e in matching | opened}
            for i, (_, b) in enumerate(pairs):
                for j, (a, _) in enumerate(pairs):
                    if i != j:
                        wiring[b, a] = small.inputs[i, j]
            image = dag.replay(small, wiring)
            assert tables(small, full, columns)[image[out]] == truth
            count, _, loss = profile.check_cut(selected, fixed, small, image)
            both, _, same_loss = profile.check_cut(set(profile.head) & flexible, fixed, small, image)
            assert same_loss == loss
            samples += 1
            hits += count
            flexible_hits += both
            total += loss
    assert hits == samples*(alpha*len(heads_and) + beta*len(heads_or))
    assert flexible_hits == samples*beta*len(profile.head)
    flexible_only = variables-1 + Fraction(m*m+m+2, variables)*profile.total_fee
    assert Fraction(total, samples) >= formula
    assert Fraction(total, samples) >= flexible_only
    print(f'{dag.size(out)} gates, {samples} ordered restrictions, '
          f'mean loss {Fraction(total, samples)}, certified at least {max(formula, flexible_only)}')


def check_guard(m):
    """A false baseline and two foreign bits that must be detected jointly."""
    pairs = tuple((2*i, 2*i+1) for i in range(m))
    a, b = zip(*pairs)
    matching, ordinary = allowed(pairs)
    guard = {(b[i], b[j]) for i in range(m) for j in range(m) if i != j}
    guard.update((a[i], b[j]) for i in range(m) for j in range(i))
    assert len(guard) == 3*m*(m-1)//2
    # All ordinary tours are present. Equality of counts rules out any extra tour
    # on the entire maximum graph and hence on every one of its subgraphs.
    maximum = set(arcs(2*m)) - guard
    assert tour_count(rows_of(2*m, maximum)) == factorial(m-1)

    def check_conflict(cross, e, f):
        assert cross <= ordinary and {e, f} & guard
        baseline = matching | cross
        for additions in (set(), {e}, {f}, {e, f}):
            count = tour_count(rows_of(2*m, baseline | additions))
            assert bool(count) == (len(additions) == 2)

    cities = list(range(m))
    for i, j in combinations(cities, 2):
        other = [v for v in cities if v not in (i, j)]
        order = [i, other[0], j, *other[1:]]
        swap = {i: j, j: i}
        cross = {(b[swap.get(u, u)], a[v]) for u, v in directed_cycle(order)}
        check_conflict(cross, (a[i], b[j]), (a[j], b[i]))

    for i in cities:
        for j in cities:
            for k in cities:
                if i == j or i == k:
                    continue
                if j == k:
                    segments = [(a[i], b[i])]
                else:
                    segments = [(a[i], b[j]), (a[k], b[i])]
                segments.extend((a[v], b[v]) for v in cities if v not in (i, j, k))
                cross = {(end, segments[(pos+1) % len(segments)][0])
                         for pos, (_, end) in enumerate(segments)}
                check_conflict(cross, (a[i], a[j]), (b[k], b[i]))
    print(f'{2*m} vertices, sharp guard reads {len(guard)} arcs, '
          f'{m*(m-1)**2 + m*(m-1)//2} two-bit obstructions checked')


def check_guard_classes(m):
    # The two-bit obstructions leave one choice per city and one per unordered pair.
    city_pairs = list(combinations(range(m), 2))
    base = set(arcs(2*m))
    observed = set()
    for directions in product(range(2), repeat=len(city_pairs)):
        backward = set()
        for (u, v), reverse in zip(city_pairs, directions, strict=True):
            i, j = (v, u) if reverse else (u, v)
            backward.add((2*i, 2*j+1))
        for cut in range(1 << m):
            guard = backward.copy()
            for i in range(m):
                other = [j for j in range(m) if i != j]
                if cut >> i & 1:
                    guard.update((2*j+1, 2*i+1) for j in other)
                else:
                    guard.update((2*i, 2*j) for j in other)
            if tour_count(rows_of(2*m, base-guard)) == factorial(m-1):
                observed.add((frozenset(backward), cut))
    predicted = set()
    for order in permutations(range(m)):
        forbidden = frozenset((2*j, 2*i+1) for i, j in combinations(order, 2))
        for length in range(m+1):
            predicted.add((forbidden, sum(1 << i for i in order[:length])))
    assert observed == predicted and len(observed) == factorial(m)*(m+1)
    print(f'{2*m} vertices, all {1 << (m+len(city_pairs))} minimum-support candidates: '
          f'{len(observed)} admit exactly the canonical tours')


def room_bounds(m, small_size):
    """Integer lower bounds on the available quarter budget at a given small optimum."""
    if m < 4:
        raise ValueError('the size recurrence starts at eight large vertices')
    n = 2*m
    variables = n*(n-1)
    a = Fraction(2*m*m-3*m-1, variables)
    h = Fraction(5*(m*m-2*m-1)*(m-1), variables*(m-2))
    numerator = variables-1 + a*(4*variables-3) + h*(3*variables-2) + small_size
    exact = numerator / (1+2*a+2*h)
    coarse = Fraction(27*variables+4*small_size-14*n-39, 18)

    def rounded_room(bound):
        minimum = -(-bound.numerator // bound.denominator)
        return minimum//4-small_size

    return rounded_room(coarse), rounded_room(exact)


def check_exterior_slices(m):
    dag = Circuit(2*m)
    output = held_karp(dag, 2*m)
    big = live_gates(dag, output)

    def representatives(pairs):
        small, image = dag.contract(pairs)
        live = set(live_gates(small, image[output]))
        assert check_all_graphs(small, image[output]) == factorial(len(pairs)-1)
        first = {}
        for g in big:
            if image[g] in live:
                first.setdefault(image[g], g)
        assert len(first) == len(live)
        return set(first.values())

    paired = representatives(tuple((2*i, 2*i+1) for i in range(m)))
    intersections = []
    for successor in range(2, 2*m):
        # Each outside test forces a different sole successor for vertex zero.
        parts = [(0, successor)] + [(i, i) for i in range(1, 2*m) if i != successor]
        exterior = representatives(parts)
        assert len(paired-exterior) <= len(big)-len(exterior)
        intersections.append(len(paired & exterior))
    print(f'{2*m} vertices, {len(paired)} inner gate representatives, '
          f'intersections with disjoint full exterior tests {intersections}')


if __name__ == '__main__':
    for size in (3, 4, 5, 6, 8):
        check_pivots(size)
    for circuit in (row_circuit(6), guarded_circuit(6), and_readers(6)):
        check_ledger(*circuit)
    for size in (4, 5, 6):
        check_guard(size)
    check_guard_classes(4)
    for size in (3, 4):
        check_exterior_slices(size)
    m = 1024
    trial = 27*m*(m-1)//17
    assert room_bounds(m, trial) == (369, 699)
    print(f'illustration only: m={m}, S(m)={trial}, coarse/exact spare gates {room_bounds(m, trial)}')
