"""Essentiality after almost all the zero pins of one oriented pairing."""
from fractions import Fraction
from itertools import permutations

from absorbing_readers import ReaderProfile
from cycle_cover_queries import tour_count
from hamiltonian_boards import cycle_masks
from pair_certificate import all_inputs, tables
from paired_contraction import Circuit, allowed, held_karp, pairings
from private_reader_forest import guarded_circuit, row_circuit
from single_cycle_controls import directed_cycle, rows_of


def partial_pins(pairs):
    # The city order supplies a reserved off-diagonal cycle and two same-side arcs.
    m = len(pairs)
    entries, exits = zip(*pairs, strict=True)
    ones, free = allowed(pairs)
    spare = {(entries[i], exits[(i+1) % m]) for i in range(m)}
    spare.update((b, a) for a, b in pairs)
    spare.update(((entries[0], entries[1]), (exits[-1], exits[0])))
    zeros = {(u, v) for u in range(2*m) for v in range(2*m) if u != v} - ones - free - spare
    assert len(zeros) == 3*m*m-4*m-2
    return ones, zeros


def pivotal_tour(pairs, edge):
    m = len(pairs)
    left, right = zip(*pairs, strict=True)
    u, v = edge
    cities = list(range(m))
    if u in right and v in left:
        i, j = right.index(u), left.index(v)
        shift = int(i == j)
        first = (i-shift) % m
        order = [first, j] + [k for k in cities if k not in (first, j)]
        walk = [w for k in order for w in (left[k], right[(k+shift) % m])]
        return directed_cycle(walk)
    if u in left and v in right:
        i, j = left.index(u), right.index(v)
        delta = cities.copy()
        order = [i]
        if i != j:
            delta[i] = j
            k = j
            while k != i:
                order.append(k)
                delta[k] = (k+1) % m
                k = delta[k]
        order += [k for k in cities if k not in order]
        return directed_cycle([w for k in order for w in (left[k], right[delta[k]])])
    aa = edge if u in left else (left[0], left[1])
    bb = edge if u in right else (right[-1], right[0])
    i, l = left.index(aa[0]), right.index(bb[1])
    delta = cities.copy()
    k = l
    while k != i:
        delta[k] = (k+1) % m
        k = delta[k]
    successor = {left[k]: right[delta[k]] for k in cities if k != i}
    successor.update((aa, bb))
    starts = [a for a in left if a != aa[1]]
    walk = []
    for w in starts:
        walk.append(w)
        while w in successor:
            w = successor[w]
            walk.append(w)
    assert sorted(walk) == list(range(2*m))
    return directed_cycle(walk)


def check_essentiality(m):
    pairs = tuple((2*i, 2*i+1) for i in range(m))
    ones, zeros = partial_pins(pairs)
    for u in range(2*m):
        for v in range(2*m):
            if u == v:
                continue
            e = (u, v)
            tour = pivotal_tour(pairs, e)
            assert e in tour and not (tour-{e}) & zeros
            opened = tour | ones
            assert tour_count(rows_of(2*m, opened)) > 0
            assert tour_count(rows_of(2*m, opened-{e})) == 0
    print(f'{2*m} vertices: {len(zeros)} simultaneous zero pins, {2*m*(2*m-1)} pivotal witnesses')


def check_cut_ledger(dag, out):
    m = dag.order//2
    profile = ReaderProfile(dag, out)
    raw = len(dag.edges)
    u = 3*m*m-m
    alpha, beta = Fraction(3*m*m-4*m-2, raw), Fraction(m, raw)
    a = sum(dag.nodes[g][0] == 'and' for g in profile.head.values())
    expected = u+m+(Fraction(u, raw)-alpha-beta)*profile.total_fee+(alpha-beta)*a
    total = selected = samples = 0
    full, cols = all_inputs(Circuit(m))
    tours = cycle_masks(m)
    small_truth = sum(1 << x for x in range(1 << len(cols)) if any(x & t == t for t in tours))
    # All orderings of the three cities, to randomize the reservations equivariantly.
    for pairs in pairings(m):
        small, image = dag.contract(pairs)
        assert tables(small, full, cols)[image[out]] == small_truth
        fixed = set(dag.edges)-allowed(pairs)[1]
        for ordered in permutations(pairs):
            ones, zeros = partial_pins(ordered)
            chosen = {e for e, g in profile.head.items()
                      if (e in zeros if dag.nodes[g][0] == 'and' else e in ones)}
            count, _, loss = profile.check_cut(chosen, fixed, small, image)
            selected += count
            total += loss
            samples += 1
    assert selected == samples*(alpha*a+beta*(len(profile.head)-a))
    assert Fraction(total, samples) >= expected
    print(f'{dag.size(out)} gates: all {samples} ordered completions satisfy the cut ledger')


def and_readers(n):
    dag = Circuit(n)
    guards = [dag.fold('or', (w for e, w in dag.inputs.items() if e[0] == u)) for u in (0, 1)]
    ports = {e: dag.gate('and', w, guards[int(e[0] == 0)]) for e, w in dag.inputs.items()}
    base = Circuit(n)
    root = held_karp(base, n)
    return dag, base.replay(dag, ports)[root]


if __name__ == '__main__':
    for size in (3, 4, 5, 8):
        check_essentiality(size)
    for circuit in (row_circuit(6), guarded_circuit(6), and_readers(6)):
        check_cut_ledger(*circuit)
