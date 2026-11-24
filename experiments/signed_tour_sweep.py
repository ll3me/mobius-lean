"""Signed closed-walk inclusion-exclusion compiled into an unlabelled Boolean DAG."""
from collections import Counter
from math import factorial

from boolean_sweep import (DiagramSignatures, PolynomialSignatures, affine_rebuild,
                           private_parities, rebuild_private_parities, rewrite_windows,
                           sweep, xnor_gate, xor_gate)
from hamiltonian_boards import cycle_masks
from pair_certificate import all_inputs, tables
from paired_contraction import Circuit, held_karp, pairings


def word_add(dag, left, right, carry=0):
    result = []
    for i, (a, b) in enumerate(zip(left, right, strict=True)):
        parity = xor_gate(dag, a, b)
        result.append(xor_gate(dag, parity, carry))
        if i+1 < len(left):
            carry = dag.gate('or', dag.gate('and', a, b), dag.gate('and', parity, carry))
    return tuple(result)


def walk_count(dag, deleted, width):
    zero = (0,) * width
    vertices = [u for u in range(dag.order) if not deleted >> u & 1]
    states = {u: (int(u == 0),) + zero[1:] for u in vertices}
    for step in range(dag.order):
        updated = {}
        for v in [0] if step+1 == dag.order else vertices:
            total = zero
            for u in vertices:
                if u != v:
                    term = tuple(dag.gate('and', bit, dag.inputs[u, v]) for bit in states[u])
                    total = word_add(dag, total, term)
            updated[v] = total
        states = updated
    return states[0]


def signed_tour_circuit(n):
    dag = Circuit(n)
    width = factorial(n-1).bit_length()
    # Materialize the count words in the same order as the tagged control.
    # Only the gate graph and its output pass to the rewriter.
    terms = [(deleted.bit_count() % 2, walk_count(dag, deleted, width))
             for deleted in range(0, 1 << n, 2)]
    total = (0,) * width
    for subtract, count in terms:
        if any(count):
            word = tuple(dag.neg(bit) for bit in count) if subtract else count
            total = word_add(dag, total, word, subtract)
    return dag, dag.fold('or', total)


def expected_decisions(dag):
    tours = cycle_masks(dag.order)
    counts = [sum((mask & tour) == tour for tour in tours) for mask in range(1 << len(dag.edges))]
    return sum((n > 0) << mask for mask, n in enumerate(counts)), counts


def check_sweep(dag, out, signatures, truth, columns):
    result, g, counts = sweep(dag, out, signatures)
    size = result.size(g)
    assert tables(result, *columns)[g] == truth
    assert size <= counts.paid_classes <= counts.positions
    return size, counts


def check_distributivity():
    dag = Circuit(3)
    x, y, z = list(dag.inputs.values())[:3]
    left = dag.gate('and', x, xor_gate(dag, y, z))
    right = xor_gate(dag, dag.gate('and', x, y), dag.gate('and', x, z))
    out = xor_gate(dag, left, right)
    columns = all_inputs(dag)
    assert tables(dag, *columns)[out] == 0
    window, w = rewrite_windows(dag, out)
    affine, a = affine_rebuild(window, w)
    assert (dag.size(out), window.size(w), affine.size(a)) == (15, 15, 15)
    for sig in (PolynomialSignatures(8), DiagramSignatures(8)):
        assert check_sweep(window, w, sig, 0, columns)[0] == 0


def check_optimal_parity():
    # These two raw arcs survive a real pairing, and (0,1) becomes one.
    dag = Circuit(4)
    x, y, z = (dag.inputs[e] for e in ((1, 2), (3, 0), (0, 1)))
    root = xor_gate(dag, xor_gate(dag, x, z), y)
    residual, image = dag.contract(((0, 1), (2, 3)))
    wdag, w = rewrite_windows(residual, image[root])
    adag, a = affine_rebuild(wdag, w)
    u, v = residual.inputs.values()
    xnor = xnor_gate(residual, u, v)
    columns = all_inputs(residual)
    assert (dag.size(root), residual.size(image[root]), wdag.size(w), adag.size(a),
            residual.size(xnor)) == (8, 5, 5, 5, 4)
    assert tables(residual, *columns)[image[root]] == tables(residual, *columns)[xnor] == 9
    assert tables(wdag, *columns)[w] == tables(adag, *columns)[a] == 9
    regions = private_parities(dag, root)
    assert set(regions) == {root}
    rebuilt, g = rebuild_private_parities(dag, root, ((0, 1), (2, 3)), regions)
    assert rebuilt.size(g) == 4 and tables(rebuilt, *columns)[g] == 9


def check_quarter_on_parity(n):
    m = n//2
    dag = Circuit(n)
    raw = list(dag.inputs.values())
    d = len(raw)
    q = raw[0]
    for i, x in enumerate(raw[1:]):
        gate = xnor_gate if i % 2 == 0 else xor_gate
        q = gate(dag, q, x)
    assert dag.size(q) == 4*(d-1)
    regions = private_parities(dag, q)
    assert set(regions) == {q}
    free = m*(m-1)
    orientation_sign = regions[q][1] ^ (m % 2)
    base = Circuit(m)
    columns = all_inputs(base)
    expected = sum((orientation_sign ^ (w.bit_count() % 2)) << w for w in range(1 << free))
    for pairing in pairings(m):
        small, out = rebuild_private_parities(dag, q, pairing, regions)
        assert small.size(out) == 4*(free-1)
        assert small.size(out)*d <= free * dag.size(q)
        assert tables(small, *columns)[out] == expected


def check_hamiltonian_with_parity():
    # Partition the four Shannon cofactors of H_6 by whether two arcs agree.
    dag = Circuit(6)
    e, f = (dag.inputs[p] for p in ((0, 1), (0, 2)))
    h = Circuit(6)
    g = held_karp(h, 6)
    branches = []
    for first in (0, 1):
        for second in (0, 1):
            mapping = dict(dag.inputs)
            mapping[(0, 1)], mapping[(0, 2)] = first, second
            branches.append(h.replay(dag, mapping)[g])
    parity = xor_gate(dag, e, f)
    # If e,f differ, e distinguishes 01 and 10. If equal, e distinguishes 00 and 11.
    def choose(bit, no, yes):
        return dag.gate('or', dag.gate('and', dag.neg(bit), no), dag.gate('and', bit, yes))
    out = choose(parity, choose(e, branches[0], branches[3]), choose(e, branches[1], branches[2]))
    regions = private_parities(dag, out)
    assert parity in regions
    base = Circuit(3)
    cols = all_inputs(base)
    truth, _ = expected_decisions(base)
    for pairing in pairings(3):
        small, root = rebuild_private_parities(dag, out, pairing, regions)
        assert tables(small, *cols)[root] == truth


def check_case(n):
    m = n//2
    source, root = signed_tour_circuit(n)
    assert not private_parities(source, root)
    small = Circuit(m)
    truth, counts = expected_decisions(small)
    columns = all_inputs(small)
    pool = pairings(m) if n <= 6 else [tuple((2*i, 2*i+1) for i in range(m))]
    stats = Counter()
    for pairs in pool:
        residual, image = source.contract(pairs)
        out = image[root]
        # Remove all generator metadata, including the map from source gates.
        del image
        base = residual.size(out)
        assert tables(residual, *columns)[out] == truth
        window, w = rewrite_windows(residual, out)
        affine, a = affine_rebuild(window, w)
        assert tables(window, *columns)[w] == tables(affine, *columns)[a] == truth
        sizes = (base, window.size(w), affine.size(a))
        outputs = []
        for sig in (PolynomialSignatures(8), DiagramSignatures(8), DiagramSignatures(512)):
            size, audit = check_sweep(window, w, sig, truth, columns)
            outputs.append(size)
            if n == 8:
                print(f'  {type(sig).__name__} cap {sig.limit}: {size} gates, '
                      f'{audit.shared_redirects} redirected shared gates, '
                      f'{audit.cutoff_atoms} fresh symbols, {audit.paid_classes} paid classes')
        stats[(*sizes, *outputs)] += 1
    print(f'{n}->{m}, input DAG {source.size(root)} gates, '
          f'{1<<len(small.edges)} small masks, even positive counts '
          f'{sum(k>0 and k%2==0 for k in counts)}, '
          f'maximal raw parity regions 0: {dict(stats)}')
    return stats


if __name__ == '__main__':
    check_distributivity()
    check_optimal_parity()
    check_quarter_on_parity(4)
    check_quarter_on_parity(6)
    check_hamiltonian_with_parity()
    print('Private parity trees: output phase, common-pair budget and H6 cofactors verified')
    assert check_case(4) == {(23, 1, 1, 1, 1, 1): 12}
    assert check_case(6) == {(507, 401, 9, 5, 9, 5): 120}
    assert check_case(8) == {(6075, 4776, 3726, 2701, 2606, 396): 1}
