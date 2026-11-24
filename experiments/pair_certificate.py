"""A bounded-fan-in De Morgan sufficient condition for a single Hamiltonian cycle."""
from itertools import combinations, product, zip_longest
from random import Random

from cycle_cover_queries import original, tour_count
from hamiltonian_boards import cycle_masks
from paired_contraction import Circuit, lift_graph, pairings


def exactly_one(dag, wires):
    seen = twice = 0
    for w in wires:
        twice = dag.gate('or', twice, dag.gate('and', seen, w))
        seen = dag.gate('or', seen, w)
    return dag.gate('and', seen, dag.neg(twice))


def at_most(dag, wires, limit):
    def parity(a, b, both):
        return dag.gate('and', dag.gate('or', a, b), dag.neg(both))

    def add(left, right):
        result = []
        carry = 0
        for a, b in zip_longest(left, right, fillvalue=0):
            both = dag.gate('and', a, b)
            ab = parity(a, b, both)
            propagate = dag.gate('and', ab, carry)
            result.append(parity(ab, carry, propagate))
            carry = dag.gate('or', both, propagate)
        result.append(carry)
        return result

    words = [[w] for w in wires]
    while len(words) > 1:
        tail = words[-1:] if len(words) % 2 else []
        words = [add(words[i], words[i+1]) for i in range(0, len(words)-1, 2)] + tail
    ok = 1
    for i, bit in enumerate(words[0]):
        ok = dag.gate('or' if limit >> i & 1 else 'and', dag.neg(bit), ok)
    return ok


def directed_test(dag, edge):
    n = dag.order
    entry = [exactly_one(dag, (edge[u, v] for v in range(n) if u != v)) for u in range(n)]
    exit_vertex = [dag.neg(w) for w in entry]
    checks = []
    missing = []
    for v in range(n):
        incoming = (dag.gate('and', entry[u], edge[u, v]) for u in range(n) if u != v)
        checks.append(dag.gate('or', entry[v], exactly_one(dag, incoming)))
    for u, v in dag.edges:
        # An entry must send its unique outgoing edge to an exit.
        checks.append(dag.neg(dag.fold('and', (entry[u], entry[v], edge[u, v]))))
        # u is an exit and v is an entry. Ignore the return to u's own entry.
        missing.append(dag.fold('and', (exit_vertex[u], entry[v],
                                       dag.neg(edge[v, u]), dag.neg(edge[u, v]))))
    checks.append(at_most(dag, missing, n//2-2))
    return dag.fold('and', checks)


def certificate(n):
    dag = Circuit(n)
    forward = directed_test(dag, dag.inputs)
    backward = directed_test(dag, {(u, v): dag.inputs[v, u] for u, v in dag.edges})
    return dag, forward, backward, dag.gate('or', forward, backward)


def all_inputs(dag):
    """Pack each input column of the entire small truth table into one integer."""
    width = 1 << len(dag.edges)
    ones = (1 << width)-1
    columns = []
    for i in range(len(dag.edges)):
        run = 1 << i
        columns.append((ones // ((1 << run)+1)) << run)
    return ones, columns


def tables(dag, ones, columns):
    result = [0, ones] + columns
    for op, *children in dag.nodes[len(result):]:
        a = result[children[0]]
        if op == 'not':
            result.append(ones ^ a)
        elif op == 'and':
            result.append(a & result[children[1]])
        else:
            assert op == 'or'
            result.append(a | result[children[1]])
    return result


def check_certificate():
    m = 4
    n = 2*m
    big, forward, backward, out = certificate(n)
    small = Circuit(m)
    ones, columns = all_inputs(small)
    masks = range(1 << len(small.edges))
    complete = len(masks)-1
    tours = cycle_masks(m)
    has_tour = sum(1 << word for word in masks if any(word & t == t for t in tours))
    dense = sum(1 << word for word in masks if (complete ^ word).bit_count() <= m-2)
    cases = 0
    reference = None
    for pairs in pairings(m):
        restricted, image = big.contract(pairs)
        answer = tables(restricted, ones, columns)[image[out]]
        assert answer & dense == dense and answer & ~has_tour == 0
        if reference is None:
            reference = answer
        assert answer == reference
        cases += 1
    assert reference is not None
    pins = 0
    for width in range(m-1):
        for support in combinations(range(len(small.edges)), width):
            for values in product((0, 1), repeat=width):
                opened = sum(value << i for i, value in zip(support, values))
                closed = sum((1-value) << i for i, value in zip(support, values))
                assert reference >> opened & 1 == 0 and reference >> (complete ^ closed) & 1 == 1
                pins += 1
    fixed = tuple((2*i, 2*i+1) for i in range(m))
    # Two deleted arcs in one row defeat the forward decoder. Transposition recovers it.
    free_graph = original(m)
    row = complete ^ sum(1 << free_graph.labels[0, v] for v in (1, 2))
    values = big.values(lift_graph(free_graph.graph(row), fixed))
    assert (values[forward], values[backward], values[out]) == (0, 1, 1)

    rng = Random(24)
    sample = original(n)
    graph = lift_graph(free_graph.graph(complete), fixed)
    maximum = sum(1 << i for e, i in sample.labels.items() if graph[e[0]] >> e[1] & 1)
    words = {rng.getrandbits(len(big.edges)) for _ in range(100)}
    for w in range(len(big.edges)):
        words.add(maximum ^ (1 << w))
        words.add(maximum ^ (1 << w) ^ (1 << rng.randrange(len(big.edges))))
    yes = 0
    for word in words:
        rows = sample.graph(word)
        accepted = big.values(rows)[out]
        if accepted:
            assert tour_count(rows) > 0
            yes += 1
    assert yes > 0
    print(f'{n}-vertex certificate uses {big.size(out)} paid gates; {cases} pairings x '
          f'{len(masks)} masks, {pins} signed pin patterns, {yes}/{len(words)} '
          'additional graphs certified and checked for a tour')


if __name__ == '__main__':
    check_certificate()
