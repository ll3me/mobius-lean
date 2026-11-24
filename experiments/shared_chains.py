"""Compress runs of three gates with one raw and one internal operand."""
from collections import Counter
from itertools import product

from cycle_cover_queries import original
from paired_contraction import Circuit, held_karp
from paired_fanout import live_wires


def compress(dag, out):
    gates, uses = live_wires(dag, out)
    sources = set(dag.inputs.values())
    one = {}
    counts = Counter()
    for g in gates:
        op, a, b = dag.nodes[g]
        assert op in ('and', 'or')
        internal = [v for v in (a, b) if v in gates]
        counts[len(internal)] += 1
        if len(internal) == 1:
            raw = b if internal[0] == a else a
            assert raw in sources
            one[g] = internal[0], raw
    excess = sum(uses[g]-1 for g in gates if g != out)
    assert counts[2] + 1 == counts[0] + excess
    successor = {p: g for g, (p, _) in one.items() if p in one and uses[p] == 1}
    starts = [g for g, (p, _) in one.items() if p not in successor or successor[p] != g]
    assert len(starts) <= counts[0] + counts[2] + 2*excess
    blocks = {}
    skip = set()
    for start in starts:
        chain = [start]
        while chain[-1] in successor:
            chain.append(successor[chain[-1]])
        for i in range(2, len(chain), 3):
            block = chain[i-2:i+1]
            skip.update(block[:2])
            pattern = tuple((dag.nodes[g][0], one[g][1]) for g in block)
            blocks[block[-1]] = one[block[0]][0], pattern
    assert len(one) <= 3*len(blocks)+2*len(starts)
    rebuilt = Circuit(dag.order)
    image = {v: rebuilt.inputs[e] for e, v in dag.inputs.items()}
    coefficients = {}
    for g in sorted(gates-skip):
        if g not in blocks:
            op, a, b = dag.nodes[g]
            image[g] = rebuilt.gate(op, image[a], image[b])
            continue
        boundary, pattern = blocks[g]
        if pattern not in coefficients:
            a, b = 0, 1
            for op, wire in pattern:
                x = image[wire]
                if op == 'or':
                    a = rebuilt.gate('or', a, x)
                else:
                    a = rebuilt.gate('and', a, x)
                    b = rebuilt.gate('and', b, x)
            coefficients[pattern] = a, b
        a, b = coefficients[pattern]
        image[g] = rebuilt.gate('or', a, rebuilt.gate('and', image[boundary], b))
    assert rebuilt.size(image[out]) <= len(gates)-len(blocks)+6*len(coefficients)
    return rebuilt, image[out], len(blocks), len(coefficients), excess


def check_patterns():
    for ops in product(('and', 'or'), repeat=3):
        for values in product((False, True), repeat=4):
            u, *bits = values
            direct, a, b = u, False, True
            for op, x in zip(ops, bits):
                if op == 'or':
                    direct, a = direct or x, a or x
                else:
                    direct, a, b = direct and x, a and x, b and x
            assert direct == (a or (u and b))


if __name__ == '__main__':
    check_patterns()
    dag = Circuit(4)
    tour = held_karp(dag, 4)
    wires = list(dag.inputs.values())
    starts = [dag.gate('and', x, y) for i, x in enumerate(wires[3:]) for y in wires[i+4:]]
    terms = []
    for node in starts:
        for op, x in zip(('and', 'or', 'and'), wires):
            node = dag.gate(op, node, x)
        terms.append(node)
    repeated = dag.fold('or', terms)
    source = original(4)
    for out in (tour, repeated):
        dest, result, blocks, distinct, excess = compress(dag, out)
        for word in range(1 << len(wires)):
            rows = source.graph(word)
            assert dag.values(rows)[out] == dest.values(rows)[result]
        print(f'{dag.size(out)} to {dest.size(result)} gates, {blocks} triples, '
              f'{distinct} patterns, {excess} extra internal wires')
