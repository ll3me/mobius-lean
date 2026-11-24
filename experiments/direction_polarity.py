"""Polarity, a complete source projection, and two arcs sharing one witness."""
from itertools import combinations
from math import factorial, prod

from cycle_cover_queries import cover_index, original, tour_count
from hamiltonian_boards import cycle_masks
from paired_contraction import Circuit, held_karp, lift_graph


def signs(dag, out):
    seen = set()
    todo = [(out, False)]
    while todo:
        node, odd = todo.pop()
        if (node, odd) in seen:
            continue
        seen.add((node, odd))
        op, *children = dag.nodes[node]
        if op == 'not':
            todo.append((children[0], not odd))
        elif op in ('and', 'or'):
            todo.extend((v, odd) for v in children)
    return {e: {b for b in (False, True) if (node, b) in seen}
            for e, node in dag.inputs.items()}


def check_signs():
    n = 3
    source = original(n)
    for mask in range(1 << len(source.labels)):
        dag = Circuit(n)
        tour = held_karp(dag, n)
        guard = dag.fold('or', (dag.inputs[e] for e, i in source.labels.items() if mask >> i & 1))
        out = dag.gate('and', tour, dag.gate('or', guard, dag.neg(guard)))
        observed = signs(dag, out)
        assert all(observed[e] == ({False, True} if mask >> i & 1 else {False})
                   for e, i in source.labels.items())
        for word in range(1 << len(source.labels)):
            values = dag.values(source.graph(word))
            assert values[out] == values[tour]
    print('64 polarity patterns and 64 inputs verified; at most one NOT per circuit')


def check_cities(entry_sizes, exit_sizes):
    t = len(entry_sizes)
    n = sum(entry_sizes) + sum(exit_sizes) + t
    fixed = [0]*n
    entries, exits = [], []
    next_id = 0
    for a, b in zip(entry_sizes, exit_sizes):
        entry = list(range(next_id, next_id+a))
        hub = next_id+a
        outer = list(range(hub+1, hub+1+b))
        next_id = outer[-1]+1
        for block in (entry, outer):
            for u in block:
                fixed[u] |= sum(1 << v for v in block if u != v)
        for u in entry:
            fixed[u] |= 1 << hub
        fixed[hub] = sum(1 << v for v in outer)
        entries.append(entry)
        exits.append(outer)
    small = original(t)
    switches = {(i, j): (exits[i][j % len(exits[i])], entries[j][i % len(entries[j])])
                for i, j in small.labels}
    assert len(set(switches.values())) == len(small.labels)
    lifts = prod(factorial(a-1)*factorial(b-1) for a, b in zip(entry_sizes, exit_sizes))
    for word in range(1 << len(small.labels)):
        graph = fixed.copy()
        for edge, (u, v) in switches.items():
            if word >> small.labels[edge] & 1:
                graph[u] |= 1 << v
        assert tour_count(graph) == lifts*tour_count(small.graph(word))
    print(f'{t} cities on {n} vertices: {1 << len(small.labels)} masks, {lifts} lifts per tour')


def required_tours(rows, required):
    graph = rows.copy()
    for u, v in required:
        graph[u] &= 1 << v
    return tour_count(graph)


def check_pair_conflicts():
    m = 4
    pairs = tuple((2*i, 2*i+1) for i in range(m))
    full = lambda size: [((1 << size)-1) ^ (1 << u) for u in range(size)]
    rows = lift_graph(full(m), pairs)
    index, covers = cover_index(rows)
    for i, j in combinations(range(m), 2):
        e, f = (pairs[i][1], pairs[j][0]), (pairs[j][1], pairs[i][0])
        result = (required_tours(full(2*m), (e, f)), tour_count(rows), required_tours(rows, (e,)),
                  required_tours(rows, (f,)), required_tours(rows, (e, f)), covers,
                  (index[e] & index[f]).bit_count())
        assert result == (120, 6, 2, 2, 0, 9, 1)
    dag = Circuit(2*m)
    e, f = (1, 2), (3, 0)
    required = (1 << dag.edges.index(e)) | (1 << dag.edges.index(f))
    terms = (dag.fold('and', (dag.inputs[edge] for i, edge in enumerate(dag.edges) if term >> i & 1))
             for term in cycle_masks(2*m) if term & required == required)
    witness = dag.fold('or', terms)
    z = dag.inputs[e]
    padded = dag.gate('or', witness, dag.gate('and', z, dag.neg(z)))
    small, image = dag.contract(pairs)
    assert image[witness] == 0 and small.size(image[padded]) == 2
    template = original(m)
    for word in range(1 << len(small.edges)):
        assert small.values(template.graph(word))[image[padded]] == 0
    print('six city pairs: 120,6,2,2,0,9,1; R0 retains a two-gate zero on all 4096 inputs')


if __name__ == '__main__':
    check_signs()
    check_cities((3, 1, 2), (1, 2, 1))
    check_cities((2, 1, 1, 1), (1, 1, 1, 1))
    check_pair_conflicts()
