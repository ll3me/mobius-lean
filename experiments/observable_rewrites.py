"""Check observable shared-wire substitutions against the fixed Boolean rewriter."""
from collections import Counter
from itertools import combinations, count, permutations
from subprocess import run

from boolean_sweep import (affine_rebuild, live_gates, make_gate, rewrite_windows,
                           window_replacements, xor_gate)
from cycle_cover_queries import cover_index
from hamiltonian_boards import sat_solver
from pair_certificate import all_inputs, tables
from paired_contraction import Circuit, held_karp
from paired_cover_witnesses import extend_vertex, six_vertex_family, union_rows
from signed_tour_sweep import signed_tour_circuit


def reroute(dag, out, targets):
    fresh = Circuit(dag.order)
    image = list(range(2 + len(dag.inputs)))
    for gate, (op, *args) in enumerate(dag.nodes[len(image):], len(image)):
        if gate in targets:
            assert targets[gate] < gate
            image.append(image[targets[gate]])
        else:
            image.append(make_gate(fresh, op, [image[a] for a in args]))
    return fresh, image[out]


def optimum_control_cnf(budget):
    """All topological AND/OR/NOT programs on four inputs with this many slots."""
    indices = count(1)
    clauses = []

    def fresh():
        return next(indices)

    def choose_one(wires):
        clauses.append(wires)
        clauses.extend([-a, -b] for a, b in combinations(wires, 2))

    values = [[fresh() for _ in range(16)] for _ in range(4+budget)]
    for i in range(4):
        for mask, bit in enumerate(values[i]):
            clauses.append([bit if mask >> i & 1 else -bit])
    for gate in range(4, 4+budget):
        left, right = [[fresh() for _ in range(gate)] for _ in range(2)]
        choose_one(left)
        choose_one(right)
        conj, disj, neg = [fresh() for _ in range(3)]
        choose_one([conj, disj, neg])
        for j in range(gate):
            for k in range(j):
                clauses.append([-left[j], -right[k]])
            clauses.append([-neg, -left[j], right[j]])
        for mask, z in enumerate(values[gate]):
            u, v = fresh(), fresh()
            for port, bit in ((left, u), (right, v)):
                for j, sel in enumerate(port):
                    w = values[j][mask]
                    clauses.extend(([-sel, -bit, w], [-sel, bit, -w]))
            clauses.extend(([-conj, -z, u], [-conj, -z, v], [-conj, z, -u, -v],
                            [-disj, z, -u], [-disj, z, -v], [-disj, -z, u, v],
                            [-neg, -z, -u], [-neg, z, u]))
    for mask, out in enumerate(values[-1]):
        x, y, c, z = (mask >> i & 1 for i in range(4))
        answer = ((x | y) ^ z) & (c | (x & y))
        clauses.append([out if answer else -out])
    header = f'p cnf {fresh()-1} {len(clauses)}\n'
    return header + ''.join(' '.join(map(str, row)) + ' 0\n' for row in clauses)


def check_minimum_control():
    solver = sat_solver()
    for size, status in ((7, 20), (8, 10)):
        result = run([solver, '-q', '--check'], input=optimum_control_cnf(size),
                     text=True, capture_output=True)
        assert result.returncode == status, (result.stdout, result.stderr)

    large = Circuit(6)
    pairs = ((0, 1), (2, 3), (4, 5))
    edges = ((1, 2), (3, 4), (0, 2), (5, 0))
    x, y, c, z = (large.inputs[e] for e in edges)
    g = large.gate('or', x, y)
    guard = large.gate('or', c, large.gate('and', x, y))
    root = large.gate('and', xor_gate(large, g, z), guard)
    assert large.size(root) == 8
    altered, other = reroute(large, root, {g: x})
    for mask in range(16):
        rows = [0]*6
        for i, (u, v) in enumerate(edges):
            rows[u] |= ((mask >> i) & 1) << v
        differs = large.values(rows)[root] != altered.values(rows)[other]
        assert differs == (mask & 7 == 6)

    small, image = large.contract(pairs)
    residual = image[root]
    window, w = rewrite_windows(small, residual)
    affine, a = affine_rebuild(window, w)
    assert sum(small.nodes[h][1:].count(image[g]) for h in live_gates(small, residual)) == 2
    cols = all_inputs(small)
    truth = tables(small, *cols)
    assert truth[image[x]] != truth[image[g]]
    assert truth[residual] == tables(window, *cols)[w] == tables(affine, *cols)[a]
    assert (small.size(residual), window.size(w), affine.size(a)) == (7, 7, 7)
    for target, size in ((image[x], 6), (1, 3)):
        changed, h = reroute(small, residual, {image[g]: target})
        assert changed.size(h) == size and tables(changed, *cols)[h] == truth[residual]
    print('exact 8-gate control: R0/D3/affine = 7/7/7, contextual substitutions leave 6 or 3')


def check_joint_failure():
    dag = Circuit(3)
    a, b, c = list(dag.inputs.values())[:3]
    g, k = dag.gate('or', a, b), dag.gate('or', a, c)
    out = dag.gate('or', g, k)
    cols = all_inputs(dag)
    truth = tables(dag, *cols)[out]
    for targets in ({g: b}, {k: c}, {g: b, k: c}):
        new, h = reroute(dag, out, targets)
        assert (tables(new, *cols)[h] == truth) == (len(targets) == 1)


def shared_triangles(dag, out):
    """Edges child -> root when a private child reads the root's other shared operand."""
    live = live_gates(dag, out)
    active = set(live)
    uses = Counter(a for g in live for a in dag.nodes[g][1:])
    pairs = []
    for root in live:
        if dag.nodes[root][0] == 'not':
            continue
        _, a, b = dag.nodes[root]
        for child, shared in ((a, b), (b, a)):
            if (child in active and shared in active and uses[child] == 1
                    and shared in dag.nodes[child][1:]):
                pairs.append((child, root))
    assert len({c for c, _ in pairs}) == len({r for _, r in pairs}) == len(pairs)
    return pairs


def check_window_packing():
    source, out = signed_tour_circuit(6)
    dag, image = source.contract(((0, 1), (2, 3), (4, 5)))
    root = image[out]
    live = live_gates(dag, root)
    used = set()
    witnesses = []
    for window, _, _ in window_replacements(dag, live):
        if used.isdisjoint(window):
            witnesses.append(window)
            used.update(window)
    triangles = shared_triangles(dag, root)
    result, h = rewrite_windows(dag, root)
    saved = len(live)-result.size(h)
    assert 0 < len(witnesses) <= 3*saved
    assert len(triangles) == 1
    assert tables(result, *all_inputs(result))[h] == tables(dag, *all_inputs(dag))[root]
    print(f'{len(live)} residual gates: {len(witnesses)} disjoint eligible windows, '
          f'{saved} actual three-gate-window savings')

    # Consecutive triangles can overlap. The common wire has arbitrary fan-out.
    chain = Circuit(3)
    x, y, z = list(chain.inputs.values())[:3]
    shared = chain.gate('and', x, y)
    out = chain.gate('or', shared, z)
    for i in range(12):
        out = chain.gate('or' if i % 2 else 'and', shared, out)
    pairs = shared_triangles(chain, out)
    assert len(pairs) == 12 and all(a[1] == b[0] for a, b in zip(pairs, pairs[1:]))
    result, root = rewrite_windows(chain, out)
    assert chain.size(out)-result.size(root) >= (len(pairs)+5)//6
    assert tables(result, *all_inputs(result))[root] == tables(chain, *all_inputs(chain))[out]


def tour_and_path_family(n):
    for path in permutations(range(1, n)):
        order = (0, *path)
        rows = [0]*n
        for u, v in zip(order, order[1:] + (0,), strict=True):
            rows[u] = 1 << v
        yield rows, True
        for u in range(n):
            broken = rows.copy()
            broken[u] = 0
            yield broken, False


def check_all_substitutes(dag, out, family):
    graphs = list(family)
    ones = (1 << len(graphs))-1
    columns = [sum(1 << i for i, (rows, _) in enumerate(graphs) if rows[u] >> v & 1)
               for u, v in dag.edges]
    expected = sum(1 << i for i, (_, yes) in enumerate(graphs) if yes)
    truth = tables(dag, ones, columns)
    assert truth[out] == expected
    live = live_gates(dag, out)
    uses = Counter(a for g in live for a in dag.nodes[g][1:])
    shared = [g for g in live if uses[g] >= 2]
    earlier = [0, 1, *dag.inputs.values(), *live]
    checked = only_negative_nonconstant = 0
    for g in shared:
        flipped = truth.copy()
        flipped[g] ^= ones
        for gate in live:
            if gate <= g:
                continue
            op, a, b = dag.nodes[gate]
            assert op in ('and', 'or')
            flipped[gate] = flipped[a] & flipped[b] if op == 'and' else flipped[a] | flipped[b]
        observable = flipped[out] ^ expected
        for h in earlier:
            if h >= g:
                break
            witness = observable & (truth[g] ^ truth[h])
            assert witness, (g, h)
            only_negative_nonconstant += h >= 2 and not (witness & expected)
            checked += 1
    print(f'{len(graphs)} test graphs witness all {checked} substitutions at {len(shared)} '
          f'shared gates; {only_negative_nonconstant} nonconstant alternatives pass all positives')
    return len(shared), checked, only_negative_nonconstant


def check_two_step_substitutions():
    # Vertex 4 (one-based vertex 5) lies on each stated suffix.
    negative = union_rows((1, 0, 3, 2, 5, 4), (2, 3, 4, 5, 0, 1))
    for n in (6, 8, 10):
        rows = extend_vertex(negative, 4, n-6)
        assert cover_index(rows)[1] == 2
        dag = Circuit(n)
        out = held_karp(dag, n)
        values = dag.values(rows)
        for middle, keep_first in ((1, True), (3, False)):
            a, b = dag.inputs[0, middle], dag.inputs[middle, 2]
            gate = dag.gate('and', a, b)
            assert gate < out and values[gate] == values[out] == 0
            new, root = reroute(dag, out, {gate: a if keep_first else b})
            assert new.values(rows)[root] == 1


if __name__ == '__main__':
    check_minimum_control()
    check_joint_failure()
    check_window_packing()
    check_two_step_substitutions()
    large = Circuit(12)
    out = held_karp(large, 12)
    small, image = large.contract(tuple((2*i, 2*i+1) for i in range(6)))
    root = image[out]
    window, w = rewrite_windows(small, root)
    affine, a = affine_rebuild(window, w)
    assert (large.size(out), small.size(root), window.size(w), affine.size(a)) == (101408, 254, 254, 254)
    for family in (six_vertex_family(), tour_and_path_family(6)):
        assert check_all_substitutes(small, root, family) == (50, 5311, 40)
