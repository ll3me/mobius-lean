"""Cofactors of arc pairs and the leaf budget for private OR inputs of Hamiltonicity."""
from collections import defaultdict
from fractions import Fraction
from itertools import combinations, permutations

from absorbing_readers import ReaderProfile
from cycle_cover_queries import tour_count
from hamiltonian_boards import arcs, cycle_masks
from oriented_contraction import de_morgan_circuit
from pair_certificate import all_inputs, tables
from paired_contraction import Circuit, held_karp, pairings, strong_with_cover
from single_cycle_controls import directed_cycle, rows_of


def or_background(n, e, f):
    """These fixed arcs leave the Hamiltonian decision equal to x_e OR x_f."""
    i, j = e
    k, l = f
    if {i, k}.isdisjoint({j, l}):
        left = {i, k}
        return {(a, b) for a, b in arcs(n) if a not in left or b in left}
    if j != k:
        return or_background(n, f, e)
    outside = [v for v in range(n) if v not in (i, j, l)]
    if i == l:
        walks = ((i, j, *outside), (j, i, *outside))
    else:
        spare, *rest = outside
        walks = ((i, j, spare, l, *rest), (i, spare, j, l, *rest))
    return (directed_cycle(walks[0]) | directed_cycle(walks[1])) - {e, f}


def check_cofactors(n):
    edges = arcs(n)
    tours = cycle_masks(n)
    compatible = 0
    for (i, e), (j, f) in combinations(enumerate(edges), 2):
        same_tour = e[0] != f[0] and e[1] != f[1] and e != f[::-1]
        both = (1 << i) | (1 << j)
        assert any(t & both == both for t in tours) == same_tour
        compatible += same_tour
        fixed = or_background(n, e, f)
        assert not {e, f} & fixed
        for subset in (set(), {e}, {f}, {e, f}):
            assert (tour_count(rows_of(n, fixed | subset)) > 0) == bool(subset)
    print(f'{n} vertices: {len(edges)*(len(edges)-1)//2} OR cofactors; {compatible} also admit AND')


def induced_or_rows(n, core, opened):
    """Separate consecutive core vertices with one fewer private helper paths."""
    core = sorted(core)
    helpers = sorted(set(range(n))-set(core))
    assert len(core) >= 2 and len(helpers) >= len(core)-1
    paths = [[v] for v in helpers[:len(core)-2]] + [helpers[len(core)-2:]]
    fixed = {(u, path[0]) for u in core for path in paths}
    fixed.update((path[-1], u) for path in paths for u in core)
    for path in paths:
        fixed.update(zip(path, path[1:]))
    return rows_of(n, fixed | set(opened))


def check_induced_or():
    for n, core in ((6, range(3)), (8, range(4))):
        edges = list(permutations(core, 2))
        for word in range(1 << len(edges)):
            opened = [e for i, e in enumerate(edges) if word >> i & 1]
            assert (tour_count(induced_or_rows(n, core, opened)) > 0) == bool(word)
    # At the scale of the eight-arc proof, check actual labelled tours.
    n, k = 32, 16
    core = range(k)
    edges = [(i, i+1) for i in range(0, k, 2)]
    paths = [[v] for v in range(k, 2*k-2)] + [list(range(2*k-2, n))]
    for word in range(1 << len(edges)):
        opened = [e for i, e in enumerate(edges) if word >> i & 1]
        rows = induced_or_rows(n, core, opened)
        if not opened:
            assert not strong_with_cover(rows)
            continue
        e = opened[0]
        blocks = [list(e), *([v] for v in core if v not in e)]
        walk = [v for block, path in zip(blocks, paths, strict=True) for v in block+path]
        assert sorted(walk) == list(range(n)) and all(rows[u] >> v & 1 for u, v in directed_cycle(walk))


def row_circuit(n):
    """Read one row once, grouped at a single output. Every OR has a private AND above it."""
    dag = Circuit(n)
    blocked = dag.neg(dag.fold('or', (dag.inputs[e] for e in dag.edges if e[0] == 1)))
    terms = []
    for v in range(1, n):
        rest = [i for i in range(1, n) if i != v]
        paths = []
        for perm in permutations(rest):
            walk = (v, *perm, 0)
            paths.append(dag.fold('and', (dag.inputs[e] for e in zip(walk, walk[1:]))))
        head = dag.gate('or', dag.inputs[0, v], blocked)
        terms.append(dag.gate('and', head, dag.fold('or', paths)))
    return dag, dag.fold('or', terms)


def guarded_circuit(n, dual=False, guard_from_heads=False):
    """Two disjoint tours can guard raw ORs while keeping the answer on every large graph."""
    source = Circuit(n)
    root = held_karp(source, n)
    if dual:
        source, root = de_morgan_circuit(source, root)
    dag = Circuit(n)
    forward = directed_cycle(tuple(range(n)))
    reverse = sorted((b, a) for a, b in forward)
    found = dag.fold('and', (dag.inputs[e] for e in sorted(forward)))
    ports = {e: dag.gate('or', x, found) for e, x in dag.inputs.items() if e not in forward}
    if guard_from_heads:
        # The second guard is true exactly when one of the two tours is present.
        # It has a single consumer, so its AND tree belongs to this head's sibling.
        alternative = dag.fold('and', (ports[e] for e in reverse))
        special = next(e for e in dag.edges if e not in forward and e not in reverse)
        ports[special] = dag.gate('or', dag.inputs[special], alternative)
        ports.update({e: dag.inputs[e] for e in forward})
    else:
        found_reverse = dag.fold('and', (dag.inputs[e] for e in reverse))
        ports.update({e: dag.gate('or', dag.inputs[e], found_reverse) for e in forward})
    return dag, source.replay(dag, ports)[root]


def audit_forest(dag, out):
    profile = ReaderProfile(dag, out)
    n, total = dag.order, len(dag.inputs)
    literal = {wire: e for e, wire in dag.inputs.items()}
    for gate in profile.gates:
        op, *args = dag.nodes[gate]
        if op == 'not' and dag.nodes[args[0]][0] == 'input':
            literal[gate] = literal[args[0]]
    gates = sorted(profile.gates - literal.keys())
    shared = {g for g in gates if len(profile.reads[g]) >= 2}
    slots = defaultdict(list)
    for g in gates:
        for j, w in enumerate(dag.nodes[g][1:]):
            if w in literal:
                slots[literal[w]].append((g, j))
    single = {e: uses[0] for e, uses in slots.items() if len(uses) == 1}
    single_slots = set(single.values())
    tree = {}
    for g in reversed(gates):
        tree[g] = g if g == out or g in shared else tree[profile.reads[g][0]]
    groups = defaultdict(list)
    for e, (g, _) in single.items():
        groups[tree[g]].append(e)
    for group in groups.values():
        if len(group) >= 2:
            assert (len({u for u, _ in group}) == 1 or len({v for _, v in group}) == 1
                    or (len(group) == 2 and group[0] == group[1][::-1]))

    def branch_leaves(parent, side):
        leaves, nots = set(), set()
        todo = [(parent, side)]
        while todo:
            g, j = todo.pop()
            w = dag.nodes[g][j+1]
            if w in literal or w in shared:
                leaves.add((g, j))
            else:
                op, *args = dag.nodes[w]
                if op == 'not':
                    nots.add(w)
                todo.extend((w, u) for u in range(len(args)))
        return leaves, nots

    first, second, exempt, positive, exposed = {}, {}, set(), {}, {}
    stem_nots = set()
    private_or = {e for e, g in profile.head.items() if dag.nodes[g][0] == 'or'}
    charged_slots = set()
    for e, (g, j) in single.items():
        first[e] = branch_leaves(g, 1-j)
        assert first[e][0].isdisjoint(single_slots | charged_slots)
        charged_slots.update(first[e][0])
        if e not in private_or:
            continue
        forced = 1
        path_nots = []
        while g != tree[g]:
            parent, = profile.reads[g]
            op, *args = dag.nodes[parent]
            if op == 'not':
                forced ^= 1
                path_nots.append(parent)
            elif (op == 'and' and forced) or (op == 'or' and not forced):
                leaves, _ = branch_leaves(parent, 1-args.index(g))
                assert leaves.isdisjoint(single_slots | charged_slots)
                charged_slots.update(leaves)
                second[e] = (parent, 1-args.index(g))
                break
            g = parent
        else:
            assert groups[g] == [e]
            exempt.add(e)
            if g != out:
                exposed[g] = e
                if forced:
                    positive[g] = e
                else:
                    assert path_nots and path_nots[0] not in stem_nots
                    stem_nots.add(path_nots[0])

    raw_extra = sum(len(items)-1 for items in slots.values())
    repeated = total-len(single)
    share_extra = sum(len(profile.reads[g])-1 for g in shared)
    negations = sum(dag.nodes[g][0] == 'not' for g in gates)
    leaf_budget = share_extra+len(shared)+raw_extra+repeated
    cheap_slots = sum(len(profile.reads[g]) for g in positive)
    all_cheap = rescued = 0
    sibling_nots = set()
    branches = list(first.values()) + [branch_leaves(*slot) for slot in second.values()]
    for leaves, nots in branches:
        sources = {dag.nodes[g][1+j] for g, j in leaves}
        assert len(leaves) != 1 or not sources <= exposed.keys()
        if not sources <= positive.keys():
            continue
        if nots:
            assert nots.isdisjoint(stem_nots | sibling_nots)
            sibling_nots.add(min(nots))
        else:
            assert len(sources) >= (n+1)//4
            all_cheap += 1
    slack = leaf_budget-len(branches)
    assert len(charged_slots) <= leaf_budget
    assert sum(len(profile.reads[g]) for g in exposed) <= 2*slack
    assert len(single)+len(private_or) <= leaf_budget+1
    assert len(stem_nots)+len(sibling_nots) <= negations
    singled = [e for e, slot in second.items() if len(branch_leaves(*slot)[0]) == 1]
    for e in singled:
        gate, _ = second[e]
        leaves, nots = branch_leaves(*second[e])
        if nots or dag.nodes[gate][0] == 'or':
            rescued += 1
            continue
        (parent, side), = leaves
        w = dag.nodes[parent][1+side]
        if w in shared:
            for f in groups[w]:
                g, j = single[f]
                neg = dag.nodes[g][1+j] != dag.inputs[f]
                while g != w:
                    g, = profile.reads[g]
                    neg ^= dag.nodes[g][0] == 'not'
                assert neg, (e, f)
    assert rescued <= negations
    assert len(second) <= 2*slack+3*negations+2*profile.total_fee+share_extra-len(shared)

    nested = {tree[g] for g in gates if any(w in shared for w in dag.nodes[g][1:])}
    bottom = sum(len(group) for root, group in groups.items() if root not in nested)
    assert (n-2)*bottom <= raw_extra+repeated
    assert len(single) <= Fraction(2*raw_extra, n-2)+(n-1)*(1+len(nested-{out}))
    size = dag.size(out)
    fees = profile.total_fee
    and_count = len(profile.head)-len(private_or)
    assert size-total+1 == fees+share_extra+negations
    assert 2*total-1 <= 2*(size-total+1)+2*fees+and_count
    assert cheap_slots >= 2*(len(exempt)-len(stem_nots)-1)
    min_leaves = (n+1)//4
    assert (min_leaves-1)*cheap_slots <= min_leaves*(slack+len(sibling_nots))
    if n >= 32:
        assert 13*total <= 12*(size-total+1)+15*fees+7*and_count+7
    print(f'{size} gates: F={fees}, private AND/OR={and_count}/{len(private_or)}, '
          f'second sides={len(second)}, exposed positive/negated roots={len(positive)}/{len(stem_nots)}, '
          f'sides made only of positive exposed sources without NOT={all_cheap}')
    return profile, len(second), len(stem_nots), all_cheap


def check_circuits(n):
    circuits = [row_circuit(n), guarded_circuit(n), guarded_circuit(n, dual=True),
                guarded_circuit(n, guard_from_heads=True)]
    results = []
    for dag, out in circuits:
        profile, *counts = audit_forest(dag, out)
        results.append(counts)
        if n == 4:
            full, columns = all_inputs(dag)
            tours = cycle_masks(n)
            expected = sum(1 << x for x in range(1 << len(columns)) if any(x & t == t for t in tours))
            assert tables(dag, full, columns)[out] == expected
        if n == 6:
            losses = []
            target = Circuit(n//2)
            full, columns = all_inputs(target)
            masks = cycle_masks(n//2)
            expected = sum(1 << x for x in range(1 << len(columns)) if any(x & t == t for t in masks))
            for pairs in pairings(n//2):
                small, image = dag.contract(pairs)
                assert tables(small, full, columns)[image[out]] == expected
                losses.append(dag.size(out)-small.size(image[out]))
            m = n//2
            need = 4*len(dag.inputs)-2*dag.size(out)-2*n+1
            gamma = Fraction(m-2, 4*m-2)
            old = 3*m*m+m-2
            a = sum(dag.nodes[g][0] == 'and' for g in profile.head.values())
            observed = Fraction(sum(losses), len(losses))
            assert observed >= old+1+Fraction(profile.total_fee-(n-2), 2)+gamma*a
            assert observed >= old+1+gamma*max(0, need)
    assert results[0][0] >= n-1 and results[2][1] and results[3][2]


def check_common_guard(n, mixed):
    m = n//2
    dag = Circuit(n)
    tour = directed_cycle(tuple(range(n)))
    found = dag.fold('and', (dag.inputs[e] for e in sorted(tour)))
    if mixed:
        rows = range(m+1)
        dead = dag.fold('or', (dag.neg(dag.fold('or', (dag.inputs[e] for e in dag.edges if e[0] == u)))
                               for u in rows))
        guard = dag.gate('or', found, dead)
        group = {e for e in dag.edges if e[0] not in rows and e not in tour}
    else:
        reverse = {(v, u) for u, v in tour}
        alt = dag.fold('and', (dag.inputs[e] for e in sorted(reverse)))
        veto = next(e for e in dag.edges if e not in tour | reverse)
        guard = dag.gate('and', dag.gate('or', found, alt), dag.neg(dag.inputs[veto]))
        group = set(dag.edges)-tour-reverse-{veto}
    base = Circuit(n)
    root = held_karp(base, n)
    mapping = dict(dag.inputs)
    for e in sorted(group):
        mapping[e] = dag.gate('or', mapping[e], guard)
    out = base.replay(dag, mapping)[root]
    profile = ReaderProfile(dag, out)
    assert len(group) >= n-1 and all(profile.head[e] == mapping[e] for e in group)
    repaired = None
    if mixed:
        bypassed = base.replay(dag, dag.inputs)[root]
        repaired = dag.gate('or', found, dag.gate('and', dag.neg(guard), bypassed))
        assert dag.size(repaired) <= dag.size(out)-len(group)+3
    full, columns = all_inputs(Circuit(m))
    tours = cycle_masks(m)
    expected = sum(1 << x for x in range(1 << len(columns)) if any(x & t == t for t in tours))
    hit = constant = samples = loss_total = 0
    size = dag.size(out)
    for pairs in pairings(m):
        small, image = dag.contract(pairs)
        values = tables(small, full, columns)
        assert values[image[out]] == expected
        matched = bool(group & set(pairs))
        if mixed:
            assert 0 < values[image[guard]] < full and values[image[repaired]] == expected
        elif matched:
            assert image[guard] == 0
        hit += matched
        constant += image[guard] < 2
        samples += 1
        loss_total += size-small.size(image[out])
    beta = Fraction(1, 2*(n-1))
    q = len(group)*beta/(1 + Fraction(len(group)-1, 2*(n-3)))
    assert Fraction(hit, samples) >= q
    if not mixed:
        extra_uses = len(profile.reads[guard])-1
        # Only the group's uses were present when the original profile was built.
        assert extra_uses >= len(group)-1
        lower = 3*m*m+m-2+Fraction(m*m-m+1, 2*m-1)+extra_uses*(q-2*beta)
        assert Fraction(loss_total, samples) >= lower
    print(f'{len(group)} private ORs, {"mixed" if mixed else "one negative literal"} guard: '
          f'{hit}/{samples} pairings hit a reader arc, {constant}/{samples} propagate a constant')


if __name__ == '__main__':
    for size in (4, 5, 6, 8):
        check_cofactors(size)
    for size in (4, 6):
        check_circuits(size)
    check_induced_or()
    for mixed_guard in (False, True):
        check_common_guard(6, mixed_guard)
