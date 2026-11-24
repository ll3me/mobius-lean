"""Paired restrictions of Hamiltonicity, shared monotone circuits, and fixed supports."""
from collections import Counter
from fractions import Fraction
from itertools import combinations, permutations, product
from math import comb, factorial

from cycle_cover_queries import original, tour_count, with_hubs
from hamiltonian_boards import arcs, coefficients, connected_cover


def pairings(m, root_is_entry=False):
    vertices = tuple(range(2*m))
    for entries in combinations(vertices, m):
        if root_is_entry and 0 not in entries:
            continue
        for exits in permutations(v for v in vertices if v not in entries):
            yield tuple(zip(entries, exits))


def allowed(pairs):
    paired = set(pairs)
    cross = {(b, v) for a, b in pairs for v, _ in pairs if v != a}
    return paired, cross


def lift_graph(rows, pairs, y=None):
    result = [0] * (2*len(pairs))
    for i, (a, b) in enumerate(pairs):
        if y is None or y >> i & 1:
            result[a] |= 1 << b
        for j, (v, _) in enumerate(pairs):
            if rows[i] >> j & 1:
                result[b] |= 1 << v
    return result


def strongly_connected(rows):
    n = len(rows)
    reach = [v | (1 << i) for i, v in enumerate(rows)]
    for k in range(n):
        for i in range(n):
            if reach[i] >> k & 1:
                reach[i] |= reach[k]
    return all(v == (1 << n)-1 for v in reach)


def strong_with_cover(rows):
    n = len(rows)
    outgoing = [[j for j in range(n) if row >> j & 1] for row in rows]
    incoming = [[i for i in range(n) if j in outgoing[i]] for j in range(n)]
    return connected_cover(outgoing, incoming)


def recover_pairs(rows):
    entries = [i for i, row in enumerate(rows) if row.bit_count() == 1]
    return sorted((i, rows[i].bit_length()-1) for i in entries)


class Circuit:
    """R0. Unique source nodes and free constants. Each internal gate costs one."""
    def __init__(self, n):
        self.order = n
        self.edges = arcs(n)
        self.nodes = [('const', 0), ('const', 1)] + [('input', e) for e in self.edges]
        self.inputs = {e: i+2 for i, e in enumerate(self.edges)}
        self.memo = {}

    def intern(self, key):
        if key not in self.memo:
            self.memo[key] = len(self.nodes)
            self.nodes.append(key)
        return self.memo[key]

    def neg(self, a):
        if a < 2:
            return 1-a
        if self.nodes[a][0] == 'not':
            return self.nodes[a][1]
        return self.intern(('not', a))

    def gate(self, op, a, b):
        if a == b:
            return 0 if op == 'xor' else a
        a, b = sorted((a, b))
        if a == 0:
            return 0 if op == 'and' else b
        if a == 1:
            if op == 'xor':
                return self.neg(b)
            return b if op == 'and' else 1
        return self.intern((op, a, b))

    def fold(self, op, args):
        result = 1 if op == 'and' else 0
        for x in args:
            result = self.gate(op, result, x)
        return result

    def size(self, out):
        active = set()
        todo = [out]
        while todo:
            i = todo.pop()
            if i < len(self.inputs)+2 or i in active:
                continue
            active.add(i)
            todo.extend(self.nodes[i][1:])
        return len(active)

    def values(self, rows):
        result = [0, 1] + [int(bool(rows[u] & (1 << v))) for u, v in self.edges]
        for op, *args in self.nodes[len(result):]:
            x = result[args[0]]
            if op == 'not':
                result.append(1-x)
            else:
                y = result[args[1]]
                result.append({'and': x & y, 'or': x | y, 'xor': x ^ y}[op])
        return result

    def affine_rows(self):
        """Eliminate the linear equations, keeping each nonlinear output as an atom."""
        rows = [0, 1]
        for i in range(2, len(self.nodes)):
            op, *args = self.nodes[i]
            if op == 'xor':
                rows.append(rows[args[0]] ^ rows[args[1]])
            elif op == 'not':
                rows.append(1 ^ rows[args[0]])
            else:
                rows.append(1 << i)
        return rows

    def adjacent_repeats(self):
        """Only the two-gate window identities used in the padding example."""
        dest = Circuit(self.order)
        image = [0, 1] + [dest.inputs[e] for e in self.edges]
        for op, *args in self.nodes[len(image):]:
            if op == 'not':
                image.append(dest.neg(image[args[0]]))
                continue
            a, b = (image[i] for i in args)
            for child, other in ((a, b), (b, a)):
                node = dest.nodes[child]
                if node[0] == op and other in node[1:]:
                    value = (node[2] if other == node[1] else node[1]) if op == 'xor' else child
                    break
            else:
                value = dest.gate(op, a, b)
            image.append(value)
        return dest, image

    def replay(self, dest, mapping):
        image = [0, 1] + [mapping.get(e, 0) for e in self.edges]
        for op, *args in self.nodes[len(image):]:
            mapped = [image[i] for i in args]
            image.append(dest.neg(mapped[0]) if op == 'not' else dest.gate(op, *mapped))
        return image

    def contract(self, pairs):
        """Contract directed pairs in the given order. A singleton (v, v) stays free."""
        small = Circuit(len(pairs))
        mapping = {e: 1 for e in pairs}
        for i, (_, b) in enumerate(pairs):
            for j, (a, _) in enumerate(pairs):
                if i != j:
                    mapping[b, a] = small.inputs[i, j]
        return small, self.replay(small, mapping)


def held_karp(dag, n):
    # Nonempty subsets of the vertices other than the fixed root 0.
    states = {}
    for mask in range(2, 1 << n, 2):
        members = [i for i in range(1, n) if mask >> i & 1]
        for v in members:
            if len(members) == 1:
                states[mask, v] = dag.inputs[0, v]
            else:
                states[mask, v] = dag.fold('or', (
                    dag.gate('and', states[mask ^ (1 << v), u], dag.inputs[u, v])
                    for u in members if u != v))
    return dag.fold('or', (dag.gate('and', states[(1 << n)-2, v], dag.inputs[v, 0])
                           for v in range(1, n)))


def hk_size(n):
    q = n-1
    return q*(q-2)*2**(q-1)+3*q-1


def incident_guard(dag, root):
    any_one, two = 0, 0
    for edge, wire in dag.inputs.items():
        if root in edge:
            two = dag.gate('or', two, dag.gate('and', any_one, wire))
            any_one = dag.gate('or', any_one, wire)
    return two


def dispatch(dag, big, pairs):
    small = Circuit(len(pairs))
    slim = held_karp(small, len(pairs))
    paired, cross = allowed(pairs)
    required = dag.fold('and', (dag.inputs[e] for e in sorted(paired)))
    retained = paired | cross
    foreign = dag.fold('or', (wire for e, wire in dag.inputs.items() if e not in retained))
    mapping = {(i, j): dag.inputs[pairs[i][1], pairs[j][0]] for i, j in small.edges}
    embedded = small.replay(dag, mapping)[slim]
    return dag.gate('or', dag.gate('and', required, embedded), dag.gate('and', foreign, big))


def check_circuits(m):
    n = 2*m
    dag = Circuit(n)
    tour = held_karp(dag, n)
    rows = dag.fold('and', (dag.fold('or', (dag.inputs[u, v] for v in range(n) if v != u))
                            for u in range(n)))
    guard = incident_guard(dag, 0)
    length = 17
    padded = tour
    for _ in range(length):
        padded = dag.gate('and', padded, guard)
    xor_padded = tour
    for _ in range(length):
        xor_padded = dag.gate('xor', dag.gate('xor', xor_padded, guard), guard)
    public = tuple((2*i, 2*i+1) for i in range(m))
    selective = dispatch(dag, tour, public)
    if m == 2:
        template = original(n)
        for word in range(1 << len(dag.edges)):
            values = dag.values(template.graph(word))
            assert values[selective] == values[tour] == values[padded] == values[xor_padded]
    assert dag.size(tour) == hk_size(n)
    assert dag.size(rows) == n*(n-1)-1
    cases = 0
    for pairs in pairings(m):
        small, wires = dag.contract(pairs)
        assert small.size(wires[tour]) == hk_size(m)
        assert small.size(wires[rows]) == m*(m-1)-1
        assert small.size(wires[padded]) >= length
        # Follow the still reachable chain by its two inputs, regardless of names.
        here = wires[padded]
        for _ in range(length):
            op, a, b = small.nodes[here]
            assert op == 'and' and wires[guard] in (a, b)
            here = b if a == wires[guard] else a
        assert here == wires[tour]
        here = wires[xor_padded]
        for _ in range(2*length):
            op, a, b = small.nodes[here]
            assert op == 'xor' and wires[guard] in (a, b)
            here = b if a == wires[guard] else a
        assert here == wires[tour]
        affine = small.affine_rows()
        assert affine[wires[xor_padded]] == affine[wires[tour]]
        if pairs == public:
            assert small.size(wires[selective]) == hk_size(m)
            cleaned, local = small.adjacent_repeats()
            assert local[wires[xor_padded]] == local[wires[tour]]
            baseline = cleaned.gate('and', local[wires[tour]], local[wires[guard]])
            assert local[wires[padded]] in (baseline, local[wires[tour]])
        cases += 1
    print(f'{cases} pairings on {n} vertices: Held-Karp {hk_size(n)} -> {hk_size(m)}, '
          f'row predicate {n*(n-1)-1} -> {m*(m-1)-1}, all {length} padding gates survived')


def check_diagonal(r):
    big = Circuit(r+2)
    slots = big.edges[:2*r]
    out = big.fold('and', (big.inputs[e] for e in slots))
    assert big.size(out) == 2*r-1
    for pairs in pairings(r):
        small = Circuit(r+2)
        mapping = {slots[j]: small.inputs[small.edges[i]] for i, pair in enumerate(pairs) for j in pair}
        image = big.replay(small, mapping)
        folded_first = any(set(pair) == {0, 1} for pair in pairs)
        assert small.size(image[out]) == 2*r-1-int(folded_first)


def partial_permutations(n):
    for d in range(1, n+1):
        for tails in combinations(range(n), d):
            for heads in permutations(range(n), d):
                if all(u != v for u, v in zip(tails, heads)):
                    yield tuple(zip(tails, heads))


def completions(support, entries, m):
    """Count allowed mate bijections for this coloring by inclusion-exclusion."""
    forced, forbidden = {}, []
    for u, v in support:
        if (u in entries) == (v in entries):
            return 0
        if u in entries:
            forced[u] = v
        else:
            forbidden.append((v, u))
    if any(forced.get(a) == b for a, b in forbidden):
        return 0
    occupied = set(forced.values())
    h = sum(a not in forced and b not in occupied for a, b in forbidden)
    left = m-len(forced)
    return sum((-1)**j*comb(h, j)*factorial(left-j) for j in range(h+1))


def check_supports(m):
    n = 2*m
    edges = arcs(n)
    bit = {e: 1 << i for i, e in enumerate(edges)}
    assignments = list(pairings(m))
    live = [sum(bit[e] for e in a | b) for a, b in map(allowed, assignments)]
    colors = [set(a) for a in combinations(range(n), m)]
    maxima = Counter()
    total = 0
    for support in partial_permutations(n):
        d = len(support)
        mask = sum(bit[e] for e in support)
        p = Fraction(sum(z & mask == mask for z in live), len(live))
        assert p == Fraction(sum(completions(support, a, m) for a in colors), len(live))
        maxima[d] = max(maxima[d], p)
        used, greedy = set(), []
        for u, v in support:
            if u not in used and v not in used:
                greedy.append((u, v))
                used.update((u, v))
        t = (d+2)//3
        assert len(greedy) >= t
        opposite = Fraction(sum(all((u in a) != (v in a) for u, v in greedy[:t])
                                for a in colors), len(colors))
        exact = Fraction(2**t*comb(2*m-2*t, m-t), comb(2*m, m))
        assert p <= opposite == exact <= Fraction(2, 3)**t
        assert p <= exact / 2**t
        if len(used) == 2*d:
            assert p == Fraction(comb(2*m-2*d, m-d), comb(2*m, m))
        # A separate rational bound from the number of forced matching arcs.
        tail_bound = sum(Fraction(comb(m, d-r), factorial(r)) for r in range(max(0, d-m), min(m,d)+1))
        assert p <= tail_bound / comb(2*m, d)
        if d == n and len(support) and one_tour(support):
            assert p == Fraction(factorial(m-1), factorial(2*m-1))
        total += 1
    print(f'{total} partial permutations, {len(live)} oriented pairings; '
          f'max survival by width: {[str(maxima[d]) for d in sorted(maxima)]}')


def check_arbitrary_supports():
    pool = list(pairings(3))
    counts = Counter()
    for fixed, free in map(allowed, pool):
        possible = sorted(fixed | free)
        for d in range(1, len(possible) + 1):
            counts.update(combinations(possible, d))

    for support, count in counts.items():
        neighbors = {}
        for u, v in support:
            neighbors.setdefault(u, set()).add(v)
            neighbors.setdefault(v, set()).add(u)
        vertices = len(neighbors)
        unseen = set(neighbors)
        components = 0
        while unseen:
            components += 1
            stack = [unseen.pop()]
            while stack:
                new = neighbors[stack.pop()] & unseen
                unseen.difference_update(new)
                stack.extend(new)
        assert 4 * len(support) <= (vertices - components + 1)**2
        assert count * comb(vertices, vertices//2) <= len(pool) * 2**components
    assert len(counts) == 44_400

    # Two tails times two heads. Compare R0 on the actual AND gates to the
    # probability of the prescribed colors followed by avoiding all four mates.
    m = 4
    dag = Circuit(2*m)
    output = dag.fold('and', (dag.inputs[u, v] for u in (0, 1) for v in (2, 3)))
    pool = list(pairings(m))
    survivors = sum(dag.contract(pairs)[1][output] != 0 for pairs in pool)
    expected = Fraction(comb(2*m-4, m-2), comb(2*m, m)) * Fraction(comb(m-2, 2), comb(m, 2))
    assert Fraction(survivors, len(pool)) == expected
    print(f'{len(counts)} nonempty six-vertex supports; four-arc AND survives '
          f'{survivors}/{len(pool)} eight-vertex pairings')


def one_tour(permutation):
    successor = dict(permutation)
    path, u = set(), 0
    while u not in path:
        path.add(u)
        u = successor[u]
    return u == 0 and len(path) == len(successor)


def check_midpoints(m):
    pairs = list(pairings(m, root_is_entry=True))
    presentations = 0
    for others in combinations(range(1, 2*m), m-1):
        subset = {0, *others}
        closed = sum(all((u in subset) == (v in subset) for u, v in p) for p in pairs)
        assert Fraction(closed, len(pairs)) == Fraction(comb(m, m//2), comb(2*m, m))
        presentations += 1
    print(f'{presentations} rooted midpoints verified against {len(pairs)} pairings')


def check_graphs(m):
    source = original(m)
    fixed = tuple(zip(range(m), range(m, 2*m)))
    for mask in range(1 << len(source.labels)):
        rows = source.graph(mask)
        h, s, c = tour_count(rows), strongly_connected(rows), strong_with_cover(rows)
        for y in range(1 << m):
            lifted = lift_graph(rows, fixed, y)
            all_open = y == (1 << m)-1
            assert tour_count(lifted) == all_open*h
            assert strongly_connected(lifted) == (all_open and s)
            assert strong_with_cover(lifted) == (all_open and c)
        hub_rows = with_hubs(source, 2).graph(mask)
        assert all(v.bit_count() >= 2 for v in hub_rows)
        # Interleave and permute the hidden terminal names.
        n = len(hub_rows)
        scrambled = tuple((2*i+1, 2*((i+1) % n)) for i in reversed(range(n)))
        assert recover_pairs(lift_graph(hub_rows, scrambled)) == sorted(scrambled)
    print(f'all {1 << len(source.labels)} source graphs on {m}: HC, strong connectivity, '
          'and strong-plus-cover factorization; pairing decoded on the two-hub subfamily')


def can_commit(rows, tails):
    heads = [[j for j in range(len(rows)) if rows[i] >> j & 1] for i in tails]
    for picked in product(*heads):
        constrained = rows.copy()
        for i, j in zip(tails, picked):
            constrained[i] = 1 << j
        if strongly_connected(constrained):
            return True
    return False


def level(rows, t):
    # An extension to t chosen tails is also an extension for any subset.
    return strongly_connected(rows) and all(can_commit(rows, tails) for tails in
                                           combinations(range(len(rows)), min(t, len(rows))))


def check_levels():
    for m in (3, 4):
        source = original(m)
        size = 1 << len(source.labels)
        hc = coefficients([tour_count(source.graph(mask)) != 0 for mask in range(size)])
        for t in range(3):
            truth = [level(source.graph(mask), t) for mask in range(size)]
            values = coefficients(truth)
            assert all(values[s] == hc[s] for s in range(size) if s.bit_count() <= m+t)
            if m == 3:
                pairs = tuple((2*i, 2*i+1) for i in range(m))
                for mask, value in enumerate(truth):
                    for y in range(1 << m):
                        assert level(lift_graph(source.graph(mask), pairs, y), t) == (
                            value and y == (1 << m)-1)
        print(f'm={m}: the first three commitment levels agree through the claimed degrees')
    for t in range(3):
        # t+1 hubs, and t+2 disjoint bidirected pairs after removing the hubs.
        n = 3*t+5
        rows = [0]*n
        for i, j in arcs(n):
            if min(i, j) <= t or (i-t-1)//2 == (j-t-1)//2:
                rows[i] |= 1 << j
        assert strong_with_cover(rows) and not tour_count(rows)
        assert level(rows, t) and not can_commit(rows, tuple(range(t+1)))
        print(f'{n} vertices: passes any {t} tail commitments, fixing all {t+1} hubs fails')


if __name__ == '__main__':
    check_graphs(3)
    check_levels()
    check_supports(3)
    check_arbitrary_supports()
    check_midpoints(4)
    for half in (2, 3, 4):
        check_circuits(half)
        check_diagonal(half)
