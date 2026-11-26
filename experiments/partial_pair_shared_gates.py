"""Check shared gate names and their distinct readers beyond direct pin readers."""
from collections import Counter, defaultdict, deque
from itertools import combinations, permutations
from math import comb, factorial

from boolean_sweep import live_gates
from euclidean_pair_prices import row_ports
from hamiltonian_boards import cycle_masks
from paired_contraction import Circuit, held_karp, hk_size
from read_one_contraction import formal_support


def check_types_and_density():
    for n in range(4, 11):
        vertices = range(n)
        pairs = list(permutations(vertices, 2))
        for d in range(1, n):
            tails = set(range(d))
            for heads_tuple in combinations(vertices, d):
                heads = set(heads_tuple)
                misses = {(a, b) for a, b in pairs if (a in tails) != (b in heads)}
                assert len(misses) == 2*d*(n-d) - len(tails ^ heads)
                assert len(misses) >= min(d, n-d)*(n-2)
        for u, v in pairs:
            pinned = sum(a == u or b == v or (a, b) == (v, u) for a, b in pairs)
            assert pinned == 2*(n-1)
    for d in range(2, 101):
        for a in range(1, d):
            b = d-a
            assert 9**(d-1) <= comb(d, a)*(9**(a-1)*4**b + 9**(b-1)*4**a)
    print('Oriented-pair mismatch counts through n=10; density product inequality through d=100')


def check_support_cut(n, radius):
    dag = Circuit(n)
    root = held_karp(dag, n)
    active, types, full = formal_support(dag, root)
    uses = Counter(v for g in active for v in dag.nodes[g][1:])
    candidates = [g for g in sorted(active) if uses[g] >= 2 and
                  radius <= types[g][0].bit_count() <= n-radius]
    tours = set(cycle_masks(n))
    assert full[root] == tours and candidates
    # Check individual and simultaneous cuts, including cuts retaining a nonempty output.
    for removed in ({g} for g in candidates[:8]):
        check_deleted_supports(dag, root, active, types, tours, removed)
    check_deleted_supports(dag, root, active, types, tours, set(candidates))


def check_deleted_supports(dag, root, active, types, tours, removed):
    supports = {v: {1 << i} for i, v in enumerate(dag.inputs.values())}
    for g in sorted(active):
        op, a, b = dag.nodes[g]
        if g in removed:
            supports[g] = set()
        elif op == 'and':
            supports[g] = {x | y for x in supports[a] for y in supports[b]}
        else:
            assert op == 'or'
            supports[g] = supports[a] | supports[b]
    covered = set()
    for g in removed:
        tails, heads = types[g]
        compatible = set()
        for tour in tours:
            mapped_heads = sum(1 << v for i, (u, v) in enumerate(dag.edges)
                               if tour & (1 << i) and tails & (1 << u))
            if mapped_heads == heads:
                compatible.add(tour)
        d = tails.bit_count()
        assert len(compatible) <= factorial(d)*factorial(dag.order-d)
        covered.update(compatible)
    assert tours - supports[root] <= covered and supports[root] <= tours


def check_two_site_net(dag, active, ports, uncharged):
    """Charge first readers, private gates and one producer per live result.

    Distinct charged-signal paths certify a layout-independent lower bound on
    that debit for this prescribed two-site placement of the original terminals.
    """
    xs = [dag.inputs[x] for x, _ in ports]
    ys = [dag.inputs[y] for _, y in ports]
    terminals = set(xs + ys)
    charged = (set(active)-uncharged) | terminals
    adjacent = defaultdict(list)
    for g in active:
        incident = [v for v in (g, *dag.nodes[g][1:]) if v in charged]
        for a, b in combinations(incident, 2):
            adjacent[a].append(b)
            adjacent[b].append(a)
    used = set()
    lengths = [0]*len(ports)
    # Route actual cell partners, which also certifies the Euclidean wire sum
    # if different data bits are placed at different sites.
    for i in (3, 5, 4, 0, 1, 2):
        forbidden = used | (terminals - {xs[i], ys[i]})
        queue = deque([xs[i]])
        parent = {xs[i]: None}
        while queue:
            u = queue.popleft()
            if u == ys[i]:
                break
            for v in adjacent[u]:
                if v not in forbidden and v not in parent:
                    parent[v] = u
                    queue.append(v)
        else:
            raise AssertionError("missing charged path")
        path = []
        while u is not None:
            path.append(u)
            u = parent[u]
        assert path[0] == ys[i] and path[-1] == xs[i] and used.isdisjoint(path)
        assert all(v in adjacent[u] for u, v in zip(path, path[1:]))
        used.update(path)
        lengths[i] = len(path)
    print(f'Full debit on the 14-vertex two-site test: {len(lengths)} disjoint charged paths '
          f'of lengths {lengths}; net shared-source rank credit 0')


def gate_ledger(dag, root, blocks, ports=None):
    small, image = dag.contract(blocks)
    active = live_gates(dag, root)
    raw = set(dag.inputs.values())
    pins = {v for v in raw if image[v] < 2}
    free_raw = raw - pins
    direct = {g for g in active if pins.intersection(dag.nodes[g][1:])}
    uses = Counter(v for g in active for v in dag.nodes[g][1:])
    zero_shared = {g for g in active if uses[g] >= 2 and image[g] == 0
                   and not raw.intersection(dag.nodes[g][1:])}
    readers = {g for g in active if dag.nodes[g][0] == 'and'
               and zero_shared.intersection(dag.nodes[g][1:])
               and free_raw.intersection(dag.nodes[g][1:])}
    assert direct.isdisjoint(zero_shared | readers) and zero_shared.isdisjoint(readers)
    assert all(image[g] == 0 for g in readers)
    # First creation of a live residual gate cannot be a bypass or a constant.
    live_small = set(live_gates(small, image[root]))
    reps = {}
    for g in active:
        if image[g] in live_small:
            reps.setdefault(image[g], g)
    assert reps.keys() == live_small
    marked = set(reps.values())
    assert not (direct | zero_shared | readers).intersection(marked)
    lost = len(active) - len(live_small)
    assert lost >= len(direct) + len(zero_shared) + len(readers)
    if ports is not None:
        targets = {g for g in active if uses[g] >= 2 and g not in direct and g not in marked}
        check_two_site_net(dag, active, ports, targets)
    return len(direct), len(zero_shared), len(readers), lost


def path_counts(n):
    t = n-3
    names = (t+2)*2**t - 6*t - 4
    readers = 2*t*(t-1)*(2**(t-2)-1) + t*(2**t-t-2)
    explicit_names = sum(comb(t,r)*(2*r+1) for r in range(2,t))
    explicit_names += sum(comb(t,r) for r in range(1,t-1))
    explicit_readers = sum(comb(t,r)*(2*r*(t-r)+t) for r in range(2,t))
    assert (names, readers) == (explicit_names, explicit_readers)
    return names, readers


def check_joint_pairing():
    n = 8
    dag = Circuit(n)
    root = held_karp(dag, n)
    active, types, _ = formal_support(dag, root)
    uses = Counter(v for g in active for v in dag.nodes[g][1:])
    shared = {g for g in active if uses[g] >= 2}
    middle = {g for g in active if 3 <= types[g][0].bit_count() <= n-3}
    reserved = middle & shared
    consumers = {g for g in middle-reserved if shared.intersection(dag.nodes[g][1:])}
    pairs = [(1,2), (3,4)]
    blocks = pairs + [(i,i) for i in range(n) if all(i not in pair for pair in pairs)]
    small, image = dag.contract(blocks)
    pinned = {v for v in dag.inputs.values() if image[v] < 2}
    direct = {g for g in active if pinned.intersection(dag.nodes[g][1:])}
    def mismatches(g, pair):
        tails, heads = types[g]
        a, b = pair
        return bool(tails & (1 << a)) != bool(heads & (1 << b))
    # The first restriction pays consumer gates; the second pays separate origins.
    # Test direct readers against the final union of pins for both pools.
    consumer_credit = {g for g in consumers-direct if mismatches(g, pairs[0])}
    source_credit = {g for g in reserved-direct if mismatches(g, pairs[1])}
    assert consumer_credit and source_credit and consumer_credit.isdisjoint(source_credit)
    assert all(image[g] == 0 for g in consumer_credit | source_credit)
    assert dag.size(root)-small.size(image[root]) >= len(direct | consumer_credit | source_credit)
    print(f'H_8 on the same two pairs {pairs}: {len(direct)} first readers, '
          f'{len(source_credit)} distinct shared sources plus {len(consumer_credit)} separate consumers')


def check_held_karp(n):
    dag = Circuit(n)
    root = held_karp(dag, n)
    assert dag.size(root) == hk_size(n)
    pairs = list(permutations(range(1,n), 2)) if n <= 8 else [(11,3) if n == 14 else (1,2)]
    for a, b in pairs:
        blocks = [(a,b)] + [(i,i) for i in range(n) if i not in (a,b)]
        ports = None
        if n == 14:
            order, _, ports, test_blocks = row_ports(2, 3, 0)
            assert order == n and blocks == test_blocks
        direct, names, readers, lost = gate_ledger(dag, root, blocks, ports)
        assert (names, readers) == path_counts(n)
    print(f'H_{n}, {len(pairs)} oriented pair(s): first {direct}, deep shared zeros {names}, '
          f'distinct free-arc readers {readers}, disjoint increment {names+readers}, total {lost}')


if __name__ == '__main__':
    check_types_and_density()
    for size in (5, 6):
        check_support_cut(size, 2)
    check_joint_pairing()
    for size in (6, 8, 10, 12, 14):
        check_held_karp(size)
