"""Check same-pair deletion when the first reader of a private input is absorbed."""
from collections import Counter, defaultdict
from fractions import Fraction
from itertools import permutations
from math import ceil

from cycle_cover_queries import tour_count
from hamiltonian_boards import arcs, cycle_masks
from oriented_contraction import de_morgan_circuit
from paired_contraction import Circuit, allowed, held_karp, pairings
from paired_fanout import live_wires
from single_cycle_controls import directed_cycle, rows_of


def check_rectangle(n):
    """Test every type of residual arc with an independent Hamiltonian oracle."""
    m = n // 2
    entries, exits = tuple(range(m)), tuple(range(m, n))
    rectangle = {(a, b) for a in entries for b in exits}
    matching = set(zip(entries, exits))
    bits = {edge: 1 << i for i, edge in enumerate(arcs(n))}
    block_mask = sum(bits[e] for e in rectangle)
    tours = cycle_masks(n)
    for a, b in sorted(rectangle):
        left = tuple(u for u in entries if u != a) + (a,)
        right = (b,) + tuple(v for v in exits if v != b)
        fixed = set(zip(left, left[1:])) | set(zip(right, right[1:])) | {(right[-1], left[0])}
        maximum = block_mask | sum(bits[e] for e in fixed)
        assert {t & block_mask for t in tours if t & maximum == t} == {bits[a, b]}

    for e in set(bits) - rectangle:
        u, v = e
        # Put the two cities consecutively. In an A-A or B-B step, or a
        # return to one's own entry, just one city must be visited backwards.
        i, j = u % m, v % m
        order = [i] if i == j else [i, j]
        order.extend(t for t in range(m) if t not in (i, j))
        reverse = i if i == j or u in entries else (j if v in exits else None)
        walk = []
        for t in order:
            walk.extend((t+m, t) if t == reverse else (t, t+m))
        tour = directed_cycle(walk)
        assert e in tour and (tour & rectangle) <= matching and len(matching - tour) <= 1
        assert tour_count(rows_of(n, tour | matching)) == 1
        assert tour_count(rows_of(n, (tour | matching) - {e})) == 0
    print(f'{n} vertices: verified essentiality for all {len(bits)} arcs of the rectangle construction')


class ReaderProfile:
    def __init__(self, dag, out):
        self.dag, self.out = dag, out
        self.gates, uses = live_wires(dag, out)
        self.reads = defaultdict(list)
        literal = {wire: e for e, wire in dag.inputs.items()}
        raw_wires = set(literal)
        self.tickets = {e: [] for e in dag.edges}
        for g in sorted(self.gates):
            op, *args = dag.nodes[g]
            for a in args:
                self.reads[a].append(g)
            if op == 'not':
                if args[0] in raw_wires:
                    e = literal[args[0]]
                    literal[g] = e
                    self.tickets[e].append(g)
            else:
                for a in args:
                    if a in literal:
                        self.tickets[literal[a]].append(g)
        self.fees = {e: len(slots)-1 for e, slots in self.tickets.items()}
        assert all(weight >= 0 for weight in self.fees.values())
        self.head = {e: self.reads[w][0] for e, w in dag.inputs.items() if self.fees[e] == 0}
        assert len(set(self.head.values())) == len(self.head)
        for e, h in self.head.items():
            op, a, b = dag.nodes[h]
            assert op in ('and', 'or')
            assert (b if a == dag.inputs[e] else a) not in literal
        self.repeated_tickets = [(e, g) for e, slots in self.tickets.items() if self.fees[e]
                                 for g in slots]
        self.first_head = {}
        candidates = set(self.head.values())
        for g in sorted(self.gates, reverse=True):
            if g in candidates:
                self.first_head[g] = g
            elif g == out:
                self.first_head[g] = None
            else:
                self.first_head[g] = self.first_head[self.reads[g][0]]
        self.repeated = len(dag.edges) - len(self.head)
        self.total_fee = sum(self.fees.values())
        assert len(self.repeated_tickets) == self.total_fee + self.repeated
        assert all(uses[w] >= 1 for w in dag.inputs.values())

    def reachable_after_cut(self, stops):
        active, leaves = set(), set()
        todo = [self.out]
        while todo:
            g = todo.pop()
            if g in stops or self.dag.nodes[g][0] == 'input':
                leaves.add(g)
            elif g not in active:
                active.add(g)
                todo.extend(self.dag.nodes[g][1:])
        return active, leaves

    def check_cut(self, selected, fixed, small, image):
        dag = self.dag
        stops = {self.head[e] for e in selected}
        active, leaves = self.reachable_after_cut(stops)
        assert leaves == stops | {dag.inputs[e] for e in dag.edges if e not in selected}
        pruned = self.gates - active - stops
        lost = 0
        for e, g in self.repeated_tickets:
            assert g not in stops
            if g in pruned:
                assert self.first_head[g] in stops
                lost += e in fixed
        assert lost <= 2 * len(pruned)

        replay = {dag.inputs[e]: image[dag.inputs[e]] for e in dag.edges if e not in selected}
        for h in stops:
            replay[h] = int(dag.nodes[h][0] == 'or')
            assert replay[h] == image[h]
        for g in sorted(active):
            op, *args = dag.nodes[g]
            replay[g] = (small.neg(replay[args[0]]) if op == 'not' else
                         small.gate(op, replay[args[0]], replay[args[1]]))
        assert replay[self.out] == image[self.out]
        fees = sum(self.fees[e] for e in fixed)
        actual = len(self.gates) - small.size(image[self.out])
        assert actual >= len(fixed) + fees + len(stops) + len(pruned) - lost
        return len(stops), lost, actual


def check_pair_averages(dag, out, name):
    profile = ReaderProfile(dag, out)
    m = dag.order // 2
    beta = Fraction(1, 4*m-2)
    alpha = (m-1)*beta
    p = (3*m-1)*beta
    and_inputs = {e for e, h in profile.head.items() if dag.nodes[h][0] == 'and'}
    or_inputs = set(profile.head) - and_inputs
    totals = {'matching': Counter(), 'rectangle': Counter()}
    for pairs in pairings(m):
        matching, free = allowed(pairs)
        fixed = set(dag.edges) - free
        left, right = zip(*pairs)
        block = {(a, b) for a in left for b in right}
        small, image = dag.contract(pairs)
        chosen_ones = or_inputs & matching
        for rule, zero_set in [('rectangle', block - matching)] + [
                ('matching', set(zip(left, other))) for other in permutations(right)
                if all(b != c for b, c in zip(right, other))]:
            selected = chosen_ones | (and_inputs & zero_set)
            hits, lost, actual = profile.check_cut(selected, fixed, small, image)
            totals[rule].update(cases=1, hits=hits, lost=lost, actual=actual)
    u = 3*m*m - m
    for rule, counts in totals.items():
        a = beta if rule == 'matching' else alpha
        hits = beta*len(or_inputs) + a*len(and_inputs)
        assert hits * counts['cases'] == counts['hits']
        assert counts['lost'] <= counts['cases'] * a * len(profile.repeated_tickets)
        bound = u + p*profile.total_fee + hits - a*len(profile.repeated_tickets)/2
        assert counts['actual'] >= counts['cases'] * bound
        print(f'{name}, {rule}: {counts["cases"]} cuts, F={profile.total_fee}, '
              f'private AND/OR={len(and_inputs)}/{len(or_inputs)}, '
              f'lost fixed literal positions across cuts={counts["lost"]}, '
              f'certified deletions >= {ceil(bound)}')
    return totals


def masked_circuit(n, concentrated):
    """On a known tour, changing arcs outside that tour preserves Hamiltonicity."""
    base = Circuit(n)
    out = held_karp(base, n)
    dag = Circuit(n)
    mapping = dag.inputs.copy()
    if concentrated:
        tour = directed_cycle(tuple(range(n)))
        guard = dag.fold('and', (dag.inputs[e] for e in sorted(tour)))
        for e in set(dag.edges) - tour:
            mapping[e] = dag.gate('or', dag.inputs[e], guard)
    else:
        marked = [(0, 1), (2, 3), (4, 5)]
        tours = (directed_cycle((0,) + tail) for tail in permutations(range(1, n)))
        eligible = [t for t in tours if t.isdisjoint(marked)]
        for i, e in enumerate(marked):
            tour = eligible[i]
            guard = dag.fold('and', (dag.inputs[f] for f in sorted(tour)))
            mapping[e] = (dag.gate('or', dag.inputs[e], guard) if i % 2 == 0 else
                          dag.gate('and', dag.inputs[e], dag.neg(guard)))
    return dag, base.replay(dag, mapping)[out]


def check_formula_forest(dag, out):
    """Count actual leaf positions of incomparable siblings, including signed input leaves."""
    gates, uses = live_wires(dag, out)
    literals = dict((w, w) for w in dag.inputs.values())
    for g in sorted(gates):
        op, *args = dag.nodes[g]
        if op == 'not' and args[0] in literals:
            literals[g] = args[0]
    signed_uses = defaultdict(list)
    for g in gates:
        if g in literals:
            continue
        for side, operand in enumerate(dag.nodes[g][1:]):
            if operand in literals:
                signed_uses[literals[operand]].append((g, side))
    heads = {uses_of_input[0] for uses_of_input in signed_uses.values() if len(uses_of_input) == 1}
    used_leaves = set()
    wide = cut = 0
    for h, side in heads:
        stack = [(h, 1-side)]
        support = set()
        boundary = False
        while stack:
            g, operand_index = stack.pop()
            operand = dag.nodes[g][1+operand_index]
            if operand in literals or uses[operand] >= 2:
                assert (g, operand_index) not in used_leaves
                used_leaves.add((g, operand_index))
                if operand in literals:
                    wire = literals[operand]
                    assert len(signed_uses[wire]) >= 2
                    support.add(wire)
                else:
                    boundary = True
            else:
                stack.extend((operand, j) for j in range(len(dag.nodes[operand])-1))
        if boundary:
            cut += 1
        else:
            assert len(support) >= dag.order-2
            wide += 1
    signed_extra = sum(len(items)-1 for items in signed_uses.values())
    internal_extra = sum(max(0, uses[g]-1) for g in gates if g not in literals)
    assert cut <= 2*internal_extra and wide*(dag.order-2) <= 2*signed_extra
    print(f'{dag.order}-vertex forest: {cut} siblings have shared leaves, {wide} have only raw leaves')


if __name__ == '__main__':
    for size in (4, 6, 8):
        check_rectangle(size)
    core = Circuit(6)
    dual, root = de_morgan_circuit(core, held_karp(core, 6))
    check_pair_averages(dual, root, 'six-vertex De Morgan')
    for concentrated in (False, True):
        dag, out = masked_circuit(6, concentrated)
        result = check_pair_averages(dag, out, 'one common guard' if concentrated else 'three guards')
        check_formula_forest(dag, out)
        if not concentrated:
            assert all(row['lost'] > 0 for row in result.values())
