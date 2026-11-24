"""Directed Hamiltonicity on full four-dimensional boards with one physical bit per arc."""
from collections import Counter, defaultdict
from itertools import permutations, product
from pathlib import Path
from shutil import which
from subprocess import run

from face_multiplicity import equality_lines, line
from free_direction_coloring import (attachment_coordinates, costs_on_one_world,
                                     lines3, solve_attachment)
from port_k4 import phase3
from read_bounded_boards import Circuit, PinnedCircuitRows


def arcs(m):
    if m < 2:
        raise ValueError("at least two vertices are required")
    return [(u, v) for u in range(m) for v in range(m) if u != v]


def less_than(dag, left, right):
    """Unsigned comparison, adding successively more significant bit pairs."""
    result = dag.both(dag.neg(left[0]), right[0])
    for a, b in zip(left[1:], right[1:]):
        lower = dag.both(dag.neg(a), b)
        at_most = dag.either(dag.neg(a), b)
        result = dag.either(lower, dag.both(at_most, result))
    return result


def verifier(m):
    edges = arcs(m)
    width = max(1, (m - 2).bit_length())
    dag = Circuit(len(edges) + (m - 1) * width)
    checks = []

    def exactly_one(wires):
        seen = wires[0]
        for wire in wires[1:]:
            checks.append(dag.neg(dag.both(seen, wire)))
            seen = dag.either(seen, wire)
        checks.append(seen)

    for vertex in range(m):
        exactly_one([i for i, (u, _) in enumerate(edges) if u == vertex])
        exactly_one([i for i, (_, v) in enumerate(edges) if v == vertex])
    ranks = {u: range(len(edges) + (u - 1) * width, len(edges) + u * width)
             for u in range(1, m)}
    for i, (u, v) in enumerate(edges):
        if u != 0 and v != 0:
            checks.append(dag.either(dag.neg(i), less_than(dag, ranks[u], ranks[v])))
    out = checks[0]
    for wire in checks[1:]:
        out = dag.both(out, wire)
    # All DAG inputs are private witness wires. Only the geometric arc blocks
    # below read the mask. In particular, an open edge need not be selected.
    return PinnedCircuitRows(dag, out, symbol_gates=())


class BoardFamily:
    def __init__(self, m):
        self.edges = arcs(m)
        self.checker = verifier(m)
        self.dimension = 2
        self.fixed = []
        self.switches = []

        copies = defaultdict(list)
        for row_number, variables in enumerate(self.checker.templates):
            a, b = self.axis(), self.axis()
            self.fixed.append((1, 2, a, b))
            for variable, point in zip(variables, (a, b, a ^ b)):
                copies[variable].append((row_number, point))

        def equal(a, b):
            t, f, j = self.axis(), self.axis(), self.axis()
            self.fixed.extend((1, 2, p, q) for p, q, _ in equality_lines(a, b, t, f, j))

        for occurrences in copies.values():
            for (i, a), (j, b) in zip(occurrences, occurrences[1:]):
                if i == j:
                    # The sum of two points in one row is its third point.
                    relay = self.axis()
                    equal(a, relay)
                    equal(relay, b)
                else:
                    equal(a, b)

        for index in range(len(self.edges)):
            port = copies[3 + 2 * index][-1][1]  # positive DAG input
            p, f, j, toggle = self.axis(), self.axis(), self.axis(), self.axis()
            self.fixed.extend((1, 2, a, b) for a, b, c in lines3((p, f, j))
                              if (a, b, c) != line(p, f))
            self.switches.append((p, port, toggle))
        h, k, t = self.axis(), self.axis(), self.axis()
        self.aux = (h, k, t)
        self.attachment = [(h, k, a, b) for a, b, _ in lines3((1, 2, t))]

    def axis(self):
        result = 1 << self.dimension
        self.dimension += 1
        return result

    def boards(self, mask):
        if not 0 <= mask < 1 << len(self.edges):
            raise ValueError("edge mask outside this family")
        switches = [(1, 2, p, port ^ (toggle if (mask >> i) & 1 else 0))
                    for i, (p, port, toggle) in enumerate(self.switches)]
        return self.fixed + switches + self.attachment

    @property
    def field_bytes(self):
        return (self.dimension + 7) // 8

    def pack(self, mask):
        return b''.join(axis.to_bytes(self.field_bytes, 'little')
                        for board in self.boards(mask) for axis in board)

    def bit_positions(self):
        return [(4 * (len(self.fixed) + i) + 3) * (8 * self.field_bytes)
                + toggle.bit_length() - 1 for i, (_, _, toggle) in enumerate(self.switches)]


def cycle_masks(m):
    indices = {edge: i for i, edge in enumerate(arcs(m))}
    tours = []
    for tail in permutations(range(1, m)):
        order = (0,) + tail
        tours.append(sum(1 << indices[u, v] for u, v in zip(order, order[1:] + (0,))))
    return tours


def connected_cover(outgoing, incoming):
    """Strong connectivity and a perfect matching between tails and heads."""
    n = len(outgoing)
    for graph in (outgoing, incoming):
        seen = {0}
        todo = [0]
        while todo:
            for v in graph[todo.pop()]:
                if v not in seen:
                    seen.add(v)
                    todo.append(v)
        if len(seen) != n:
            return False
    left_mate, right_mate = [None] * n, [None] * n
    for start in range(n):
        parent, todo, end = {}, [start], None
        while todo and end is None:
            u = todo.pop()
            for v in outgoing[u]:
                if v in parent:
                    continue
                parent[v] = u
                if right_mate[v] is None:
                    end = v
                    break
                todo.append(right_mate[v])
        if end is None:
            return False
        while end is not None:
            u = parent[end]
            old = left_mate[u]
            left_mate[u], right_mate[end] = end, u
            end = old
    return True


def sparse_decision(m, mask, extra):
    """A monotone polynomial-time decision for extra = O(log m)."""
    outgoing = [[] for _ in range(m)]
    incoming = [[] for _ in range(m)]
    for i, (u, v) in enumerate(arcs(m)):
        if (mask >> i) & 1:
            outgoing[u].append(v)
            incoming[v].append(u)
    if mask.bit_count() > m + extra:
        return connected_cover(outgoing, incoming)
    if not all(outgoing):
        return False
    for successor in product(*outgoing):
        seen, u = set(), 0
        while u not in seen:
            seen.add(u)
            u = successor[u]
        if u == 0 and len(seen) == m:
            return True
    return False


def coefficients(truth_table):
    result = list(map(int, truth_table))
    stride = 1
    while stride < len(result):
        for start in range(stride, len(result), 2 * stride):
            for i in range(start, start + stride):
                result[i] -= result[i - stride]
        stride *= 2
    return result


def witness_table(family):
    """Evaluate all edge selections simultaneously; enumerate every rank assignment."""
    checker = family.checker
    edge_bits = len(family.edges)
    size = 1 << edge_bits
    full = (1 << size) - 1
    inputs = [sum(1 << s for s in range(size) if (s >> i) & 1) for i in range(edge_bits)]
    rank_bits = checker.dag.inputs - edge_bits
    accepted = 0
    for ranks in range(1 << rank_bits):
        values = inputs + [full if (ranks >> i) & 1 else 0 for i in range(rank_bits)]
        for op, *args in checker.dag.ops[checker.dag.inputs:]:
            if op == 'not':
                values.append(full ^ values[args[0]])
            else:
                values.append(values[args[0]] & values[args[1]])
        accepted |= values[checker.out]
    return [s for s in range(size) if (accepted >> s) & 1]


def check_slices(m, family, geometric_tours):
    tours = set(cycle_masks(m))
    assert geometric_tours == set(witness_table(family)) == tours
    truth = [any(s & mask == s for s in tours) for mask in range(1 << len(family.edges))]
    coeff = coefficients(truth)
    for s, value in enumerate(coeff):
        if s.bit_count() <= m:
            assert value == int(s in tours)
    overlaps = {p | q for p in tours for q in tours if p != q and (p | q).bit_count() == m + 3}
    for s, value in enumerate(coeff):
        if m < s.bit_count() <= m + 3:
            assert value == -int(s in overlaps)
    for extra in (0, 1, 2, 3):
        easy = [sparse_decision(m, s, extra) for s in range(len(truth))]
        other = coefficients(easy)
        assert all(coeff[s] == other[s] for s in range(len(truth)) if s.bit_count() <= m + extra)
        assert all(easy[s | (1 << i)] for s, yes in enumerate(easy) if yes
                   for i in range(len(family.edges)))
    if m == 4:
        # Bidirected triangle 0,1,2 with vertex 3 attached only to 0.
        joined = sum(1 << i for i, (u, v) in enumerate(family.edges)
                     if max(u, v) < 3 or min(u, v) == 0)
        assert joined.bit_count() == 8 and easy[joined] and not truth[joined]
    print(f'm={m}: {len(truth)} masks, {len(tours)} cycle monomials, '
          f'{len(overlaps)} first pair overlaps; sparse cutoffs 0 through 3')


def decoded_boards(family, mask):
    data = memoryview(family.pack(mask))
    w = family.field_bytes
    return [tuple(int.from_bytes(data[i+j*w:i+(j+1)*w], 'little') for j in range(4))
            for i in range(0, len(data), 4*w)]


def geometry(family, mask, solver, check_tables=False):
    boards = decoded_boards(family, mask)
    assert boards == family.boards(mask)
    rows = [line(a, b) for u, v, a, b in boards[:-7] if (u, v) == (1, 2)]
    assert len(set(rows)) == len(rows) == len(boards) - 7
    assert max(Counter(p for row in rows for p in row).values()) <= 3
    ids = {p: i+1 for i, p in enumerate(sorted({p for row in rows for p in row}))}
    clauses = []
    for row in rows:
        a, b, c = (ids[p] for p in row)
        clauses.extend(((a, b, c), (-a, -b), (-a, -c), (-b, -c)))
    port_ids = [ids[p] for _, p, _ in family.switches]
    models = set()
    while True:
        body = '\n'.join(' '.join(map(str, row)) + ' 0' for row in clauses)
        result = run([solver, '-q'], input=f'p cnf {len(ids)} {len(clauses)}\n{body}\n',
                     text=True, capture_output=True)
        if result.returncode == 20:
            break
        if result.returncode != 10:
            raise RuntimeError(f'CaDiCaL exited with {result.returncode}: {result.stderr}')
        true_ids = {int(t) for row in result.stdout.splitlines() if row.startswith('v ')
                    for t in row.split()[1:] if int(t) > 0}
        marked = {p for p, i in ids.items() if i in true_ids}
        assert all(sum(p in marked for p in row) == 1 for row in rows)
        selected = sum(1 << i for i, v in enumerate(port_ids) if v in true_ids)
        assert selected not in models and (selected & mask) == selected
        models.add(selected)
        clauses.append(tuple(-v if v in true_ids else v for v in port_ids))
    if check_tables and models:
        def image(x):
            p = x & ~3
            return (x & 3) | (4 if p and p not in marked else 0)

        cap = solve_attachment()

        def cap_table(tag, x, y):
            return cap[tag, attachment_coordinates(x, family.aux),
                       attachment_coordinates(y, family.aux)]

        _, costs = costs_on_one_world([
            (boards[:-7], lambda tag, x, y: phase3(image(x), image(y))),
            (boards[-7:], cap_table)])
        assert costs == [128] * len(boards)
    return models


def check_bits(family):
    first = family.pack(0)
    positions = family.bit_positions()
    assert len(set(positions)) == len(positions)
    expected = bytearray(first)
    for i, p in enumerate(positions):
        assert not (first[p // 8] & (1 << (p % 8)))
        expected[p // 8] ^= 1 << (p % 8)
        assert expected == family.pack(1 << i)
        expected[p // 8] ^= 1 << (p % 8)
    for p in positions:
        expected[p // 8] ^= 1 << (p % 8)
    assert expected == family.pack((1 << len(positions)) - 1)
    return len(first) * 8


def sat_solver():
    solver = which('cadical')
    if not solver:
        local = Path(__file__).resolve().parents[1] / '.toolchain' / 'bin' / 'cadical'
        if local.is_file():
            solver = str(local)
        else:
            prefix = run(['lean', '--print-prefix'], check=True, capture_output=True, text=True)
            solver = str(Path(prefix.stdout.strip()) / 'bin' / 'cadical')
    return solver


def main():
    solver = sat_solver()
    for m in (2, 3, 4):
        family = BoardFamily(m)
        tours = geometry(family, (1 << len(family.edges)) - 1, solver, check_tables=(m == 2))
        check_slices(m, family, tours)
        length = check_bits(family)
        example = cycle_masks(m)[0]
        if m <= 3:
            for mask in range(1 << len(family.edges)):
                assert geometry(family, mask, solver) == {t for t in tours if t & mask == t}
        else:
            # Two disjoint directed 2-cycles pass every in/out-degree test.
            pairs = {(0, 1), (1, 0), (2, 3), (3, 2)}
            subtour = sum(1 << i for i, e in enumerate(family.edges) if e in pairs)
            assert not geometry(family, subtour, solver)
            assert geometry(family, example, solver) == {example}
        print(f'  {len(family.boards(0))} full boards, dimension {family.dimension}, '
              f'{length} input bits, {len(family.edges)} distinct switch positions')


if __name__ == '__main__':
    main()
