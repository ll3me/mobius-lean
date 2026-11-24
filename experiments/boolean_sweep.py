"""Rebuild a shared De Morgan DAG using exact, bounded signatures for each wire.

The passes take only the input order, the topological gate list and the output.
They substitute an earlier wire only after matching exact Boolean functions.
"""
from collections import Counter
from dataclasses import dataclass
from functools import lru_cache
from itertools import combinations
from operator import and_, or_, xor

from paired_contraction import Circuit

DIAGRAM_OP = {'and': and_, 'or': or_, 'not': xor}


def xor_gate(dag, a, b):
    return dag.gate('and', dag.gate('or', a, b), dag.neg(dag.gate('and', a, b)))


def xnor_gate(dag, a, b):
    return dag.gate('or', dag.gate('and', a, b), dag.neg(dag.gate('or', a, b)))


def xor_inputs(dag, wire):
    """The XOR/XNOR patterns in R+, including commuted operands."""
    op, *children = dag.nodes[wire]
    if op not in ('and', 'or'):
        return None
    other = 'or' if op == 'and' else 'and'
    left, right = children
    for positive, negative in ((left, right), (right, left)):
        side = dag.nodes[positive]
        neg = dag.nodes[negative]
        if side[0] == other and neg[0] == 'not':
            twin = dag.nodes[neg[1]]
            if twin[0] == op and side[1:] == twin[1:]:
                return side[1], side[2], int(op == 'or')
    return None


def live_gates(dag, output):
    """Return the reachable gates in their original topological order."""
    first = 2 + len(dag.inputs)
    reached = set()
    pending = [output]
    while pending:
        g = pending.pop()
        if g >= first and g not in reached:
            reached.add(g)
            pending.extend(dag.nodes[g][1:])
    return sorted(reached)


def make_gate(dag, op, args):
    return dag.neg(args[0]) if op == 'not' else dag.gate(op, *args)


@lru_cache(None)
def short_circuits(arity):
    """Truth tables and cheapest programs of at most two gates for a window."""
    patterns = 1 << arity
    ones = (1 << patterns) - 1
    inputs = [0, ones] + [sum(((p >> i) & 1) << p for p in range(patterns))
                          for i in range(arity)]
    best = {table: ((), i) for i, table in enumerate(inputs)}

    def extensions(values):
        for op in ('and', 'not', 'or'):
            for i, a in enumerate(values):
                if op == 'not':
                    yield (op, i), ones ^ a
                else:
                    combine = and_ if op == 'and' else or_
                    for j in range(i+1, len(values)):
                        yield (op, i, j), combine(a, values[j])

    singles = [(gate, table) for gate, table in extensions(inputs) if table not in best]
    for gate, table in singles:
        best.setdefault(table, ((gate,), len(inputs)))
    for gate, table in singles:
        for other, result in extensions(inputs + [table]):
            best.setdefault(result, ((gate, other), len(inputs)+1))
    return inputs, best


def windows_at(dag, root, uses):
    """Connected single-output windows with at most three internal gates."""
    first = len(dag.inputs) + 2
    pending = [(root,)]
    visited = set(pending)
    closed = []
    while pending:
        nodes = pending.pop()
        inner_uses = Counter(a for g in nodes for a in dag.nodes[g][1:])
        if all(inner_uses[g] == uses[g] for g in nodes[:-1]):
            closed.append(nodes)
        if len(nodes) < 3:
            for a in inner_uses:
                if a >= first and a not in nodes:
                    grown = tuple(sorted((*nodes, a)))
                    if grown not in visited:
                        visited.add(grown)
                        pending.append(grown)
    return sorted(closed)


def find_replacement(dag, live):
    uses = Counter(a for g in live for a in dag.nodes[g][1:])
    for root in live:
        for window in windows_at(dag, root, uses):
            boundary = sorted({a for g in window for a in dag.nodes[g][1:] if a not in window})
            inputs, catalog = short_circuits(len(boundary))
            tables = dict(zip(boundary, inputs[2:]))
            for g in window:
                op, *args = dag.nodes[g]
                a = tables[args[0]]
                if op == 'not':
                    tables[g] = inputs[1] ^ a
                else:
                    combine = and_ if op == 'and' else or_
                    tables[g] = combine(a, tables[args[1]])
            program = catalog.get(tables[root])
            if program is not None and len(program[0]) < len(window):
                return root, boundary, program
    return None


def rewrite_windows(dag, output):
    while True:
        live = live_gates(dag, output)
        edit = find_replacement(dag, live)
        if edit is None:
            return dag, output
        target, boundary, (code, index) = edit
        dest = Circuit(dag.order)
        image = {i: i for i in range(2 + len(dag.inputs))}
        for g in live:
            if g == target:
                wires = [0, 1] + [image[a] for a in boundary]
                for op, *args in code:
                    wires.append(make_gate(dest, op, [wires[i] for i in args]))
                image[g] = wires[index]
            else:
                op, *args = dag.nodes[g]
                image[g] = make_gate(dest, op, [image[a] for a in args])
        dag, output = dest, image[output]


def affine_rebuild(dag, output):
    """The affine candidate of R+, including the cost of lowering each XOR."""
    dest = Circuit(dag.order)
    basis = [0, *dest.inputs.values()]
    rows = {0: 0, 1: 1, **{w: 1 << i for i, w in enumerate(basis[1:], 1)}}
    materialized = {row: w for w, row in rows.items()}
    atoms = {}

    def lower(row):
        if row not in materialized:
            wire = 0
            remaining = row & ~1
            while remaining:
                bit = remaining & -remaining
                wire = xor_gate(dest, wire, basis[bit.bit_length()-1])
                remaining ^= bit
            materialized[row] = dest.neg(wire) if row & 1 else wire
        return materialized[row]

    for g in live_gates(dag, output):
        op, *args = dag.nodes[g]
        shape = xor_inputs(dag, g)
        p = rows[args[0]]
        if shape:
            a, b, neg = shape
            row = rows[a] ^ rows[b] ^ neg
        elif op == 'not':
            row = p ^ 1
        else:
            p, q = sorted((p, rows[args[1]]))
            if p < 2:
                row = q if (p == 1 and op == 'and') or (p == 0 and op == 'or') else p
            elif p == q:
                row = p
            elif p ^ q == 1:
                row = int(op == 'or')
            else:
                key = (op, p, q)
                if key not in atoms:
                    wire = dest.gate(op, lower(p), lower(q))
                    row = 1 << len(basis)
                    basis.append(wire)
                    materialized[row] = wire
                    atoms[key] = row
                row = atoms[key]
        rows[g] = row
    return dest, lower(rows[output])


class PolynomialSignatures:
    """Boolean-ring monomials are bit sets of variables. Opaque wires get fresh symbols."""
    zero = frozenset()
    one = frozenset((0,))

    def __init__(self, limit):
        if limit < 1:
            raise ValueError('at least one monomial is required')
        self.limit = limit
        self.variables = 0

    def atom(self):
        monomial = 1 << self.variables
        self.variables += 1
        return frozenset((monomial,))

    def gate(self, dag, w, forms):
        op, *args = dag.nodes[w]
        p = forms[args[0]]
        shape = xor_inputs(dag, w)
        if shape:
            a, b, neg = shape
            row = forms[a] ^ forms[b]
            if neg:
                row ^= self.one
        elif op == 'not':
            row = p ^ self.one
        else:
            q = forms[args[1]]
            product = set()
            for a in p:
                for b in q:
                    product.symmetric_difference_update((a | b,))
            row = frozenset(product)
            if op == 'or':
                row = row ^ p ^ q
        return row if len(row) <= self.limit else self.atom()


class DiagramSignatures:
    """Reduced ordered binary decision diagrams, with a fixed cap per wire."""
    zero = 0
    one = 1

    def __init__(self, limit):
        if limit < 1:
            raise ValueError('at least one decision node is required')
        self.limit = limit
        self.nodes = [None, None]
        self.keys = {}
        self.variables = 0

    def node(self, variable, low, high):
        if low == high:
            return low
        key = (variable, low, high)
        if key not in self.keys:
            self.keys[key] = len(self.nodes)
            self.nodes.append(key)
        return self.keys[key]

    def atom(self):
        variable = self.variables
        self.variables += 1
        return self.node(variable, 0, 1)

    def gate(self, dag, w, forms):
        op, *args = dag.nodes[w]
        a = forms[args[0]]
        b = self.one if op == 'not' else forms[args[1]]
        combine = DIAGRAM_OP[op]
        memo = {}
        visited = set()

        # Evaluate both cofactors before the parent. A finite cap can still
        # give a path deeper than Python's call stack when two inputs combine.
        root = tuple(sorted((a, b)))
        pending = [root]
        while pending:
            key = pending[-1]
            x, y = key
            if key in memo:
                pending.pop()
                continue
            if y < 2:
                memo[key] = combine(x, y)
                continue
            variable = min(self.nodes[z][0] for z in key if z >= 2)
            x0, x1 = self.cofactors(x, variable)
            y0, y1 = self.cofactors(y, variable)
            low = tuple(sorted((x0, y0)))
            high = tuple(sorted((x1, y1)))
            if low not in memo:
                pending.append(low)
            elif high not in memo:
                pending.append(high)
            else:
                result = self.node(variable, memo[low], memo[high])
                if result >= 2:
                    visited.add(result)
                    if len(visited) > self.limit:
                        return self.atom()
                memo[key] = result
        return memo[root]

    def cofactors(self, node, variable):
        if node >= 2 and self.nodes[node][0] == variable:
            return self.nodes[node][1:]
        return node, node


@dataclass
class SweepCounts:
    positions: int
    paid_classes: int
    shared_redirects: int
    cutoff_atoms: int


def sweep(dag, output, signatures):
    """Each certified equal wire redirects to the earliest available representative."""
    dest = Circuit(dag.order)
    first = len(dag.inputs) + 2
    image = {i: i for i in range(first)}
    forms = [signatures.zero, signatures.one] + [signatures.atom() for _ in dag.inputs]
    representatives = {p: i for i, p in enumerate(forms)}
    live = live_gates(dag, output)
    uses = Counter(a for g in live for a in dag.nodes[g][1:])
    classes = set()
    shared_redirects = 0
    for g in live:
        op, *args = dag.nodes[g]
        wire = make_gate(dest, op, [image[a] for a in args])
        if wire == len(forms):
            forms.append(signatures.gate(dest, wire, forms))
        key = forms[wire]
        classes.add(key)
        previous = representatives.setdefault(key, wire)
        if wire != previous and uses[g] >= 2:
            shared_redirects += 1
        image[g] = previous
    classes.difference_update(forms[:first])
    counts = SweepCounts(len(live), len(classes), shared_redirects,
                         signatures.variables - len(dag.inputs))
    return dest, image[output], counts


def private_parities(dag, output):
    """Find maximal private standard-block trees on distinct raw inputs."""
    live = live_gates(dag, output)
    uses = Counter(a for g in live for a in dag.nodes[g][1:])
    first = 2 + len(dag.inputs)
    rows = {wire: (1 << i, 0) for i, wire in enumerate(dag.inputs.values())}
    absorbed = set()
    for g in live:
        shape = xor_inputs(dag, g)
        if shape is None:
            continue
        a, b, sign = shape
        if a not in rows or b not in rows:
            continue
        left, right = dag.nodes[g][1:]
        negative = left if dag.nodes[left][0] == 'not' else right
        opposite = dag.nodes[negative][1]
        if any(uses[k] != 1 for k in (left, right, opposite)):
            continue
        if any(k >= first and uses[k] != 2 for k in (a, b)):
            continue
        p, pa = rows[a]
        q, pb = rows[b]
        if p & q:
            continue
        rows[g] = p | q, pa ^ pb ^ sign
        absorbed.update((a, b))
    return {g: row for g, row in rows.items() if g >= first and g not in absorbed}


def rebuild_private_parities(dag, output, pairs, regions):
    dest = Circuit(len(pairs))
    mapping = dict.fromkeys(dag.edges, 0)
    for i, (entry, exit_vertex) in enumerate(pairs):
        mapping[entry, exit_vertex] = 1
        for j, (other, _) in enumerate(pairs):
            if i != j:
                mapping[exit_vertex, other] = dest.inputs[i, j]
    raw = [mapping[e] for e in dag.edges]
    image = {i: wire for i, wire in enumerate([0, 1, *raw])}

    # Region interiors have no external readers. Only their roots and the
    # outside gates need replaying.
    keep = set()
    pending = [output]
    while pending:
        g = pending.pop()
        if g not in image and g not in keep:
            keep.add(g)
            if g not in regions:
                pending.extend(dag.nodes[g][1:])
    for g in sorted(keep):
        if g not in regions:
            op, *args = dag.nodes[g]
            image[g] = make_gate(dest, op, [image[a] for a in args])
            continue
        support, sign = regions[g]
        free = []
        while support:
            bit = support & -support
            wire = raw[bit.bit_length()-1]
            if wire < 2:
                sign ^= wire
            else:
                free.append(wire)
            support ^= bit
        if len(free) < 2:
            wire = free[0] if free else 0
            image[g] = dest.neg(wire) if sign else wire
        else:
            acc = free[0]
            for wire in free[1:-1]:
                acc = xor_gate(dest, acc, wire)
            last = free[-1]
            final_gate = xnor_gate if sign else xor_gate
            image[g] = final_gate(dest, acc, last)
    return dest, image[output]
