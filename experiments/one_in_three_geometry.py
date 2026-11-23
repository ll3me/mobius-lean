"""Compile positive 1-in-3 to an unweighted set of genuine signed XOR squares.

Input JSON is a list of clauses, each a list of three positive-literal variable
identifiers (nonnegative integers, repetitions allowed). Output coordinates
are ordinary bit vectors written as integers. Each square [x,y,d] asks for
odd parity on its two row and two column entries. The decision threshold is
the maximum allowed number of failed squares. No port labels or block
metadata are needed by the target verifier.
"""
import argparse
from collections import Counter, defaultdict
from dataclasses import dataclass
from itertools import product
import json
from pathlib import Path

from optimal_support import template

SQUARES = tuple(template(True))
PORTS = (0, 2, 5)
ENDS = (0, 11)


def corners(square):
    x, y, d = square
    return ((0, x, y), (0, x ^ d, y ^ d), (1, x, y ^ d), (1, x ^ d, y))


def canonical(square):
    x, y, d = square
    return min((x, y, d), (x ^ d, y ^ d, d))


def wire(source, target):
    """A common linear map on both coordinates, plus two anchor translations."""
    x, y, d = source
    u, v, e = target
    linear = {0: 0}
    for basis, image in zip((2, 12, 4, 13), (d, e, x ^ u, y ^ v)):
        linear.update({z ^ basis: value ^ image for z, value in linear.items()})
    assert len(set(linear.values())) == 16
    chart = [(x ^ linear[i], y ^ linear[5] ^ linear[j], linear[h]) for i, j, h in SQUARES]
    assert (chart[ENDS[0]], chart[ENDS[1]]) == (source, target)
    return chart


class Space:
    def __init__(self):
        self.width = 0

    def port(self):
        start = self.width
        self.width += 3
        return tuple(1 << (start + i) for i in range(3))

    def block(self):
        start = self.width
        self.width += 6
        return [((16 ^ x) << start, (32 ^ y) << start, d << start) for x, y, d in SQUARES]


def compress(points, width):
    """Choose linear-map columns so each coordinate pair stays distinguishable.

    A pair forbids a value only when processing its highest differing bit.
    The least allowed column is at most the number of unordered pairs.
    """
    values = dict.fromkeys(points, 0)
    for bit in range(width):
        groups = defaultdict(lambda: ([], []))
        for point, value in values.items():
            groups[point >> (bit + 1)][(point >> bit) & 1].append(value)
        forbidden = {a ^ b for low, high in groups.values() for a in low for b in high}
        column = 0
        while column in forbidden:
            column += 1
        for point in values:
            if (point >> bit) & 1:
                values[point] ^= column
    assert len(set(values.values())) == len(values)
    return values


class SquareSet:
    """Collect selected faces while preserving all active chart coordinates."""
    def __init__(self):
        self.rows = []
        self.points = set()

    def select(self, chart, omit=()):
        for i, square in enumerate(chart):
            x, y, d = square
            self.points.update((x, y, x ^ d, y ^ d))
            if i not in omit:
                self.rows.append(square)

    def compressed(self, width):
        mapped = compress(self.points, width)

        def project(square):
            x, y, d = square
            direction = mapped[x] ^ mapped[x ^ d]
            assert direction and direction == mapped[y] ^ mapped[y ^ d]
            return canonical((mapped[x], mapped[y], direction))

        squares = [project(square) for square in self.rows]
        assert len(squares) == len(set(squares))
        bits = max(mapped.values(), default=0).bit_length()
        assert bits <= (len(mapped) * (len(mapped) - 1) // 2).bit_length()
        return bits, squares, project


@dataclass
class Instance:
    width: int
    squares: list
    threshold: int
    clause_rows: list
    variable_ports: dict

    def data(self):
        return dict(width=self.width, squares=self.squares, threshold=self.threshold)


def compile_formula(clauses):
    if not isinstance(clauses, (tuple, list)) or any(
        not isinstance(clause, (tuple, list)) or len(clause) != 3 or
        any(type(v) is not int or v < 0 for v in clause) for clause in clauses
    ):
        raise ValueError('Expected a list of three-variable clauses with nonnegative integer identifiers')
    space = Space()
    variables = {v: space.port() for v in sorted({v for clause in clauses for v in clause})}
    target = SquareSet()
    clause_rows = []
    for clause in clauses:
        block = space.block()
        clause_rows.append(range(len(target.rows), len(target.rows) + 15))
        target.select(block)
        for i, v in zip(PORTS, clause):
            relay = space.port()
            target.select(wire(block[i], relay), ENDS)
            target.select(wire(relay, variables[v]), ENDS)
        for i, interior in enumerate(block):
            if i in PORTS:
                continue
            pin = space.block()
            target.select(pin, (0,))
            target.select(wire(interior, pin[0]), ENDS)

    m = len(clauses)
    assert space.width == 3 * len(variables) + 87 * m
    width, squares, project = target.compressed(space.width)
    assert len(squares) == 417 * m
    return Instance(width, squares, m, clause_rows, {v: project(sq) for v, sq in variables.items()})


def syndromes(squares):
    """Eliminate the actual phase bits and retain parity constraints on defects."""
    cell_ids, basis, dependencies = {}, {}, []
    for index, square in enumerate(squares):
        equation = 0
        for cell in corners(square):
            equation ^= 1 << cell_ids.setdefault(cell, len(cell_ids))
        history = 1 << index
        while equation:
            pivot = equation.bit_length() - 1
            if pivot not in basis:
                basis[pivot] = (equation, history)
                break
            previous, proof = basis[pivot]
            equation ^= previous
            history ^= proof
        if not equation:
            dependencies.append(history)
    columns = [0] * len(squares)
    needed = 0
    for i, history in enumerate(dependencies):
        if history.bit_count() % 2:
            needed |= 1 << i
        while history:
            low = history & -history
            columns[low.bit_length() - 1] |= 1 << i
            history ^= low
    return needed, columns, len(basis)


def check_threshold(clauses):
    """Compare all assignments with threshold feasibility of the emitted squares.

    Each disjoint 15-face clause must fail, so at threshold precisely one face
    from each such clause and no other selected face may fail. We test all
    15 choices per clause using the GF(2) dependencies of the entire output.
    """
    instance = compile_formula(clauses)
    keys = sorted(instance.variable_ports)
    rows = instance.squares + [instance.variable_ports[v] for v in keys]
    target, columns, _ = syndromes(rows)
    possible = {0}
    for group in instance.clause_rows:
        possible = {s ^ columns[i] for s in possible for i in group}
    # These checks use the emitted square set alone, including unsatisfiable inputs.
    frequencies = Counter(c for sq in instance.squares for c in corners(sq))
    occurrences = Counter(v for clause in clauses for v in clause)
    _, _, rank = syndromes(instance.squares)
    assert len(frequencies) == 798 * len(clauses) + 4 * len(keys)
    assert len(frequencies) - rank == 397 * len(clauses) + 3 * len(keys)
    assert max(frequencies.values(), default=0) <= max(4, max(occurrences.values(), default=0))
    accepts = 0
    for bits in product((0, 1), repeat=len(keys)):
        assignment = dict(zip(keys, bits))
        expected = all(sum(assignment[v] for v in clause) == 1 for clause in clauses)
        rhs = target
        for i, b in enumerate(bits, len(instance.squares)):
            if b:
                rhs ^= columns[i]
        assert (rhs in possible) == expected, (clauses, assignment)
        # Build an exact-cost syndrome: one bad clause port and, for each
        # disagreeing occurrence, the second template face of its first wire.
        defects = []
        for clause, group in zip(clauses, instance.clause_rows):
            values = [assignment[v] for v in clause]
            chosen = next((j for j, value in enumerate(values) if value), 0)
            defects.append(group[PORTS[chosen]])
            for j, value in enumerate(values):
                if value != (j == chosen):
                    defects.append(group.stop + 26 * j)
        assert len(defects) == len(clauses) + sum(abs(sum(assignment[v] for v in c) - 1) for c in clauses)
        for row in defects:
            rhs ^= columns[row]
        assert rhs == 0, 'A claimed attaining phase assignment failed the independent elimination'
        accepts += expected
    return instance, accepts


def check_single_clause_cost():
    """Independently test all eight optima by allowing arbitrary faulty rows."""
    instance = compile_formula([(0, 1, 2)])
    rows = instance.squares + list(instance.variable_ports.values())
    target, columns, _ = syndromes(rows)
    singles = set(columns[:len(instance.squares)])
    pairs = {a ^ b for a in singles for b in singles}
    for bits in product((0, 1), repeat=3):
        rhs = target
        for i, b in enumerate(bits, len(instance.squares)):
            if b:
                rhs ^= columns[i]
        if rhs == 0:
            cost = 0
        elif rhs in singles:
            cost = 1
        elif rhs in pairs:
            cost = 2
        else:
            assert any(rhs ^ a in pairs for a in singles)
            cost = 3
        assert cost == 1 + abs(sum(bits) - 1)
    print('Single-clause minimum failures by Hamming weight 0,1,2,3: 2,1,2,3.')


def self_check():
    cases = [
        ([], 1),
        ([(0, 0, 0)], 0),
        ([(0, 0, 1)], 1),
        ([(0, 1, 2), (0, 3, 4)], 5),
        ([(0, 1, 2), (2, 3, 4), (4, 5, 0)], 4),
        ([(0, 1, 2), (0, 1, 3), (0, 2, 3), (1, 2, 3)], 0),
    ]
    for clauses, expected in cases:
        instance, accepts = check_threshold(clauses)
        assert accepts == expected
        print(f'{len(clauses)} clauses: {len(instance.squares)} distinct squares, width {instance.width}, '
              f'{accepts} satisfying assignments at threshold {instance.threshold}.')
    check_single_clause_cost()


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('formula', nargs='?', type=Path, help='input JSON; omit to run the exact finite checks')
    args = parser.parse_args()
    if args.formula is None:
        self_check()
    else:
        print(json.dumps(compile_formula(json.loads(args.formula.read_text())).data()))
