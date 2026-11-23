"""Unweighted signed-square budget for cubic positive 1-in-3 instances.

Each of m triples has three occurrences, and every named variable occurs
exactly three times (repetitions count). A satisfying source assignment then
has m/3 true variables. The target has 104m distinct odd-square constraints,
maximum tagged-cell frequency three, and budget floor(m/3). Output JSON needs
only width, squares and threshold; variable ports below are an audit aid.

Run `python3 -B experiments/cubic_ports.py` to check the small instances, or
pass a JSON file of triples to print the compiled target. Independent syndrome
checks on small instances try *all* allowed failed rows for every assignment.

Correctness uses disjoint charges. When a true variable's distinguished
relay is true it violates its first NOT, and when that relay is false its
14-face pin must pay. An all-false clause must pay in its twelve interior
faces or on one of its three paths from false variables. These latter costs
are disjoint from every true-variable charge and from other clauses' paths.
Writing T for the number of true variables, Z for all-false clauses, and b
for paid faces, gives b >= T+Z and 3T >= m-Z, hence 3b >= m+2Z. At budget
floor(m/3) this forces Z=0, T=m/3 and exactly one true occurrence per clause.
Conversely a satisfying assignment permits all clause/wire interiors to
succeed; the one distinguished pin per true variable pays once. All these
claims refer only to the listed squares, leaving the rest of the tables free.
"""
import argparse
from collections import Counter, defaultdict
from dataclasses import dataclass
from itertools import combinations, product
import json
from pathlib import Path

from one_in_three_geometry import ENDS, PORTS, Space, SquareSet, corners, syndromes, wire


@dataclass
class CubicInstance:
    width: int
    squares: list
    threshold: int
    variables: dict
    pin_fault: dict

    def data(self):
        return {'width': self.width, 'squares': self.squares, 'threshold': self.threshold}


def compile_cubic(clauses):
    if not isinstance(clauses, (list, tuple)) or any(
        not isinstance(c, (list, tuple)) or len(c) != 3 or
        any(type(v) is not int or v < 0 for v in c) for c in clauses
    ):
        raise ValueError('expected an array of triples of nonnegative integer variable names')
    counts = Counter(v for c in clauses for v in c)
    if any(k != 3 for k in counts.values()):
        raise ValueError('each named variable must occur exactly three times')
    m = len(clauses)
    assert len(counts) == m
    space = Space()
    variables = {v: space.port() for v in sorted(counts)}
    target = SquareSet()
    pin_fault, pinned_ports = {}, []
    for clause in clauses:
        local = space.block()
        target.select(local, PORTS)
        for var, port in zip(clause, PORTS):
            if var not in pin_fault:
                pin = space.block()
                relay = pin[ENDS[0]]
                pinned_ports.append(relay)
                pin_fault[var] = len(target.rows)  # first selected row of this pin
                target.select(pin, (ENDS[0],))
            else:
                relay = space.port()
            target.select(wire(variables[var], relay), ENDS)
            target.select(wire(relay, local[port]), ENDS)
    assert len(target.rows) == 12*m + 13*6*m + 14*m == 104*m
    assert space.width == 3*m + 6*m + 6*m + 3*(2*m)
    width, out, project = target.compressed(space.width)
    projected_variables = {v: project(sq) for v,sq in variables.items()}
    assert len(set(out)) == 104*m
    assert len(set(projected_variables.values())) == m and not set(out).intersection(projected_variables.values())
    cell_counts = Counter(cell for sq in out for cell in corners(sq))
    expected = Counter({2: 196*m, 3: 8*m}) if m else Counter()
    assert Counter(cell_counts.values()) == expected
    assert {c for c, k in cell_counts.items() if k == 3} == {
        c for sq in [*variables.values(), *pinned_ports] for c in corners(project(sq))}
    assert len(target.points) <= 480*m  # 8m charts, 15 squares, four coordinate values apiece
    assert width <= (len(target.points)*(len(target.points)-1)//2).bit_length()
    return CubicInstance(width,out,m//3,projected_variables,pin_fault)


def min_frequency_two(squares):
    """Exact minimum when each tagged cell appears at most twice.

    Cells of frequency two give graph edges between constraint vertices; a
    cell of frequency one gives a freely selectable half-edge. A component
    with such a half-edge can meet every parity. In a component with none,
    the sum of the parity demands must be even; otherwise one failed vertex
    is necessary and sufficient. A spanning tree realizes any such demand.
    """
    uses = defaultdict(list)
    for j, sq in enumerate(squares):
        if sq[2] == 0:
            raise ValueError('a nonzero square direction is required')
        for cell in corners(sq):
            uses[cell].append(j)
    graph = [[] for _ in squares]
    free = set()
    for owners in uses.values():
        if len(owners) == 1:
            free.add(owners[0])
        elif len(owners) == 2:
            u, v = owners
            graph[u].append(v)
            graph[v].append(u)
        else:
            raise ValueError('tagged-cell frequency exceeds two')
    visited = set()
    cost = 0
    for start in range(len(graph)):
        if start in visited:
            continue
        visited.add(start)
        part = [start]
        for v in part:
            for w in graph[v]:
                if w not in visited:
                    visited.add(w)
                    part.append(w)
        if len(part) % 2 and free.isdisjoint(part):
            cost += 1
    return cost


def check_cubic(clauses, expected_solutions):
    out = compile_cubic(clauses)
    keys = list(out.variables)
    raw_target, raw_cols, rank = syndromes(out.squares)
    target, cols, _ = syndromes(out.squares + [out.variables[v] for v in keys])
    # Complete enumeration on these small budgets; any selected face may fail.
    def within_budget(columns):
        assert out.threshold <= 2
        possible = {0}
        if out.threshold >= 1:
            possible.update(columns)
        if out.threshold == 2:
            possible.update(a ^ b for a,b in combinations(columns,2))
        return possible

    possible = within_budget(cols[:len(out.squares)])
    raw_possible = within_budget(raw_cols)
    accepted = 0
    for bits in product((0,1),repeat=len(keys)):
        valuation = dict(zip(keys,bits))
        correct = all(sum(valuation[v] for v in c) == 1 for c in clauses)
        rhs = target
        for i, bit in enumerate(bits, len(out.squares)):
            if bit:
                rhs ^= cols[i]
        assert (rhs in possible) == correct, (clauses,valuation)
        if correct:
            # The chosen pin row is the only expense per true variable.
            assert sum(bits) == out.threshold
            for v in keys:
                if valuation[v]:
                    rhs ^= cols[out.pin_fault[v]]
            assert rhs == 0, 'a canonical accepting defect pattern had no actual table extension'
            accepted += 1
    assert accepted == expected_solutions
    assert (raw_target in raw_possible) == bool(accepted)
    print(f'{len(clauses)} clauses; {len(out.squares)} actual squares; width {out.width}; '
          f'budget {out.threshold}; rank {rank}; feasible {accepted}/{2**len(keys)} assignments')


def self_check():
    g = Space()
    a,b = g.block(),g.block()
    assert [min_frequency_two(rows) for rows in (a,a[1:],a+b)] == [1,0,2]
    print('frequency-two exact minimum: full=1, punctured=0, two disjoint full copies=2')
    check_cubic([], 1)
    check_cubic([(0,0,0)], 0)
    check_cubic([(0,1,2)]*3, 3)
    check_cubic(list(combinations(range(4),3)), 0)
    check_cubic([(0,0,1),(1,1,2),(2,2,0)], 0)
    check_cubic([(0,0,1),(0,1,2),(1,2,2)], 1)
    # Nondivisibility makes this five-variable input unsatisfiable.
    check_cubic([(0,1,2),(0,1,3),(0,1,4),(2,3,4),(2,3,4)], 0)
    # Both six-clause cases have no repeated clauses or literals, and a budget
    # of two. Their opposite outcomes do not follow from divisibility alone.
    for offset, expect in [(2,3), (3,0)]:
        check_cubic([(i,(i+1)%6,(i+offset)%6) for i in range(6)], expect)


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('formula', nargs='?', type=Path)
    args = parser.parse_args()
    if args.formula is None:
        self_check()
    else:
        print(json.dumps(compile_cubic(json.loads(args.formula.read_text())).data()))
