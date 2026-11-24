"""Count nonoptimal full boards in the vertex-deletion reduction to three-coloring."""
from itertools import combinations
from subprocess import run

from axis_relations import solve
from face_multiplicity import color_network
from free_direction_coloring import (attachment_coordinates, costs_on_one_world, lines3,
                                     solve_attachment, span_points)
from hamiltonian_boards import sat_solver
from port_k4 import phase3
from unary_sat import Builder, Encoding


def private_caps(rows, count):
    """The low two bits span U. Each attachment needs three fresh axes outside U."""
    first_bit = max((p.bit_length() for row in rows for p in row), default=2)
    for i in range(count):
        axes = tuple(1 << (first_bit + 3*i + j) for j in range(3))
        h, k, t = axes
        yield axes, [(h, k, a, b) for a, b, _ in lines3((1, 2, t))]


def directions_feasible(charts, budget, solver):
    """Necessary condition: each optimal board has exactly one marked physical direction."""
    directions = [span_points(chart)[1:] for chart in charts]
    assert len({frozenset(row) for row in directions}) == len(charts)
    marks = {d: i for i, d in enumerate(sorted(set().union(*directions)), 1)}
    formula = Builder(len(marks) + len(charts))
    at_least = [formula.one] + [formula.zero] * (budget + 1)
    for skip, row in enumerate(directions, len(marks) + 1):
        seen = formula.zero
        for d in row:
            formula.clauses.append((skip, -seen, -marks[d]))
            seen = formula.binary('or', seen, marks[d])
        formula.clauses.append((skip, seen))
        # at_least[j] is true when at least j boards have been skipped so far.
        for j in range(budget + 1, 0, -1):
            with_skip = formula.binary('and', skip, at_least[j-1])
            at_least[j] = formula.binary('or', at_least[j], with_skip)
    formula.clauses.append((-at_least[-1],))
    encoding = Encoding(formula.n, tuple(formula.gates), tuple(formula.clauses))
    result = run([solver, '-q'], input='\n'.join(encoding.dimacs()) + '\n',
                 text=True, capture_output=True)
    if result.returncode not in (10, 20):
        raise RuntimeError(f'CaDiCaL exited with {result.returncode}: {result.stderr}')
    return result.returncode == 10


def check_clique(n, cap_values, solver):
    edges = list(combinations(range(n), 2))
    rows, pins = color_network(n, edges)
    # Keep the first three vertices with distinct colors. All copies of each
    # deleted vertex can be unselected, including those on intact edge boards.
    for v, row in enumerate(rows[:n]):
        for color, p in enumerate(row):
            pins[p] = int(v == color)
    kept_vertices = min(n, 3)
    kept = rows[:kept_vertices] + rows[n:]
    chosen = solve([(row, ()) for row in kept], pins)
    assert chosen is not None

    def image(x):
        p = x & ~3
        return (x & 3) | (4 if p and not chosen[p] else 0)

    main = [(1, 2, a, b) for a, b, _ in rows]
    parts = [(main, lambda tag, x, y: phase3(image(x), image(y)))]
    for axes, charts in private_caps(rows, n):
        def cap_table(tag, x, y, axes=axes):
            return cap_values[tag, attachment_coordinates(x, axes), attachment_coordinates(y, axes)]
        parts.append((charts, cap_table))

    _, costs = costs_on_one_world(parts)
    assert len(costs) == 8*n + 57*len(edges)
    assert [i for i, cost in enumerate(costs) if cost != 128] == list(range(kept_vertices, n))
    charts = [chart for boards, _ in parts for chart in boards]
    loss = n - kept_vertices
    assert directions_feasible(charts, loss, solver)
    if loss:
        assert not directions_feasible(charts, loss - 1, solver)
    print(f'K{n}: minimum {loss} nonoptimal boards out of {len(costs)}')


if __name__ == '__main__':
    cap_values = solve_attachment()
    solver = sat_solver()
    for n in (3, 4, 5):
        check_clique(n, cap_values, solver)
