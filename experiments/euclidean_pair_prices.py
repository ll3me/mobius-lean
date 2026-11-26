"""Check a Hamiltonian port tensor before and after one oriented pair.

Run with python3 experiments/euclidean_pair_prices.py.
"""
from collections import defaultdict
from functools import cache
from itertools import combinations

from boolean_sweep import affine_rebuild, live_gates, rewrite_windows
from paired_contraction import Circuit, held_karp, hk_size


def row_ports(rows, columns, selected, *, padded=True):
    """Arc labels are masks of required switches. A zero mask is a fixed open arc."""
    cells = rows * columns
    first_column = 4 * rows
    c = first_column + columns
    d = c + 1
    edges = {}
    data = []

    def add(tail, head, mask=0):
        assert tail != head and (tail, head) not in edges
        edges[tail, head] = mask

    for i in range(rows):
        a, left, middle, right = range(4*i, 4*i+4)
        next_a = 4 * ((i+1) % rows)
        add(a, left)
        add(left, middle)
        add(middle, right, 1 << (2*cells+rows) if i == selected else 0)
        add(right, next_a)
        add(c, right, 1 << (2*cells+i))
        add(right, middle)
        add(middle, left)
        add(left, d)
        for j in range(columns):
            cell = i*columns+j
            b = first_column+j
            pred = d if j == 0 else b-1
            add(a, b, 1 << cell)
            add(pred, next_a, 1 << (cells+cell))
            data.append(((a, b), (pred, next_a)))
    for j in range(columns-1):
        add(first_column+j, first_column+j+1)
    if padded:
        spacer = d+1
        add(first_column+columns-1, spacer)
        add(spacer, c)
    else:
        add(first_column+columns-1, c)
    add(d, first_column)
    order = d+1+int(padded)
    pair = (c, 4*selected+3)
    blocks = [pair] + [(v, v) for v in range(order) if v not in pair]
    return order, edges, data, blocks


def tour_supports(order, edges):
    """Enumerate rooted spanning cycles on the all-open graph, retaining multiplicity."""
    adj = [[] for _ in range(order)]
    for (u, v), mask in edges.items():
        adj[u].append((v, mask))

    @cache
    def walk(u, remaining):
        if not remaining:
            return tuple(mask for v, mask in adj[u] if v == 0)
        out = []
        for v, mask in adj[u]:
            if remaining & (1 << v):
                out.extend(mask | rest for rest in walk(v, remaining ^ (1 << v)))
        return tuple(out)

    return sorted(walk(0, (1 << order)-2))


def matrix_rank(supports, cells, controls):
    """Build the actual acceptance rows and eliminate them over F₂."""
    values = 1 << cells
    parts = [(s % values, s // values % values, s // (values*values)) for s in supports]
    y_columns = {b: sum(1 << y for y in range(values) if y & b == b) for _, b, _ in parts}
    rows = set()
    for control in range(1 << controls):
        enabled = [(a, y_columns[b]) for a, b, z in parts if z & control == z]
        for x in range(values):
            row = 0
            for a, columns in enabled:
                if x & a == a:
                    row |= columns
            rows.add(row)
    pivots = {}
    for row in rows:
        while row:
            lead = row.bit_length()
            if lead not in pivots:
                pivots[lead] = row
                break
            row ^= pivots[lead]
    return len(pivots)


def check_optimal_control(order, data, blocks, rows, columns, selected):
    """A different graph predicate on the same raw arc positions and actual pair."""
    dag = Circuit(order)
    terms = [dag.gate('and', dag.inputs[x], dag.inputs[y]) for x, y in data]
    core = dag.fold('or', terms[selected*columns:(selected+1)*columns])
    rest = dag.fold('or', terms[:selected*columns] + terms[(selected+1)*columns:])
    c, _ = blocks[0]
    switch = dag.inputs[c, 4*((selected+1) % rows)+3]
    background = dag.inputs[0, 4]
    guard = dag.gate('or', switch, background)
    root = dag.gate('or', core, dag.gate('and', guard, rest))
    small, image = dag.contract(blocks)
    assert image[switch] == 0 and image[background] >= 2
    window, w = rewrite_windows(small, image[root])
    affine, a = affine_rebuild(window, w)
    sizes = dag.size(root), small.size(image[root]), window.size(w), affine.size(a)
    optimum = 2*rows*columns
    assert sizes == (optimum+1, optimum, optimum, optimum)
    return sizes


def check(rows, columns):
    cells = rows*columns
    for selected in range(rows):
        order, edges, data, blocks = row_ports(rows, columns, selected)
        before = tour_supports(order, edges)
        # The paired forward arc is forced open. Only block-end to block-start
        # arcs remain free. The resulting graph has its own rooted cycle search.
        after_edges = {(i, j): edges[tail, head]
                       for i, (_, tail) in enumerate(blocks)
                       for j, (head, _) in enumerate(blocks) if i != j and (tail, head) in edges}
        after = tour_supports(order-1, after_edges)
        # A different background in exactly the same pair image. The spare
        # vertex plays c and the contracted vertex plays the old right endpoint.
        _, template, _, _ = row_ports(rows, columns, selected, padded=False)
        block = {v: i for i, ends in enumerate(blocks) for v in ends}
        c, _ = blocks[0]
        rename = {v: block[order-1 if v == c else v] for v in range(order-1)}
        assert len(set(rename.values())) == order-1
        data_mask = (1 << (2*cells))-1
        rerouted = {(rename[u], rename[v]): mask & data_mask for (u, v), mask in template.items()}
        restored = tour_supports(order-1, rerouted)
        lifted = {blocks[0]: 0}
        lifted.update({(blocks[i][1], blocks[j][0]): mask for (i, j), mask in rerouted.items()})
        assert all(lifted[e] == edges[e] for pair in data for e in pair)
        assert tour_supports(order, lifted) == restored
        expected_before, expected_after, expected_restored = [], [], []
        for cell in range(cells):
            i = cell // columns
            bits = (1 << cell) | (1 << (cell+cells))
            expected_restored.append(bits)
            if i == selected:
                expected_after.append(bits)
            else:
                bits |= 1 << (2*cells+rows)
            expected_before.append(bits | (1 << (2*cells+i)))
        assert before == sorted(expected_before) and after == sorted(expected_after)
        assert restored == sorted(expected_restored)
        ranks = (matrix_rank(before, cells, rows+1), matrix_rank(after, cells, 0),
                 matrix_rank(restored, cells, 0))
        assert ranks == ((1 << cells)-1, (1 << columns)-1, (1 << cells)-1)
        sizes = check_optimal_control(order, data, blocks, rows, columns, selected)
    print(f'{rows}x{columns}, {order} vertices, all {rows} row choices: '
          f'ranks {ranks[0]} -> {ranks[1]}, restored {ranks[2]}; '
          f'control gates {sizes[0]} -> {min(sizes[1:])}')


def check_price_charge(dag, root, small, image, data):
    """Certify bounded raw/surviving charges on the actual 14-vertex DAG."""
    active = live_gates(dag, root)
    surviving = set(live_gates(small, image[root]))
    representative = {}
    for gate in active:
        if image[gate] in surviving:
            representative.setdefault(image[gate], gate)
    assert representative.keys() == surviving
    xs = [dag.inputs[x] for x, _ in data]
    ys = [dag.inputs[y] for _, y in data]
    charged = set(xs + ys) | set(representative.values())
    # Two charged signals meeting at a gate share its physical site.
    adjacent = defaultdict(list)
    for gate in active:
        incident = [s for s in (gate, *dag.nodes[gate][1:]) if s in charged]
        for a, b in combinations(incident, 2):
            adjacent[a].append(b)
            adjacent[b].append(a)

    separator = set(ys[:3])

    def reach(seeds):
        seen = set(seeds) - separator
        todo = list(seen)
        while todo:
            for v in adjacent[todo.pop()]:
                if v not in separator and v not in seen:
                    seen.add(v)
                    todo.append(v)
        return seen

    left = reach(xs)
    assert left.isdisjoint(ys)
    # No cheaper two-site layout: three vertex-disjoint charged paths connect X to Y.
    assert ys[1] in adjacent[xs[0]] and ys[2] in adjacent[xs[1]]
    assert (set(adjacent[xs[2]]) & set(adjacent[ys[0]])) - set(xs + ys)
    cells = len(data)
    two_site_credit = ((1 << cells)-2).bit_length() - len(separator)
    assert cells == 6 and two_site_credit == 3

    # Use a noncollinear placement too: the component of the fourth Y source
    # occupies the third corner. All six data pairs span a unit-length side.
    third = reach([ys[3]])
    assert third.isdisjoint(left) and ys[4] not in third
    sites = {s: (0 if s in left else 2 if s in third else 1) for s in charged - separator}
    readers = {s: set() for s in separator}
    for gate in active:
        locations = {sites[s] for s in (gate, *dag.nodes[gate][1:]) if s in sites}
        assert len(locations) <= 1
        location = next(iter(locations), 1)
        for operand in dag.nodes[gate][1:]:
            if operand in readers:
                readers[operand].add(location)
    # Put the three raw sources at corner 1. Each is read at corners 0 and 1.
    assert all(at == {0, 1} for at in readers.values())
    # W=3/2, U+B=3 and price >= W log2(2^(6/W)-1) = W log2(15).
    # Thus 2^(D+2) >= 15, with an integer lower bound on D.
    three_site_credit = (15-1).bit_length() - 2
    assert three_site_credit == 2
    return two_site_credit, three_site_credit


def check_full_decider():
    order, _, data, blocks = row_ports(2, 3, 0)
    dag = Circuit(order)
    root = held_karp(dag, order)
    small, image = dag.contract(blocks)
    original, remaining = dag.size(root), small.size(image[root])
    assert (original, remaining) == (hk_size(order), hk_size(order-1))
    two, three = check_price_charge(dag, root, small, image, data)
    print(f'Full H_{order} Held–Karp, pair {blocks[0]}: '
          f'{original} -> {remaining} using R0, {original-remaining} gates deleted')
    print(f'Geometric deletion certificates on that DAG: two sites >= {two}, '
          f'unit equilateral triangle >= {three}')


if __name__ == '__main__':
    for case in ((2, 2), (2, 3), (3, 2), (2, 4), (3, 3), (4, 2)):
        check(*case)
    check_full_decider()
