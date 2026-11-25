"""Matrix subfunctions of directed Hamiltonicity and their shared gates on one pairing."""
from collections import Counter
from fractions import Fraction
from itertools import product
from math import ceil

from boolean_sweep import affine_rebuild, live_gates, rewrite_windows
from cycle_cover_queries import cover_index, set_bits, tour_count
from hamiltonian_boards import cycle_masks
from pair_certificate import tables
from paired_contraction import Circuit, held_karp, lift_graph, strongly_connected
from paired_cover_witnesses import cycles, extend_vertex
from paired_tag_ports import with_fixed_covers


def matrix_graph(anchors, width, background, left, right, exit_anchor, return_after):
    """The anchor, left and right vertices each have an always-open directed cycle."""
    rows = []
    for start, length in ((0, anchors), (anchors, width), (anchors+width, width)):
        rows.extend(1 << (start+(i+1) % length) for i in range(length))
    for i in range(width):
        if left >> i & 1:
            rows[exit_anchor] |= 1 << (anchors+i)
        if right >> i & 1:
            rows[anchors+width+(i-1) % width] |= 1 << ((return_after+1) % anchors)
        last_left = anchors + (i-1) % width
        for j in range(width):
            if background >> (i*width+j) & 1:
                rows[last_left] |= 1 << (anchors+width+j)
    return rows


def check_subfunctions(anchors, width, all_ports):
    ports = range(1 << width) if all_ports else [1 << i for i in range(width)]
    order = anchors + 2*width
    pairing = tuple((2*i, 2*i+1) for i in range(order))
    checked = 0
    for t, background in product(range(anchors), range(1 << (width*width))):
        for left, right in product(ports, repeat=2):
            rows = matrix_graph(anchors, width, background, left, right, t, t)
            count = sum((left >> i) & (right >> j) & (background >> (i*width+j)) & 1
                        for i, j in product(range(width), repeat=2))
            assert tour_count(rows) == tour_count(lift_graph(rows, pairing)) == count
            if left and right and background:
                assert strongly_connected(rows)
            checked += 1
    # Independent ORs over the anchors can mix an exit and a return from different tests.
    mismatch = matrix_graph(anchors, width, 1, 1, 1, 0, 1)
    assert strongly_connected(mismatch) and tour_count(mismatch) == 0
    return checked


def check_many_covers(width, padding):
    def expand(rows):
        return extend_vertex(with_fixed_covers(rows, width), 0, padding)

    # The three internal cycles and all internal chain arcs are common to every test.
    common = expand(matrix_graph(width, width, 0, 0, 0, 0, 0))
    pairs = tuple((2*i, 2*i+1) for i in range(len(common)))
    common_count = cover_index(common)[1]
    assert common_count == cover_index(lift_graph(common, pairs))[1] >= 1 << width
    for right in (1, 2):
        small = expand(matrix_graph(width, width, 1, 1, right, 0, 0))
        assert all(common_row & row == common_row for common_row, row in zip(common, small))
        for graph in (small, lift_graph(small, pairs)):
            assert strongly_connected(graph)
            arc_masks, count = cover_index(graph)
            successors = [[-1]*len(graph) for _ in range(count)]
            for (u, v), mask in arc_masks.items():
                for cover in set_bits(mask):
                    successors[cover][u] = v
            assert all(sorted(succ) == list(range(len(graph))) for succ in successors)
            assert sum(cycles(succ) == (len(graph),) for succ in successors) == int(right == 1)
    return len(common), common_count


def negative_test_masks(dag, anchors, width, t, root_role):
    """One packed truth table per wire and negative addresses grouped by the *same* matrix."""
    columns = [0] * len(dag.edges)
    expected = offset = 0
    groups = []
    for background in range(1, 1 << (width*width)):
        negatives = 0
        for i, j in product(range(width), repeat=2):
            rows = matrix_graph(anchors, width, background, 1 << i, 1 << j, t, t)
            slot = 1 << offset
            for e, (u, v) in enumerate(dag.edges):
                if rows[(u+root_role) % dag.order] >> ((v+root_role) % dag.order) & 1:
                    columns[e] |= slot
            if background >> (i*width+j) & 1:
                expected |= slot
            else:
                negatives |= slot
            offset += 1
        groups.append(negatives)
    return tables(dag, (1 << offset)-1, columns), groups, expected


def shared_levels(dag, live):
    """Count shared nonliteral gates along the longest path ending at each gate."""
    uses = Counter(child for g in live for child in dag.nodes[g][1:])
    depth = {}
    shared = {}
    for g in live:
        op, *args = dag.nodes[g]
        level = max(depth.get(child, 0) for child in args)
        literal = op == 'not' and dag.nodes[args[0]][0] == 'input'
        if uses[g] >= 2 and not literal:
            level += 1
            shared[g] = level
        depth[g] = level
    return shared


def check_all_graphs(dag, output):
    """The minimum accepting arc sets characterize this entire monotone truth table."""
    terms = {wire: {1 << i} for i, wire in enumerate(dag.inputs.values())}
    terms[0], terms[1] = set(), {0}
    for g in live_gates(dag, output):
        op, u, v = dag.nodes[g]
        assert op in ('and', 'or')
        seen = set()
        choices = terms[u] | terms[v] if op == 'or' else {x | y for x in terms[u] for y in terms[v]}
        for mask in sorted(choices, key=int.bit_count):
            if not any(mask & small == small for small in seen):
                seen.add(mask)
        terms[g] = seen
    assert terms[output] == set(cycle_masks(dag.order))
    return len(terms[output])


def trace_held_karp():
    anchors = width = 2
    order = anchors + 2*width
    pairing = tuple((2*i, 2*i+1) for i in range(order))
    source = Circuit(2*order)
    output = held_karp(source, 2*order)
    live = live_gates(source, output)
    small, image = source.contract(pairing)
    root = image[output]
    inner_live = set(live_gates(small, root))
    windows, win_root = rewrite_windows(small, root)
    affine, affine_root = affine_rebuild(windows, win_root)
    sizes = (len(inner_live), windows.size(win_root), affine.size(affine_root))
    assert sizes[0] == min(sizes)  # R+ keeps R0 on ties.
    tours = check_all_graphs(small, root)
    print(f'Held-Karp: {len(live)} gates, candidates {sizes}, '
          f'{tours} minimal accepting graphs, {len(live)-min(sizes)} gates deleted')

    original_levels = shared_levels(source, live)
    residual_levels = shared_levels(small, sorted(inner_live))
    for root_role in range(order):
        test_hits = Counter()
        for t in range(anchors):
            values, groups, expected = negative_test_masks(small, anchors, width, t, root_role)
            assert values[root] == expected
            for g, value in enumerate(values):
                if any(0 < (value & group) < group for group in groups):
                    test_hits[g] += 1
        nested = [g for g, d in original_levels.items() if d >= 2 and test_hits[image[g]] == anchors]
        images = {image[g] for g in nested} & inner_live
        second = sum(d == 2 and test_hits[g] == anchors for g, d in residual_levels.items())
        deeper = sum(d > 2 and test_hits[g] == anchors for g, d in residual_levels.items())
        print(f'root role {root_role}: {len(nested)} nested original gates, {len(images)} live images, '
              f'{second} second-level and {deeper} deeper shared gates in R+ vary on both negative tests')


def certified_deletion(m, size):
    if m < 16:
        raise ValueError('the comparison with the eight-arc estimate requires m >= 16')
    n = 2*m
    variables = n*(n-1)
    baseline = 3*m*m+m-2
    loss = ceil(Fraction(3*size, 4))
    gap = max(0, loss-baseline)
    width = m//2
    weight = Fraction(3*m*(m-1), variables*(19*width-20))
    forest = (21*width-18)*variables - (10*width-8)*size - (16*width-14)
    combined = 3*m*m + ceil(weight * max(0, forest))
    old_bounds = [baseline + (m+1)//2, ceil(Fraction(33*variables-18*size-16*n-47, 4))]
    first_forest = Fraction(n-4, 4*(n-1)) * (4*variables-2*size-2*n+1)
    old_bounds.append(baseline + 1 + ceil(max(0, first_forest)))
    if n >= 46:
        old_bounds.append(baseline+1+ceil(Fraction(25*variables-12*size-15*n+11, 30)))
    if n >= 64 and size <= 2*variables:
        old_bounds.append(baseline+ceil(Fraction(gap, 30)))
    return max(old_bounds), combined, loss, gap


if __name__ == '__main__':
    for anchors, width, all_ports in ((2, 2, True), (3, 3, False)):
        print(f'{anchors} blocks of width {width}: {check_subfunctions(anchors, width, all_ports)} graph pairs')
    for width, padding in ((2, 0), (3, 1)):
        order, covers = check_many_covers(width, padding)
        print(f'{2*order} to {order} vertices: {covers} input-independent covers on the common subgraph')
    trace_held_karp()
    for m in range(242, 2049):
        n = 2*m
        _, bound, target, gap = certified_deletion(m, 2*n*(n-1))
        assert bound >= target-gap+ceil(Fraction(gap, 20))
    m = 1024
    print('Hypothetical s=2N at m=1024, old certificate, combined certificate, target, old gap:',
          certified_deletion(m, 2*(2*m)*(2*m-1)))
