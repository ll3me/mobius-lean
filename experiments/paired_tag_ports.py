"""Check fixed Hamiltonian port locations for permutations and repeated destinations."""
from itertools import product

from cycle_cover_queries import FIXED, Template, cover_index, set_bits, split_cities, tour_count
from paired_contraction import lift_graph, strongly_connected
from paired_cover_witnesses import cycles, extend_vertex


def tagged_graph(destinations, left_bits, right_bits):
    """Each source and destination bit controls the direction of one vertex pair."""
    width = len(destinations)
    left = [1 + 2*i for i in range(width)]
    right = [1 + 2*(width+j) for j in range(width)]
    rows = [0] * (4*width + 1)
    rows[0] = 3 << left[0]

    for starts, bits in ((left, left_bits), (right, right_bits)):
        for index, start in enumerate(starts):
            bit = (bits >> index) & 1
            rows[start+bit] = 1 << (start+1-bit)

    for i, j in enumerate(destinations):
        # Leave the left pair at lane 1-x and enter the right pair at lane x.
        rows[left[i]] |= 1 << (right[j]+1)
        rows[left[i]+1] |= 1 << right[j]
        following = 3 << left[i+1] if i+1 < width else 1
        for lane in (0, 1):
            rows[right[j]+lane] |= following
    return rows


def check_port_positions(destinations):
    width = len(destinations)
    base = tagged_graph(destinations, 0, 0)
    for i, target in enumerate(destinations):
        left_zero = 1 + 2*i
        selected = [j for j in range(width) if (base[left_zero] >> (2+2*(width+j))) & 1]
        assert selected == [target]
    for bit in range(2*width):
        word = 1 << bit
        changed = tagged_graph(destinations, word % (1 << width), word >> width)
        flips = {(u, v) for u, (a, b) in enumerate(zip(base, changed))
                 for v in set_bits(a ^ b)}
        start = 1 + 2*bit
        assert flips == {(start, start+1), (start+1, start)}


def check_tags(records, payload_width):
    width = records * payload_width
    order = 4*width + 1
    pairing = tuple((2*v, 2*v+1) for v in range(order))
    payload_mask = (1 << payload_width) - 1
    tested = positive = 0
    for tags in product(range(records), repeat=records):
        targets = [j*payload_width + bit for j in tags for bit in range(payload_width)]
        check_port_positions(targets)
        for x, y in product(range(1 << width), repeat=2):
            expected = len(set(tags)) == records and all(
                ((x >> (i*payload_width)) & payload_mask) ==
                ((y >> (j*payload_width)) & payload_mask) for i, j in enumerate(tags))
            small = tagged_graph(targets, x, y)
            assert tour_count(small) == int(expected)
            assert tour_count(lift_graph(small, pairing)) == int(expected)
            tested += 1
            positive += expected
    return tested, positive


def with_fixed_covers(rows, width):
    """Replace vertex zero by a chain of bidirectional pairs, then split cities."""
    extended = extend_vertex(rows, 0, 2*width-1)
    chain = [0] + list(range(len(rows), len(extended)))
    for first, second in zip(chain[::2], chain[1::2]):
        extended[second] |= 1 << first
    arcs = {(u, v): FIXED for u, row in enumerate(extended) for v in set_bits(row)}
    return split_cities(Template(len(extended), arcs)).graph(0)


def check_fixed_covers(width):
    # Removing all port and connector arcs gives a common subgraph of every input.
    empty = [0] * (4*width+1)
    common = with_fixed_covers(empty, width)
    pairing = tuple((2*v, 2*v+1) for v in range(len(common)))
    for rows in (common, lift_graph(common, pairing)):
        assert strongly_connected(rows)
        assert cover_index(rows)[1] == 1 << width

    if width <= 2:
        for right_bits in (0, 1):
            tagged = tagged_graph(tuple(range(width)), 0, right_bits)
            small = with_fixed_covers(tagged, width)
            for rows in (small, lift_graph(small, pairing)):
                masks, count = cover_index(rows)
                tours = 0
                for cover in range(count):
                    successor = [-1] * len(rows)
                    for (u, v), mask in masks.items():
                        if (mask >> cover) & 1:
                            successor[u] = v
                    assert sorted(successor) == list(range(len(rows)))
                    tours += cycles(successor) == (len(rows),)
                assert count >= 1 << width
                assert tours == int(right_bits == 0)


if __name__ == '__main__':
    for records, bits in ((1, 1), (2, 1), (3, 1), (2, 2)):
        total, positive = check_tags(records, bits)
        print(f'records={records}, payload width={bits}, '
              f'{total} small/lifted graph pairs checked, {positive} with one tour')
    for width in range(1, 5):
        check_fixed_covers(width)
    print('Common covers checked before and after lifting for widths 1 through 4')
