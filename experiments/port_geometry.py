"""Realize gluings of the three open squares of TwoPhases.certificate over F2.

Run `python3 -B experiments/port_geometry.py` for the fixed example suite.
Add `--coordinates` to print four compressed basis images and two offsets per block.
Input `--wiring FILE` accepts a JSON object with `blocks` and `wires`. Each
wire is a list of [block,port,reverse] incidences; port is 0,1,2, naming
original square indices 0,2,5. Reverse is 0 or 1 (opposite anchor). Unlisted
ports are external. A wire may meet more than two blocks. Relative anchor
choices are part of the input. All tests concern the 30 active tagged cells
of each certificate. Unused entries in both ambient tables are free, and no
constraint on the other ambient squares is assumed. The explicit instance is
12 odd square equations per block plus its port list. For b blocks, the
compressed witness uses w <= floor(log2(225*b*b+1)) bits per coordinate,
hence O(b log(b+1)) bits for all selected tests, or O(b**4) entries if one
expands both whole ambient phase tables. This is a bound for successful
fixed-slot direct identifications, not an embedding of every port wiring.
"""
import argparse
from collections import defaultdict
from itertools import combinations, permutations, product
import json
from pathlib import Path

from optimal_support import template


SQUARES = tuple(template(True))
PORTS = (0, 2, 5)
assert tuple(SQUARES[j] for j in PORTS) == ((0, 5, 2), (0, 8, 8), (2, 3, 7))


def corners(x, y, d):
    return ((0, x, y), (0, x ^ d, y ^ d), (1, x, y ^ d), (1, x ^ d, y))


LOCAL = tuple(corners(*rectangle) for rectangle in SQUARES)
CELLS = sorted(set(c for sq in LOCAL for c in sq))
assert len(CELLS) == 30 and sum(tag == 0 for tag, _, _ in CELLS) == 15
assert len(set(c for j in PORTS for c in LOCAL[j])) == 12


class Basis:
    """Reduced row echelon basis with the highest set bit as pivot."""
    def __init__(self, rows=()):
        self.rows = {}
        for row in rows:
            self.insert(row)

    def reduce(self, row):
        for pivot in sorted(self.rows, reverse=True):
            if row >> pivot & 1:
                row ^= self.rows[pivot]
        return row

    def insert(self, row):
        row = self.reduce(row)
        if row:
            pivot = row.bit_length() - 1
            for p in self.rows:
                if self.rows[p] >> pivot & 1:
                    self.rows[p] ^= row
            self.rows[pivot] = row

    def key(self):
        return tuple(sorted(self.rows.items()))


class Equivalence:
    def __init__(self, labels):
        self.parents = {x: x for x in labels}

    def find(self, x):
        while x != self.parents[x]:
            self.parents[x] = self.parents[self.parents[x]]
            x = self.parents[x]
        return x

    def join(self, x, y):
        self.parents[self.find(x)] = self.find(y)


class Obstruction(ValueError):
    pass


def validate(blocks, wires):
    if not isinstance(blocks, int) or blocks < 1:
        raise ValueError('blocks must be a positive integer')
    seen = set()
    for wire in wires:
        if len(wire) < 2:
            raise ValueError('external ports should be left unlisted')
        for block, port, turn in wire:
            if not (0 <= block < blocks and 0 <= port < 3 and turn in (0, 1)):
                raise ValueError(f'invalid incidence: {(block, port, turn)}')
            if (block, port) in seen:
                raise ValueError(f'port assigned twice: {(block, port)}')
            seen.add((block, port))


def free_vector(block, local, offset=0):
    # Six independent vectors per block: four columns then x and y origins.
    return (local | offset) << (6 * block)


def port_forms(inc):
    i, p, rev = inc
    x, y, d = SQUARES[PORTS[p]]
    if rev:
        x, y = x ^ d, y ^ d
    return free_vector(i, x, 16), free_vector(i, y, 32), free_vector(i, d)


def port_cells(inc):
    i, p, rev = inc
    cells = LOCAL[PORTS[p]]
    return [(i, cells[k ^ rev]) for k in range(4)]


def project(rows, total, keep):
    """Project affine binary equations, with RHS in bit `total`, onto `keep`.

    Pivoting only hidden columns computes the linear combinations of equations
    whose hidden coefficients vanish. Such combinations give exactly the
    constraints on extendible boundary assignments, by Gaussian elimination.
    """
    hidden_pivots = {}
    image = Basis()
    hidden_mask = ((1 << total) - 1) ^ keep
    for row in rows:
        while row & hidden_mask:
            pivot = (row & hidden_mask).bit_length() - 1
            if pivot not in hidden_pivots:
                hidden_pivots[pivot] = row
                break
            row ^= hidden_pivots[pivot]
        else:
            image.insert(row)
    return image


def odd_mask(indices):
    row = 0
    for i in indices:
        row ^= 1 << i
    return row


def tree_extension(images, values):
    """Complete compatible port bits by leaf elimination on each block.

    The edges are the private cells shared by two of the twelve hard tests.
    A spanning tree lets one satisfy every vertex except the root in order;
    the residual root equation is exactly XOR of the boundary bits = 0.
    """
    out = dict(values)
    for block in images:
        tests = {j: corners(*r) for j, r in enumerate(block) if j not in PORTS}
        owners = defaultdict(list)
        for j, cells in tests.items():
            for cell in cells:
                if cell not in values:
                    owners[cell].append(j)
        adjacency = {j: [] for j in tests}
        for cell, ends in owners.items():
            assert len(ends) == 2 and cell not in out
            u, v = ends
            adjacency[u].append((v, cell))
            adjacency[v].append((u, cell))
            out[cell] = 0
        root = min(tests)
        parent = {root: None}
        order = [root]
        for u in order:
            for v, cell in adjacency[u]:
                if v not in parent:
                    parent[v] = cell
                    order.append(v)
        assert len(order) == len(tests)
        for v in reversed(order[1:]):
            cell = parent[v]
            out[cell] ^= 1 ^ (sum(out[c] for c in tests[v]) % 2)
        if sum(out[c] for c in tests[root]) % 2 != 1:
            raise ValueError('a block received incompatible port bits')
        assert all(sum(out[c] for c in cells) % 2 == 1 for cells in tests.values())
    assert all(out[c] == v for c, v in values.items())
    return out


def compress_charts(charts, address):
    """Greedily quotient away unused directions while protecting inequalities.

    One differing coordinate protects each distinct pair of active cells with
    the same tag. Also protect all 15 nonzero local directions in each block.
    A quotient by the line spanned by z kills precisely z. A missing positive
    integer can be found among the first |protected|+1 candidates. Iteration
    stops at width w with 2**w - 1 <= 225 * blocks**2. No ambient table is built.
    """
    forbidden = set()
    for F in charts:
        sums = [0]
        for v in F['basis']:
            sums += [s ^ v for s in sums]
        forbidden.update(sums[1:])
    for tag in [0, 1]:
        cells = {p for p in address.values() if p[0] == tag}
        for (_, a, b), (_, x, y) in combinations(sorted(cells), 2):
            forbidden.add((a ^ x) or (b ^ y))
    assert 0 not in forbidden and len(forbidden) <= 225*len(charts)**2
    images = [dict(basis=F['basis'][:], x_offset=F['x_offset'], y_offset=F['y_offset']) for F in charts]
    width = max(v.bit_length() for F in images for v in [*F['basis'], F['x_offset'], F['y_offset']])
    while len(forbidden) < (1 << width) - 1:
        z = next(v for v in range(1, len(forbidden)+2) if v not in forbidden)
        bit = z.bit_length() - 1
        lower = (1 << bit) - 1

        def quotient(v):
            if v >> bit & 1:
                v ^= z
            return (v & lower) | ((v >> (bit + 1)) << bit)

        forbidden = {quotient(v) for v in forbidden}
        assert 0 not in forbidden
        images = [dict(basis=[quotient(v) for v in F['basis']],
                       x_offset=quotient(F['x_offset']), y_offset=quotient(F['y_offset'])) for F in images]
        width -= 1
    return images, width


def materialize(charts):
    images, address = [], {}
    for i, F in enumerate(charts):
        line = [0]
        for v in F['basis']:
            line += [t ^ v for t in line]
        assert len(set(line)) == 16
        sx, sy = F['x_offset'], F['y_offset']
        images.append([(sx ^ line[x], sy ^ line[y], line[d]) for x, y, d in SQUARES])
        for tag, x, y in CELLS:
            address[i, (tag, x, y)] = tag, sx ^ line[x], sy ^ line[y]
    return images, address


def classify_port_states(images, projection, indexed_cells):
    """Compare corner-level feasibility, odd parity, and exactly one defect.

    For small examples enumerate all defect assignments on the physical ports,
    including shared ports. One reference corner encoding plus the three
    independent parity-preserving variations per port span its entire encoding
    fiber. The closed-square linear system and tree decoder are affine, so
    validity of this spanning set certifies every corner encoding for that
    pattern. The chosen defect positions impose no further equations on the
    private entries once the boundary is fixed.
    """
    port_ids, port_cells = {}, []
    per_block = []
    for block in images:
        ids = []
        for j in PORTS:
            cells = tuple(sorted(corners(*block[j])))
            if cells not in port_ids:
                port_ids[cells] = len(port_cells)
                port_cells.append(cells)
            ids.append(port_ids[cells])
        per_block.append(ids)
    k = len(port_cells)
    if k > 7:
        return None  # no unnecessarily exponential step on a user wiring
    assert len({c for cells in port_cells for c in cells}) == 4*k
    checks = [(row, 1 << len(indexed_cells)) for row in projection.rows.values()]
    accepted, odd_count = [], 0
    for state in product((0, 1), repeat=k):
        # Each port's score is 1 XOR its failure bit. The first of its four
        # tagged cells carries that score in the reference encoding.
        values = {c: (1 ^ state[j]) if n == 0 else 0 for j, cells in enumerate(port_cells)
                  for n, c in enumerate(cells)}
        packed = odd_mask(indexed_cells[c] for c, bit in values.items() if bit)
        extendible = all((row & (packed | rhs)).bit_count() % 2 == 0 for row, rhs in checks)
        counts = [sum(state[j] for j in ids) for ids in per_block]
        assert extendible == all(v % 2 == 1 for v in counts)
        odd_count += extendible
        if not extendible or not all(v == 1 for v in counts):
            continue
        accepted.append(''.join(map(str, state)))
        # Verify the affine extension on a full spanning set of encodings for
        # this exact state, checking all fifteen square values in each block.
        adjustments = [None, *((cells[0], c) for cells in port_cells for c in cells[1:])]
        for change in adjustments:
            trial = values.copy()
            if change:
                for c in change:
                    trial[c] ^= 1
            sol = tree_extension(images,trial)
            for block, ids in zip(images, per_block):
                defects = [1 ^ (sum(sol[c] for c in corners(*r)) % 2) for r in block]
                assert sum(defects) == 1 and [defects[j] for j in PORTS] == [state[i] for i in ids]
    return {'block_port_ids': per_block, 'patterns_checked': 2**k, 'parity_only_patterns': odd_count,
            'exactly_one_patterns': accepted, 'corner_encodings_per_pattern': 2**(3*k)}


def verify_projection(images, address, blocks, wires):
    # Actual table variables are indexed by global (role, x, y), never by block.
    global_cells = {c: i for i, c in enumerate(sorted(set(address.values())))}
    n = len(global_cells)
    rows = []
    checks = []
    all_ports = set()
    exposed = set()
    glued = {(i, p) for wire in wires for i, p, _ in wire}
    for i in range(blocks):
        expected = 0
        for j, rect in enumerate(images[i]):
            cells = [global_cells[c] for c in corners(*rect)]
            form = odd_mask(cells)
            if j in PORTS:
                all_ports.update(cells)
                expected ^= form
                if (i, PORTS.index(j)) not in glued:
                    exposed.update(cells)
            else:
                rows.append(form | (1 << n))  # each closed square must be odd
        checks.append(expected)  # 12 closed odd squares give even boundary XOR
    all_mask = odd_mask(all_ports)
    outer_mask = odd_mask(exposed)
    full = project(rows, n, all_mask)
    expected = Basis(checks)
    if full.key() != expected.key():
        raise Obstruction('actual affine projection on all port bits differs from the block parity laws')
    outer = project(rows, n, outer_mask)
    assert outer.key() == project(checks, n, outer_mask).key()
    assert full.reduce(1 << n) != 0 and outer.reduce(1 << n) != 0
    # An independent extension algorithm checks zero and every allowable
    # boundary basis vector. The extension uses only XOR and a constant.
    # Also reject a unit perturbation violating the parity check.
    inverse = {i: c for c, i in global_cells.items()}
    free = sorted(all_ports - expected.rows.keys())
    for bit in [None, *free]:
        pattern = 0 if bit is None else 1 << bit
        for pivot, row in expected.rows.items():
            pattern |= ((row & pattern).bit_count() % 2) << pivot
        assert all((row & pattern).bit_count() % 2 == 0 for row in checks)
        tree_extension(images, {inverse[i]: pattern >> i & 1 for i in all_ports})
    if checks and any(checks):
        nonzero = next(row for row in checks if row)
        bit = (nonzero & -nonzero).bit_length()-1
        try:
            tree_extension(images, {inverse[i]: int(i == bit) for i in all_ports})
        except ValueError:
            pass
        else:
            raise AssertionError('the independent tree decoder accepted an invalid boundary')
    rank = len(Basis(rows).rows)
    private_mask = ((1 << n) - 1) ^ all_mask
    private_rank = len(Basis(row & private_mask for row in rows).rows)
    states = classify_port_states(images, full, global_cells)
    return {'port_states': states, 'private_column_rank': private_rank, 'active_cells': n, 'closed_equations': len(rows), 'closed_rank': rank,
            'private_free_bits_given_all_ports': n - rank - len(all_ports) + len(full.rows),
            'free_bits_given_exterior': n - rank - len(exposed) + len(outer.rows),
            'all_port_bits': len(all_ports), 'all_port_equations': len(full.rows),
            'all_port_free_bits': len(all_ports) - len(full.rows), 'external_bits': len(exposed),
            'external_equations': len(outer.rows), 'external_free_bits': len(exposed) - len(outer.rows)}


def realize(blocks, wires):
    """The initial quotient for fixed incidences/orientations; exact collisions.

    Every collection of per-block affine embeddings with shared linear part on
    x and y and these exact labelled gluings factors through this quotient.
    Thus collisions already present here cannot be fixed by increasing width.
    """
    validate(blocks, wires)
    relations = Basis()
    wanted_cells = Equivalence((i, c) for i in range(blocks) for c in CELLS)
    wanted_tests = Equivalence((i, j) for i in range(blocks) for j in range(15))
    for wire in wires:
        first = wire[0]
        for other in wire[1:]:
            for a, b in zip(port_forms(first), port_forms(other)):
                relations.insert(a ^ b)
            for a, b in zip(port_cells(first), port_cells(other)):
                wanted_cells.join(a, b)
            wanted_tests.join((first[0], PORTS[first[1]]), (other[0], PORTS[other[1]]))
    free = [k for k in range(6 * blocks) if k not in relations.rows]

    def image(mask):
        normal = relations.reduce(mask)
        return sum(((normal >> p) & 1) << i for i, p in enumerate(free))

    charts, images, address = [], [], {}
    used, used_tests = {}, {}
    for i in range(blocks):
        line = [image(free_vector(i, x)) for x in range(16)]
        if len(set(line)) != 16:
            raise Obstruction(f'block {i} has a collapsed nonzero direction')
        sx, sy = image(free_vector(i, 0, 16)), image(free_vector(i, 0, 32))
        charts.append({'basis': [line[1 << j] for j in range(4)], 'x_offset': sx, 'y_offset': sy})
        images.append([(sx ^ line[x], sy ^ line[y], line[d]) for x, y, d in SQUARES])
        for c in CELLS:
            tag, x, y = c
            actual = tag, sx ^ line[x], sy ^ line[y]
            ref = (i, c)
            address[ref] = actual
            if actual in used and wanted_cells.find(ref) != wanted_cells.find(used[actual]):
                raise Obstruction(f'extra tagged-cell contact {used[actual]} = {ref}')
            used[actual] = ref
        for j, rect in enumerate(images[-1]):
            physical = tuple(sorted(corners(*rect)))
            ref = i, j
            if physical in used_tests and wanted_tests.find(ref) != wanted_tests.find(used_tests[physical]):
                raise Obstruction(f'extra full-square contact {used_tests[physical]} = {ref}')
            used_tests[physical] = ref
    # Check the converse of the collision tests with the concrete coordinate masks.
    for wire in wires:
        typed = [tuple(address[c] for c in port_cells(inc)) for inc in wire]
        assert len(set(typed)) == 1
    small_charts, width = compress_charts(charts, address)
    compact_images, compact = materialize(small_charts)
    mapped = {}
    for ref, location in address.items():
        if location in mapped:
            assert mapped[location] == compact[ref]
        mapped[location] = compact[ref]
    assert len(set(mapped.values())) == len(mapped)
    assert len({tuple(sorted(corners(*r))) for block in compact_images for r in block}) == len(used_tests)
    out = verify_projection(compact_images, compact, blocks, wires)
    out.update({'universal_width': len(free), 'compressed_width': width,
                'relation_rank': len(relations.rows), 'distinct_tests': len(used_tests),
                'charts': small_charts})
    return out


def cycle_witness(n):
    """Explicit all-forward loose ring for every n >= 3.

    In the space on a_i,b_i,q_i modulo the single sum_i(a_i+b_i+q_i)=0,
    give block i basis (a_i,q_i,b_i,q_{i-1}). Its y-offset is the prefix
    sum of a_k+b_k+q_k, and all x-offsets are zero. This glues port 0 at i
    to port 1 at i+1. For i,j nonadjacent, either arc from i to j contains
    an intermediate k: its private a_k prevents their y-planes intersecting,
    even modulo the one relation. For neighbors only the shared direction
    can lie in both linear parts (the relation contains some third a_k).
    Their coordinate planes thus meet only in the designated square; the
    local active corners of slots 0 and 1 there agree exactly as tagged.
    """
    if n < 3:
        raise ValueError('a loose ring needs at least three blocks')
    vectors = [1 << j for j in range(3*n - 1)] + [(1 << (3*n-1)) - 1]
    charts = []
    sy = 0
    for i in range(n):
        a,b,q = vectors[3*i:3*i+3]
        charts.append({'basis':[a,q,b,vectors[3*((i-1)%n)+2]], 'x_offset':0, 'y_offset':sy})
        sy ^= a ^ b ^ q
    assert sy == 0
    wiring = [[(i,0,0),((i+1)%n,1,0)] for i in range(n)]
    result = explicit_witness(charts, wiring)
    assert result['closed_rank'] == 12*n and result['active_cells'] == 26*n
    assert result['free_bits_given_exterior'] == 10*n+1 and result['external_equations'] == 1
    return charts


def examples():
    yield 'one block', 1, []
    yield 'two blocks, one port', 2, [[(0,0,0),(1,0,0)]]
    yield 'one port shared by three blocks', 3, [[(0,0,0),(1,0,0),(2,0,0)]]
    yield 'loose triangle', 3, [[(0,0,0),(1,1,0)],[(1,0,0),(2,1,0)],[(2,0,0),(0,1,0)]]


def explicit_witness(charts, wires):
    """Recheck a proposed coordinate assignment without the quotient algorithm."""
    count = len(charts)
    validate(count, wires)
    images, address = materialize(charts)
    intended_cells = Equivalence(address)
    intended_tests = Equivalence((i,j) for i in range(count) for j in range(15))
    for first, *others in wires:
        for other in others:
            for a, b in zip(port_cells(first), port_cells(other)):
                assert address[a] == address[b]
                intended_cells.join(a,b)
            intended_tests.join((first[0],PORTS[first[1]]),(other[0],PORTS[other[1]]))
    assert len({intended_cells.find(i) for i in address}) == len(set(address.values()))
    test_count = len({tuple(sorted(corners(*r))) for block in images for r in block})
    assert len({intended_tests.find(i) for i in intended_tests.parents}) == test_count
    result = verify_projection(images,address,count,wires)
    assert result['private_free_bits_given_all_ports'] == 7*count
    return result


def small_witnesses():
    """Minimum-width witnesses checked directly from their local bases."""
    identity = {'basis': [1,2,4,8], 'x_offset': 0, 'y_offset': 0}
    two = [identity, {'basis': [11,2,10,14], 'x_offset': 0, 'y_offset': 4}]
    explicit_witness(two, [[(0,0,0),(1,0,0)]])
    reverse = [identity, {'basis': [9,10,7,2], 'x_offset': 2, 'y_offset': 5},
               {'basis': [5,8,14,10], 'x_offset': 8, 'y_offset': 11}]
    ring = [[(i,0,0),((i+1)%3,1,1)] for i in range(3)]
    witness = explicit_witness(reverse,ring)
    assert witness['active_cells'] == 78 and witness['external_free_bits'] == 11
    # With these local anchors the x-offsets on the cycle must satisfy
    # XOR_i turn_i * shared_direction_i = 0. With one turn this would kill a
    # direction. With two it equates two distinct directions in a local block.
    for turns in product(range(2), repeat=3):
        wiring = [[(i,0,0),((i+1)%3,1,turns[i])] for i in range(3)]
        try:
            realize(3,wiring)
        except Obstruction as err:
            assert 0 < sum(turns) < 3 and 'collapsed' in str(err)
        else:
            assert sum(turns) in (0,3)
    return [('two-block direct witness', two), ('loose triangle with three reversals', reverse)]


def direct_pair_audit():
    """Every relative turn for every ordered two-block matching of slots."""
    result = {}
    for size in (1, 2, 3):
        clean = collapsed = extra = 0
        for left in combinations(range(3), size):
            for right in permutations(range(3), size):
                for turns in product(range(2), repeat=size):
                    wires = [[(0, a, 0), (1, b, t)] for a, b, t in zip(left, right, turns)]
                    try:
                        realize(2, wires)
                        clean += 1
                    except Obstruction as err:
                        if 'collapsed' in str(err):
                            collapsed += 1
                        elif 'extra' in str(err):
                            extra += 1
                        else:
                            raise
        result[size] = (clean, collapsed, extra)
    assert result == {1: (17, 0, 1), 2: (3, 56, 13), 3: (0, 47, 1)}
    # Small forced failure independent of the relative turns: left x-anchor
    # displacement is zero; right displacement 2 is outside span(8,7).
    assert 2 not in {0, 8, 7, 8 ^ 7}
    for t, u in product(range(2), repeat=2):
        try:
            realize(2, [[(0,0,0),(1,1,t)],[(0,1,0),(1,2,u)]])
        except Obstruction as err:
            assert 'collapsed' in str(err)
        else:
            raise AssertionError('a direction collapse was missed')
    return result


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--wiring', type=Path)
    parser.add_argument('--coordinates', action='store_true')
    args = parser.parse_args()
    cases = examples()
    if args.wiring:
        given = json.loads(args.wiring.read_text())
        cases = [(str(args.wiring), given['blocks'], given['wires'])]
    if not args.wiring:
        print('direct two-block slot matches, (clean, collapsed, extra contacts):', direct_pair_audit())
        assert len(Basis(odd_mask(CELLS.index(c) for c in sq) for sq in LOCAL).rows) == 14
        print('one certificate: whole 15-row rank 14; 18 private columns have rank 11')
        for n in range(3, 9):
            cycle_witness(n)
        print('closed-form direct cycle: tested sizes 3 through 8')
        for name, charts in small_witnesses():
            print(name + ': certified width 4')
            if args.coordinates:
                print('  charts: ' + json.dumps(charts))
    for name, n, wires in cases:
        try:
            out = realize(n, wires)
        except Obstruction as err:
            print(f'{name}: obstruction: {err}')
            if args.wiring:
                raise SystemExit(1)
            raise AssertionError('default example unexpectedly obstructed') from err
        charts = out.pop('charts')
        states = out['port_states']
        if not args.wiring and name == 'one block':
            assert out['private_column_rank'] == 11 and states['corner_encodings_per_pattern'] == 512
            assert len(states['exactly_one_patterns']) == 3 and states['parity_only_patterns'] == 4
        if not args.wiring and name == 'two blocks, one port':
            assert set(states['exactly_one_patterns']) == {'10000','01010','01001','00110','00101'}
            assert states['patterns_checked'] == 32 and states['parity_only_patterns'] == 8
        if not args.wiring and name == 'loose triangle':
            assert states['patterns_checked'] == 64 and len(states['exactly_one_patterns']) == 4
        print(name + ': ' + json.dumps(out, sort_keys=True))
        if args.coordinates:
            print('  charts: ' + json.dumps(charts))


if __name__ == '__main__':
    main()
