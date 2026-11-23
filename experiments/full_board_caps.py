"""Replace punctured charts by a union of complete, unweighted four-dimensional boards.

One cap owns the two line tests of each possible port. A cap's other three
axes are fresh. The two halves can construct their charts independently.
"""
import argparse
import json
from pathlib import Path
from dataclasses import dataclass
from itertools import combinations, product
from collections import Counter

from axis_relations import FULL, chart_values, corners, ground, matrix_half, placed_faces, solve


@dataclass
class Family:
    cores: list
    caps: list


def family(k, mask, side):
    """All coordinate reservations and the division of cap ownership are public."""
    extremes = [matrix_half(k, 0, side), matrix_half(k, (1 << (k*k))-1, side)]
    possible = {v for part in extremes for ports,_ in part.boards for v in ports}
    assert extremes[0].next_axis == extremes[1].next_axis
    # Both halves allocate private coordinates with opposite parity.
    # The next cap coordinate starts above every core coordinate on either side.
    base = extremes[0].next_axis - side + 2
    caps = []
    for v in sorted(possible):
        if side and v < 2*k:
            continue  # the left side already owns the public cap
        caps.append((v, base+3*v, base+3*v+1, base+3*v+2))
    return Family(matrix_half(k,mask,side).boards, caps)


def formula_family(variables, clauses):
    """Compile zero-based positive exactly-one triples to complete boards."""
    if variables < 0 or any(len(row) != 3 or any(x < 0 or x >= variables for x in row)
                            for row in clauses):
        raise ValueError('expected zero-based triples of valid variables')
    cores = []
    port_axes = list(range(variables))
    cap_base = variables + 19*len(clauses)
    for i,row in enumerate(clauses):
        start = variables + 19*i
        def private(shape):
            return start + shape-1
        center = tuple(private(q) for q in (1,2,3,4))
        cores.append((center[:3],center))
        port_axes.extend(private(q) for q in (1,2,3,5,6,7))
        for j,variable in enumerate(row):
            first = tuple(private(q) for q in (1+j,5+j,8+2*j,9+2*j))
            second = (private(5+j),variable,private(14+2*j),private(15+2*j))
            cores.extend([(first[:2],first),(second[:2],second)])
    caps = [(v,cap_base+3*i,cap_base+3*i+1,cap_base+3*i+2) for i,v in enumerate(port_axes)]
    return Family(cores,caps)


def write_boards(path, families):
    """The exported instance contains only complete charts and a threshold."""
    charts = [[axes for _,axes in f.cores] + f.caps for f in families]
    width = max((max(axes) + 1 for part in charts for axes in part), default=0)
    threshold = sum(126*len(f.cores)+128*len(f.caps) for f in families)
    data = dict(width=width, threshold=threshold, boards=charts)
    path.write_text(json.dumps(data, separators=(',',':'))+'\n')


def all_faces(axes):
    c = chart_values(axes)
    for x,y,d in FULL:
        X,Y,D = c[x],c[y],c[d]
        yield min((X,Y,D),(X^D,Y^D,D))


def verify_union(halves, expected):
    """Reconstruct the entire physical union and compare it with the ownership count."""
    cores = [row for half in halves for row in half.cores]
    caps = [cap for half in halves for cap in half.caps]
    cap_axes = {c[0] for c in caps}
    assert len(cap_axes) == len(caps)
    assert all(v in cap_axes for ports,_ in cores for v in ports)
    assert all(v not in cap_axes for ports,axes in cores for v in axes[len(ports):])
    core_coords = {v for _,axes in cores for v in axes}
    fresh = [v for cap in caps for v in cap[1:]]
    assert core_coords.isdisjoint(fresh) and len(set(fresh)) == len(fresh)

    values = solve(cores)
    assert (values is not None) == expected
    whole, owned, cell_sets, signs = set(), set(), [], {}
    for half in halves:
        cells = set()
        for ports,axes in half.cores + [((),cap) for cap in half.caps]:
            coords = chart_values(axes)
            complete = set(all_faces(axes))
            assert len(complete) == 1920
            whole.update(complete)
            owner = set(placed_faces(coords,len(ports))) if ports else complete
            assert owned.isdisjoint(owner)
            owned.update(owner)
            selected = None
            if values is not None:
                if ports:
                    slots = [i for i,v in enumerate(ports) if values[v]]
                    assert len(slots) == 1
                    selected = slots[0]
                else:
                    selected = 0 if values.get(axes[0],0) else 1
            table = ground(selected) if selected is not None else None
            for x,y in product(range(16),repeat=2):
                for tag in (0,1):
                    cell = (tag,coords[x],coords[y])
                    cells.add(cell)
                    if table is not None:
                        bit = table[16*x+y]
                        assert signs.setdefault(cell,bit) == bit
        cell_sets.append(cells)
    assert owned == whole
    assert len(whole) == sum(1920-2*len(ports) for ports,_ in cores) + 1920*len(caps)
    threshold = 126*len(cores) + 128*len(caps)
    if values is not None:
        assert sum(sum(signs[q] for q in corners(f))%2 == 0 for f in whole) == threshold
    return len(whole), cell_sets, threshold


def check_geometry(k, a, b):
    halves = [family(k,a,0), family(k,b,1)]
    count, cells, threshold = verify_union(halves,bool(a & b))
    shared = {(t,x,y) for v in range(2*k) for x in (0,1<<v) for y in (0,1<<v) for t in (0,1)}
    assert cells[0] & cells[1] == shared
    cores = sum(len(half.cores) for half in halves)
    caps = sum(len(half.caps) for half in halves)
    print(f'k={k} masks {a},{b}: {cores} core + {caps} cap complete boards, '
          f'{count} distinct squares, {len(shared)} shared cells, threshold {threshold}, '
          f'intersects={bool(a & b)}.')


def self_test():
    # Both a repeated variable and an absent source variable are allowed.
    for variables,clauses in [(4,[(0,1,2),(0,0,1)]),(3,[(0,0,0)]),(2,[])]:
        f = formula_family(variables,clauses)
        assert len(f.cores)+len(f.caps) == variables + 13*len(clauses)
        possible = any(all(sum(z[i] for i in row) == 1 for row in clauses)
                       for z in product((0,1),repeat=variables))
        square_count,_,threshold = verify_union([f],possible)
        assert square_count == 1920*(variables+13*len(clauses)) - 30*len(clauses)
        assert threshold == 126*7*len(clauses) + 128*(variables+6*len(clauses))
    for side in (0,1):
        ref = family(2,0,side)
        for mask in range(16):
            h = family(2,mask,side)
            assert h.caps == ref.caps
            assert len(h.cores)==len(ref.cores)
    # Check every coordinate chart of every 2x2 pair before the full
    # table-level enumeration of representative accepting and rejecting inputs.
    for a,b in product(range(16),repeat=2):
        halves = [family(2,a,0),family(2,b,1)]
        charts = [axes for f in halves for _,axes in f.cores] + [cap for f in halves for cap in f.caps]
        pairs = [pair for axes in charts for pair in combinations(sorted(axes),2)]
        assert len(set(pairs)) == len(pairs)
        multiplicity = Counter(v for axes in charts for v in axes)
        duplicates = 2*sum(count-1 for count in multiplicity.values())
        assert len(charts)*1920 - duplicates == 233992
    print('All 256 complete-board layouts for 2x2 masks have the expected intersections.')
    check_geometry(1, 1, 1)
    check_geometry(2, 9, 5)
    check_geometry(2, 9, 6)

if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    inp = parser.add_mutually_exclusive_group()
    inp.add_argument('--matrix', nargs=3, metavar=('K','LEFT','RIGHT'))
    inp.add_argument('--formula', type=Path, help='JSON with variables and zero-based clauses')
    parser.add_argument('--emit', type=Path, help='write a complete-board instance as JSON')
    args = parser.parse_args()
    if args.matrix is None and args.formula is None:
        if args.emit:
            parser.error('choose a source instance to export')
        self_test()
    else:
        if not args.emit:
            parser.error('provide an output path with --emit')
        if args.matrix is not None:
            k,a,b = (int(x,0) for x in args.matrix)
            halves = [family(k,a,0),family(k,b,1)]
        else:
            source = json.loads(args.formula.read_text())
            halves = [formula_family(source['variables'],source['clauses'])]
        write_boards(args.emit, halves)
