"""Compose punctured four-dimensional sign boards via actual shared coordinates.

One local factor has four distinct coordinate axes, the first 1--3 of which
are ports. Delete the two geometric faces in the line tile of each port;
all remaining faces are listed once and have unit cost. Input bits in the
two-party experiments belong to the respective local descriptions.
"""
import argparse
import json
from pathlib import Path
from dataclasses import dataclass
from functools import lru_cache
from itertools import combinations, product

from port_k4 import phase3


def corners(q):
    x, y, d = q
    return ((0,x,y), (0,x^d,y^d), (1,x,y^d), (1,x^d,y))


FULL = tuple((x,y,d) for d in range(1,16) for x in range(16) if x < (x^d) for y in range(16))


@lru_cache(None)
def retained(arity):
    deleted = {(0,y,1 << i) for i in range(arity) for y in (0,1 << i)}
    return tuple(q for q in FULL if q not in deleted)


@lru_cache(None)
def ground(slot):
    def project(x):
        return (x % (1 << slot)) | ((x >> (slot+1)) << slot)
    return tuple(phase3(project(x),project(y)) for x in range(16) for y in range(16))


def xor_score(bits, q):
    x, y, d = q
    return bits[16*x+y] ^ bits[16*(x^d)+(y^d)] ^ bits[16*x+(y^d)] ^ bits[16*(x^d)+y]


class Half:
    """Shared axis names are 0..public-1. Each party owns its own private axes."""
    def __init__(self, public, side):
        self.public = public
        self.next_axis = public + side
        self.boards = []

    def fresh(self):
        a = self.next_axis
        self.next_axis += 2
        return a

    def one(self, *ports):
        if not 1 <= len(ports) <= 3 or len(set(ports)) != len(ports):
            raise ValueError('one to three distinct port axes required')
        axes = tuple(ports) + tuple(self.fresh() for _ in range(4-len(ports)))
        self.boards.append((tuple(ports),axes))

    def proxy(self, axis):
        relay, local = self.fresh(), self.fresh()
        self.one(axis,relay)
        self.one(relay,local)
        return local

    def choose_one(self, axes):
        """A chain of ternary one-hot gates; used truth can never exceed one."""
        one, previous = self.fresh(), self.fresh()
        self.one(one)
        self.one(one,previous)
        for x in axes:
            unused, used = self.fresh(), self.fresh()
            self.one(previous,x,unused)
            self.one(unused,used)
            previous = used
        self.one(previous)


def matrix_half(k, mask, side):
    if k < 1 or mask < 0 or mask >= 1 << (k*k):
        raise ValueError('invalid square Boolean matrix')
    part = Half(2*k,side)
    x = [part.proxy(i) for i in range(k)]
    y = [part.proxy(k+j) for j in range(k)]
    part.choose_one(x)
    part.choose_one(y)
    # These two nontrivial shared-axis constraints connect the incidence
    # graph even for the all-allowed mask. Choosing bridge=false is feasible.
    bridge = part.fresh()
    part.one(x[0],bridge,part.fresh())
    part.one(bridge,y[0],part.fresh())
    for i in range(k):
        for j in range(k):
            dummy, slack = part.fresh(), part.fresh()
            allowed = mask & (1 << (i*k+j))
            part.one(x[i], dummy if allowed else y[j], slack)
    return part


def relation_half(k, mask, side):
    """Realize any relation on k shared bits, with input-independent board count."""
    if k < 1 or mask < 0 or mask >= 1 << (1 << k):
        raise ValueError('invalid Boolean relation')
    part = Half(k,side)
    values = [part.proxy(i) for i in range(k)]
    neg = [part.fresh() for _ in values]
    bridge = part.fresh()
    for x, nx in zip(values,neg):
        part.one(x,nx)
        part.one(x,bridge,part.fresh())
    for pattern in range(1 << k):
        choices = [part.fresh() for _ in range(k)]
        part.choose_one(choices)
        part.one(choices[0],bridge,part.fresh())
        # For a forbidden pattern, its chosen coordinate must differ. For
        # an allowed pattern a fresh unconstrained blocker suffices instead.
        allowed = mask & (1 << pattern)
        for i, choice in enumerate(choices):
            dummy, slack = part.fresh(), part.fresh()
            matches = values[i] if pattern & (1 << i) else neg[i]
            part.one(choice,dummy if allowed else matches,slack)
    return part


def solve(boards, pins=None):
    """Return one direction assignment for the exact threshold, or None."""
    rows = [ports for ports,_ in boards]
    def search(values):
        while True:
            before = len(values)
            for row in rows:
                free = [v for v in row if v not in values]
                ones = sum(values.get(v,0) for v in row)
                if ones > 1 or not (ones or free):
                    return None
                if ones:
                    values.update((v,0) for v in free)
                elif len(free) == 1:
                    values[free[0]] = 1
            if len(values) == before:
                break
        row = min(([v for v in r if v not in values] for r in rows if any(v not in values for v in r)),
                  key=len, default=[])
        if not row:
            return values
        for bit in (0,1):
            child = values.copy()
            child[row[0]] = bit
            result = search(child)
            if result is not None:
                return result
        return None
    return search(dict(pins or {}))


def chart_values(axes):
    result = [0]
    for i in axes:
        result += [x ^ (1 << i) for x in result]
    return result


@dataclass
class Physical:
    faces: set
    cells: set
    signs: dict | None
    cost: int | None


def placed_faces(coords, arity):
    for x,y,d in retained(arity):
        X,Y,D = coords[x],coords[y],coords[d]
        yield min((X,Y,D),(X^D,Y^D,D))


def physical(boards, values=None):
    """Enumerate all real unweighted faces, check coordinate contacts, and score a lift."""
    pairs, faces, cells = set(), set(), set()
    port_owners = {}
    signs = {} if values is not None else None
    for ports,axes in boards:
        for a in axes:
            if a in port_owners:
                assert port_owners[a] and a in ports
            port_owners[a] = a in ports
        for a,b in combinations(sorted(axes),2):
            assert (a,b) not in pairs, 'two boards share a plane'
            pairs.add((a,b))
        coords = chart_values(axes)
        if signs is not None:
            selected = [i for i,v in enumerate(ports) if values[v]]
            assert len(selected) == 1
            table = ground(selected[0])
        for x,X in enumerate(coords):
            for y,Y in enumerate(coords):
                for tag in (0,1):
                    addr = (tag,X,Y)
                    cells.add(addr)
                    if signs is not None:
                        bit = table[16*x+y]
                        assert signs.setdefault(addr,bit) == bit
        for actual in placed_faces(coords,len(ports)):
            assert actual not in faces, 'a counted test would be duplicated'
            faces.add(actual)
    if signs is None:
        return Physical(faces,cells,None,None)
    cost = sum(sum(signs[c] for c in corners(q)) % 2 == 0 for q in faces)
    assert cost == 126*len(boards)
    return Physical(faces,cells,signs,cost)


def connected(boards):
    pending = [set(p) for p,_ in boards]
    seen = pending.pop()
    while pending:
        for i, row in enumerate(pending):
            if row & seen:
                seen.update(pending.pop(i))
                break
        else:
            return False
    return True


def write_instance(path, boards):
    """Write real squares in board order, keeping the two parties' inputs contiguous."""
    width = max((max(axes)+1 for _,axes in boards), default=0)
    with path.open('w') as f:
        f.write('{"width": %d, "threshold": %d, "squares": [' % (width, 126*len(boards)))
        separator = ''
        for ports,axes in boards:
            for face in placed_faces(chart_values(axes),len(ports)):
                f.write(separator + json.dumps(face))
                separator = ','
        f.write(']}\n')


def test():
    assert len(FULL) == 1920
    for n in (1,2,3):
        face_list = retained(n)
        assert len(face_list) == 1920-2*n
        for s in range(4):
            assert sum(not xor_score(ground(s),q) for q in face_list) == (126 if s<n else 128)
    for k in (1,2):
        bound = 1 << (k*k)
        for a in range(bound):
            left = matrix_half(k,a,0)
            assert connected(left.boards)
            for i,j in product(range(k),repeat=2):
                pins = {u: int(u in (i,k+j)) for u in range(2*k)}
                assert (solve(left.boards,pins) is not None) == bool(a & (1 << (k*i+j)))
            for b in range(bound):
                boards = left.boards + matrix_half(k,b,1).boards
                assert (solve(boards) is not None) == bool(a & b)
    for a in range(16):
        part = relation_half(2,a,0)
        assert connected(part.boards)
        for w in range(4):
            assert (solve(part.boards,{i:(w>>i)&1 for i in range(2)}) is not None) == bool(a & (1<<w))
    k = 2
    left, right = matrix_half(k,9,0), matrix_half(k,5,1)
    solution = solve(left.boards+right.boards)
    assert solution is not None
    lhs, rhs = physical(left.boards,solution), physical(right.boards,solution)
    assert not lhs.faces.intersection(rhs.faces)
    seam = lhs.cells & rhs.cells
    expected = {(tag,x,y) for i in range(2*k) for x in (0,1<<i) for y in (0,1<<i) for tag in (0,1)}
    assert seam == expected and len(seam) == 12*k+2
    assert all(lhs.signs[c]==rhs.signs[c] for c in seam)
    # One ternary board and two unary pin boards on its first two axes.
    small = Half(0,0)
    x,y,z = (small.fresh() for _ in range(3))
    small.one(x,y,z)
    small.one(x)
    small.one(y)
    assert solve(small.boards) is None
    bits = {}
    for (_,axes),s in zip(small.boards,(0,0,1)):
        c = chart_values(axes)
        for i,j in product(range(16),repeat=2):
            assert bits.setdefault((c[i],c[j]),ground(s)[16*i+j]) == ground(s)[16*i+j]
    bad = 0
    for ports,axes in small.boards:
        c = chart_values(axes)
        for x,y,d in retained(len(ports)):
            bad += not (bits[c[x],c[y]] ^ bits[c[x^d],c[y^d]] ^ bits[c[x],c[y^d]] ^ bits[c[x^d],c[y]])
    assert bad == 380
    print('3 actual blocks: separate minima 378; glued optimum 380 (attaining full phase tables checked).')
    print('All 256 pairs of 2x2 matrices checked at the direction layer; all 16 relations on two bits checked.')
    print(f'Physical 2x2 accepting join: {len(left.boards)+len(right.boards)} boards, '
          f'{len(lhs.faces)+len(rhs.faces)} distinct faces, {len(seam)} shared tagged cells, '
          f'{lhs.cost+rhs.cost} actual failures.')


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--matrix', nargs=3, metavar=('K','LEFT','RIGHT'),
                        help='row-major integer masks; accept iff the masks share a 1')
    parser.add_argument('--emit', type=Path, help='write the actual unweighted geometric instance')
    args = parser.parse_args()
    if args.matrix is None:
        if args.emit:
            parser.error('--emit requires --matrix')
        test()
    else:
        k, a, b = (int(x,0) for x in args.matrix)
        boards = matrix_half(k,a,0).boards + matrix_half(k,b,1).boards
        if args.emit:
            write_instance(args.emit,boards)
        print(json.dumps(dict(boards=len(boards), squares=sum(1920-2*len(p) for p,_ in boards),
                              seam_cells=12*k+2, threshold=126*len(boards),
                              attainable=bool(a & b))))
