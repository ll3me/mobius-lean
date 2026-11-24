"""Exact restrictions to three distinct 3-planes through a common 2-plane.

Uses the 512 checked decoder rows but independently verifies its nullspace
and all 15 ground states. Every anchor is an actual tagged table cell.
"""
from functools import reduce
from itertools import combinations, product
from operator import xor

from overlap_fibers import (Span, cell, chart, pack,
                            project_kernel, read_decoder, read_grounds)
from port_k4 import phase3


def station_map(q):
    return tuple(cell(t, (x & 3) ^ (q if x & 4 else 0), (y & 3) ^ (q if y & 4 else 0))
                 for t in range(2) for x in range(8) for y in range(8))


def raw_dimension(n):
    N = 1 << n
    rows = []
    for d in range(1, N):
        for x in range(N):
            for y in range(N):
                rows.append((1 << (x*N+y)) ^ (1 << ((x^d)*N+(y^d))) ^
                            (1 << (N*N+x*N+(y^d))) ^ (1 << (N*N+(x^d)*N+y)))
    return 2*N*N-len(Span(rows))


def canonical(lift):
    # lift=None denotes a clear station, lift in {0,1,2,3} its marked vector.
    def image(x):
        return x if lift is None else ((x & 3) ^ (lift if x & 4 else 0))
    return pack(phase3(image(x), image(y)) for t in range(2) for x in range(8) for y in range(8))


def sigma(bits):
    return reduce(xor, ((bits >> (x*8+y)) & 1 for x,y in product((0,4), repeat=2)))


def restrict(table, ids):
    return pack(table[i] for i in ids)


def local_certificate():
    decoder, grounds = read_decoder(), read_grounds()
    q = (4, 8, 12)
    ids = [station_map(p) for p in q]
    core = [cell(t, x, y) for t in range(2) for x in range(4) for y in range(4)]
    all_sites = [a for station in ids for a in station]
    joint = project_kernel([decoder[i] for i in all_sites])
    dims = [raw_dimension(d) for d in (2,3,4)]
    assert dims == [14, 30, 62]
    assert len(project_kernel([decoder[i] for i in core])) == dims[0]
    assert all(len(project_kernel([decoder[i] for i in face])) == dims[1] for face in ids)
    assert all(len(project_kernel([decoder[i] for face in pair for i in face])) == 46
               for pair in combinations(ids,2))
    assert len(set(all_sites)) == 320 and len(joint) == 61
    # The 62-dimensional candidate space consists of 3 individually
    # homogeneous station tables agreeing on their rank-14 common core.
    assert 14 + 3*(30-14) == 62
    def three_sigma(v):
        return reduce(xor, (sigma(v>>(128*i)) for i in range(3)))
    assert all(three_sigma(v) == 0 for v in joint.rows.values())
    # A clear-core homogeneous perturbation with sigma=1 on just ONE
    # station proves the extra constraint is genuinely independent.
    change = pack(((x>>2) & ((y>>2) ^ t)) for t in range(2)
                  for x in range(8) for y in range(8))
    assert sigma(change) == 1 and joint.remainder(change) != 0
    for station in range(3):
        local = project_kernel([decoder[i] for i in ids[station]])
        assert local.remainder(change) == 0
        assert three_sigma(change << (128*station)) == 1
    # Four row entries fix sigma; two column entries also fix the success
    # of the square (0,0,P). A purely quotient bad lift is then impossible.
    sites = (0, 4, 32, 36, 64+4, 64+32)
    pins = (0, 0, 0, 1, 0, 0)
    for lift in (None, 0, 1, 2, 3):
        raw = canonical(lift)
        assert (tuple(raw >> i & 1 for i in sites) == pins) == (lift != 0)
    for d, g in grounds.items():
        baseline = restrict(g, all_sites)
        assert three_sigma(baseline) == int(d not in q)
        if d < 4:
            continue
        # These shared full 128-bit stations depend only on the point's
        # label, zero through three or clear, and never on its incident line.
        a, u = q.index(d & 12), d & 3
        desired = sum(canonical(u if i == a else None) << (128*i) for i in range(3))
        assert joint.remainder(desired ^ baseline) == 0
        for diff in product((0,1), repeat=3):
            twist = sum((change << (128*i)) for i, e in enumerate(diff) if e)
            assert (joint.remainder(desired ^ twist ^ baseline) == 0) == (sum(diff)%2 == 0)
    print('Homogeneous dimensions: core 14, one face 30, two faces 46, three faces 61; '
          'exactly one independent ternary parity, two completions per compatible triple.')
    print('All 12 outside directions admit the pointwise canonical 128-bit tables; '
          'all 8 binary corrections tested for each.')


def fan(m):
    assert m >= 2
    hub = 1
    lines, colored = [], {}
    for i in range(m):
        s, a, b = (1 << (1+i+j*m) for j in range(3))
        u = s ^ hub
        lines.extend([(hub, s, u), (s, a, s^a), (u, b, u^b)])
        colored[s] = colored[b] = True
    names = {p for line in lines for p in line}
    for p in names:
        colored.setdefault(p, False)
    assert all(l[0]^l[1] == l[2] and sum(colored[p] for p in l)==1 for l in lines)
    assert all(len(set(a) & set(b)) <= 1 for a,b in combinations(lines, 2))
    for l in lines[::3]:
        assert all(sum(p in a for a in lines) >= 2 for p in l)
    return lines, colored


def physical_fan(m, word, query, wanted):
    """Independent global raw-equation check with actual pinned sign cells."""
    lines, colored = fan(m)
    boards = [chart(0,(1,2,4*l[0],4*l[1])) for l in lines]
    # Only the physical tiles below force the bad directions of queried
    # main boards. For this independent linear check we also specify the
    # canonical choices on the private leaf boards (which have a witness).
    ds = [4*(next(i for i,p in enumerate(l) if colored[p])+1) for l in lines]
    variables = {}
    eqs = Span()
    def index(key):
        return variables.setdefault(key,len(variables)+1)
    for box, d in zip(boards, ds):
        for e,x,y in product(range(1,16),range(16),range(16)):
            if x > x^e:
                continue
            faces = [(0,box[x],box[y]),(0,box[x^e],box[y^e]),
                     (1,box[x],box[y^e]),(1,box[x^e],box[y])]
            eqs.add(reduce(xor,(1 << index(c) for c in faces),int(e != d)))
    def pin(point, chosen, shift):
        for x,y,t in product((0,1), repeat=3):
            X,Y = 4*x*point,4*y*point
            ref = phase3(0 if chosen else 4*x,0 if chosen else 4*y)
            correction = shift & x & (y ^ t)
            eqs.add((1 << index((t,X,Y))) | (ref ^ correction))
    pin(1,False,0)
    for i in range(m):
        pin(1<<(1+i),True,(word >> i) & 1)
    pin(1^(1<<(1+query)), False,wanted)
    possible = 0 not in eqs.rows
    assert possible == (((word >> query) & 1) == wanted)
    print(f'{len(lines)} complete boards; actual tagged cells {len(variables)}, '
          f'left {word:0{m}b}, query ({query},{wanted}), extension={possible}')


def four_face_boundary():
    # a+b=c+e=3. Both boards meet on the unprescribed station 3.
    points = (1, 2, 4, 7)
    lifts = (1, None, 0, None)
    variables = {}
    equations = Span()

    def variable(tag, x, y):
        return 1 << variables.setdefault((tag, x, y), len(variables) + 1)

    for a, b, lift in ((1, 2, 1), (4, 7, 0)):
        box = chart(0, (1, 2, 4*a, 4*b))
        for direction, x, y in product(range(1, 16), range(16), range(16)):
            if x > x ^ direction:
                continue
            row = (variable(0, box[x], box[y]) ^ variable(0, box[x^direction], box[y^direction])
                   ^ variable(1, box[x], box[y^direction]) ^ variable(1, box[x^direction], box[y]))
            equations.add(row ^ int(direction != (4 ^ lift)))

    change = pack((x >> 2) & ((y >> 2) ^ tag)
                  for tag, x, y in product(range(2), range(8), range(8)))
    count = 0
    for shifts in product(range(2), repeat=4):
        pinned = Span()
        pinned.rows = equations.rows.copy()
        parity = 0
        for p, lift, shift in zip(points, lifts, shifts):
            raw = canonical(lift) ^ (change if shift else 0)
            parity ^= sigma(raw) ^ int(lift not in (None, 0))
            for tag, x, y in product(range(2), range(8), range(8)):
                xx, yy = (x & 3) ^ ((x >> 2)*4*p), (y & 3) ^ ((y >> 2)*4*p)
                bit = (raw >> (64*tag+8*x+y)) & 1
                pinned.add(variable(tag, xx, yy) ^ bit)
        possible = 0 not in pinned.rows
        assert possible == (parity == 0)
        count += possible
    assert count == 8
    print(f'two boards, four prescribed faces: {count}/16 twists extend in the actual square equations')


def main():
    local_certificate()
    four_face_boundary()
    physical_fan(2,2,0,0)
    physical_fan(2,2,0,1)
    physical_fan(3,5,1,1)
    physical_fan(3,5,2,1)


if __name__=='__main__':
    main()
