"""Test the overlapping full-board construction on small simple graphs of degree <= 4.

Every genuine graph edge owns one global coordinate axis shared only by its
two endpoints. The graph is allowed cycles. Each board contributes its full
set of 1920 unanchored tests, and the union counts duplicates only once.
"""
from itertools import combinations
from functools import lru_cache

from axis_relations import FULL, chart_values, corners
from one_in_three_geometry import canonical
from port_k4 import phase3


@lru_cache(None)
def quotient_table(d):
    pivot = d.bit_length()-1
    def quotient(x):
        if x & (1 << pivot):
            x ^= d
        return (x % (1 << pivot)) | ((x >> (pivot+1)) << pivot)
    return [phase3(quotient(x),quotient(y)) for x in range(16) for y in range(16)]


def largest_matching(edges):
    # Exhaustion is an independent small-graph oracle for the theorem.
    for count in range(len(edges),-1,-1):
        for matching in combinations(edges,count):
            if len(set(v for e in matching for v in e)) == 2*count:
                return matching


def check(n, edges):
    selected = set(largest_matching(edges))
    names = {edge:i for i,edge in enumerate(edges)}
    next_axis = len(edges)
    faces = set()
    cells = {}
    for v in range(n):
        at_v = [edge for edge in edges if v in edge]
        if len(at_v)>4:
            raise ValueError('degree exceeds four')
        coords = chart_values([names[e] for e in at_v] + list(range(next_axis,next_axis+4-len(at_v))))
        next_axis += 4-len(at_v)
        d = next((1 << i for i,e in enumerate(at_v) if e in selected), 3)
        table = quotient_table(d)
        for x in range(16):
            for y in range(16):
                key = coords[x],coords[y]
                assert cells.setdefault(key, table[16*x+y]) == table[16*x+y]
        for x,y,d in FULL:
            faces.add(canonical((coords[x],coords[y],coords[d])))
    assert len(faces) == 1920*n - 2*len(edges)
    actual = sum(1 ^ (sum(cells[x,y] for _,x,y in corners(q)) % 2) for q in faces)
    assert actual == 128*n-2*len(selected)
    print(f'{n} boards, {len(edges)} shared axes, matching {len(selected)}, {actual} geometric failures.')


if __name__ == '__main__':
    for n, edges in [(1,[]),(3,list(combinations(range(3),2))),
                     (4,list(combinations(range(4),2))),
                     (5,list(combinations(range(5),2))),
                     (6,[(i,j) for i in range(3) for j in range(3,6)])]:
        check(n,edges)
