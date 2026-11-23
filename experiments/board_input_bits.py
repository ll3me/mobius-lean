"""Fixed-width binary body for complete-board formulas; compare literal source-bit positions."""
from itertools import combinations, product

from full_board_caps import formula_family, verify_union
from axis_relations import solve


def lean_ordered_charts(family):
    """The Lean compiler places all three first wires before the three second wires."""
    if len(family.cores) % 7:
        raise ValueError("expected a formula compiled with seven cores per row")
    charts = []
    for base in range(0, len(family.cores), 7):
        charts.extend(family.cores[base + tag][1] for tag in (0, 1, 3, 5, 2, 4, 6))
    return charts + family.caps


def encode_boards(family, dimension):
    """Pack four zero-based axis fields per chart, LSB first. Shape is public."""
    width = max(1, (dimension - 1).bit_length())
    payload = bytearray()
    buffer = used = 0
    for chart in lean_ordered_charts(family):
        for axis in chart:
            if not 0 <= axis < dimension:
                raise ValueError("axis outside the public ambient space")
            buffer |= axis << used
            used += width
            while used >= 8:
                payload.append(buffer & 255)
                buffer >>= 8
                used -= 8
    if used:
        payload.append(buffer)
    return bytes(payload)


def decode_boards(payload, count, dimension):
    """Read the fixed-width charts, rejecting malformed sizes or axis fields."""
    if count < 0 or dimension < 0:
        raise ValueError("negative chart count or ambient dimension")
    width = max(1, (dimension - 1).bit_length())
    bits = 4*count*width
    if len(payload) != (bits + 7)//8:
        raise ValueError("incorrect complete-board body length")
    data = int.from_bytes(payload, "little")
    if data >> bits:
        raise ValueError("nonzero trailing padding")
    mask = (1 << width) - 1
    charts = [tuple((data >> (width*(4*i+j))) & mask for j in range(4)) for i in range(count)]
    if any(max(chart) >= dimension or len(set(chart)) != 4 for chart in charts):
        raise ValueError("expected four distinct axes within each complete board")
    return charts


def cover_rows(n, edges, x):
    if len(x) != n or any(not (0 <= u < n and 0 <= v < n) for u,v in edges):
        raise ValueError("invalid graph or assignment")
    false = 2*n + len(edges)
    rows = [(false,false,false+1)]
    rows.extend((2*u,2*v,2*n+i) for i,(u,v) in enumerate(edges))
    rows.extend((2*v + int(bit), false, false) for v,bit in enumerate(x))
    return false+2, rows


def location(n, edges, v):
    variables = 2*n + len(edges) + 2
    rows = 1 + len(edges) + n
    width = (4*variables + 37*rows - 1).bit_length()
    return (4*(7*(1+len(edges)+v) + 4) + 1)*width


def check_graph(n, edges):
    positions = [location(n,edges,v) for v in range(n)]
    assert len(set(positions)) == n
    base = None
    for x in product((False,True),repeat=n):
        variables,rows = cover_rows(n,edges,x)
        family = formula_family(variables,rows)
        dimension = 4*variables + 37*len(rows)
        count = variables + 13*len(rows)
        packed = encode_boards(family,dimension)
        assert decode_boards(packed,count,dimension) == lean_ordered_charts(family)
        bits = int.from_bytes(packed,"little")
        if base is None:
            base = bits
        assert bits ^ base == sum((1 << p) for p,on in zip(positions,x) if on)
        assert all(((bits >> p)&1) == on for p,on in zip(positions,x))
        accepts = all(x[u] or x[v] for u,v in edges)
        assert (solve(family.cores) is not None) == accepts
        if n <= 1:
            verify_union([family],accepts)
    print(f'{n} vertices, {len(edges)} edges: all {2**n} assignments checked; '
          f'{count} complete boards, {len(positions)} unique physical input bits.')


def induced_submatching(edges, side):
    """Greedily retain crossing edges with no other edge among their endpoints."""
    neighbors = {}
    for a,b in edges:
        neighbors.setdefault(a,set()).add(b)
        neighbors.setdefault(b,set()).add(a)
    chosen, blocked = [], set()
    for u,v in edges:
        if (u in side) == (v in side) or u in blocked or v in blocked:
            continue
        chosen.append((u,v) if u in side else (v,u))
        blocked.update({u,v} | neighbors[u] | neighbors[v])
    return chosen


def verify_tensor_minor(n,edges,side):
    pairs = induced_submatching(edges,side)
    t = len(pairs)
    assert t
    pivots = {}
    for a in range(1 << t):
        row = 0
        for b in range(1 << t):
            cover = [True]*n
            for i,(u,v) in enumerate(pairs):
                cover[u] = bool((a>>i)&1)
                cover[v] = bool((b>>i)&1)
            value = all(cover[u] or cover[v] for u,v in edges)
            assert value == ((a|b) == (1<<t)-1)
            row |= int(value) << b
        while row:
            i = row.bit_length()-1
            if i not in pivots:
                pivots[i] = row
                break
            row ^= pivots[i]
    assert len(pivots) == 1 << t  # a nonsingular integer minor, already nonsingular mod 2


if __name__ == '__main__':
    check_graph(0,[])
    check_graph(1,[(0,0)])
    check_graph(4,list(combinations(range(4),2)))
    prism = [(0,1),(1,2),(0,2),(3,4),(4,5),(3,5),(0,3),(1,4),(2,5)]
    check_graph(6,prism)
    check_graph(2,[(0,1),(0,1)])
    for size in (2,3,4):
        for side in combinations(range(6),size):
            verify_tensor_minor(6,prism,set(side))
    pairs = [(i,i+4) for i in range(4)]
    verify_tensor_minor(8,pairs,set(range(4)))
    print('Checked all balanced prism cuts and a rank-16 induced-matching minor.')
