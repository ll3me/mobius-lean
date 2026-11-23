"""Three-coloring in simultaneous optima of complete, unweighted four-dimensional boards.

Input charts are four independent bit masks. No direction, pin, selected
square, or port annotation is part of the exported instance.
"""
import argparse
from functools import lru_cache
from itertools import combinations, product
import json
from pathlib import Path

from port_k4 import phase3


def span_points(basis):
    points = [0]
    for b in basis:
        points += [x ^ b for x in points]
    assert len(set(points)) == len(points)
    return points


def lines3(basis):
    points = span_points(basis)[1:]
    return sorted({tuple(sorted((a,b,a^b))) for a,b in combinations(points,2)})


def bridge(a, b, t):
    c = a ^ b
    return [(a,t), (b,a^t), (c,t)]


def graph_charts(n, edges):
    if not isinstance(n,int) or n < 0:
        raise ValueError('expected a nonnegative vertex count')
    if any(not 0 <= u < v < n for u,v in edges) or len(set(edges)) != len(edges):
        raise ValueError('expected a simple graph with canonical endpoints')
    # The two low bits are the shared two-plane U.
    axes = [(1 << (2+2*i), 1 << (3+2*i)) for i in range(n)]
    pairs = list(axes)
    for j, (u,v) in enumerate(edges):
        for h in range(2):
            t = 1 << (2+2*n+2*j+h)
            pairs.extend(bridge(axes[u][h],axes[v][h],t))
        pairs.append(tuple(axes[u][h]^axes[v][h] for h in range(2)))
    main = [(1,2,a,b) for a,b in pairs]
    fresh = 2 + 2*n + 2*len(edges)
    h, k, t = [1 << (fresh+i) for i in range(3)]
    accessory = [(h,k,a,b) for a,b,_ in lines3((1,2,t))]
    return main, accessory, (h,k,t)


def exact_directions(charts):
    """Necessary for actual phase tables: the square (0,0,d) reads identical
    physical cells on *every* board containing d. Check that exactly one
    global physical direction is marked on each board, using Algorithm X.
    No graph-color or Fano identities are used by this checker.
    """
    by_point = {}
    for i,chart in enumerate(charts):
        for d in span_points(chart)[1:]:
            by_point[d] = by_point.get(d,0) | (1 << i)
    candidates = {mask:pt for pt,mask in by_point.items()}
    covers = [[b for b in candidates if b & (1 << i)] for i in range(len(charts))]

    @lru_cache(None)
    def search(rem):
        if not rem:
            return ()
        opts = min(([b for b in covers[i] if b & rem == b]
                    for i in range(len(charts)) if rem & (1 << i)),key=len)
        for b in opts:
            answer = search(rem ^ b)
            if answer is not None:
                return (candidates[b],) + answer
        return None

    return search((1 << len(charts))-1)


def coloring(n, edges):
    return next((z for z in product((1,2,3),repeat=n)
                 if all(z[u] != z[v] for u,v in edges)),None)


def linear_witness(colors, edges):
    mask = sum(color << (2+2*v) for v,color in enumerate(colors))
    for i,(u,v) in enumerate(edges):
        for h in range(2):
            a,b = (colors[q]>>h & 1 for q in (u,v))
            # All three bridge lines are nonzero; this choice works in all four cases.
            bit = int(not (a and not b))
            mask |= bit << (2+2*len(colors)+2*i+h)
    return mask


def solve_attachment():
    """Solve the seven physical boards in five real coordinates, prescribing
    the bad direction 4 and fixing the 32 shared tagged cells on U to the
    same quaternion signs used by every color witness. The input instance
    itself has neither pins nor prescribed directions.
    """
    ids, pivots = {}, {}
    def var(tag,x,y):
        return 1 << (ids.setdefault((tag,x,y),len(ids)+1))
    def add(eq):
        while eq > 1:
            j = eq.bit_length()-1
            if j not in pivots:
                pivots[j] = eq
                return
            eq ^= pivots[j]
        assert eq == 0
    for a,b,_ in lines3((1,2,16)):
        pts = span_points((4,8,a,b))
        for x,y,d in product(range(16),range(16),range(1,16)):
            if x < x^d:
                X,Y,D = pts[x],pts[y],pts[d]
                add(var(0,X,Y)^var(0,X^D,Y^D)^var(1,X,Y^D)^var(1,X^D,Y)^int(D!=4))
    for t,x,y in product(range(2),range(4),range(4)):
        add(var(t,x,y)^phase3(x,y))
    solution = 1
    for j,row in sorted(pivots.items()):
        solution |= ((row & solution).bit_count()%2) << j
    return {c:(solution>>i)&1 for c,i in ids.items()}


def attachment_coordinates(x, aux_axes):
    return (x & 3) | sum(1 << (2+i) for i,a in enumerate(aux_axes) if x & a)


def costs_on_one_world(parts):
    signs = {}
    charts = []
    for board_list, phase in parts:
        charts.extend(board_list)
        for basis in board_list:
            pts = span_points(basis)
            for tag,x,y in product(range(2),pts,pts):
                bit = phase(tag,x,y)
                assert signs.setdefault((tag,x,y),bit) == bit
    costs = []
    for basis in charts:
        pts = span_points(basis)
        bad = sum(1-(signs[0,x,y]^signs[0,x^d,y^d]^signs[1,x,y^d]^signs[1,x^d,y])
                  for d in pts[1:] for x in pts if x < x^d for y in pts)
        costs.append(bad)
    return len(signs), costs


def verify_tables(main, extra, aux_axes, mask, attached):
    def proj(x):
        return (x & 3) | (4 * ((x & mask).bit_count()%2))
    def cap(tag,x,y):
        return attached[tag,attachment_coordinates(x,aux_axes),attachment_coordinates(y,aux_axes)]
    cells,costs = costs_on_one_world([(main,lambda tag,x,y: phase3(proj(x),proj(y))), (extra,cap)])
    assert all(cost==128 for cost in costs)
    return cells


def common_core_world(tag,x,y,h=1):
    # Orient every line {a,b,a+b} cyclically in numerical order. Double
    # these quaternion signs along the core quotient by direction 1.
    a,b = x>>2,y>>2
    dual = (0,2,1,3)[h]
    t,s = ((v & dual).bit_count()%2 for v in (x,y))
    p,q = (b,a) if s else (a,b)
    r = p^q
    quat = bool(p and q and (p==q or p<q<r or q<r<p or r<p<q))
    return int(quat) ^ int(t and b!=0) ^ (t&s)


def soft_witness(main,extra,axes,attached):
    def project(x):
        z = attachment_coordinates(x,axes)
        return (((z>>2)&3) ^ ((z>>1)&1)) | ((z>>2)&4)
    def adjusted(tag,x,y):
        if x<4 and y<4:
            return common_core_world(tag,x,y)
        return attached[tag,attachment_coordinates(x,axes),attachment_coordinates(y,axes)]
    # Deleting *any* of the seven sheets suffices to restore a global optimum.
    # Use a quotient linear functional with that sheet's line as its kernel.
    fano = lines3((1,2,16))
    for j,line in enumerate(fano):
        if set(line) == {1,2,3}:
            local = project
            h = 1
        else:
            h, = set(line) & {1,2,3}
            normal, = [w for w in span_points((1,2,16))[1:]
                       if all((w&q).bit_count()%2==0 for q in line)]
            def local(x):
                z = attachment_coordinates(x,axes)
                return ((z>>2)&3) | (4*((z&normal).bit_count()%2))
        _,costs = costs_on_one_world([(main,lambda tag,x,y:common_core_world(tag,x,y,h)),
                                      (extra[:j]+extra[j+1:],lambda tag,x,y:phase3(local(x),local(y)))])
        assert set(costs) == {128}
    print('All seven single deletions restore simultaneous optima, checked on the rejecting graph.')
    proofs = [(lambda tag,x,y: phase3(project(x),project(y)), [128]*6+[384]),
              (adjusted,[128]*4+[154]*2+[216])]
    for cap,expected in proofs:
        _,costs = costs_on_one_world([(main,common_core_world),(extra,cap)])
        assert costs[:len(main)] == [128]*len(main)
        assert sorted(costs[len(main):]) == sorted(expected)
        print(f'Soft witness: {sum(v!=128 for v in costs)} nonoptimal boards, '
              f'{sum(costs)-128*len(costs)} extra board-counted failures.')


def test():
    fano = lines3((1,2,4))
    assert not any(all(sum((w>>(x-1))&1 for x in line)==2 for line in fano) for w in range(128))
    for a,b,c in product(range(2),repeat=3):
        witnesses = [t for t,p,q in product(range(2),repeat=3)
                     if all(sum(row)==2 for row in ((a,t,p),(b,p,q),(c,t,q)))]
        assert bool(witnesses) == (a^b==c)
    attached = solve_attachment()
    for n in (3,4,5):
        edges = list(combinations(range(n),2))
        yes = 0
        for bits in range(1 << len(edges)):
            graph = [e for j,e in enumerate(edges) if bits & (1 << j)]
            main,extra,axes = graph_charts(n,graph)
            z = coloring(n,graph)
            assert (z is not None) == (exact_directions(main+extra) is not None)
            yes += z is not None
        print(f'{n} vertices: all {1<<len(edges)} simple graphs checked using physical direction incidence; {yes} colorable.')
    for n,graph in [(3,list(combinations(range(3),2))), (4,list(combinations(range(4),2))[1:])]:
        main,extra,aux = graph_charts(n,graph)
        tested = verify_tables(main,extra,aux,linear_witness(coloring(n,graph),graph),attached)
        print(f'{n} vertices, {len(graph)} edges: {len(main)+7} boards, {tested} tagged cells, exactly 128 failures on every complete board.')
    graph = list(combinations(range(4),2))
    main,extra,axes = graph_charts(4,graph)
    assert exact_directions(main) is not None and exact_directions(main+extra) is None
    soft_witness(main,extra,axes,attached)
    print('K4: the 46 main boards admit common-core directions; after the seven-board attachment, no labeling of actual directions works.')


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--graph',type=Path,help='JSON with vertex count and zero-based undirected edges')
    parser.add_argument('--emit',type=Path,help='write only the four spanning vectors of each complete board')
    args = parser.parse_args()
    if args.graph is None and args.emit is None:
        test()
    elif args.graph and args.emit:
        data = json.loads(args.graph.read_text())
        edges = [tuple(sorted(e)) for e in data['edges']]
        main,extra,_ = graph_charts(data['vertices'],edges)
        args.emit.write_text(json.dumps(dict(dimension=5+2*data['vertices']+2*len(edges),boards=main+extra))+'\n')
    else:
        parser.error('--graph and --emit are used together')
