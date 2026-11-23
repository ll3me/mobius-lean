"""A reusable left summary for unpinned complete boards on k real stations."""
from itertools import combinations, product

from free_direction_coloring import exact_directions, lines3, solve_attachment, span_points, verify_tables


def halves(k, graph, query):
    """Size and shared addresses depend only on k, even when the graph changes."""
    pairs = list(combinations(range(k),2))
    e = [1 << (2+i) for i in range(k)]
    neutral = [1 << (2+k+i) for i in range(k)]
    start = 2+2*k
    dummy = [(1 << (start+2*i),1 << (start+2*i+1)) for i in range(len(pairs))]
    left = [(1,2,x,y) for x,y in zip(e,neutral)]
    for j,(u,v) in enumerate(pairs):
        a,b = (e[u],e[v]) if (graph>>j)&1 else dummy[j]
        left.append((1,2,a,b))
    start += 2*len(pairs)
    right = []
    mask = 0
    for u in range(k):
        a,b = 1 << (start+2*u),1 << (start+2*u+1)
        # On the omitted line the unique linear selector is zero, and on
        # the four other points it is one. Prescribe s(e_u) via this line.
        zero = u in query
        omitted = set(span_points((e[u],a) if zero else (a,b))) - {0}
        right.extend((1,2,p,q) for p,q,r in lines3((e[u],a,b)) if {p,q,r} != omitted)
        mask |= b if zero else e[u]
        mask |= neutral[u]  # a neutral board accepts either station value
    for a,_ in dummy:
        mask |= a
    start += 2*k
    h,j,t = [1 << (start+i) for i in range(3)]
    extra = [(h,j,a,b) for a,b,_ in lines3((1,2,t))]
    return left,right,extra,(h,j,t),mask


def cells(boards):
    return {(t,x,y) for basis in boards for pts in [span_points(basis)]
            for t,x,y in product(range(2),pts,pts)}


def test():
    triples = lines3((1,2,4))
    for omit in triples:
        valid = [mask for mask in range(128)
                 if all(sum((mask>>(x-1))&1 for x in row)==2 for row in triples if row!=omit)]
        assert valid == [sum(1<<(x-1) for x in range(1,8) if x not in omit)]
    for k in (2,3,4):
        pairs = list(combinations(range(k),2))
        signatures = set()
        for graph in range(1 << len(pairs)):
            answers = []
            for i,query in enumerate(pairs):
                left,right,extra,_,_ = halves(k,graph,query)
                assert len(left)==k+len(pairs) and len(right)==6*k and len(extra)==7
                got = exact_directions(left+right+extra) is not None
                assert got == (not (graph>>i)&1)
                answers.append(got)
            signatures.add(tuple(answers))
        assert len(signatures) == 1 << len(pairs)
        print(f'{k} shared stations: {len(signatures)} distinguishable left graphs, all {len(pairs)} future pair queries tested.')
    k,graph,query = 4,5,(1,3)
    left,right,extra,axes,mask = halves(k,graph,query)
    shared = cells(left) & cells(right+extra)
    expected = cells([(1,2,1<<(2+i)) for i in range(k)])
    assert shared==expected and len(shared)==32+96*k
    verify_tables(left+right,extra,axes,mask,solve_attachment())
    print(f'Checked the complete optimizing tables on a {len(left)+len(right)+len(extra)}-board join with exactly {len(shared)} common real tagged cells.')


if __name__ == '__main__':
    test()
