"""One four-dimensional center, p independent petals on each of two axes.

All coordinates below are in a single binary vector space. Costs in this
file count each geometric tagged square once, even at a common tile.
"""
from itertools import product

from axis_relations import FULL, chart_values, corners, ground

LINE = ((0,0,1),(0,1,1))


def tile(table, d):
    return {(tag,a,b): table[tag][16*(a*d)+b*d] for tag,a,b in product(range(2),repeat=3)}


def defect(table, q):
    return 1 ^ (sum(table[tag][16*x+y] for tag,x,y in corners(q)) % 2)


def leaf_extension(boundary):
    """Extend every raw tile, including the two signs when defect count is one."""
    flat = tuple(tuple(boundary[tag, x & 1, y & 1] for x in range(16) for y in range(16))
                 for tag in range(2))
    sign = tuple(defect(flat,q) for q in LINE)
    seed = [list(ground(1 if sign == (0,0) else 0)) for _ in range(2)]
    if sum(sign) == 1:
        # Start with both axis squares bad, then fix the one with desired defect zero.
        seed[0][0 if sign[0] == 0 else 1] ^= 1
    delta = {key:val ^ boundary[key] for key,val in tile(seed,1).items()}
    result = tuple(tuple(seed[tag][16*x+y] ^ delta[tag,x & 1,y & 1]
                         for x in range(16) for y in range(16)) for tag in range(2))
    assert tile(result,1) == boundary
    return result


def normalize(X,Y,D):
    return min((X,Y,D),(X^D,Y^D,D))


def fan(p, center):
    charts = [((0,1,2,3),center)]
    for side in range(2):
        extension = leaf_extension(tile(center, 1 << side))
        for i in range(p):
            start = 4 + 3*(side*p+i)
            charts.append(((side,start,start+1,start+2),extension))
    actual, faces = {}, set()
    duplicated_bad = 0
    for axes,local in charts:
        coords = chart_values(axes)
        for tag, x, y in product(range(2),range(16),range(16)):
            cell = tag,coords[x],coords[y]
            assert actual.setdefault(cell,local[tag][16*x+y]) == local[tag][16*x+y]
        for q in FULL:
            X,Y,D = (coords[a] for a in q)
            face = normalize(X,Y,D)
            if face in faces:
                duplicated_bad += defect(local,q)
            faces.add(face)
    assert len(faces) == 1920*(1+2*p) - 4*p
    bad = sum(1 ^ (sum(actual[cell] for cell in corners(q)) % 2) for q in faces)
    return bad, duplicated_bad


def main():
    for bits in product((0,1),repeat=8):
        boundary = dict(zip(product(range(2), repeat=3), bits))
        tables = leaf_extension(boundary)
        t = sum(defect(tables,q) for q in LINE)
        assert sum(defect(tables,q) for q in FULL) - t == (128,140,126)[t]
    center = [list(ground(0)),list(ground(0))]
    assert sum(defect(center,q) for q in FULL) == 128
    revised = [r.copy() for r in center]
    for tab in revised:
        tab[16*2+2] ^= 1
    assert sum(defect(revised,q) for q in FULL) == 154
    for p in (1,5,14,28):
        anchored_center, old_duplicates = fan(p,center)
        sacrifice, new_duplicates = fan(p,revised)
        assert (anchored_center,old_duplicates) == (128+254*p,2*p)
        assert (sacrifice,new_duplicates) == (154+252*p,4*p)
        print(f'{p} petals per axis: best with center optimal {anchored_center}, '
              f'explicit nonoptimal-center witness {sacrifice}.')
    print('All 256 concrete eight-bit interfaces lift to costs 128/140/126 outside the shared line.')


if __name__ == '__main__':
    main()
