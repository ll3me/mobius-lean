"""Search and independently check a two-defect K4 on the original four-bit domain."""

from collections import Counter
from itertools import combinations
from random import Random

from one_in_three_geometry import ENDS, canonical, corners, wire

EDGES = tuple(combinations(range(4), 2))
INTERNAL = tuple(i for i in range(15) if i not in ENDS)


def compatible(p, q):
    x, y, d = p
    u, v, e = q
    a, b = x ^ u, y ^ v
    sub = (0, d, e, d ^ e)
    return d != e and a not in sub and b not in sub and (a ^ b) not in sub


def equations(ports):
    data = []
    for edge, (i, j) in enumerate(EDGES):
        chart = wire(ports[i], ports[j])
        for face in INTERNAL:
            data.append((edge, face, canonical(chart[face])))
    return data


def packed(square):
    bits = 0
    for tag, x, y in corners(square):
        bits ^= 1 << (256*tag + 16*x + y)
    return bits


def echelon(forms):
    """Reduce all equation rows, tracking the corresponding RHS row combinations."""
    basis, dependencies = {}, []
    for i, vector in enumerate(forms):
        comb = 1 << i
        while vector:
            p = vector.bit_length()-1
            if p not in basis:
                basis[p] = vector, comb
                break
            row, source = basis[p]
            vector ^= row
            comb ^= source
        else:
            dependencies.append(comb)
    return basis, dependencies


def solve(system, target):
    basis, dependencies = system
    if any((target & d).bit_count() % 2 for d in dependencies):
        return None
    assignment = 0
    for p in sorted(basis):
        form, comb = basis[p]
        if ((form & assignment).bit_count() + (comb & target).bit_count()) % 2:
            assignment |= 1 << p
    return assignment


def check_assignment(ports):
    data = equations(ports)
    if len({q for _, _, q in data}) != 78:
        return None
    forms = [packed(q) for _,_,q in data]
    system = echelon(forms)
    full = (1 << 78)-1
    for a,b in combinations(range(78),2):
        target = full ^ (1 << a) ^ (1 << b)
        answer = solve(system,target)
        if answer is not None:
            assert [i for i,f in enumerate(forms) if (f&answer).bit_count()%2 == 0] == [a,b]
            return answer, (a,b), data, len(system[0])
    return None


def search(seed=1):
    rng = Random(seed)
    initial = ((0,5,2), (4,8,12))
    pool = [(x,y,d) for d in range(1,16) for x in range(16) for y in range(16)
            if compatible(initial[0],(x,y,d)) and compatible(initial[1],(x,y,d))]
    rng.shuffle(pool)
    for p,q in combinations(pool,2):
        if (p[2] == 8 or q[2] == 8) and compatible(p,q):
            ports=(*initial,p,q)
            result=check_assignment(ports)
            if result:
                return ports,result
    raise ValueError('No four-bit K4 witness in this search.')


# First two ports keep the identity chart. The other two determine the
# remaining five GL(4,2) charts; row and column tables always share addresses.
PORTS = ((0, 5, 2), (4, 8, 12), (5, 14, 15), (1, 3, 8))
GAUSSIAN = (
    226164189177522500245151737758017633069269865194634599156977890305702363136,
    29117639627547775358470814009643733826051453228222242992937472458760344698880,
)
NEAR = (
    115340367647218111683266917363723575547885951215506551248727091356869701271552,
    115340367647218111683266917363723575547885909677131682970106063112899068035072,
)


def phase3(p, q):
    a, b, c = [(p >> i) & 1 for i in range(3)]
    u, v, w = [(q >> i) & 1 for i in range(3)]
    return (u & (a ^ (b & c))) ^ (v & (a ^ b ^ (a & c))) ^ (w & (a ^ b ^ c ^ (a & b)))


def quotient_mask(project):
    return sum(phase3(project(x), project(y)) << (16*x + y)
               for x in range(16) for y in range(16))


def failure_indices(squares, row, col):
    """Direct, Boolean evaluation, independent of the packed matrix helper."""
    failed = []
    for i, (x, y, d) in enumerate(squares):
        parity = ((row >> (16*x + y)) ^ (row >> (16*(x ^ d) + (y ^ d))) ^
                  (col >> (16*x + (y ^ d))) ^ (col >> (16*(x ^ d) + y))) & 1
        if parity == 0:
            failed.append(i)
    return failed


def main():
    ports, (assignment, fail, data, rank) = search()
    assert ports == PORTS and rank == 75
    forms = [packed(q) for _, _, q in data]
    selected = [q for _, _, q in data]
    system = echelon(forms)
    all_good = (1 << len(forms)) - 1
    assert solve(system, all_good) is None
    assert all(solve(system, all_good ^ (1 << i)) is None for i in range(len(forms)))
    assert (assignment % (1 << 256), assignment >> 256) == GAUSSIAN
    assert failure_indices(selected, *GAUSSIAN) == list(fail) == [0, 65]
    assert len(set(selected)) == len(selected) == 78

    full = [(x, y, d) for d in range(1, 16) for x in range(16) for y in range(16)]
    counts = Counter(d for _, _, d in selected)
    endpoint_directions = {p[2] for p in ports}
    assert counts == {d: 3 if d in endpoint_directions else 6 for d in range(1, 16)}

    ground8 = quotient_mask(lambda x: x & 7)
    ground2 = quotient_mask(lambda x: (x & 5) | ((x & 8) >> 2))
    for direction, mask in [(8, ground8), (2, ground2)]:
        assert failure_indices(full, mask, mask) == [
            i for i, q in enumerate(full) if q[2] == direction]
        assert len(failure_indices(selected, mask, mask)) == 3

    assert NEAR == (ground2 ^ (1 << 19), ground2 ^ (1 << 115))
    for i,new in zip((19,115), NEAR):
        assert (ground2 >> i) & 1 == 1 and (new >> i) & 1 == 0
    assert failure_indices(selected, *NEAR) == [35, 45]
    assert len(failure_indices(full, *NEAR)) == 304
    assert len(failure_indices(full, *GAUSSIAN)) == 2948

    # A single table bit can toggle only one unoriented square per direction.
    # At least two selected tests read every active bit, so a single flip of
    # any full optimum cannot reduce its score on this K4.
    incidence = Counter(c for q in selected for c in corners(q))
    assert min(incidence.values()) >= 2
    for direction in endpoint_directions:
        baseline = {q for q in selected if q[2] == direction}
        subset_bits = Counter(c for q in baseline for c in corners(q))
        assert max(subset_bits.values()) == 1
        assert all(degree >= 2*subset_bits[c] for c,degree in incidence.items())

    # Two distinct bit flips toggle at least 28 geometric tests: the stars of
    # size 15 at distinct cells meet in at most one test. At most two toggled
    # tests are in the sole bad direction of a ground state. Thus two flips
    # from any full optimum cost at least 2*(128+28-4) = 304 anchored tests.
    geometric = [q for q in full if q == canonical(q)]
    stars = Counter(c for q in geometric for c in corners(q))
    shared = Counter(pair for q in geometric for pair in combinations(sorted(corners(q)),2))
    assert len(geometric) == 1920 and len(stars) == 512 and set(stars.values()) == {15}
    assert max(shared.values()) == 1
    print('K4 ports (x,y,d):', ports)
    print('78 distinct squares; GF(2) rank 75; zero or one failure impossible.')
    print('Ground-state direction frequencies in the selected faces:', sorted(counts.items()))
    print('Full optimal quotient tables: 256 anchored full failures, 3 selected failures.')
    for title, pair in [('Gaussian', GAUSSIAN), ('Two flips from a quotient optimum', NEAR)]:
        print(title, '| full anchored:', len(failure_indices(full,*pair)))
        print('  row:', pair[0])
        print('  col:', pair[1])
        for i in failure_indices(selected,*pair):
            edge, face, square = data[i]
            print('  failure: 0-based index',i,'edge',EDGES[edge],
                  '1-based template face',face+1,'canonical square',square)


if __name__ == '__main__':
    main()
