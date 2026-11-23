"""Exact five-bit checks for the affine-plane inequality and its sharp example.

Uses only the Python standard library. The universal argument is in
docs/FiveRowAffine.md. Random test cases below check the coordinate change;
they play no role in proving the universal bound.
"""
from collections import Counter
from itertools import combinations
from random import Random

V = range(32)
PLANES = tuple((a, b, a ^ b) for a, b in combinations(V[1:], 2) if b < (a ^ b))


def dot(a, b):
    return (a & b).bit_count() % 2


def octonion_slope(i):
    a, b, c = ((i >> k) & 1 for k in range(3))
    return (a ^ (b & c)) | ((a ^ b ^ (a & c)) << 1) | ((a ^ b ^ c ^ (a & b)) << 2)


def rectangle_bad(f, g, i, y, d):
    return 1 ^ f[i][y] ^ f[i ^ d][y ^ d] ^ g[i][y ^ d] ^ g[i ^ d][y]


def slice_matrix(f, g, r):
    return [[1 ^ f[i][r ^ j] ^ f[j][r ^ i] ^ g[i][r ^ i] ^ g[j][r ^ j]
             for j in V] for i in V]


def switched(slopes, switches):
    return [[1 ^ dot(slopes[i], j) ^ dot(slopes[j], i) ^ switches[i] ^ switches[j]
             for j in V] for i in V]


def check_design():
    assert len(PLANES) == 155
    assert Counter(d for p in PLANES for d in p) == Counter({d: 15 for d in V[1:]})
    for k, bound in [(1, 156), (2, 139), (3, 130)]:
        assert (544 - 88*k + 12*k*k + 2)//3 == bound


def check_example():
    phase = [[dot(octonion_slope(i), y) for y in V] for i in V]
    for r in V:
        matrix = slice_matrix(phase, phase, r)
        assert all(matrix[i][j] == (i & 7 == j & 7) for i in V for j in V)
        assert sum(map(sum, matrix)) == 128
    failures = [sum(rectangle_bad(phase, phase, x, y, d) for x in V for y in V)
                for d in V[1:]]
    assert sum(failures) == 3072
    assert [i + 1 for i, count in enumerate(failures) if count] == [8, 16, 24]


def check_general_formula():
    rng = Random(19260817)
    for _ in range(3):
        left = [rng.randrange(32) for _ in V]
        right = [rng.randrange(32) for _ in V]
        h, k, v = ([rng.randrange(2) for _ in V] for _ in range(3))
        f = [[dot(left[i], j) ^ dot(right[j], i) ^ h[i] ^ k[j] ^ v[i ^ j]
              for j in V] for i in V]
        g = [[rng.randrange(2) for _ in V] for _ in V]
        all_bad = 0
        for r in V:
            s = [left[i] ^ right[r ^ i] for i in V]
            c = [dot(left[i], r) ^ h[i] ^ k[r ^ i] ^ g[i][r ^ i] for i in V]
            m = slice_matrix(f, g, r)
            assert m == switched(s, c)
            assert all(m[i][j] == rectangle_bad(f, g, i, r ^ j, i ^ j) for i in V for j in V)
            w = sum(map(sum, m))
            assert w >= 128
            all_bad += w - 32
        direct = sum(rectangle_bad(f, g, i, y, d) for i in V for y in V for d in V[1:])
        assert direct == all_bad


def affine_slice_class():
    """Compare coefficients of x_A y_B r_D in the symmetrized slice of f."""
    # Node 1024 denotes the coefficient zero. Every constraint identifies
    # two coefficients, so connected components suffice over GF(2).
    parents = list(range(1025))

    def root(a):
        while parents[a] != a:
            parents[a] = parents[parents[a]]
            a = parents[a]
        return a

    def join(a, b):
        a, b = root(a), root(b)
        if a != b:
            parents[a] = b

    for a in V:
        for b in V:
            if min(a.bit_count(), b.bit_count()) < 2:
                continue
            for d in V:
                left = 1024 if b & d else 32*a + (b | d)
                right = 1024 if a & d else 32*b + (a | d)
                join(left, right)

    groups = {}
    for i in range(1024):
        key = root(i)
        if key != root(1024):
            groups.setdefault(key, set()).add(divmod(i, 32))
    predicted = []
    for a in V:
        for b in V:
            if min(a.bit_count(), b.bit_count()) <= 1:
                predicted.append({(a, b)})
            elif a.bit_count() == b.bit_count() == 2 and a <= b:
                predicted.append({(a, b), (b, a)})
    predicted.append({(a, b) for a in V for b in V
                      if (a ^ b) == 31 and min(a.bit_count(), b.bit_count()) == 2})
    assert {frozenset(g) for g in groups.values()} == {frozenset(g) for g in predicted}
    assert len(groups) == 404
    return len(groups)


def check_changed_rows():
    for s in range(13):
        assert s*(16-s) - 2*min(3*s, 24) >= 0
    # The full, unpunctured kernel has nontrivial Fourier values -7 and 1.
    # Removing k-1 signs changes any coefficient by at most k-1.
    original = [1 - 2*int(d & 7 == 0) + int(d == 0) for d in V]
    coefficients = [sum(w*(-1)**dot(c, d) for d, w in enumerate(original)) for c in V]
    assert coefficients[0] == 25 and set(coefficients[1:]) == {-7, 1}
    for k in range(1, 11):
        assert 26-k >= 6+k

    # Directly verify the collision lower bound and its exact rowwise
    # convolution expression on both sparse and dense perturbations.
    phase = [[dot(octonion_slope(i), y) for y in V] for i in V]
    rng = Random(20261123)
    for k in (1, 4, 8, 10):
        active = set(rng.sample(list(V), k))
        h, ell = ([[rng.randrange(2) if i in active else 0 for y in V] for i in V]
                  for _ in range(2))
        f = [[phase[i][y] ^ h[i][y] for y in V] for i in V]
        g = [[phase[i][y] ^ ell[i][y] for y in V] for i in V]
        anchored = sum(rectangle_bad(f, g, i, y, d) for i in V for y in V for d in V[1:])
        rowwise = sum((original[d] - int(d != 0 and (i ^ d) in active)) *
                      (h[i][y ^ d] ^ ell[i][y]) for i in active for d in V for y in V)
        assert (anchored - 3072)//2 >= rowwise >= 0


if __name__ == '__main__':
    check_design()
    check_example()
    check_general_formula()
    check_changed_rows()
    print('155 planes; each other point lies on 15. Minimum-row bounds: 156, 139, 130.')
    print('Projection: 3072/31744. Failed directions: 8, 16, 24.')
    print('Three seeded two-table checks satisfy the slice identity entry by entry.')
    print('Eight arbitrary rows with the second table free: cut and convolution checks passed.')
    print('Dimension of the first-table class with affine plane scores:',
          affine_slice_class(), 'out of 1024.')
