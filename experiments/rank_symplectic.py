"""Exact row and column decompositions of the symplectic crossing; standard library only."""

from collections import Counter
from itertools import product
from math import comb
from random import Random


def pauli(label, x, y):
    a, b = label
    if y != x ^ a:
        return 0
    return (-1) ** ((b & x).bit_count() % 2)


def basis(column, label, x, y):
    if column:
        # Left multiplication by J; its transpose is its inverse.
        return (-1) ** (x & 1) * pauli(label, x ^ 1, y)
    return pauli(label, x, y)


def local(n, x, y, u, v):
    crossing = int(x == v and y == u)
    p = pauli((1, 1), x, y) * pauli((1, 1), v, u)
    q = int(x == u and v == y)
    return q, crossing - p - q, p


def spectrum(n, label):
    a, b = label
    p = n * int(label == (1, 1))
    q = (-1) ** ((a & b).bit_count() % 2)
    return q, 1-p-q, p


def convolution(a, b):
    result = [0] * (len(a) + len(b) - 1)
    for i, x in enumerate(a):
        for j, y in enumerate(b):
            result[i+j] += x*y
    return result


def block_test(n):
    labels = list(product(range(n), repeat=2))
    expected = Counter({(-1, 2-n, n): 1, (-1, 2, 0): n*(n-1)//2-1,
                        (1, 0, 0): n*(n+1)//2})
    assert Counter(spectrum(n, lab) for lab in labels) == expected
    result = []
    for column in (False, True):
        matrices = [[{} for _ in labels] for _ in range(3)]
        for x, y, u, v in product(range(n), repeat=4):
            left, right = ((x, u), (v, y)) if column else ((x, y), (v, u))
            i, j = n*left[0]+left[1], n*right[0]+right[1]
            for matrix, value in zip(matrices, local(n, x, y, u, v)):
                if value:
                    matrix[i][j] = value
        ranks = [0, 0, 0]
        for lab in labels:
            vector = [basis(column, lab, x, y) for x, y in labels]
            eigen = spectrum(n, lab)
            if column:
                eigen = eigen[::-1]
            assert sum(x*x for x in vector) == n
            for k, (matrix, value) in enumerate(zip(matrices, eigen)):
                ranks[k] += value != 0
                for i, line in enumerate(matrix):
                    assert sum(a*vector[j] for j, a in line.items()) == value*vector[i]
        # Orthogonality using each vector's n nonzero positions.
        for a in range(n):
            sector = [[basis(column, (a, b), x, x ^ a ^ int(column)) for x in range(n)]
                      for b in range(n)]
            assert all(sum(x*y for x,y in zip(v,w)) == n*int(i == j)
                       for i,v in enumerate(sector) for j,w in enumerate(sector))
        result.append(ranks)
    return list(zip(*result))


def grouped_ranks(n, t):
    """Exact rational ranks, from all eigenvalues of the coefficient matrices."""
    a = n*(n-1)//2
    b = n*(n+1)//2
    values = [(-1, 2-n, n), (-1, 2, 0), (1, 0, 0)]
    ranks = [0] * (2*t+1)
    for rare in range(t+1):
        for middle in range(t-rare+1):
            common = t-rare-middle
            eigen = [1]
            for count, poly in zip((rare,middle,common), values):
                for _ in range(count):
                    eigen = convolution(eigen, poly)
            size = comb(t, rare)*comb(t-rare, middle)*(a-1)**middle*b**common
            for k, e in enumerate(eigen):
                ranks[k] += size * (e != 0)
    return list(zip(ranks, reversed(ranks)))


def central_leading_labels(n, t):
    """Multiplicity of labels reaching degree t as their highest degree."""
    a, b = n*(n-1)//2, n*(n+1)//2
    return sum(comb(t, r)*comb(t-r, r)*(a-1)**(t-2*r)*b**r
               for r in range(t//2+1))


def grouped_entries(n, tiles):
    poly = [1]
    for tile in tiles:
        poly = convolution(poly, local(n, *tile))
    return poly


def grouped_factors(n, tiles, column):
    """Integer eigenbasis factors return n^t times every coefficient at once."""
    polys = [0] * (2*len(tiles)+1)
    groups = []
    for x, y, u, v in tiles:
        left, right = ((x,u),(v,y)) if column else ((x,y),(v,u))
        a = left[0] ^ left[1] ^ int(column)
        groups.append([((a,b), basis(column,(a,b),*left)*basis(column,(a,b),*right))
                       for b in range(n)])
    for word in product(*groups):
        eigen = [1]
        sign = 1
        for label, value in word:
            sign *= value
            if not sign:
                break
            local_poly = spectrum(n, label)
            eigen = convolution(eigen, local_poly[::-1] if column else local_poly)
        if sign:
            for k, e in enumerate(eigen):
                polys[k] += sign*e
    return polys


def main():
    for n in (4, 8, 16):
        ranks = block_test(n)
        a = n*(n-1)//2
        assert ranks == [(n*n, 1), (a,a), (1,n*n)]
        print(f'n={n}: local ranks (Q,E,P) = {ranks}')
    rng = Random(7621)
    for n in (4,8):
        for t in (1,2,3):
            for _ in range(40):
                tiles = []
                for _ in range(t):
                    x,y,v = (rng.randrange(n) for _ in range(3))
                    u = x ^ y ^ v  # test nontrivial, XOR-compatible matrix entries
                    tiles.append((x,y,u,v))
                true_values = grouped_entries(n, tiles)
                assert sum(true_values) == int(all(x == v and y == u for x,y,u,v in tiles))
                for column in (False, True):
                    assert grouped_factors(n, tiles, column) == [n**t*s for s in true_values]
    for n, numerator, denominator in ((4,34,3), (8,39,1)):
        for t in (1,2,4,8,16,32):
            ranks = grouped_ranks(n,t)
            leading = central_leading_labels(n,t)
            assert leading <= ranks[t][0] == ranks[t][1]
            if n == 8:
                assert (2*t+1)*leading >= 39**t
            best = max(r*c for r,c in ranks)
            assert best * denominator**(2*t) <= numerator**(2*t)
            if t in (2,8,32):
                print(f'n={n}, t={t}: worst grouped rank product = {best}')
    print('All entry, spectrum, factorization, and finite rate checks passed.')


if __name__ == '__main__':
    main()
