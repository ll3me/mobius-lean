"""Exact rational ranks for the four-bit pullback of the eight-square crossing."""

from fractions import Fraction
from itertools import product


def sign(x, y):
    """The Appendix F three-bit phase, pulled back by dropping the high bit."""
    a, b, c = (x >> i & 1 for i in range(3))
    coeff = (a ^ (b & c), a ^ b ^ (a & c), a ^ b ^ c ^ (a & b))
    parity = sum(bit * (y >> i & 1) for i, bit in enumerate(coeff)) % 2
    return 1 - 2 * parity


def row(x, y, u, v):
    return sign(x, y) * sign(v, u) if x ^ y == v ^ u else 0


def flip_origin(piece, x, y, u, v):
    """Change only the full four-bit table entry at (0,0)."""
    changed = (x == y == 0) != (v == u == 0)
    return -piece if changed else piece


def rational_rank(matrix):
    """Sparse Gaussian elimination with exact rational arithmetic."""
    basis = {}
    for source in matrix:
        current = dict(source)
        while current:
            pivot = min(current)
            coefficient = current[pivot]
            if pivot not in basis:
                basis[pivot] = {j: Fraction(a, coefficient) for j, a in current.items()}
                break
            for j, a in basis[pivot].items():
                value = current.get(j, 0) - coefficient * a
                if value:
                    current[j] = value
                else:
                    current.pop(j, None)
    return len(basis)


def main():
    names = ('pullback R', 'pullback C', 'residual / 2', 'three plus one R', 'three plus one C',
             'flipped R', 'flipped C', 'shared flip residual', 'row flip residual')
    matrices = {name: [[{} for _ in range(256)] for _ in range(2)] for name in names}
    support = shared_support = row_support = 0
    for x, y, u, v in product(range(16), repeat=4):
        crossing = int(x == v and y == u)
        r, c = row(x, y, u, v), row(x, u, y, v)
        defect = int(v == x ^ 8 and u == y ^ 8)
        assert r + c - 2 * crossing == 2 * defect
        support += defect

        # Exact baseline W_3 times W_1, decomposing only the three-bit block.
        low = (x & 7, y & 7, u & 7, v & 7)
        a, b, e, f = low
        high_crossing = (x >> 3 == v >> 3 and y >> 3 == u >> 3)
        base_r = row(a, b, e, f) * high_crossing
        base_c = row(a, e, b, f) * high_crossing
        assert base_r + base_c == 2 * crossing

        flipped_r, flipped_c = flip_origin(r, x, y, u, v), flip_origin(c, x, u, y, v)
        shared_defect = flipped_r + flipped_c - 2 * crossing
        row_defect = flipped_r + c - 2 * crossing
        assert shared_defect in (-2, 0, 2) and row_defect in (-2, 0, 2)
        shared_support += shared_defect != 0
        row_support += row_defect != 0

        cuts = ((16*x + y, 16*v + u), (16*x + u, 16*v + y))
        values = (r, c, defect, base_r, base_c, flipped_r, flipped_c, shared_defect//2, row_defect//2)
        for name, value in zip(names, values):
            if value:
                for matrix, (i, j) in zip(matrices[name], cuts):
                    matrix[i][j] = value

    assert (support, shared_support, row_support) == (256, 308, 282)
    for matrix in matrices['residual / 2']:
        assert all(len(line) == 1 for line in matrix)
        assert {next(iter(line)) for line in matrix} == set(range(256))

    expected = ((16, 128), (128, 16), (256, 256), (32, 256), (256, 32),
                (16, 157), (157, 16), (253, 253), (255, 254))
    print(f'Checked 16^4 = 65536 entries. Residual support: {support}.')
    print('Both residual flattenings are permutation matrices.')
    print(f'Flipping (0,0) in both tables: {shared_support} failures; row table only: {row_support}.')
    print('Tensor                 (xy)|(vu)   (xu)|(vy)')
    for name, ranks in zip(names, expected):
        result = tuple(rational_rank(matrix) for matrix in matrices[name])
        assert result == ranks, (name, result)
        print(f'{name:22} {result[0]:9} {result[1]:11}')


if __name__ == '__main__':
    main()
