"""Certify that every optimal four-bit signing fails on one entire direction.

Run `python3 experiments/optimal_support.py` for determinant checks, or add
`--witness` to print the columns and linear maps for each exhibited minor.
No external packages are required. A map is recorded by the images of the
four standard basis vectors 1, 2, 4, 8 in least-significant-bit order.

For any optimum, every translate of each GL(4,2) image of the relevant
15-square parity certificate contains exactly one failed anchored test.
Indeed each translate contains at least one, and summing the 256 counts
gives exactly 256 because the template contains each nonzero direction once.
Let F_d(x,y) be the indicator of a failed test. The nonconstant character
(u,v) of the translated identity gives a homogeneous linear equation on
its Walsh coefficients Fhat_d(u,v); the sign in column d is the character
at the square's anchor. Translation within a square makes some coefficients
zero automatically. On the remaining columns, the integer matrices below
have full rank over Q because their square minors are nonzero modulo 101.
The four representative character pairs exhaust the GL(4,2) orbits: either
one component is zero, both components are the same nonzero vector, or
they are independent. GL(4,2) acts contragrediently on character indices.
Thus all nonconstant coefficients vanish and each F_d is constant. The
optimal count of 256 out of 3840 then forces exactly one failed direction.
Each direction is attainable by pulling the three-bit construction back
from its quotient. For each of these 15 patterns the solutions form a
translate of the kernel of the same binary equation matrix.
"""

import argparse
import ast
from collections import Counter
from pathlib import Path
import re


PRIME = 101
ROOT = Path(__file__).resolve().parents[1]
CHARACTERS = [(1, 0), (0, 1), (1, 1), (1, 2)]


def template(two_tables):
    module = 'TwoPhases' if two_tables else 'SignObstruction'
    source = (ROOT / 'Mobius' / (module + '.lean')).read_text()
    match = re.search(r'def certificate : List Rectangle :=\s*(\[[^\]]+\])', source)
    if match is None:
        raise ValueError(f'Missing rectangle certificate in {module}.lean')
    squares = ast.literal_eval(match.group(1))
    if sorted(d for x, y, d in squares) != list(range(1, 16)):
        raise ValueError('Expected one square in every nonzero direction')
    cells = Counter()
    for x, y, d in squares:
        for i, j, off_diagonal in [(x, y, False), (x ^ d, y ^ d, False),
                                   (x ^ d, y, True), (x, y ^ d, True)]:
            cells[i, j, two_tables and off_diagonal] += 1
    if any(count % 2 for count in cells.values()):
        raise ValueError('The proposed odd parity certificate has an unpaired cell')
    return squares


def automorphisms():
    # The odd multiplier permutes all 16-bit masks. Traversing them in this
    # order avoids an extended initial segment fixing the same basis vector.
    for index in range(1 << 16):
        mask = (40503 * index + 1) % (1 << 16)
        basis = tuple((mask >> (4 * i)) & 15 for i in range(4))
        image = [0]
        for b in basis:
            image += [x ^ b for x in image]
        if len(set(image)) == 16:
            yield basis, image


def parity(x):
    return x.bit_count() % 2


def allowed_directions(u, v, two_tables):
    if two_tables:
        # The shift (d,d) preserves both tags. A single axis shift may swap them.
        return [d for d in range(1, 16) if parity((u ^ v) & d) == 0]
    return [d for d in range(1, 16) if parity(u & d) == parity(v & d) == 0]


def determinant(rows):
    """Independent modular determinant of the selected integer square minor."""
    n = len(rows)
    a = [[entry % PRIME for entry in row] for row in rows]
    result = 1
    for col in range(n):
        pivot = next((i for i in range(col, n) if a[i][col]), None)
        if pivot is None:
            return 0
        if pivot != col:
            a[col], a[pivot] = a[pivot], a[col]
            result = -result
        result = result * a[col][col] % PRIME
        inverse = pow(a[col][col], -1, PRIME)
        for i in range(col + 1, n):
            factor = a[i][col] * inverse
            for j in range(col, n):
                a[i][j] = (a[i][j] - factor * a[col][j]) % PRIME
    return result


def certificate(squares, u, v, two_tables):
    cols = allowed_directions(u, v, two_tables)
    pivots = {}
    rows, maps = [], []
    for basis, image in automorphisms():
        signs = {image[d]: (-1) ** (parity(u & image[x]) ^ parity(v & image[y]))
                 for x, y, d in squares}
        row = [signs[d] for d in cols]
        reduced = row.copy()
        for col, base_row in pivots.items():
            factor = reduced[col]
            reduced = [(a - factor * b) % PRIME for a, b in zip(reduced, base_row)]
        pivot = next((j for j, a in enumerate(reduced) if a), None)
        if pivot is None:
            continue
        inverse = pow(reduced[pivot], -1, PRIME)
        pivots[pivot] = [a * inverse % PRIME for a in reduced]
        rows.append(row)
        maps.append(basis)
        if len(rows) == len(cols):
            det = determinant(rows)
            if det == 0:
                raise ArithmeticError('Rank selection and determinant disagree')
            return cols, maps, det
    raise ArithmeticError(f'No nonsingular minor found for character {(u, v)}')


def score_rank(two_tables):
    """Compute binary rank from all 3840 coefficient rows using packed integers."""
    pivots = {}
    for d in range(1, 16):
        for x in range(16):
            for y in range(16):
                row = 0
                for i, j, off in [(x, y, False), (x ^ d, y ^ d, False),
                                   (x ^ d, y, True), (x, y ^ d, True)]:
                    variable = 16 * i + j + (256 if two_tables and off else 0)
                    row ^= 1 << variable
                while row:
                    pivot = row.bit_length() - 1
                    if pivot not in pivots:
                        pivots[pivot] = row
                        break
                    row ^= pivots[pivot]
    return len(pivots)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--witness', action='store_true', help='print exact minor indices')
    args = parser.parse_args()
    for two_tables in [False, True]:
        label = 'two tables' if two_tables else 'one table'
        squares = template(two_tables)
        for u, v in CHARACTERS:
            cols, maps, det = certificate(squares, u, v, two_tables)
            print(f'{label}, (u,v)=({u},{v}), columns={len(cols)}, det mod {PRIME}={det}')
            if args.witness:
                print(f'  directions: {cols}\n  GL basis images: {maps}')
        rank = score_rank(two_tables)
        variables = 512 if two_tables else 256
        dimension = variables - rank
        print(f'{label}, 3840 x {variables} score matrix: rank over GF(2)={rank}, '
              f'kernel dimension={dimension}, optimum signings=15*2^{dimension}')


if __name__ == '__main__':
    main()
