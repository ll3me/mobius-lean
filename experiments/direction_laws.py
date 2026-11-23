"""Eliminate the unknown phase, retaining every homogeneous direction table.

Usage: python3 experiments/direction_laws.py [max_width]
The default widths 1..5 are small; the number of square tests grows as 8**m.
"""

from argparse import ArgumentParser
from math import comb


def direction_equations(width):
    """Return an echelon basis of the constraints on the nonzero directions."""
    q = 1 << width
    direction_bits = q - 1
    pivots = {}
    row_count = 0
    for direction in range(1, q):
        # Four anchors describe the same elementary square.
        representatives = [x for x in range(q) if x < (x ^ direction)]
        for x in representatives:
            for y in representatives:
                row_count += 1
                row = 1 << (direction - 1)
                for a in (x, x ^ direction):
                    for b in (y, y ^ direction):
                        row ^= 1 << (direction_bits + a * q + b)
                # Phase columns are numbered above direction columns. When the
                # former cancel completely, this is a constraint on g alone.
                while row:
                    column = row.bit_length() - 1
                    if column not in pivots:
                        pivots[column] = row
                        break
                    row ^= pivots[column]
    return row_count, [v for k, v in pivots.items() if k < direction_bits]


def check(width):
    row_count, constraints = direction_equations(width)
    direction_count = (1 << width) - 1
    dimension = direction_count - len(constraints)
    predicted = sum(comb(width, degree) for degree in range(1, min(3, width) + 1))
    assert dimension == predicted
    extra = ""
    if width <= 4:
        feasible = [g for g in range(1 << direction_count)
                    if all((g & row).bit_count() % 2 == 0 for row in constraints)]
        best = min(direction_count - g.bit_count() for g in feasible)
        assert len(feasible) == 1 << dimension
        assert best == (1 << max(0, width - 3)) - 1
        extra = f", checked {len(feasible)} feasible signatures; minimum misses {best}"
    print(f"m={width}: {row_count} squares, signature dimension {dimension}{extra}")


if __name__ == "__main__":
    parser = ArgumentParser(description=__doc__)
    parser.add_argument("max_width", type=int, nargs="?", default=5)
    args = parser.parse_args()
    if args.max_width < 1:
        parser.error("max_width must be positive")
    for m in range(1, args.max_width + 1):
        check(m)
