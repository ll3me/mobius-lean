"""Check the intact rectangular crossings used to transfer Singh's slice bound."""
from itertools import product
from optimal_residual import sign


def check(changed_row, changed_column, clean_letters):
    def table(x, y, changed):
        return -sign(x, y) if (x, y) in changed else sign(x, y)

    checked = 0
    for x, y, u_label, v_label in product(range(16), clean_letters, clean_letters, range(16)):
        # On the original tensor, both output labels have been translated by 8.
        u, v = u_label ^ 8, v_label ^ 8
        physical = -2 * int(x == v and y == u)
        if x ^ y == v ^ u:
            physical += table(x, y, changed_row) * table(v, u, changed_row)
            physical += table(x, u, changed_column) * table(v, y, changed_column)
        assert physical == 2 * int(x == v_label and y == u_label)
        checked += 1
    return checked


if __name__ == '__main__':
    row = {(0, 0)}
    for weight, col, excluded in ((282, set(), {0,8}), (304, {(0,1)}, {0,8,1,9})):
        letters = sorted(set(range(16)) - excluded)
        count = check(row, col, letters)
        print(f'{weight} failures: exact 16 by {len(letters)} crossing, checked {count} entries.')
