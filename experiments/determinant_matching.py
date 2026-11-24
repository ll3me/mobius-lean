"""Exact checks of modular cancellation and uniform determinant readouts for matching boards."""
from fractions import Fraction
from functools import lru_cache
from itertools import combinations, permutations, product
from math import prod
from random import Random

from axis_relations import solve
from hybrid_matching_boards import board_network
from optimal_residual import rational_rank
from overlap_fibers import Span


def matching_count(n, edges):
    adj = [0] * n
    for a, b in edges:
        adj[a] |= 1 << b
        adj[b] |= 1 << a

    @lru_cache(None)
    def count(active):
        if not active:
            return 1
        first = active & -active
        rest = active ^ first
        total = count(rest)
        neighbors = adj[first.bit_length() - 1] & rest
        while neighbors:
            partner = neighbors & -neighbors
            total += count(rest ^ partner)
            neighbors ^= partner
        return total

    return count((1 << n) - 1)


def parity_determinant(n, edges):
    rows = [1 << i for i in range(n)]
    for a, b in edges:
        rows[a] |= 1 << b
        rows[b] |= 1 << a
    return int(len(Span(rows)) == n)


THETA = tuple(edge for k in range(2, 5) for edge in ((0, k), (1, k)))
SQUARES = tuple((3 << (2*i)) | (3 << (2*j)) for i, j in combinations(range(3), 2))


def theta_det(mask, path_values, modulus=None):
    # Directed paths 0 -> k -> 1 have the prescribed product u_k.
    mat = [[int(i == j) for j in range(5)] for i in range(5)]
    for i, u in enumerate(path_values):
        k = i + 2
        if mask & (1 << (2*i)):
            mat[0][k], mat[k][0] = 1, -1
        if mask & (2 << (2*i)):
            inv = Fraction(1, u) if modulus is None else pow(u, -1, modulus)
            mat[k][1], mat[1][k] = u, -inv
    value = 0
    for p in permutations(range(5)):
        sign = (-1) ** sum(p[i] > p[j] for i, j in combinations(range(5), 2))
        value += sign * prod(mat[i][p[i]] for i in range(5))
    return value if modulus is None else value % modulus


def rank(rows):
    return rational_rank([{j: a for j, a in enumerate(row) if a} for row in rows])


def check_theta():
    signs = [(1, a, b) for a, b in product((1, -1), repeat=2)]
    signed_tests = [[theta_det(mask, u) for u in signs] for mask in (0, *SQUARES)]
    assert rank(signed_tests) == 4
    assert rank([[a*b for a in left for b in right]
                 for left, right in product(signed_tests, repeat=2)]) == 16
    for u in (tuple(map(Fraction, (1, 2, 3))), (Fraction(-1, 3), Fraction(4), Fraction(1, 2))):
        gram = [[(a/b + b/a) / 2 for b in u] for a in u]
        assert rank(gram) == 2
        for (i, j), mask in zip(combinations(range(3), 2), SQUARES):
            assert theta_det(mask, u) == 7 - 2 * gram[i][j]
    for mask in range(64):
        edges = [e for i, e in enumerate(THETA) if mask >> i & 1]
        count = matching_count(5, edges)
        assert sum(theta_det(mask, u) for u in signs) == 4 * count
        assert parity_determinant(5, edges) == count % 2
        # Exact modular check of two complex-phase formulas, in a field
        # containing primitive third and fourth roots (3 and 5 respectively).
        assert (2 * theta_det(mask, (1, 3, 9), 13) + theta_det(mask, (1, 1, 1), 13)
                - 3 * count) % 13 == 0
        complete = [i for i in range(3) if (mask >> (2*i)) & 3 == 3]
        u = [1, 1, 1]
        if len(complete) == 2:
            u[complete[1]] = 5
        elif len(complete) == 3:
            u[2] = 3
        assert theta_det(mask, u, 13) == count % 13
    print('theta: 64 masks; exact sign recovery; signed test ranks 4,16; reciprocal local rank 2')


def decorate(n, edges):
    blocks = [[(5*v+a, 5*v+b) for a, b in THETA] for v in range(n)]
    incidence = [0] * n
    external = []
    for a, b in edges:
        external.append((5*a+2+incidence[a], 5*b+2+incidence[b]))
        incidence[a] += 1
        incidence[b] += 1
    assert incidence == [3] * n
    return blocks, external


def check_boards():
    blocks, external = decorate(4, list(combinations(range(4), 2)))
    edges = [e for block in blocks for e in block] + external
    lines, ports, _ = board_network(20, edges)
    assert (len(lines), len(ports)) == (60, 30)
    for masks in product((0, *SQUARES), repeat=4):
        kept = [e for block, mask in zip(blocks, masks)
                for i, e in enumerate(block) if mask >> i & 1]
        assert matching_count(20, kept) == 7 ** sum(mask != 0 for mask in masks)
        assert parity_determinant(20, kept) == 1
    rng = Random(517)
    for mask in [(1 << 30)-1, *(rng.getrandbits(30) for _ in range(64))]:
        kept = [e for i, e in enumerate(edges) if mask >> i & 1]
        assert parity_determinant(20, kept) == matching_count(20, kept) % 2
    print('60 boards, 30 ports: 256 tensor-test masks and 65 full/random masks verified')


def check_parity_cuts():
    edges = list(combinations(range(4), 2))
    n = len(edges)
    lines, ports, clear = board_network(4, edges)
    clauses = [(line, ()) for line in lines]
    indicator, parity = [], []
    for mask in range(1 << n):
        allowed = [e for i, e in enumerate(edges) if mask >> i & 1]
        endpoints = [v for e in allowed for v in e]
        pins = dict.fromkeys(clear, 0)
        pins.update((p, mask >> i & 1) for i, p in enumerate(ports))
        feasible = solve(clauses, pins) is not None
        assert feasible == (len(endpoints) == len(set(endpoints)))
        indicator.append(int(feasible))
        parity.append(parity_determinant(4, allowed))
    for mask, bit in enumerate(parity):
        assert bit == sum(ok for word, ok in enumerate(indicator) if not word & ~mask) % 2
    cut_count = 0
    for cut in range(1 << n):
        if not n <= 3*cut.bit_count() <= 2*n:
            continue
        left = [x for x in range(1 << n) if not x & ~cut]
        right = [x for x in range(1 << n) if not x & cut]
        def cut_rank(values):
            return len(Span(sum(values[x | y] << j for j, y in enumerate(right)) for x in left))
        assert cut_rank(parity) == cut_rank(indicator) >= 2
        cut_count += 1
    print(f'K4: parity-count and membership ranks agree at all {cut_count} balanced cuts')


if __name__ == '__main__':
    check_theta()
    check_boards()
    check_parity_cuts()
