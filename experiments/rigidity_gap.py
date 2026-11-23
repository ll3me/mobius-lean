"""Finite orbit checks for the four-bit two-table defect gap.

Use geometric directed squares, identifying opposite anchors. Write the
weight as 128+e and let E_d be the count in direction d. Each sign variable
occurs exactly once among the 128 tests for d, so every E_d has parity e.

Compare the given syndrome to the optimum which fails on direction d. Its
binary difference C intersects every certificate evenly. Let h=128−E_d;
C has h elements in d and h+e elsewhere. For a random affine certificate
conditioned to contain a particular r in d, at least one other element of C
must be present if r is in C. For each other q, summing those conditional
probabilities over the h elements r is bounded by the sum of its largest h
coincidence weights. The weights below enumerate all changes of basis; the
factor 2 in the denominator comes from the two translations producing r for
each basis. Relative anchor classes modulo the two opposite-anchor moves
have two geometric representatives in direction d. Consequently
h <= (h+e)*sum(largest h weights). Any nonzero C has >=15 elements because
any q has coincidence probability <=1/14. In particular h=0 is impossible
when 0<e<15.

On the full 256-element anchor group write F_d for the bad indicator and
G_d(chi)=Fhat_d(chi)/2. Every shifted template has 1+2t failures with t>=0
and sum(t)=e. For chi nontrivial, the Walsh transform of the equality gives
|sum_d sign_d G_d(chi)| <= e. Only d with (u+v)·d=0 can contribute.
The exact sign rows, up to overall sign, contain every direction-Walsh row,
so character orthogonality gives sum_d G_d(chi)^2 <= e^2. Summing the 255
nontrivial frequencies and applying Parseval on the anchor group gives
sum_d E_d(128−E_d) <= 255 e^2. The small integer check at the end combines
that bound with the coincidence weights. No floating point is used.
"""
from collections import Counter
from itertools import accumulate

from optimal_support import CHARACTERS, allowed_directions, automorphisms, template


def coincidence_counts(squares):
    counts = Counter()
    for _, image in automorphisms():
        anchors = {image[d]: (image[x], image[y]) for x, y, d in squares}
        x, y = anchors[1]
        a, b = anchors[2]
        # (1,1) and (2,2) reanchoring toggles both relative coordinates.
        dx, dy = x ^ a, y ^ b
        counts[dx & 12, dx ^ dy] += 1
    assert len(counts) == 64 and sum(counts.values()) == 20160
    return counts


def signature_rows(squares, u, v):
    cols = allowed_directions(u, v, True)
    full = (1 << len(cols)) - 1
    counts = Counter()
    for _, image in automorphisms():
        signs = {image[d]: ((u & image[x]).bit_count() ^ (v & image[y]).bit_count()) & 1
                 for x, y, d in squares}
        word = sum(signs[d] << i for i, d in enumerate(cols))
        counts[min(word, full ^ word)] += 1
    return cols, counts


def tagged_cells(x, y, d):
    return {(0, x, y), (0, x ^ d, y ^ d), (1, x, y ^ d), (1, x ^ d, y)}


def verify_small_codewords(counts):
    # In a codeword C every oddly sized template has an EVEN number of toggles.
    # If r belongs to C, condition on templates containing r. Every other test
    # sharing a tagged cell with r has probability 1/14; all remaining tests
    # have probability <=1/105. Thus each r has degree >= k below in the
    # graph of tagged-cell sharing on the W elements of C. Conditional on two
    # tests with different source colors and different sink colors, they are
    # nonadjacent and their common neighbors lie in just two cross color pairs.
    # In each cross pair only two tests can share an R (or C) cell with the
    # specified test, so the common degree is <=4. The same bound holds for
    # two nonadjacent edges among tests with one fixed source/sink: these are
    # distinct edges of K16 indexed by their two tagged cells of common color.
    # Pairwise intersection first forces a common color, then a common cell.
    # Such a star has just 15 tests, and the minimum nonzero weight is 15.
    r = tagged_cells(0, 0, 1)
    for x in range(16):
        for y in range(16):
            count = counts[x & 12, x ^ y]
            if r & tagged_cells(x, y, 2):
                assert count * 14 == 40320
            else:
                assert count * 105 <= 40320
    for weight in range(15, 24):
        minimum_degree = next(k for k in range(weight) if 15*k+2*(weight-1-k) >= 210)
        assert 2*minimum_degree - (weight-2) > 4
    print('difference code: every nonzero weight <=23 is a full 15-test tagged-cell star')


def verify_signs(squares):
    for u, v in CHARACTERS:
        cols, counts = signature_rows(squares, u, v)
        full = (1 << len(cols)) - 1
        for j in range(16):
            word = sum(((j & d).bit_count() % 2) << i for i, d in enumerate(cols))
            assert min(word, full ^ word) in counts
        print(f'characters {(u, v)}: {len(counts)} direction signatures up to sign')


def gap_check():
    squares = template(True)
    verify_signs(squares)
    counts = coincidence_counts(squares)
    verify_small_codewords(counts)
    multiplicities = Counter(counts.values())
    weights = sorted(list(counts.values()) * 2, reverse=True)
    cumulative = [0] + list(accumulate(weights))
    denominator = cumulative[-1]
    assert denominator == 40320 and 14 * weights[0] == denominator
    print('relative class counts:', dict(sorted(multiplicities.items())))
    for e in range(1, 8):
        allowed = [128-h for h in range(1, 129) if (128-h-e) % 2 == 0
                   and h * denominator <= (h+e)*cumulative[h]]
        cap = max(allowed, default=0)
        # For each d, E_d(128−E_d) >= E_d(128−cap).
        lower = (128+e) * (128-cap)
        assert 15*cap < 128+e or lower > 255*e*e
        print(f'e={e}: E_d <= {cap}, variance >= {lower}, upper {255*e*e}')
    print('nonoptimal two-table count >=272 out of 3840 anchored tests')


if __name__ == '__main__':
    gap_check()
