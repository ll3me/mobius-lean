"""Five-bit lower bounds from the four-bit second weight and incidence arithmetic.

Reconstructs all permitted parity patterns up to a change of coordinates.
Uses only integer arithmetic; no optimization solver is used.
"""
from collections import Counter
from math import comb


POINTS = tuple(range(1, 32))
HYPERPLANES = tuple(tuple(a for a in POINTS if (a & d).bit_count() % 2 == 0)
                    for d in POINTS)
FULL_MASK = (1 << 32) - 2


def quadratics(n):
    """All Boolean quadratic functions on n bits vanishing at the origin."""
    monomials = [1 << i for i in range(n)]
    monomials += [(1 << i) | (1 << j) for i in range(n) for j in range(i)]
    masks = [sum(1 << x for x in range(1 << n) if x & t == t) for t in monomials]
    value = 0
    yield value
    for i in range(1, 1 << len(masks)):
        value ^= masks[(i & -i).bit_length() - 1]
        yield value


def residual_patterns(base, total):
    odd = total % 2
    slack = 15*total - 124*base
    for rank in ([0] if odd else range(3)):
        # When the global parity is even, the row/column parity linear
        # forms may have rank 0, 1, or 2. Send their joint kernel to
        # the first 5-rank coordinates by a linear change of basis.
        kernel_order = 1 << (5 - rank)
        kernel_mask = ((1 << kernel_order) - 1) & FULL_MASK
        for q in quadratics(5 - rank):
            zero_set = kernel_mask ^ q
            even_slices = (31 + 2*zero_set.bit_count() if odd else
                           2*(32-kernel_order) + 4*zero_set.bit_count())
            if even_slices > slack or (even_slices - slack) % 2:
                continue
            budget = (slack - even_slices)//2
            residues = []
            for h in HYPERPLANES:
                inside = sum((zero_set >> a) & 1 for a in h)
                even_here = 15 + 2*inside if odd else 4*inside + 2*sum(
                    a >= kernel_order for a in h)
                linear = 8*odd - 60*base + 7*total - even_here
                if linear % 2:
                    break
                residues.append((linear//2) % 8)
            else:
                if (max(residues) <= budget and sum(residues) <= 15*budget and
                    15*budget <= sum(r + 8*((budget-r)//8) for r in residues) and
                    (sum(residues) - 15*budget) % 8 == 0):
                    yield even_slices, budget, residues


def ordered_counts(n, values, total):
    """All counts of n items with allowed weights and specified total."""
    if len(values) == 1:
        if n*values[0] == total:
            yield Counter({values[0]: n})
        return
    v = values[-1]
    for k in range(min(n, total//v) + 1):
        for left in ordered_counts(n-k, values[:-1], total-k*v):
            yield left + Counter({v: k})


def choose(n, i):
    return comb(n, i) if 0 <= i <= n else 0


def code_spectrum_ok(length, counts):
    """The count of Fourier coefficients of each weight must be nonnegative.

    The 32 messages are allowed to produce repeated words. Expanding a sum
    of characters over all messages shows that, for each k, the Krawtchouk
    sum equals 32 times the number of zero-sum k-subsets of the columns.
    """
    messages = Counter({length-w: n for w, n in counts.items() if n})
    messages[0] += 1  # also include the zero vector d
    # Every codeword has the same number of preimages under a linear map.
    if 32 % messages[0] or any(n % messages[0] for n in messages.values()):
        return False
    for k in range(length + 1):
        total = sum(n*sum((-1)**j * choose(w, j) * choose(length-w, k-j)
                          for j in range(k+1)) for w, n in messages.items())
        if total < 0 or total % 32:
            return False
    return True


def check():
    # Every candidate below these starts has already been excluded by the
    # averaged lower bound with at least 28 even four-dimensional slices.
    for base, totals in [(71, (589, 590)), (141, (1168, 1169, 1170))]:
        for total in totals:
            survived = Counter()
            spectra = {}
            for even_slices, budget, residues in residual_patterns(base, total):
                hist = tuple(sorted(Counter(residues).items()))
                survived[even_slices, budget, hist] += 1
                if len(hist) == 1:
                    r, n = hist[0]
                    key = budget, r
                    if key not in spectra:
                        spectra[key] = any(code_spectrum_ok(budget, dist) for dist in
                            ordered_counts(n, tuple(range(r, budget+1, 8)), 15*budget))
                    assert not spectra[key]
                    continue
                assert base == 141 and total == 1170 and budget == 11
                assert hist == ((3, 15), (7, 16))
                # Total hyperplane counts are 15*11=165. Their 31 least
                # residues sum to 157, so exactly one of the fifteen 3s is 11.
                for j, r in enumerate(residues):
                    if r != 3:
                        continue
                    v = residues.copy()
                    v[j] += 8
                    eight_t = [sum(v[d-1] for d in h) - 7*budget for h in HYPERPLANES]
                    assert any(x < 0 or x % 8 for x in eight_t)
            print(f'base={base}, total={total}: {dict(survived)}; all excluded.')
    print('Five-bit anchored lower bounds: 2364/31744 (one table), 2342/31744 (two).')


if __name__ == '__main__':
    check()
