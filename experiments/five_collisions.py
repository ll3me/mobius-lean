"""Exact local collision and five-dimensional counting bounds.

The first check enumerates GL(4,2) and the shifts placing the direction-1
test at the origin. It keeps the labels of both tables when requested.
The remaining checks are integer inequalities. See docs/FiveCollisions.md.
"""
from collections import Counter
from fractions import Fraction
from itertools import product

from optimal_support import automorphisms, template


def canonical(x, y, d, tagged):
    if tagged:
        return min((x, y), (x ^ d, y ^ d))
    return min(x, x ^ d), min(y, y ^ d)


def pair_probability(tagged):
    squares = template(tagged)
    shifts = [(0, 0), (1, 1)] if tagged else list(product((0, 1), repeat=2))
    counts = Counter()
    maps = 0
    for _, image in automorphisms():
        maps += 1
        reps = {image[d]: (image[x], image[y]) for x, y, d in squares
                if image[d] in (1, 2)}
        x, y = reps[1]
        u, v = reps[2]
        for a, b in shifts:
            counts[canonical(x ^ u ^ a, y ^ v ^ b, 2, tagged)] += 1
    assert maps == 20160 and len(counts) == (128 if tagged else 64)
    return Fraction(min(counts.values()), sum(counts.values()))


def largest_square_sum(total, active, cap):
    """Maximize the sum of squared margins with a common parity and upper cap."""
    smallest = 1 if total % 2 else 2
    if total % 2 and active != 15:
        return None
    if cap < smallest or total < active * smallest:
        return None
    cap -= (cap - smallest) % 2
    margins = [smallest] * active
    remaining = total - sum(margins)
    for i in range(active):
        increment = min(remaining, cap - smallest)
        remaining -= increment
        margins[i] += increment
    if remaining:
        return None
    return sum(x*x for x in margins)


def required_cap(delta, base, multiplicity, denominator):
    total = base + delta
    for cap in range(1, base + 1):
        for active in range(1, 16):
            squares = largest_square_sum(total, active, cap)
            if squares is None:
                continue
            maximum_odd = active - (1 - active % 2)
            max_hits = min(maximum_odd, 1 + multiplicity * delta)
            if total*total - squares <= denominator * delta * max_hits:
                return cap
    return None


def check_five(base, mult, denominator, lower, cutoff):
    # Below the claimed bound, every direction's total is at most this cap.
    cap = lower - 1 - 8*base
    for delta in range(cutoff):
        needed = required_cap(delta, base, mult, denominator)
        assert needed is None or needed > cap
    # Thus every four-dimensional slice has at least base+cutoff failures.
    # cutoff is odd and at least 28 slices must have an even count.
    assert cutoff % 2 == 1
    assert 15*(lower - 1) < 124*(base + cutoff) + 28


def main():
    for tagged, base, mult, denominator, lower, cutoff in [
        (False, 64, 4, 126, 556, 3),
        (True, 128, 2, 252, 1102, 5),
    ]:
        p = pair_probability(tagged)
        assert p == Fraction(1, denominator)
        thresholds = [required_cap(s, base, mult, denominator) for s in range(cutoff)]
        check_five(base, mult, denominator, lower, cutoff)
        print(f'{"Two" if tagged else "One"} table(s): pair probability at least {p}; '
              f'local caps {thresholds}; five-bit anchored lower {mult * lower}/31744.')


if __name__ == '__main__':
    main()
