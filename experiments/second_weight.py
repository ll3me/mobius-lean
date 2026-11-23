"""Exact certificate checker for the four-bit, independent-table second weight.

See docs/SecondWeight.md for the proof. No numerical optimizer is used here.
A geometric test identifies (x,y,d) with (x+d,y+d,d); anchored counts are twice
its weight. The JSON contains only proposed invertible binary maps and positive
integer mixing weights. All inequalities are recomputed.
"""
from collections import Counter
from fractions import Fraction
from functools import lru_cache
from itertools import accumulate, combinations
import json
from pathlib import Path

from optimal_support import automorphisms, template
from rigidity_gap import coincidence_counts, verify_small_codewords, signature_rows, CHARACTERS

DIRS = 15
ORDER = 20160
FULL = (1 << DIRS) - 1
SQUARES = tuple(sorted(template(True), key=lambda r: r[2]))
WITNESSES = json.loads(Path(__file__).with_name('second_weight_witnesses.json').read_text())
PART_LIMIT = {8:32, 9:35, 10:38, 11:41, 12:42}
EXCEPTION = (6,2,1,1,1,1)


def basis_image(basis):
    image = [0]
    for b in basis:
        assert 0 <= b < 16
        image += [x ^ b for x in image]
    assert sorted(image) == list(range(16))
    return image


def collisions(image):
    """Masks of directions meeting the same translated comparison chart."""
    anchors = {image[d]:(image[x],image[y]) for x,y,d in SQUARES}
    groups = {}
    for x,y,d in SQUARES:
        a,b = anchors[d]
        for offset in (0,d):
            shift = (x ^ a ^ offset, y ^ b ^ offset)
            groups[shift] = groups.get(shift,0) | (1 << (d-1))
    assert sum(m.bit_count() for m in groups.values()) == 30
    return tuple(sorted(m for m in groups.values() if m.bit_count() >= 2))


@lru_cache(None)
def subsets(k):
    return tuple(sum(1 << i for i in indices) for indices in combinations(range(DIRS), k))


def partitions(n, cap):
    if n == 0:
        yield ()
    for t in range(min(n,cap),0,-1):
        for rest in partitions(n-t,t):
            yield (t,*rest)


@lru_cache(None)
def certified_min(mixture, k):
    if k <= 1:
        return 0
    # Combining repeated collision masks reduces the work of the exact check.
    weighted = Counter()
    for basis, positive in mixture:
        assert isinstance(positive,int) and positive > 0
        for m in collisions(basis_image(basis)):
            weighted[m] += positive
    return min(sum(w*((m & s).bit_count()//2) for m,w in weighted.items()) for s in subsets(k))


def excludes(e, part):
    sizes = tuple(max(2*t+1-j,0) for j,t in enumerate(part))
    for pairs in WITNESSES:
        mix = tuple((tuple(basis),w) for basis,w in pairs)
        denominator = sum(w for _,w in mix)
        if sum(certified_min(mix,k) for k in sizes) > denominator*e:
            return True
    return False


def candidates(e, patterns):
    # For a single known star of size k on one chart, compute a universal
    # lower bound over its direction masks and all changes of comparison chart.
    @lru_cache(None)
    def impossible_size(k):
        for sub in subsets(k):
            if not any(sum((m&sub).bit_count()//2 for m in p)>e for p in patterns):
                return False
        return True

    allowed = []
    for part in partitions(e,7):
        if sum(t*t for t in part) <= PART_LIMIT[e]:
            allowed.append(part)
            continue
        if impossible_size(2*part[0]+1) or excludes(e,part):
            continue
        assert e == 12 and part == EXCEPTION, (e,part)
        allowed.append(part)
    return allowed


def forced_average(patterns, parts):
    """A fixed 13-star is transported. Count forced excesses in every chart."""
    ordered = sorted(parts,key=lambda p:-sum(t*t for t in p))
    @lru_cache(None)
    def upper(required):
        for p in ordered:
            if len(required)<=len(p) and all(a>=b for a,b in zip(p,required)):
                return sum(t*t for t in p)
        return None

    largest = 0
    for known in subsets(13):
        total = 0
        for masks, multiplicity in patterns.items():
            lower = tuple(sorted((n for m in masks if (n:=(m&known).bit_count()//2)),reverse=True))
            value = upper(lower)
            if value is None:  # Such a set cannot occur in a candidate.
                break
            total += multiplicity * value
        else:
            largest = max(largest,total)
    return Fraction(largest,ORDER)


def orbit_constants():
    minima = []
    for u,v in CHARACTERS:
        cols, counts = signature_rows(SQUARES,u,v)
        full = 2**len(cols)-1
        # The uniformly weighted direction characters have identity covariance.
        chars = []
        for j in range(16):
            b = sum((((j&d).bit_count()%2)<<i) for i,d in enumerate(cols))
            chars.append(min(b,full^b))
        freq = Counter(chars)
        assert set(freq) == set(counts) and sum(counts.values()) == ORDER
        minima.append(min(Fraction(16*counts[c],ORDER*w) for c,w in freq.items()))
    assert minima[:3] == [Fraction(24,35)]*3
    assert minima[3] == Fraction(244,315)
    return minima[0], minima[3]


def variance_min(e, cap, active):
    # A concave quadratic has a minimum at the most concentrated admissible
    # marginals. The improving pair move is (a,b) -> (a+2,b-2) for a>=b.
    parity = e%2
    counts = [max(parity,2-parity) if i<active else parity for i in range(15)]
    remaining = 128+e-sum(counts)
    for i in range(15):
        take = min(remaining,cap-counts[i])
        assert take%2==0 and take>=0
        counts[i] += take
        remaining -= take
    assert remaining==0
    return sum(x*(128-x) for x in counts)


def main():
    pair_counts = coincidence_counts(SQUARES)
    verify_small_codewords(pair_counts)
    cum = [0]+list(accumulate(sorted(list(pair_counts.values())*2,reverse=True)))
    assert cum[-1]==40320
    simple, independent = orbit_constants()
    patterns = Counter(collisions(image) for _,image in automorphisms())
    assert sum(patterns.values())==ORDER
    print(f'{len(patterns)} collision profiles for {ORDER} invertible maps.')
    for e in range(1,13):
        # C = symmetric difference with the ground mask in direction d.
        # Its weight is 2h+e. A nonempty word of weight <=23 must be a whole
        # 15-test cell star, and that changes geometric optimum weight by 13.
        possible = [128-h for h in range(129) if (128-h)%2==e%2
                    and 2*h+e>23 and h*40320 <= (h+e)*cum[h]]
        cap=max(possible,default=0)
        if 15*cap<128+e:
            print(f'e={e}: excluded by directional cap {cap}.')
            continue
        v=variance_min(e,cap,0)
        if v>255*e**2:
            print(f'e={e}: excluded by Parseval, {v} > {255*e**2}.')
            continue
        parts=candidates(e,patterns)
        def required_moment(active):
            v=variance_min(e,cap,active)
            lower=independent*v-(independent-simple)*45*e**2
            return (lower+e**2)/256
        lo=required_moment(0)
        if e<12:
            up=max(sum(t*t for t in p) for p in parts)
            assert lo>up,(e,lo,up)
            print(f'e={e}: average sum of squares >= {lo}, <= {up}.')
            continue
        # With no 13-star exclude every part containing a 6 (larger stars already excluded).
        no_star=max(sum(t*t for t in p) for p in parts if max(p)<6)
        assert lo>no_star
        high=forced_average(patterns,parts)
        lo_high=required_moment(13)
        assert lo_high>high
        print(f'e=12, no 13-star: average >= {lo}, <= {no_star}.')
        print(f'e=12, a 13-star: average >= {lo_high}, <= {high}.')
    print('No geometric weights 129..140. Anchored counts are 256 or at least 282.')


if __name__ == '__main__':
    main()
