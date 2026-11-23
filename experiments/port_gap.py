"""Check all directional pair frequencies for the 266 anchored weak gap.

Each matrix occurs with all 256 anchor translations. Condition on a fixed
geometric face of direction d. Each basis has exactly two translations
placing its direction-d face there. Canonical relative keys quotient the
opposite-anchor shifts (d,d) and (e,e). Every key therefore represents
two geometric faces in the e-slice; each has the recorded multiplicity.
"""
from array import array

from optimal_support import automorphisms, template


def relative(d, e, x, y):
    """Return a canonical packed pair of relative anchors."""
    return 16*min(x, x ^ d, x ^ e, x ^ d ^ e) + (x ^ y)


def main():
    faces = template(True)  # Includes paired-cell and unique-direction checks.
    keys = [(d, e) for d in range(1, 16) for e in range(1, 16) if d != e]
    counts = {pair: array('H', [0])*256 for pair in keys}
    relative_keys = {(d, e): [relative(d, e, offset // 16, offset % 16)
                              for offset in range(256)] for d, e in keys}
    n = 0
    for _, g in automorphisms():
        n += 1
        anchors = [0]*16
        for x, y, d in faces:
            anchors[g[d]] = 16*g[x]+g[y]
        for pair, row in counts.items():
            d, e = pair
            key = relative_keys[pair][anchors[d] ^ anchors[e]]
            row[key] += 1
    assert n == 20160
    for (d, e), row in counts.items():
        representatives = [int(row[relative(d, e, x, y)])
                           for x in range(16) if x < (x ^ e) for y in range(16)]
        assert len(representatives) == 128
        assert sum(representatives) == 40320
        assert min(representatives) == 160 and max(representatives) == 2880
    print('All 210 ordered direction pairs, 128 geometric displacements each: '
          'mass 40320, min 160, max 2880.')
    for excess in range(1, 5):
        # E=128-h is maximal among 15 directions summing to 128+excess,
        # so E>=9. The double-count gives E*(h+excess)<=252*excess.
        possible = [h for h in range(120)
                    if (128-h)*(h+excess) <= 252*excess]
        assert all(2*h+excess < 15 for h in possible)
        print(f'excess {excess}: h in {possible}; '
              f'maximum nonzero difference weight {2*max(possible)+excess} < 15')


if __name__ == '__main__':
    main()
