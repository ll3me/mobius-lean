#!/usr/bin/env python3
"""Classify optimum extensions of three actual hyperplane boundary pairs.

Each physical R/C address is stored once. Coefficients are the checked
four-bit homogeneous decoder, which overlap_fibers.read_decoder also tests
against all 3,840 square equations and an independent full-rank elimination.
"""

from itertools import combinations, product
from functools import reduce
from operator import xor
from pathlib import Path
import re

from overlap_fibers import Span, block, cell, pack, phase3, project_kernel, read_decoder, read_grounds


def orthogonal(rows, n):
    """Generate the kernel of the binary matrix with the given parity checks."""
    echelon = Span(rows)
    pivots = sorted(echelon.rows)
    basis = []
    for free in range(n):
        if free in echelon.rows:
            continue
        v = 1 << free
        for i in pivots:
            if (v & echelon.rows[i]).bit_count() % 2:
                v |= 1 << i
        basis.append(v)
    return basis


def face(normal):
    return tuple(x for x in range(16) if (x & normal).bit_count() % 2 == 0)


def restriction(table, sites):
    return pack(table[s] for s in sites)


def signature(table):
    row = ((0, 3), (1, 1), (3, 0), (3, 3))
    col = ((0, 2), (1, 1), (2, 0), (2, 2))
    return (sum(table[cell(0, x, y)] for x, y in row)
            + sum(table[cell(1, x, y)] for x, y in col)) % 2


def visible(d, spaces):
    return tuple(d if d in u else 0 for u in spaces)


def pair_space(decoder, all_sites, pair_sites):
    """Impose the three homogeneous two-face image tests on physical addresses."""
    index = {site: i for i, site in enumerate(all_sites)}
    checks = []
    for sites in pair_sites:
        image = project_kernel([decoder[s] for s in sites])
        for parity in orthogonal(image.rows.values(), len(sites)):
            checks.append(sum(1 << index[s] for j, s in enumerate(sites) if parity >> j & 1))
    return Span(orthogonal(checks, len(all_sites)))


def pencil_perturbation(s):
    tag, xy = divmod(s, 256)
    x, y = divmod(xy, 16)
    if (x & 3) not in (0, 3) or (y & 3) not in (0, 3):
        return 0
    u, v = x & 1, y & 1
    return (u if tag else 1-u) & v


def all_clear(s):
    xy = s % 256
    x, y = divmod(xy, 16)
    def fold(z):
        return (z >> 2) + (4 if z & 3 else 0)
    return phase3(fold(x), fold(y))


def inspect(normals, decoder, grounds):
    spaces = [set(face(h)) for h in normals]
    sites = [set(block(sorted(u))) for u in spaces]
    pair_ids = list(combinations(range(3), 2))
    pairs = [sorted(sites[i] | sites[j]) for i, j in pair_ids]
    union = sorted(set.union(*sites))
    image = project_kernel([decoder[s] for s in union])
    local = pair_space(decoder, union, pairs)
    assert all(local.remainder(v) == 0 for v in image.rows.values())

    pair_images = [project_kernel([decoder[s] for s in col]) for col in pairs]
    assert all(len(im) == 46 for im in pair_images)
    directions = set(range(1, 16))
    profiles = {d: visible(d, spaces) for d in directions}
    patterns = sorted({(a,b,c) for a,b,c in product(range(16), repeat=3)
                       if all(any(profiles[d][i] == (a,b,c)[i] and profiles[d][j] == (a,b,c)[j]
                                  for d in directions) for i,j in pair_ids)})
    possible_global = {}
    for d in directions:
        residue = image.remainder(restriction(grounds[d], union))
        possible_global.setdefault(residue, set()).add(d)
    proper_pencil = normals == (1,2,3)
    expected = (61,62,16,15) if proper_pencil else (54,54,14,14)
    assert (len(image),len(local),len(patterns),len(possible_global)) == expected

    pair_opportunities = [
        {d: im.remainder(restriction(grounds[d], col)) for d in directions}
        for im,col in zip(pair_images,pairs)
    ]
    def pairs_allow(table):
        return [
            {d for d,c in options.items() if c == im.remainder(restriction(table, col))}
            for options, im, col in zip(pair_opportunities,pair_images,pairs)
        ]
    representatives = {}
    for profile in patterns:
        compatible = [d for d in directions if profiles[d] == profile]
        root = (grounds[compatible[0]] if compatible
                else tuple(all_clear(s) for s in range(512)))
        lifts = (0,1) if proper_pencil else (0,)
        for bit in lifts:
            table = tuple(b ^ (bit * pencil_perturbation(s)) for s,b in enumerate(root))
            two = pairs_allow(table)
            for (i,j),allow in zip(pair_ids,two):
                assert allow == {d for d in directions if (profiles[d][i],profiles[d][j]) ==
                                 (profile[i],profile[j])}
                assert allow
            residue = image.remainder(restriction(table,union))
            assert residue not in representatives
            sigma = signature(table) if proper_pencil else None
            representatives[residue] = profile, sigma
            whole = possible_global.get(residue, set())
            expected_dirs = {d for d in compatible
                             if not proper_pencil or sigma == int(d in (2,3))}
            assert whole == expected_dirs
    # For each visible profile the solutions of the pair tests form one
    # affine coset of 'local': on a pair, compatible d have the same
    # restricted basepoint modulo the pair's homogeneous image.
    for (i,j), records in zip(pair_ids,pair_opportunities):
        for a,b in combinations(directions, 2):
            assert ((records[a] == records[b]) ==
                    ((profiles[a][i],profiles[a][j]) == (profiles[b][i],profiles[b][j])))
    assert len(representatives) == len(patterns) * 2**(len(local)-len(image))
    if proper_pencil:
        assert signature([pencil_perturbation(i) for i in range(512)]) == 1
        assert all(signature(grounds[d]) == (d in (2,3)) for d in directions)
        assert len(sites[0]&sites[1]&sites[2]) == 32
    print(f'normals {normals}: {len(union)} physical cells, union rank {len(image)}, '
          f'pair-compatible rank {len(local)}, {len(patterns)} visible profiles. '
          f'{len(possible_global)} of {len(representatives)} pair-compatible affine classes lift.')
    if proper_pencil:
        unfixed = tuple(all_clear(i) for i in range(512))
        print('All-clear pair directions AB, AC, BC:', [sorted(ds) for ds in pairs_allow(unfixed)])
        print('Exactly 15 profiles lift at the prescribed 8-cell parity, '
              'and neither parity of the all-clear profile lifts.')
    else:
        print('The all-clear profile extends along both directions 7 and 15.')


def check_interpolator(decoder):
    """Reconstruct the interpolation arrays checked in ThreeFaceCompletion.lean."""
    full = Path(__file__).resolve().parents[1] / 'Mobius' / 'ThreeFaceCompletion.lean'
    source = full.read_text()

    def field(name):
        part = source.split('private def ' + name + ' : Array ', 1)[1].split(':=', 1)[1]
        part = part.split('private def ', 1)[0]
        return list(map(lambda x: int(x, 0), re.findall(r'0x[0-9a-f]+|[0-9]+', part)))

    def choose(sites, span):
        selected = []
        for i in sites:
            if span.remainder(decoder[i]):
                span.add(decoder[i])
                selected.append(i)
        return selected

    def solve(equations):
        echelon = Span((mask << 1) | bit for mask,bit in equations)
        assert 0 not in echelon.rows
        word = 1
        for j in sorted(echelon.rows):
            if (word & echelon.rows[j]).bit_count() % 2:
                word ^= 1 << j
        return word >> 1

    A, B, C = (block(face(n)) for n in (1, 2, 3))
    span = Span()
    common = choose(block(range(0,16,4)), span)
    parity = reduce(xor, (decoder[cell(0,x,y)] for x,y in ((0,3),(3,0),(3,3))))
    assert span.remainder(parity)
    span.add(parity)
    probes = choose(C, span)
    assert common == field('corePins') and probes == field('freePins')
    assert len(common) == 14 and len(probes) == 15
    zero = [(decoder[i],0) for i in A+B] + [(parity,0)]
    generators = [solve(zero + [(decoder[i], int(j == p)) for j,i in enumerate(probes)])
                  for p in range(15)]
    extension = [pack((mask & w).bit_count() % 2 for w in generators) for mask in decoder]
    assert extension == field('extData')
    conditions = [decoder[i] for i in common] + [parity]
    dual = Span((mask << 15)|(1 << j) for j,mask in enumerate(conditions))
    error = [0]*512
    for i in C:
        residual = decoder[i] ^ reduce(xor, (decoder[t] for j,t in enumerate(probes)
                                              if extension[i] >> j & 1), 0)
        error[i] = dual.remainder(residual << 15)
        assert error[i] < 1 << 15
    assert error == field('errData')
    print('Reconstructed all 512 extension and 512 obstruction masks in the Lean interpolation proof.')


if __name__ == '__main__':
    decoder, grounds = read_decoder(), read_grounds()
    check_interpolator(decoder)
    for normals in ((1,2,3),(1,2,4)):
        inspect(normals,decoder,grounds)
