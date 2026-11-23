"""Exact cut ranks for locked optimal phases and nearby two-sided perturbations."""
from collections import Counter
from functools import lru_cache
from itertools import product
from optimal_residual import rational_rank
from two_phases import constraints, entries

V = range(16)
H = 8
TESTS = tuple(constraints(16))
INCIDENCE = [set() for _ in range(512)]
for index, r in enumerate(TESTS):
    for cell in entries(16,r):
        INCIDENCE[cell].add(index)
GROUND = {i for i, (_,_,d) in enumerate(TESTS) if d == H}
MATCH = tuple(1 << (x ^ H) for x in V)


@lru_cache(None)
def block_rank(rows):
    return rational_rank([{j:1 for j in V if row >> j & 1} for row in rows])


def outcome(changes):
    errors = GROUND.copy()
    for cell in changes:
        errors.symmetric_difference_update(INCIDENCE[cell])
    cuts = [[[0]*16 for _ in V] for _ in range(2)]
    for test in errors:
        x,y,d = TESTS[test]
        for blocks, key in zip(cuts, (x^y,x^y^d)):
            block = blocks[key]
            block[x] |= 1 << (x^d)
            block[x^d] |= 1 << x
    return (2*len(errors), *(sum(block_rank(tuple(row)) for row in blocks) for blocks in cuts))


def main():
    for j in range(17):
        b,r,c=outcome(range(j))  # row (0,s), 0 <= s < j
        assert b == 256+26*j and r == 256-j and c <= 256-j
        print(f'locked rank drop {j:2}: failures {b}, ranks ({r},{c})')

    # Matching automorphisms permute pairs and exchange endpoints in a pair.
    # Hence a,b,m characterize each single switched adjacency up to relabeling.
    for m in range(9):
        for a in range(9-m):
            p = list(range(m)) + [x for i in range(m,m+a) for x in (i,i^H)]
            mask = sum(1 << i for i in p)
            rows = tuple(MATCH[x] ^ ((65535^mask) if x in p else mask) for x in V)
            rank = block_rank(rows)
            assert rank == 16 - (len(p) in (1,15))

    values = Counter()
    example = {}
    for second in range(1,512):
        triple = outcome((0,second))
        values[triple] += 1
        example.setdefault(triple, second)
    print('Two changes, first at row (0,0), counts by (failures,row rank,column rank):')
    for triple in sorted(values):
        tag,cell = divmod(example[triple],256)
        print(triple, values[triple], ('col' if tag else 'row',*divmod(cell,16)))


if __name__ == '__main__':
    main()
