"""Finite ETH seam experiments; only Python's standard library is needed.

A clause is a tuple of signed one-based integers. Left and right subproofs
share six ordinary Boolean variables and each has one private variable.
No SAT oracle is used in either #SAT computation. A second experiment
checks the OpenAI parity-window swap operator in the rational group algebra.
"""
from fractions import Fraction
from itertools import product
from math import comb
from random import Random

ALPHABET = range(8)
PAIRS = list(product(ALPHABET, repeat=2))


def sign(x, y):
    a, b, c = [(x >> i) & 1 for i in range(3)]
    u, v, w = [(y >> i) & 1 for i in range(3)]
    phase = u*(a+b*c) + v*(a+b+a*c) + w*(a+b+c+a*b)
    return 1 if phase % 2 == 0 else -1


def pieces(x, y, u, v):
    if x ^ y ^ u ^ v:
        return 0, 0
    return sign(x,y)*sign(v,u), sign(x,u)*sign(v,y)


def passes(formula, assignment):
    return all(any(((assignment >> (abs(lit)-1)) & 1) == (lit > 0)
                   for lit in clause) for clause in formula)


def partition_count(left, right):
    # Row split xy|uv. Right sees the same first and second three-bit blocks
    # in the opposite order, enforced by the crossing x=v and y=u.
    front = {(x,y): sum(passes(left, x | (y<<3) | (a<<6)) for a in range(2))
             for x,y in PAIRS}
    back = {(u,v): sum(passes(right, v | (u<<3) | (b<<7)) for b in range(2))
            for u,v in PAIRS}
    row_total = column_total = 0
    for x,y in PAIRS:
        for u,v in PAIRS:
            row, column = pieces(x,y,u,v)
            weight = front[x,y]*back[u,v]
            row_total += weight*row
            column_total += weight*column
    expected = sum(passes(left+right, z) for z in range(256))
    assert row_total+column_total == 2*expected
    return row_total, column_total, expected


def random_formula(rng, variables, nclauses):
    return [tuple(v if rng.randrange(2) else -v for v in rng.sample(variables, 3))
            for _ in range(nclauses)]


def eight_square_checks():
    verified = cancelled = 0
    for x,y,u,v in product(ALPHABET, repeat=4):
        r,c = pieces(x,y,u,v)
        assert r+c == 2*(x==v and y==u)
        verified += 1
        cancelled += (r == -c and r != 0)
    print(f"3-bit crossing: {verified} entries, {cancelled} exact off-wire cancellations")
    assert pieces(0,0,1,1) == (-1,1)
    assert cancelled == 448
    rng=Random(1638)
    cases=[([],[]), ([()],[]), ([(1,)], [(-1,)]), ([(1,-1)],[])]
    # An even sharper failure of Boolean OR: left forces x=y=0, right forces
    # u=v=1. The incompatible branches R and C contribute opposite signs.
    left_pins = [(-i,) for i in range(1,7)]
    right_pins = [(i if i in [1,4] else -i,) for i in range(1,7)]
    cases.append((left_pins, right_pins))
    assert partition_count(left_pins,right_pins) == (-4,4,0)
    for _ in range(128):
        cases.append((random_formula(rng,list(range(1,8)),rng.randrange(1,17)),
                      random_formula(rng,[1,2,3,4,5,6,8],rng.randrange(1,17))))
    for left,right in cases:
        partition_count(left,right)
    print(f"#3SAT: {len(cases)} split formulas matched brute-force counts; signed UNSAT witness -4+4=0")


def multiply(a,b):
    # S_i compose by symmetric difference: two copies of the same swap cancel.
    out={}
    for m,x in a.items():
        for n,y in b.items():
            h=m^n
            out[h]=out.get(h,0)+x*y
    return {h:z for h,z in out.items() if z}


def add_scaled(dst, src, scale):
    for h,c in src.items():
        dst[h]=dst.get(h,0)+scale*c


def parity_window(q, left, width):
    assert 0 <= left and 1 <= width <= q-left+1
    all_swaps=(1<<q)-1
    weight={0:Fraction(q,2), **{1<<i:Fraction(-1,2) for i in range(q)}}
    result={}
    falling={0:Fraction(1)}
    # f(W)=(-1)^left sum_{j<width}(-2)^j binom(W-left,j).
    for j in range(width):
        add_scaled(result,falling,(-1)**left*(-2)**j)
        factor=weight.copy()
        factor[0]-=left+j
        falling={m:c/(j+1) for m,c in multiply(falling,factor).items()}
    kernel={m^all_swaps:c for m,c in result.items() if c}
    assert all(q-m.bit_count() <= width-1 for m in kernel)
    # Evaluate in every simultaneous ±1 sector. For 2×2 pair swaps there
    # are 3 positive local eigenvectors and 1 negative eigenvector.
    defect_rank=0
    for neg in range(1<<q):
        eigenvalue=sum(c*(-1)**((m&neg).bit_count()) for m,c in kernel.items())
        j=neg.bit_count()
        if left <= j < left+width:
            assert eigenvalue == 1
        if eigenvalue != 1:
            defect_rank+=3**(q-j)
    tail=sum(comb(q,j)*3**(q-j) for j in range(q+1) if not left <= j < left+width)
    assert defect_rank <= tail
    return len(kernel),defect_rank,tail


if __name__ == "__main__":
    eight_square_checks()
    for q,left,width in [(4,0,3),(8,1,4),(10,1,5)]:
        terms,rank,tail=parity_window(q,left,width)
        print(f"Q={q}, window [{left},{left+width-1}]: {terms} swap products, "
              f"rank(I-M)={rank}/{4**q}, tail bound={tail}")

