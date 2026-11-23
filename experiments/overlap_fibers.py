"""Exact restrictions of four-bit optimum table pairs, and genuine affine cycles.

Run with Python 3. The 512 linear masks come from the checked Lean decoder.
The only external mathematical input in the classification is the project's
theorem that every four-bit optimum fails in exactly one entire direction.
"""

from collections import defaultdict
from functools import reduce
from itertools import combinations, product
from operator import xor
from pathlib import Path
import re

from one_in_three_geometry import SQUARES
from port_k4 import phase3


class Span:
    """Row echelon basis of packed binary vectors, highest pivot first."""

    def __init__(self, rows=()):
        self.rows = {}
        for row in rows:
            self.add(row)

    def add(self, row):
        while row:
            p = row.bit_length()-1
            if p not in self.rows:
                self.rows[p] = row
                break
            row ^= self.rows[p]

    def remainder(self, row):
        for pivot in sorted(self.rows, reverse=True):
            if row >> pivot & 1:
                row ^= self.rows[pivot]
        return row

    def __len__(self):
        return len(self.rows)


def pack(bits):
    return sum(int(bit) << i for i,bit in enumerate(bits))


def cell(tag, x, y):
    return 256*tag + 16*x + y


def read_decoder():
    file = Path(__file__).resolve().parents[1]/'Mobius'/'RigidityKernelData.lean'
    source = file.read_text().split('def double : Model where',1)[1]
    rows = tuple(int(a,16) for a in re.findall(r'0x[0-9a-f]+',source.split('steps :=',1)[0]))
    assert len(rows) == 512 and len(Span(rows)) == 62
    equations = Span()
    for d,x,y in product(range(1,16), range(16), range(16)):
        cells = (cell(0,x,y), cell(0,x^d,y^d), cell(1,x,y^d), cell(1,x^d,y))
        assert reduce(xor,(rows[c] for c in cells),0)==0
        equations.add(sum(1<<c for c in cells))
    assert len(equations)==450  # verifies completeness of the supplied 62-dimensional kernel
    return rows


def quotient(d, x):
    i = (d & -d).bit_length()-1
    if x >> i & 1:
        x ^= d
    return (x & ((1<<i)-1)) | ((x >> (i+1)) << i)


def ground(d):
    return tuple(phase3(quotient(d,(v%256)//16),quotient(d,v%16)) for v in range(512))


def read_grounds():
    grounds = {d: ground(d) for d in range(1,16)}
    for d,table in grounds.items():
        for e,x,y in product(range(1,16),range(16),range(16)):
            s = (table[cell(0,x,y)] ^ table[cell(0,x^e,y^e)] ^
                 table[cell(1,x,y^e)] ^ table[cell(1,x^e,y)])
            assert s == (e != d)
    return grounds


def block(U, a=0, b=0):
    return [cell(t,a^x,b^y) for t in range(2) for x in U for y in U]


def project_kernel(rows):
    return Span(pack((r >> j) & 1 for r in rows) for j in range(62))


def projected_classes(decoder, grounds, sites):
    image = project_kernel([decoder[i] for i in sites])
    classes = defaultdict(list)
    for d,table in grounds.items():
        classes[image.remainder(pack(table[i] for i in sites))].append(d)
    return len(image), set(map(tuple,classes.values()))


def verify_separators(decoder, grounds):
    for k, rank in enumerate((2,6,14,30,62)):
        q = 2**k
        sites = block(range(q))
        dimension, classes = projected_classes(decoder,grounds,sites)
        expected = {(d,) for d in range(1,q)}
        if q<16:
            expected.add(tuple(range(q,16)))
        assert dimension == rank and classes == expected
        print(f'k={k}: {len(sites)} boundary bits, rank {rank}, {len(classes)} direction classes, '
              f'2^{62-rank} completions per allowed direction.')


def verify_two_interfaces(decoder, grounds):
    U = range(4)
    left = block(U)
    for xshift,yshift,rank,external_classes in [
            (4,4,22,[(4,5,6,7),tuple(range(8,16))]),
            (4,0,25,[(4,5,6,7),tuple(range(8,16))]),
            (4,8,26,[tuple(range(4,16))])]:
        actual, classes = projected_classes(decoder,grounds,left+block(U,xshift,yshift))
        assert actual==rank and classes=={(1,),(2,),(3,),*external_classes}
        print(f'Two disjoint k=2 cell blocks with translation ({xshift},{yshift}): '
              f'joint rank {rank}; {len(classes)} direction classes.')


def check_shell_certificates():
    # For the selected U, all template representatives with d in U are
    # anchored in one pair of U-cosets. Intersections survive arbitrary GL.
    for U in (frozenset((0,1)), frozenset((0,2,4,6)),frozenset(range(8))):
        shell_groups = 0
        covered = set()
        for a,b in product(range(16), repeat=2):
            chart = {(a^x,b^y,d) for x,y,d in SQUARES}
            assert len(chart) == 15 and not covered.intersection(chart)
            covered.update(chart)
            if not any(x in U and y in U and d in U for x,y,d in chart):
                shell_groups += 1
        assert len(covered) == 3840
        assert shell_groups == 256-len(U)**2
        print(f'Interface of order {len(U)}: {shell_groups} disjoint odd certificates fully in shell.')


def check_channel(decoder, grounds):
    U = range(8)
    left, right = block(U), block(U,8,8)
    H = project_kernel([decoder[i] for i in left])
    D = project_kernel([decoder[i]^decoder[j] for i,j in zip(left,right)])
    joint = project_kernel([decoder[i] for i in left+right])
    assert (len(H),len(D),len(joint)) == (30,16,46)
    assert all(H.remainder(v)==0 for v in D.rows.values())
    # Check the complete diagonal copy of H, not just its dimension.
    assert all(joint.remainder(v ^ (v<<128))==0 for v in H.rows.values())
    dimension, groups = projected_classes(decoder,grounds,left+right)
    assert dimension == 46 and groups == {(d,) for d in range(1,16)}

    common = pack(grounds[8][i] for i in left)
    lambdas = []
    for low in range(8):
        s = grounds[8+low]
        x,y = pack(s[i] for i in left),pack(s[i] for i in right)
        assert H.remainder(x^common)==0 and H.remainder(y^common)==0
        lambdas.append(D.remainder(x^y))
    # Fixed internal direction h has both station restrictions in one
    # (non-all-success) coset. Its transfer in the same H/D is lambda(h).
    for h in range(1,8):
        g = grounds[h]
        difference = pack(g[i]^g[j] for i,j in zip(left,right))
        assert H.remainder(difference) == 0
        assert D.remainder(difference) == lambdas[h]
    assert len(Span(lambdas)) == 3 and len(set(lambdas)) == 8
    for a,b in product(range(8), repeat=2):
        assert lambdas[a]^lambdas[b] == lambdas[a^b]
    # Three explicit quotient functionals: four row entries per boundary.
    for j, (a,b) in enumerate(((2,4),(1,4),(1,2))):
        addresses = [cell(0,t^x,t^y) for t in (0,8) for x in (0,a) for y in (0,b)]
        assert reduce(xor,(decoder[i] for i in addresses),0)==0
        vals = [reduce(xor,(grounds[8+l][i] for i in addresses),0) for l in range(8)]
        assert vals == [l>>j&1 for l in range(8)]
        print(f'R rectangle ({a},{b}) on both ends reads direction bit {j}: {vals}')
    print('Channel ranks: H=30, D=16, joint=46, states=2^14. '
          'Three independent syndrome shifts; all eight obey the XOR law.')


def chart(origin, basis):
    images=[0]
    for b in basis:
        images += [x^b for x in images]
    assert len(images)==len(set(images))==16
    return tuple(origin^v for v in images)


def intended_system(boards, local_dirs):
    """Solve actual global tagged-cell equations; a contradiction is 0=1."""
    variables, rows, unique = {}, Span(), {}
    def variable(t,x,y):
        addr=(t,x,y)
        if addr not in variables:
            variables[addr]=len(variables)+1  # reserve bit zero for RHS
        return variables[addr]
    for image,d in zip(boards, local_dirs,strict=True):
        for e,x,y in product(range(1,16),range(16),range(16)):
            if (x,y)>(x^e,y^e):  # one of two opposite anchors
                continue
            corners = (variable(0,image[x],image[y]),variable(0,image[x^e],image[y^e]),
                       variable(1,image[x],image[y^e]),variable(1,image[x^e],image[y]))
            mask = sum(1<<j for j in corners)
            rhs = int(e!=d)
            if mask in unique and unique[mask]!=rhs:
                rows.add(1)
            unique[mask]=rhs
            rows.add(mask|rhs)
    feasible=0 not in rows.rows
    return len(variables),len(unique),feasible,len(variables)-len(rows) if feasible else None


def cycle_chart(i, n):
    a, b = 8 << i, 8 << ((i+1)%n)
    return chart(a,(1,2,4,a^b))


def verify_cycles():
    for lows in [(1,2,3), (1,2,2), (0,1,2,3), (7,7,7,6)]:
        n = len(lows)
        boards=[cycle_chart(i,n) for i in range(n)]
        for i,j in combinations(range(n),2):
            overlap=set(boards[i]) & set(boards[j])
            assert len(overlap)==(8 if (i-j)%n in (1,n-1) else 0)
        count, tests, feasible, dim=intended_system(boards, [8+l for l in lows])
        assert count==384*n and tests==1696*n
        assert feasible==(reduce(xor,lows,0)==0)
        if feasible:
            assert dim==32*n+14
        print(f'Physical cycle {lows}: {count} tagged cells, {tests} distinct unoriented tests, '
              f'{"2^"+str(dim)+" completions" if feasible else "inconsistent"}.')


def verify_physical_cycle_costs():
    # Private means that the whole anchored test is outside both station
    # test collections; mixed row/column addresses are still counted.
    def station_of_test(x,y,d):
        return x >> 3 if d < 8 and (x >> 3)==(y >> 3) else None

    charts = [{(a^x,b^y,d) for x,y,d in SQUARES}
              for a,b in product(range(16),repeat=2)]
    assert len(set.union(*charts)) == sum(map(len,charts)) == 3840
    assert sum(all(station_of_test(x,y,d) is None for x,y,d in row)
               for row in charts)==128
    for d in range(1,16):
        private = sum(station_of_test(x,y,d) is None for x,y in product(range(16),repeat=2))
        assert private == (128 if d<8 else 256)

    # One exceptional page identifies its halves and quotients by h=1.
    # It has the same full raw station at both ends; the remaining even
    # number of ordinary pages with internal direction h can join these.
    h = 1
    g = ground(h)
    seam = tuple(g[cell(tag,x%8,y%8)]
                 for tag,x,y in product(range(2),range(16),range(16)))
    flags = [sum(not (seam[cell(0,x,y)] ^ seam[cell(0,x^d,y^d)] ^
                      seam[cell(1,x,y^d)] ^ seam[cell(1,x^d,y)])
                 for x,y in product(range(16),repeat=2)) for d in range(1,16)]
    assert flags == [256 if d in (h,8,8^h) else 0 for d in range(1,16)]

    for n in (3,4):
        boards=[cycle_chart(i,n) for i in range(n)]
        count,tests,possible,dim=intended_system(boards,[1]*n)
        assert count==384*n and tests==1696*n
        assert possible==(n%2==0)
        if possible:
            assert dim==32*n+14
        print(f'Common tangential direction 1, {n} pages: '
              f'{"2^"+str(dim)+" completions" if possible else "inconsistent"}.')
    print('Union anchored cost: even cycle = 192p; odd cycle >= 192p+14 '
          '(the strengthened lower bound uses the whole-board second weight 282).')


def verify_complementary_chain():
    # Central board L=(1,2,4,8); left shares (1,2), right shares (4,8).
    # Actual ℓ-bases of the two leaves make local reuse explicit.
    boards=[chart(0,(1,2,16,32)),chart(0,(1,2,4,8)),chart(0,(4,8,64,128))]
    assert (set(boards[0])&set(boards[1])==set(range(4))
            and set(boards[1])&set(boards[2])=={0,4,8,12}
            and set(boards[0])&set(boards[2])=={0})
    # Central bad direction 1 is shared on the left. Right local 4 is
    # globally 64, hence entirely outside its interface with the center.
    _,tests,valid,dim=intended_system(boards,[1,1,4])
    assert valid and dim==3*62-2*14
    assert tests==3*1920-2*(16*3//2)
    # Count the actual union once. Compatible means equal flags where glued.
    bad={}
    for board,d in zip(boards,[1,1,4]):
        for e,x,y in product(range(1,16),range(16),range(16)):
            corners=(tuple(sorted(((board[x],board[y]),(board[x^e],board[y^e])))),
                     tuple(sorted(((board[x],board[y^e]),(board[x^e],board[y])))))
            if corners in bad:
                assert bad[corners]==(d==e)
            bad[corners]=(d==e)
    assert sum(bad.values())==376
    assert len(bad)==tests
    print(f'Complementary-plane chain: {tests} distinct unoriented tests, '
          f'376 geometric/752 anchored failures achieved, 2^{dim} extensions for this direction profile.')
    # All optimum-board profiles lose at least one of two disjoint nonzero
    # separators. If any board is nonoptimal, 282+2*240=762 anchored.
    allowed=[(set(boards[0]) & set(boards[1]))-{0}, (set(boards[1]) & set(boards[2]))-{0}]
    shared=max(sum(d in h for h in allowed) for d in range(1,16))
    assert 3*256-16*shared==752 < 282+2*240


def main():
    decoder,grounds=read_decoder(),read_grounds()
    verify_separators(decoder,grounds)
    verify_two_interfaces(decoder,grounds)
    check_shell_certificates()
    check_channel(decoder,grounds)
    verify_cycles()
    verify_physical_cycle_costs()
    verify_complementary_chain()


if __name__ == '__main__':
    main()
