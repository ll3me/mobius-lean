"""A fixed-position Boolean projection from BRS Theorem 13 to whole-board words.

Run with no arguments for exact gate, source-function, and small geometry checks.
Only the Python standard library and this repository's existing compilers are used.
"""
import argparse
from itertools import combinations, product
from pathlib import Path
from random import Random

from axis_relations import FULL, ground, solve
from full_board_caps import formula_family
from board_input_bits import decode_boards, encode_boards, lean_ordered_charts


def brs(d, word):
    """BRS p.14: pairs of Boolean bits add in F3, and residue zero accepts."""
    n = 1 << d
    x = [((word >> (2*i)) & 1) + ((word >> (2*i+1)) & 1) for i in range(2*n)]
    return sum((1 if (i & j).bit_count() % 2 == 0 else -1)*x[i]*x[n+j]
               for i in range(n) for j in range(n)) % 3 == 0


class Circuit:
    """Interned binary AND and complement gates, shared on every use."""
    def __init__(self, inputs):
        self.inputs = inputs
        self.ops = [('input', i) for i in range(inputs)]
        self.memo = {}

    def gate(self, key):
        if key not in self.memo:
            self.memo[key] = len(self.ops)
            self.ops.append(key)
        return self.memo[key]

    def neg(self, a):
        return self.ops[a][1] if self.ops[a][0] == 'not' else self.gate(('not', a))

    def both(self, a, b):
        return a if a == b else self.gate(('and', min(a, b), max(a, b)))

    def either(self, a, b):
        return self.neg(self.both(self.neg(a), self.neg(b)))

    def any_three(self, a, b, c):
        return self.either(self.either(a, b), c)

    def pair(self, a, b):
        # Indicators for (a+b)=0,1,2 over F3.
        zero, two = self.neg(self.either(a, b)), self.both(a, b)
        return zero, self.neg(self.either(zero, two)), two

    def plus(self, a, b):
        # The two remaining residues determine the zero wire as well.
        one, two = [self.any_three(*(self.both(a[i], b[(j-i) % 3]) for i in range(3)))
                    for j in (1, 2)]
        return self.neg(self.either(one, two)), one, two

    def times(self, a, b):
        # The zero wire has a shorter formula when this is the final product.
        zero = self.either(a[0], b[0])
        one = self.either(self.both(a[1], b[1]), self.both(a[2], b[2]))
        return zero, one, self.neg(self.either(zero, one))

    def values(self, word):
        result = []
        for op, *args in self.ops:
            if op == 'input':
                value = (word >> args[0]) & 1
            elif op == 'not':
                value = 1-result[args[0]]
            else:
                value = result[args[0]] & result[args[1]]
            result.append(value)
        return result


def circuit(d):
    n = 1 << d
    dag = Circuit(4*n)
    pairs = [dag.pair(2*i, 2*i+1) for i in range(2*n)]
    transformed = pairs[n:]
    for j in range(d):
        stride = 1 << j
        for base in range(0, n, 2*stride):
            for i in range(base, base+stride):
                a, b = transformed[i], transformed[i+stride]
                transformed[i] = dag.plus(a, b)
                transformed[i+stride] = dag.plus(a, (b[0], b[2], b[1]))
    products = [dag.times(a, b) for a, b in zip(pairs[:n], transformed)]
    while len(products) > 1:
        products = [dag.plus(products[j], products[j+1]) for j in range(0, len(products), 2)]
    return dag, products[0][0]


class PinnedCircuitRows:
    """Compile a Boolean circuit, pinning either input bits or selected indicator gates."""
    def __init__(self, dag, out, symbol_gates=None):
        self.dag, self.out = dag, out
        n = self.dag.inputs
        self.count = 2+2*n
        self.templates = [(0, 0, 1)]  # false=0; true=1
        self.pin_rows = []
        self.pin_choices = []
        if symbol_gates is not None:
            symbol_gates = tuple(tuple(group) for group in symbol_gates)
            if any(not group for group in symbol_gates):
                raise ValueError('a symbol needs at least one selectable indicator')
        self.eval_steps = []
        positive = {}
        complements = {0: 1, 1: 0}

        def fresh():
            w = self.count
            self.count += 1
            return w

        def complement(w):
            if w not in complements:
                nw = fresh()
                complements[w], complements[nw] = nw, w
                self.templates.append((w, nw, 0))
                self.eval_steps.append(('not', nw, w))
            return complements[w]

        for i in range(n):
            off, on = 2+2*i, 3+2*i
            positive[i] = on
            complements[on], complements[off] = off, on
            self.templates.append((on, off, 0))
            if symbol_gates is None:
                self.pin_rows.append(len(self.templates))
                self.pin_choices.append((off, on))
                self.templates.append((off, 0, 0))

        # The output and every selectable indicator must retain their defining gates.
        live = {self.out}
        if symbol_gates is not None:
            live.update(wire for group in symbol_gates for wire in group)
        for j in reversed(range(n, len(self.dag.ops))):
            if j in live:
                live.update(self.dag.ops[j][1:])
        for j in sorted(live):
            if j < n:
                continue
            op, *args = self.dag.ops[j]
            a = positive[args[0]]
            if op == 'not':
                positive[j] = complement(a)
            else:
                b = positive[args[1]]
                na, nb = complement(a), complement(b)
                z, left, right, last = (fresh() for _ in range(4))
                self.templates.extend([(z, left, na), (z, right, nb), (left, right, last)])
                self.eval_steps.append(('and', z, left, right, last, a, b))
                positive[j] = z
        self.answer = positive[self.out]
        if symbol_gates is not None:
            for group in symbol_gates:
                choices = tuple(positive[wire] for wire in group)
                self.pin_rows.append(len(self.templates))
                self.pin_choices.append(choices)
                self.templates.append((choices[0], 0, 0))
        self.templates.append((self.answer, 0, 0))
        # formula_family reserves 19 private core coordinates per row and
        # three further coordinates per cap. It caps v+6m possible ports.
        m = len(self.templates)
        self.dimension = self.count + 19*m + 3*(self.count+6*m)
        self.board_count = self.count+13*m
        self.threshold = 126*7*m + 128*(self.count+6*m)

    def symbol_rows(self, symbols):
        if len(symbols) != len(self.pin_rows):
            raise ValueError('wrong number of input symbols')
        rows = self.templates.copy()
        for row, choices, symbol in zip(self.pin_rows, self.pin_choices, symbols):
            if not 0 <= symbol < len(choices):
                raise ValueError('input symbol outside its alphabet')
            rows[row] = (choices[symbol], 0, 0)
        return rows

    def values(self, word):
        values = [0]*self.count
        values[1] = 1
        for i in range(self.dag.inputs):
            bit = (word >> i) & 1
            values[2+2*i:4+2*i] = [1-bit, bit]
        for op, *args in self.eval_steps:
            if op == 'not':
                new, old = args
                values[new] = 1-values[old]
            else:
                z, left, right, last, a, b = args
                values[z] = values[a] & values[b]
                values[left], values[right] = values[a]-values[z], values[b]-values[z]
                values[last] = 1-values[left]-values[right]
        return values


class Reduction(PinnedCircuitRows):
    def __init__(self, d):
        super().__init__(*circuit(d))

    def rows(self, word):
        if not 0 <= word < 1 << self.dag.inputs:
            raise ValueError('source word outside the fixed input width')
        return self.symbol_rows([(word >> i) & 1 for i in range(self.dag.inputs)])

    def build(self, word):
        return formula_family(self.count, self.rows(word))

    def bits(self, word):
        return encode_boards(self.build(word), self.dimension)

    def changing_positions(self, width):
        # Lean chart order center, near0, near1, near2, far0, far1, far2.
        return [width*(4*(7*r+4)+1) for r in self.pin_rows]


def test_gate():
    for a, b, z in product(range(2), repeat=3):
        completions = [(l, r, t) for l, r, t in product(range(2), repeat=3)
                       if z+l+1-a == z+r+1-b == l+r+t == 1]
        assert len(completions) == int(z == (a & b))
    assert [(f, t) for f, t in product(range(2), repeat=2) if 2*f+t == 1] == [(0, 1)]


def bit_positions(data):
    for k, byte in enumerate(data):
        while byte:
            low = byte & -byte
            yield 8*k+low.bit_length()-1
            byte ^= low


def check_projection(r):
    base = r.bits(0)
    # The public width is independent of the private input bits.
    width = max(1, (r.dimension-1).bit_length())
    positions = r.changing_positions(width)
    for i, expect in enumerate(positions):
        data = r.bits(1 << i)
        assert len(data) == len(base)
        assert list(bit_positions(bytes(a ^ b for a, b in zip(base, data)))) == [expect]
        assert base[expect//8] & (1 << (expect%8)) == 0
    assert len(set(positions)) == len(positions)
    family = r.build(0)
    assert len(lean_ordered_charts(family)) == r.board_count
    assert len(base) == (4*width*r.board_count+7)//8
    all_on = bytearray(base)
    for pos in positions:
        all_on[pos//8] |= 1 << (pos%8)
    assert bytes(all_on) == r.bits((1 << r.dag.inputs)-1)
    return width, positions


def ambient_points(axes, names):
    """Intern actual ambient bit vectors by their sorted coordinate supports."""
    pts = []
    for x in range(16):
        support = tuple(sorted(axis for j, axis in enumerate(axes) if x & (1 << j)))
        pts.append(names.setdefault(support, len(names)))
    return pts


def physical(r, word, expected):
    family, rows, vals = r.build(word), r.rows(word), r.values(word)
    assert len(family.cores) == 7*len(rows)
    charts = decode_boards(r.bits(word), r.board_count, r.dimension)
    assert charts == lean_ordered_charts(family)
    assert len(charts) == r.board_count
    caps = {axes[0] for axes in family.caps}
    assert len(caps) == len(family.caps)
    assert {axis for ports, _ in family.cores for axis in ports} <= caps
    assert all(v not in caps for ports, axes in family.cores for v in axes[len(ports):])
    # Independently check all real charts intersect in at most one axis.
    pairs = set()
    for axes in charts:
        assert len(set(axes)) == 4
        for pair in combinations(sorted(axes), 2):
            assert pair not in pairs
            pairs.add(pair)

    cores = []
    for j, axes in enumerate(charts[:7*len(rows)]):
        arity = 3 if j % 7 == 0 else 2
        cores.append((axes[:arity], axes))
    assert set(cores) == set(family.cores)
    if expected:
        value = dict(enumerate(vals))
        for i, row in enumerate(rows):
            head = r.count+19*i
            for j, w in enumerate(row):
                value[head+j] = vals[w]
                value[head+4+j] = 1-vals[w]
        assert all(sum(value[v] for v in ports) == 1 for ports, _ in cores)
    else:
        # The 7-board source compiler and weak-gap theorem turn this Boolean
        # refutation into a strict global threshold rejection.
        assert solve(cores) is None

    names, line_faces, line_signs = {}, set(), {}
    count = failures = 0
    bad = [[(ground(slot)[16*x+y] ^ ground(slot)[16*(x^d)+(y^d)] ^
             ground(slot)[16*(x^d)+y] ^ ground(slot)[16*x+(y^d)]) == 0
            for x, y, d in FULL] for slot in range(4)]
    for slot, flags in enumerate(bad):
        assert flags == [d == 1 << slot for _, _, d in FULL]
    core_ports = dict((axes, ports) for ports, axes in cores)
    for axes in charts:
        ids = ambient_points(axes, names)
        if expected:
            ports = core_ports.get(axes)
            slot = (next(i for i, v in enumerate(ports) if value[v])
                    if ports else (0 if value.get(axes[0], 0) else 1))
            table = ground(slot)
            # The origin and the four axis lines include every possible shared cell.
            for i in range(4):
                for x, y, tag in product((0, 1 << i), (0, 1 << i), (0, 1)):
                    key = (tag, ids[x], ids[y])
                    bit = table[16*x+y]
                    assert line_signs.setdefault(key, bit) == bit
        for j, (x, y, d) in enumerate(FULL):
            # Physical duplicates require d to be a unit and both endpoints
            # to lie on its line. Previous pair-of-axes checks prove this.
            if d & (d-1) == 0 and x in (0, d) and y in (0, d):
                face = min((ids[x], ids[y], ids[d]), (ids[x^d], ids[y^d], ids[d]))
                if face in line_faces:
                    continue
                line_faces.add(face)
            count += 1
            if expected:
                failures += bad[slot][j]
    prediction = sum(1920-2*len(ports) for ports, _ in family.cores)+1920*len(family.caps)
    assert count == prediction
    if expected:
        assert failures == r.threshold
    details = f'{failures} failures' if expected else 'UNSAT port system'
    print(f'physical n={r.dag.inputs} word={word}: {count} distinct faces, {details}, threshold {r.threshold}')


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--depth', type=int, help='write the instance for n=4*2^depth input bits')
    parser.add_argument('--word', type=lambda s: int(s, 0), default=0)
    parser.add_argument('--output', type=Path, help='write only the packed fixed-width board coordinates')
    args = parser.parse_args()
    if args.depth is not None:
        if args.depth < 0 or args.output is None:
            parser.error('--depth must be nonnegative and requires --output')
        r = Reduction(args.depth)
        args.output.write_bytes(r.bits(args.word))
        print(f'inputs={r.dag.inputs} dimension={r.dimension} boards={r.board_count} threshold={r.threshold}')
        return
    if args.output is not None:
        parser.error('--output requires --depth')
    test_gate()
    for d in range(4):
        r = Reduction(d)
        if d <= 1:
            words = range(1 << r.dag.inputs)
        else:
            rng = Random(731+d)
            words = [rng.getrandbits(r.dag.inputs) for _ in range(64)]
        for word in words:
            values, rows = r.values(word), r.rows(word)
            assert all(sum(values[v] for v in row) == 1 for row in rows[:-1])
            assert (sum(values[v] for v in rows[-1]) == 1) == brs(d, word)
            assert values[r.answer] == r.dag.values(word)[r.out] == brs(d, word)
        print(f'd={d}: {len(words)} direct BRS comparisons, {len(r.templates)} positive triples')
        if d <= 1:
            width, positions = check_projection(r)
            print(f'  {r.board_count} whole boards, width {width}, length {len(r.bits(0))*8} padded bits, LSBs {positions}')
        if d == 0:
            physical(r, 0, True)
            physical(r, 5, False)
        if d == 1:
            physical(r, 17, False)
            physical(r, 113, brs(d, 113))


if __name__ == '__main__':
    main()
