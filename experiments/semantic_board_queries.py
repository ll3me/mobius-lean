"""Whole-board symbol queries for the Beame–Jayram–Saks quadratic form.

Run without arguments to compare circuits, pin rows, and physical board words.
The direct reference omits the diagonal of the Sylvester matrix.
"""
from itertools import product
from math import isqrt

from axis_relations import solve
from board_input_bits import encode_boards
from full_board_caps import formula_family
from read_bounded_boards import Circuit, PinnedCircuitRows, brs


def odd_prime(q):
    return q >= 3 and q % 2 == 1 and all(q % p for p in range(3, isqrt(q) + 1, 2))


def public_modulus(depth):
    q = max(3, depth) | 1
    while not odd_prime(q):
        q += 2
    return q


class ResidueCircuit(Circuit):
    """Little-endian binary wires for residues in a public odd prime field."""
    def __init__(self, n, q):
        self.q = q
        self.width = (q - 1).bit_length()
        super().__init__(n * self.width)
        self.zero = self.both(0, self.neg(0))
        self.one = self.neg(self.zero)

    def constant(self, number):
        return tuple(self.one if number >> i & 1 else self.zero for i in range(self.width))

    def xor(self, a, b):
        return self.both(self.either(a, b), self.neg(self.both(a, b)))

    def add_words(self, a, b, carry):
        result = []
        for x, y in zip(a, b):
            xy = self.xor(x, y)
            result.append(self.xor(xy, carry))
            carry = self.either(self.both(x, y), self.both(xy, carry))
        return tuple(result), carry

    def select(self, flag, yes, no):
        return tuple(self.either(self.both(flag, y), self.both(self.neg(flag), n))
                     for y, n in zip(yes, no))

    def add_mod(self, a, b):
        low, overflow = self.add_words(a, b, self.zero)
        reduced, at_least_q = self.add_words(low, self.constant((1 << self.width) - self.q),
                                             self.zero)
        return self.select(self.either(overflow, at_least_q), reduced, low)

    def sub_mod(self, a, b):
        low, no_borrow = self.add_words(a, tuple(self.neg(bit) for bit in b), self.one)
        corrected, _ = self.add_words(low, self.constant(self.q), self.zero)
        return self.select(no_borrow, low, corrected)

    def mul_mod(self, a, b):
        total = self.constant(0)
        for j, bit in enumerate(b):
            total = self.add_mod(total, tuple(self.both(bit, x) for x in a))
            if j + 1 < self.width:
                a = self.add_mod(a, a)
        return total

    def equals(self, word, value):
        literals = [bit if value >> i & 1 else self.neg(bit) for i, bit in enumerate(word)]
        match = literals[0]
        for literal in literals[1:]:
            match = self.both(match, literal)
        return match


def quadratic_rows(depth, modulus=None):
    """Produce the fixed formula and one selectable address per field symbol."""
    if depth < 0:
        raise ValueError('depth must be nonnegative')
    n = 1 << depth
    q = public_modulus(depth) if modulus is None else modulus
    if not odd_prime(q):
        raise ValueError('the Sylvester construction uses an odd prime')
    dag = ResidueCircuit(n, q)
    words = [tuple(range(i * dag.width, (i + 1) * dag.width)) for i in range(n)]
    choices = [tuple(dag.equals(word, a) for a in range(q)) for word in words]
    transformed = words.copy()
    for j in range(depth):
        stride = 1 << j
        for base in range(0, n, 2 * stride):
            for i in range(base, base + stride):
                a, b = transformed[i], transformed[i + stride]
                transformed[i] = dag.add_mod(a, b)
                transformed[i + stride] = dag.sub_mod(a, b)
    total = dag.constant(0)
    for i, (z, hz) in enumerate(zip(words, transformed)):
        # The diagonal H_ii is (-1) to the Hamming weight of i.
        off_diagonal = dag.add_mod(hz, z) if i.bit_count() % 2 else dag.sub_mod(hz, z)
        total = dag.add_mod(total, dag.mul_mod(z, off_diagonal))
    return PinnedCircuitRows(dag, dag.equals(total, 0), choices)


def reference(symbols, q):
    return sum((-1 if (i & j).bit_count() % 2 else 1) * x * y
               for i, x in enumerate(symbols) for j, y in enumerate(symbols) if i != j) % q == 0


def check_quadratic(depth, q):
    encoding = quadratic_rows(depth, q)
    width = encoding.dag.width
    n = 1 << depth
    for symbols in product(range(q), repeat=n):
        word = sum(value << (width * i) for i, value in enumerate(symbols))
        values = encoding.values(word)
        rows = encoding.symbol_rows(symbols)
        assert all(sum(values[v] for v in row) == 1 for row in rows[:-1])
        expected = reference(symbols, q)
        assert (sum(values[v] for v in rows[-1]) == 1) == expected
        assert encoding.dag.values(word)[encoding.out] == expected
    # Every binary word, including unused residue encodings, can match
    # only its actual symbols. This also exercises false selector literals.
    if n <= 2:
        for word in range(1 << (n * width)):
            values = encoding.values(word)
            for i, choices in enumerate(encoding.pin_choices):
                symbol = (word >> (i * width)) % (1 << width)
                assert [a for a, v in enumerate(choices) if values[v]] == (
                    [symbol] if symbol < q else [])
    if n == 2:
        for symbols in ([0, 1], [1, 1]):
            # Independently solve the positive triples for a yes and a no word.
            clauses = [(row, ()) for row in encoding.symbol_rows(symbols)]
            assert (solve(clauses) is not None) == reference(symbols, q)
    print(f'q={q}, {n} symbols: {q**n} direct quadratic/row comparisons')
    return encoding


def check_physical_pins(encoding):
    n = len(encoding.pin_rows)
    width = (encoding.dimension - 1).bit_length()

    def payload(symbols):
        family = formula_family(encoding.count, encoding.symbol_rows(symbols))
        return encode_boards(family, encoding.dimension)

    base_bytes = payload([0] * n)
    baseline = int.from_bytes(base_bytes, 'little')
    for i, (row, choices) in enumerate(zip(encoding.pin_rows, encoding.pin_choices)):
        board = 7 * row + 4
        offset = (4 * board + 1) * width
        assert (baseline >> offset) % (1 << width) == choices[0]
        assert len(set(choices)) == len(choices)
        for a, new_address in enumerate(choices[1:], 1):
            symbols = [0] * n
            symbols[i] = a
            data = payload(symbols)
            assert len(data) == len(base_bytes)
            actual = int.from_bytes(data, 'little')
            assert baseline ^ actual == (choices[0] ^ new_address) << offset
    print(f'{encoding.board_count} physical boards: all single-symbol address changes verified')


def canonical_word(trits):
    return sum((0, 1, 3)[a] << (2 * i) for i, a in enumerate(trits))


def check_binary_pairs(n):
    """Count the accepting canonical ternary pairs in the original binary BRS family."""
    depth = n.bit_length() - 1
    pairs = product(tuple(product(range(3), repeat=n)), repeat=2)
    accepted = sensitive = 0
    for x, y in pairs:
        # 00, 01 and 11 have respective bit sums 0, 1 and 2.
        word = canonical_word(x + y)
        if brs(depth, word):
            accepted += 1
            sensitive += all(not brs(depth, word ^ (1 << i)) for i in range(4 * n))
    assert accepted == 3**(2 * n - 1) + 2 * 3**(n - 1)
    assert 4 * sensitive >= (2**n - 2 * n) * 2**n
    print(f'binary BRS n={n}: {accepted} accepting pairs, {sensitive} sensitive to every bit')


def check_sensitive_word(depth):
    n = 1 << depth
    x = [1, 1, 1, 2] + [0] * (n - 4)
    y = [1, 2, 1, 1] + [0] * (n - 4)
    word = canonical_word(x + y)
    assert brs(depth, word)
    assert all(not brs(depth, word ^ (1 << i)) for i in range(4 * n))


if __name__ == '__main__':
    check_binary_pairs(4)
    for depth in range(2, 6):
        check_sensitive_word(depth)
    for depth, q in [(1, 3), (2, 3), (1, 5), (2, 5)]:
        example = check_quadratic(depth, q)
        if depth == 1:
            check_physical_pins(example)
