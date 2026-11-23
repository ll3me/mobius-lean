"""Ordinary 3-CNF for the decision threshold of TropicalMWIS.optimum.

Use compile_threshold(edges, prices, threshold) with zero-based vertex IDs and
one pair (false price, true price) per vertex. The resulting signed integers
use DIMACS conventions. lean_word() yields the binary Word of Complexity.SAT;
literal +j in DIMACS is Lean's positive literal at variable j-1.

CLI examples:
    python3 experiments/unary_sat.py --self-test
    python3 experiments/unary_sat.py graph.json --format dimacs
    python3 experiments/unary_sat.py - --format lean < graph.json

JSON fields are "edges", "prices", and "threshold". Numbers may be JSON
integers or binary strings such as "0b11001". A loop pays one; repeated
edges count separately, just as in TropicalMWIS.energy.

For m edges let U = m + sum(max(a,b) for a,b in prices) and take B =
max(1, U.bit_length()). Every partial sum fits in B bits. The circuit uses
at most G = 1 + 5*B*(n+m) + m + B gates, V <= n+G variables and
C <= n+4*G+1 clauses. Because each clause has at most three literals, the
unary-index Lean serialization occupies at most 1+(3*V+8)*C bits. Every
Tseitin gate is an equivalence, so each satisfying coloring has exactly one
extension on these V variables, including in the constant-threshold cases.
"""

from __future__ import annotations

import argparse
import itertools
import json
import sys
from dataclasses import dataclass
from pathlib import Path
from typing import Iterable, Iterator, Sequence


Clause = tuple[int, ...]
Edge = tuple[int, int]
Price = tuple[int, int]


def literal_value(literal: int, values: Sequence[bool]) -> bool:
    value = values[abs(literal) - 1]
    return value if literal > 0 else not value


def satisfies(clauses: Iterable[Clause], values: Sequence[bool]) -> bool:
    return all(any(literal_value(literal, values) for literal in clause) for clause in clauses)


@dataclass(frozen=True)
class Gate:
    op: str
    a: int = 0
    b: int = 0

    def value(self, values: Sequence[bool]) -> bool:
        if self.op == "false":
            return False
        a = literal_value(self.a, values)
        b = literal_value(self.b, values)
        if self.op == "and":
            return a and b
        if self.op == "or":
            return a or b
        if self.op == "xor":
            return a != b
        raise ValueError(f"unknown gate {self.op}")

    def clauses(self, z: int) -> tuple[Clause, ...]:
        a, b = self.a, self.b
        if self.op == "false":
            return ((-z,),)
        if self.op == "and":
            return ((-a, -b, z), (a, -z), (b, -z))
        if self.op == "or":
            return ((a, b, -z), (-a, z), (-b, z))
        if self.op == "xor":
            return ((a, b, -z), (-a, -b, -z), (a, -b, z), (-a, b, z))
        raise ValueError(f"unknown gate {self.op}")


@dataclass(frozen=True)
class Encoding:
    vertices: int
    gates: tuple[Gate, ...]
    clauses: tuple[Clause, ...]

    @property
    def variables(self) -> int:
        return self.vertices + len(self.gates)

    def extend(self, coloring: Sequence[bool]) -> tuple[bool, ...]:
        """The unique consistent values of all gates, before the final assertion."""
        if len(coloring) != self.vertices or any(type(v) is not bool for v in coloring):
            raise ValueError("expected one Boolean per vertex")
        values = list(coloring)
        for gate in self.gates:
            values.append(gate.value(values))
        return tuple(values)

    def dimacs(self) -> Iterator[str]:
        yield f"p cnf {self.variables} {len(self.clauses)}"
        for clause in self.clauses:
            yield " ".join(map(str, (*clause, 0)))

    def lean_word(self) -> Iterator[bool]:
        """Literal order, sign bits, and unary indices follow Complexity.SAT.encode."""
        def write_nat(n: int) -> Iterator[bool]:
            yield from itertools.repeat(True, n)
            yield False

        yield from write_nat(len(self.clauses))
        for clause in self.clauses:
            yield from write_nat(len(clause))
            for literal in clause:
                yield literal > 0
                yield from write_nat(abs(literal) - 1)


class Builder:
    def __init__(self, n: int) -> None:
        self.n = n
        self.gates: list[Gate] = []
        # Retain all input bits even when a threshold or isolated vertex is inert.
        self.clauses: list[Clause] = [(v, -v) for v in range(1, n + 1)]
        self.zero = self.emit(Gate("false"))
        self.one = -self.zero

    def emit(self, gate: Gate) -> int:
        out = self.n + len(self.gates) + 1
        self.gates.append(gate)
        self.clauses.extend(gate.clauses(out))
        return out

    def binary(self, op: str, a: int, b: int) -> int:
        # Constant propagation and aliases preserve unique Tseitin extensions.
        if a in (self.zero, self.one):
            a, b = b, a
        if op == "xor":
            if a == b:
                return self.zero
            if a == -b:
                return self.one
            if b == self.zero:
                return a
            if b == self.one:
                return -a
        elif op == "and":
            if a == -b or b == self.zero:
                return self.zero
            if a == b or b == self.one:
                return a
        elif op == "or":
            if a == -b or b == self.one:
                return self.one
            if a == b or b == self.zero:
                return a
        else:
            raise ValueError(f"unknown gate {op}")
        return self.emit(Gate(op, a, b))

    def add(self, a: Sequence[int], b: Sequence[int]) -> list[int]:
        """Add two equal-width bit vectors. The last carry is unnecessary."""
        total = []
        carry = self.zero
        for i, (x, y) in enumerate(zip(a, b, strict=True)):
            parity = self.binary("xor", x, y)
            total.append(self.binary("xor", parity, carry))
            if i + 1 != len(a):
                both = self.binary("and", x, y)
                propagate = self.binary("and", parity, carry)
                carry = self.binary("or", both, propagate)
        return total

    def selected_bit(self, vertex: int, low: int, high: int) -> int:
        if low == high:
            return self.one if low else self.zero
        return vertex if high else -vertex


def checked_int(value: object) -> int:
    if type(value) is int:
        return value
    if isinstance(value, str):
        return int(value, 0)
    raise ValueError(f"expected an integer or a binary string, got {value!r}")


def compile_threshold(
    edges: Iterable[Edge], prices: Iterable[Price], threshold: int
) -> Encoding:
    """SAT iff a coloring costs ≤ threshold. Each such coloring extends once."""
    prices = tuple((checked_int(a), checked_int(b)) for a, b in prices)
    if any(min(pair) < 0 for pair in prices):
        raise ValueError("unary prices must be nonnegative")
    n = len(prices)
    edges = tuple((checked_int(u), checked_int(v)) for u, v in edges)
    if any(not (0 <= u < n and 0 <= v < n) for u, v in edges):
        raise ValueError("edge endpoint out of range")
    threshold = checked_int(threshold)
    upper = len(edges) + sum(max(a, b) for a, b in prices)

    if threshold < 0 or threshold >= upper:
        clauses = tuple((v, -v) for v in range(1, n + 1))
        if threshold < 0:
            clauses += ((),)
        return Encoding(n, (), clauses)

    builder = Builder(n)
    bits = upper.bit_length()
    accum = [builder.zero] * bits
    for v, (a, b) in enumerate(prices, 1):
        term = [builder.selected_bit(v, (a >> j) & 1, (b >> j) & 1) for j in range(bits)]
        accum = builder.add(accum, term)
    for u, v in edges:
        equal = -builder.binary("xor", u + 1, v + 1)
        accum = builder.add(accum, [equal] + [builder.zero] * (bits - 1))

    # The comparison of low-order prefixes is updated by each new high bit.
    accept = builder.one
    for j, bit in enumerate(accum):
        op = "or" if (threshold >> j) & 1 else "and"
        accept = builder.binary(op, -bit, accept)
    builder.clauses.append((accept,))
    return Encoding(n, tuple(builder.gates), tuple(builder.clauses))


def energy(edges: Sequence[Edge], prices: Sequence[Price], z: Sequence[bool]) -> int:
    return sum(z[u] == z[v] for u, v in edges) + sum(p[b] for p, b in zip(prices, z, strict=True))


def decode_lean(bits: Iterable[bool]) -> tuple[Clause, ...]:
    """Independent round-trip reader used by the self-test."""
    stream = iter(bits)

    def read_nat() -> int:
        n = 0
        while next(stream):
            n += 1
        return n

    clauses = []
    for _ in range(read_nat()):
        clause = []
        for _ in range(read_nat()):
            positive = next(stream)
            var = read_nat() + 1
            clause.append(var if positive else -var)
        clauses.append(tuple(clause))
    if next(stream, None) is not None:
        raise ValueError("trailing encoded data")
    return tuple(clauses)


def self_test() -> None:
    for op in ("and", "or", "xor"):
        for signed_a, signed_b in itertools.product((1, -1), (2, -2)):
            gate = Gate(op, signed_a, signed_b)
            for a, b, z in itertools.product((False, True), repeat=3):
                assert satisfies(gate.clauses(3), (a, b, z)) == (z == gate.value((a, b)))
    for b in (False, True):
        assert satisfies(Gate("false").clauses(1), (b,)) == (not b)
    # Lean's encode [[[positive variable 0]]] in full, including both headers.
    assert list(Encoding(1, (), ((1,),)).lean_word()) == [True, False, True, False, True, False]
    assert list(Encoding(0, (), ((),)).lean_word()) == [True, False, False]
    assert list(Encoding(0, (), ()).lean_word()) == [False]

    examples = [
        ([], []),
        ([], [(1, 3)]),
        ([(0, 1)], [(0, 0), (0, 0)]),
        ([(0, 0), (0, 1), (1, 0)], [(0, 4), (1, 2)]),
        ([(0, 1), (1, 2), (2, 0)], [(1, 7), (5, 2), (0, 4)]),
        ([(0, 2)], [(8, 2), (3, 3), (2, 0), (0, 0)]),
    ]
    count = 0
    brute = 0
    for edges, prices in examples:
        colors = tuple(itertools.product((False, True), repeat=len(prices)))
        upper = len(edges) + sum(max(p) for p in prices)
        for k in range(-1, upper + 2):
            fmt = compile_threshold(edges, prices, k)
            assert all(len(clause) <= 3 for clause in fmt.clauses)
            assert decode_lean(fmt.lean_word()) == fmt.clauses
            for z in colors:
                expected = energy(edges, prices, z) <= k
                assert satisfies(fmt.clauses, fmt.extend(z)) == expected
                count += 1
                if len(fmt.gates) <= 10:
                    models = sum(
                        satisfies(fmt.clauses, (*z, *aux))
                        for aux in itertools.product((False, True), repeat=len(fmt.gates))
                    )
                    assert models == int(expected)
                    brute += 1
    huge = (1 << 1500) + 13
    for k in (-1, 0, huge - 1, huge, huge + 1):
        fmt = compile_threshold([], [(huge, 0)], k)
        for b in (True, False):
            assert satisfies(fmt.clauses, fmt.extend((b,))) == ((0 if b else huge) <= k)
    print(f"verified {count} coloring/threshold cases, {brute} by full auxiliary enumeration; "
          "all gate relations, Lean serialization, and 1501-bit prices checked")


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("input", nargs="?", help="input JSON file, or - for stdin")
    parser.add_argument("--format", choices=("dimacs", "lean"), default="dimacs")
    parser.add_argument("--self-test", action="store_true")
    args = parser.parse_args()
    if args.self_test or args.input is None:
        self_test()
        return
    if args.input == "-":
        obj = json.load(sys.stdin)
    else:
        with Path(args.input).open(encoding="utf-8") as stream:
            obj = json.load(stream)
    fmt = compile_threshold(obj["edges"], obj["prices"], obj["threshold"])
    if args.format == "dimacs":
        for line in fmt.dimacs():
            print(line)
    else:
        # Stream the genuine unary-index serializer without constructing the large word.
        for bit in fmt.lean_word():
            sys.stdout.write("1" if bit else "0")
        sys.stdout.write("\n")


if __name__ == "__main__":
    main()
