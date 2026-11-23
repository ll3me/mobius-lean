"""A full ordinary 3-SAT decider with a linear-time two-tape equality fast path.

The controller can read only the current symbols. Each read is a stationary
transition and each move/write is one local transition. The integer head
positions, random-access backing store and step counter belong to the tape
simulator; neither decision routine inspects them. The read-only input has a
left endmarker and an end-of-input blank. One read/write head serves a single
work tape over the fixed product alphabet Cell. All controller loops branch
on symbols or iterate over a fixed finite set; subroutine depth is bounded.

On a genuine gadget, n work slots lie between the origin and endmarker.
Each of the three index checks per clause costs at most 5n+9 transitions:
at most 2n+4 to return to the first slot, 3n for the parallel unary scan,
and at most 5 to test the marker and finish. The remaining clause overhead
is 14. Each of the 2n pin groups adds at most 2n+5 for its mark and return.
Both block starts and loop guards contribute at most 6n+12; the header and
end test cost at most 18n+6. Thus ticks <= 124n²+362n+18 <= 7N+20 for
N=20n²+92n+1. Only the general fallback enumerates assignments.
"""

from __future__ import annotations

from dataclasses import dataclass, replace
from itertools import product

from crossing_controls import gadget


@dataclass(frozen=True)
class Cell:
    kind: str = "."  # blank, '#': work origin, 'V': data slot, 'E': fast-path end
    mark: bool = False
    value: bool = False
    owed: bool = False
    variable: bool = False


BLANK = Cell()
ORIGIN = Cell("#")
BEFORE_INPUT = object()
AFTER_INPUT = object()


class Tapes:
    """Simulator only. The controller calls input_symbol, work_symbol and step."""

    def __init__(self, word: str):
        self._word = word
        self._input_head = 0
        self._work_head = 0
        self._work: dict[int, Cell] = {}
        self.ticks = 0

    def input_symbol(self):
        self.ticks += 1
        if self._input_head == -1:
            return BEFORE_INPUT
        if self._input_head == len(self._word):
            return AFTER_INPUT
        return self._word[self._input_head]

    def work_symbol(self) -> Cell:
        self.ticks += 1
        return self._work.get(self._work_head, BLANK)

    def step(self, di: int = 0, dw: int = 0, write: Cell | None = None) -> None:
        assert di in (-1, 0, 1) and dw in (-1, 0, 1)
        if write is not None:
            if write == BLANK:
                self._work.pop(self._work_head, None)
            else:
                self._work[self._work_head] = write
        self._input_head += di
        self._work_head += dw
        assert -1 <= self._input_head <= len(self._word) and self._work_head >= 0
        self.ticks += 1


class SyntaxMismatch(Exception):
    """A failed test of a grammar symbol; the handler is a fixed control state."""


def expect(t: Tapes, bit: str) -> None:
    if t.input_symbol() != bit:
        raise SyntaxMismatch
    t.step(di=1)


def read_bit(t: Tapes) -> bool:
    symbol = t.input_symbol()
    if symbol not in ("0", "1"):
        raise SyntaxMismatch
    t.step(di=1)
    return symbol == "1"


def input_home(t: Tapes) -> None:
    while t.input_symbol() is not BEFORE_INPUT:
        t.step(di=-1)
    t.step(di=1)


def work_home(t: Tapes) -> None:
    while t.work_symbol().kind != "#":
        t.step(dw=-1)
    t.step(dw=1)


def fast_index(t: Tapes, target: str, extra: bool = False) -> None:
    """Match one unary numeral against mark-position i or right-boundary n."""
    work_home(t)
    while True:
        w = t.work_symbol()
        if (w.mark if target == "i" else w.kind == "E"):
            break
        if w.kind != "V" or t.input_symbol() != "1":
            raise SyntaxMismatch
        t.step(di=1, dw=1)
    if extra:
        expect(t, "1")
    expect(t, "0")


def recognize(t: Tapes) -> bool:
    # The clause-count header must be exactly 8n ones and one zero. One
    # workspace slot per group of eight fixes n independently of the formula.
    while t.input_symbol() == "1":
        for _ in range(8):
            expect(t, "1")
        t.step(dw=1, write=Cell("V"))
    expect(t, "0")
    t.step(write=Cell("E"))
    equal = True

    for first in (True, False):
        work_home(t)
        while t.work_symbol().kind == "V":
            t.step(write=replace(t.work_symbol(), mark=True))
            data_bit = False
            for u, v in (("0", "0"), ("0", "1"), ("1", "0"), ("1", "1")):
                for bit in "1110":  # exactly three literals
                    expect(t, bit)
                sign = read_bit(t)
                if u == "0" and v == "0":
                    data_bit = sign
                elif sign != data_bit:
                    raise SyntaxMismatch
                fast_index(t, "i")
                expect(t, u)
                fast_index(t, "n")
                expect(t, v)
                fast_index(t, "n", extra=True)
            # At the work endmarker after the last n+1 comparison.
            while not t.work_symbol().mark:
                t.step(dw=-1)
            old = t.work_symbol()
            if first:
                old = replace(old, value=data_bit)
            else:
                equal = equal and (old.value == data_bit)
            t.step(dw=1, write=replace(old, mark=False))
        if t.work_symbol().kind != "E":
            raise SyntaxMismatch
    if t.input_symbol() is not AFTER_INPUT:
        raise SyntaxMismatch
    return equal


def clear_fast_workspace(t: Tapes) -> None:
    work_home(t)
    # During every partial recognition the occupied interval is contiguous.
    while t.work_symbol() != BLANK:
        t.step(dw=1, write=BLANK)
    work_home(t)


def find_clause(t: Tapes) -> None:
    work_home(t)
    while not t.work_symbol().mark:
        t.step(dw=1)


def evaluate_pass(t: Tapes) -> bool:
    """Parse one ordinary word completely and evaluate under the work assignment."""
    work_home(t)
    while t.input_symbol() == "1":
        t.step(di=1, dw=1, write=replace(t.work_symbol(), owed=True))
    expect(t, "0")
    work_home(t)
    t.step(write=replace(t.work_symbol(), mark=True))
    all_true = True
    while t.work_symbol().owed:
        # Only four arity counter values are stored in the finite control.
        arity = 0
        while t.input_symbol() == "1":
            if arity == 3:
                raise SyntaxMismatch
            arity += 1
            t.step(di=1)
        expect(t, "0")
        clause_true = False
        for _ in range(arity):
            sign = read_bit(t)
            work_home(t)
            # Slot j+1 stores variable j. Build the finite prefix of assignment
            # cells as indices are encountered, with initially false bits.
            while t.input_symbol() == "1":
                t.step(di=1, dw=1, write=replace(t.work_symbol(), variable=True))
            expect(t, "0")
            cell = t.work_symbol()
            clause_true = clause_true or (sign == cell.value)
            t.step(write=replace(cell, variable=True))
        all_true = all_true and clause_true
        find_clause(t)
        t.step(dw=1, write=replace(t.work_symbol(), mark=False))
        t.step(write=replace(t.work_symbol(), mark=True))
    t.step(write=replace(t.work_symbol(), mark=False))
    if t.input_symbol() is not AFTER_INPUT:
        raise SyntaxMismatch
    return all_true


def next_assignment(t: Tapes) -> bool:
    work_home(t)
    while True:
        cell = t.work_symbol()
        if not cell.variable:
            return False
        if not cell.value:
            t.step(write=replace(cell, value=True))
            return True
        t.step(dw=1, write=replace(cell, value=False))


def fallback(t: Tapes) -> bool:
    clear_fast_workspace(t)
    while True:
        input_home(t)
        try:
            if evaluate_pass(t):
                return True
        except SyntaxMismatch:
            return False
        if not next_assignment(t):
            return False


def decide(word: str) -> tuple[bool, str, int]:
    """Return the SAT answer, the branch used, and the local transition count."""
    t = Tapes(word)
    t.step(dw=1, write=ORIGIN)
    try:
        answer = recognize(t)
        return answer, "recognized", t.ticks
    except SyntaxMismatch:
        answer = fallback(t)
        return answer, "fallback", t.ticks


def reference(word: str) -> bool:
    """Independent property oracle for tests; not used by the decider."""
    pos = 0

    def nat():
        nonlocal pos
        end = word.index("0", pos)
        if any(c != "1" for c in word[pos:end]):
            raise ValueError
        n = end - pos
        pos = end + 1
        return n

    try:
        clauses = []
        for _ in range(nat()):
            width = nat()
            if width > 3:
                return False
            clause = []
            for _ in range(width):
                sign = word[pos]
                pos += 1
                if sign not in ("0", "1"):
                    return False
                clause.append((nat(), sign == "1"))
            clauses.append(clause)
        if pos != len(word):
            return False
    except (IndexError, ValueError):
        return False
    used = sorted({i for c in clauses for i, _ in c})
    for bits in product((False, True), repeat=len(used)):
        z = dict(zip(used, bits))
        if all(any(z[i] == sign for i, sign in c) for c in clauses):
            return True
    return False


def self_test() -> None:
    known: dict[int, set[str]] = {}
    probes = 0
    for n in range(4):
        labels = tuple(product((0, 1), repeat=n))
        accepted_layout = set()
        for x, y in product(labels, repeat=2):
            w = gadget(x, y)
            answer, path, ticks = decide(w)
            assert path == "recognized" and answer == (x == y) == reference(w)
            assert len(w) == 20*n*n+92*n+1
            assert ticks <= 124*n*n+362*n+18 <= 7*len(w)+20
            probes += 1
            accepted_layout.add(w)
        known[n] = accepted_layout

    # Every corruption either remains a genuine (possibly differently labelled)
    # gadget or takes the general SAT path. Check full recognition, not just SAT.
    sample = gadget((0,), (1,))
    changes = {sample[:i] + str(1-int(x)) + sample[i+1:] for i, x in enumerate(sample)}
    changes.update(sample[:i] + sample[i+1:] for i in range(len(sample)))
    changes.update(sample[:i] + b + sample[i:] for i in range(len(sample)+1) for b in "01")
    changes.update("".join(bits) for k in range(8) for bits in product("01", repeat=k))
    for w in changes:
        result, path, _ = decide(w)
        assert result == reference(w), (w, result)
        assert (path == "recognized") == any(w in group for group in known.values())

    def unary(k):
        return "1"*k + "0"

    def encode(clauses):
        return unary(len(clauses)) + "".join(
            unary(len(c)) + "".join(str(sign)+unary(i) for i, sign in c) for c in clauses
        )

    ordinary = [
        [[(1, 1)]], [[(0, 1)], [(0, 0)]], [[]], [[(3, 1), (3, 0)]],
        [[(0, 1)], [(1, 1)], [(2, 1)]], [[(1, 0)]*4],
        [[(0, 1), (1, 1)], [(0, 0)], [(1, 0)]],
        [[(2, 1)]] * 8, [[(0, 1)]] * 7 + [[(0, 0)]],
    ]
    for formula in ordinary:
        w = encode(formula)
        result, path, _ = decide(w)
        assert path == "fallback" and result == reference(w)
    for n in (4, 8, 16, 32):
        x = tuple(i % 2 for i in range(n))
        y = tuple(1-b for b in x)
        for z in (x, y):
            w = gadget(x, z)
            result, path, ticks = decide(w)
            assert path == "recognized" and result == (x == z) and ticks <= 124*n*n+362*n+18 <= 7*len(w)+20
    print(f"{probes + 8} genuine probes, {len(changes)} corrupt/short words, "
          f"{len(ordinary)} general formulas; two local heads, genuine probes within 7N+20 transitions.")


if __name__ == "__main__":
    self_test()
