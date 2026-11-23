"""Independent controls for the unary SAT serialization and the two-tape promise algorithm."""
from itertools import product
from math import isqrt


def unary(i):
    return '1' * i + '0'


def gadget(x, y):
    n = len(x)
    assert len(y) == n
    out = [unary(8*n)]
    for row in (x, y):
        for i, bit in enumerate(row):
            for a, b in product('01', repeat=2):
                out.extend([unary(3), str(bit), unary(i), a, unary(n), b, unary(n+1)])
    return ''.join(out)


def two_tape(word):
    """Read-only one-way input; a second head reads, writes and rewinds.

    The transition control has only the finite variables below. The unbounded
    indices implement tape heads in the simulator and are not inspected by
    the controller. The parsing logic relies on the promise of a paired gadget.
    """
    tape = {0: '#'}
    i, j = 0, 1
    phase, side, seen = 'header', 'left', False
    clause, literal, bit = 0, 0, ''
    ticks = 1  # initialize the work-tape sentinel and advance its head
    while True:
        symbol = word[i] if i < len(word) else '_'
        work = tape.get(j, '_')
        ticks += 1
        if phase == 'rewind':
            if work == '#':
                j += 1
                phase = 'compare'
            else:
                j -= 1
            continue
        if phase == 'compare':
            if work != bit:
                return False, ticks
            j += 1
            phase = 'after-pin-index'
            continue
        if symbol == '_':
            return (phase == 'clause' and (not seen or (side == 'right' and work == '_'))), ticks
        if phase == 'header':
            if symbol == '0':
                phase = 'clause'
        elif phase == 'clause':
            if symbol == '0':
                phase = 'sign'
        elif phase == 'sign':
            if clause == 0 and literal == 0:
                bit = symbol
                phase = 'pin-index'
            else:
                phase = 'index'
        elif phase == 'pin-index':
            # The first index bit is enough to recognize variable zero.
            if seen and side == 'left' and symbol == '0':
                side = 'right'
                phase = 'rewind'
                continue  # hold input on the unary terminator
            if side == 'left':
                tape[j] = bit
                j += 1
            else:
                if work != bit:
                    return False, ticks
                j += 1
            seen = True
            phase = 'index'
            continue  # reprocess this same bit in the index-reading state
        elif phase in ('index', 'after-pin-index'):
            if symbol == '0':
                literal = (literal + 1) % 3
                if literal == 0:
                    clause = (clause + 1) % 4
                phase = 'clause' if literal == 0 else 'sign'
        i += 1


def witness_code(support, n):
    """A uniquely decodable support tag bound for any positive SAT instance of length n."""
    k = max(1, isqrt(n) + (isqrt(n)**2 < n))
    assert len(set(support)) == len(support) and all(i >= 0 for i in support)
    assert sum(i+1 for i in support) <= n
    columns = [[] for _ in range(k)]
    for i in sorted(support):
        columns[i % k].append(i // k)
    payload = ''.join(''.join('1' + unary(q) for q in column) + '0' for column in columns)
    assert len(payload) <= 6*k
    return payload.ljust(6*k, '0')


def read_witness(bits, k):
    i, result = 0, []
    for r in range(k):
        while bits[i] == '1':
            i += 1
            end = bits.index('0', i)
            result.append((end-i)*k+r)
            i = end+1
        i += 1
    return sorted(result)


def supports(left, start=1):
    yield ()
    for price in range(start, left+1):
        for tail in supports(left-price, price+1):
            yield (price-1, *tail)


def main():
    count = 0
    for n in range(5):
        words = list(product((0,1), repeat=n))
        for x, y in product(words, repeat=2):
            w = gadget(x,y)
            answer, steps = two_tape(w)
            assert answer == (x == y)
            assert steps <= len(w) + 3*n + 8
            count += 1
    for n in range(41):
        k = max(1, isqrt(n) + (isqrt(n)**2 < n))
        for support in supports(n):
            assert read_witness(witness_code(support,n),k) == list(support)
    print(f'{count} serialized equality gadgets checked against the two-tape controller; N+3n+8 step budget.')
    print('Distinct-positive-index support codes of price up to 40 round-trip using at most 6 ceil(sqrt(N)) bits (N>0).')


if __name__ == '__main__':
    main()
