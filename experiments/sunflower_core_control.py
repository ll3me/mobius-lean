"""Finite-field control for which many certified shared sources cannot be paid on one pairing."""
from fractions import Fraction
from functools import reduce
from random import Random

from boolean_sweep import xor_gate
from paired_contraction import Circuit, lift_graph
from paired_fanout import live_wires


class BinaryField:
    """Polynomial-basis arithmetic for the binary fields used in the finite checks."""
    def __init__(self, order, modulus):
        self.order = order
        self.product = []
        for a in range(order):
            row = []
            for b in range(order):
                x, y, result = a, b, 0
                while y:
                    if y & 1:
                        result ^= x
                    x <<= 1
                    if x & order:
                        x ^= modulus
                    y >>= 1
                row.append(result)
            self.product.append(row)
        assert all(len(set(row)) == order for row in self.product[1:])

    def power(self, a, k):
        result = 1
        while k:
            if k & 1:
                result = self.product[result][a]
            a = self.product[a][a]
            k >>= 1
        return result

    def trace(self, a, subfield_size):
        result, size = 0, 1
        while size < self.order:
            result ^= a
            a = self.power(a, subfield_size)
            size *= subfield_size
        assert size == self.order
        return result


def check_characters(field, c):
    q = field.order
    mul = field.product
    trace = [field.trace(x, c) for x in range(q)]
    worst, chosen = 0, None
    for a in range(q):
        for b in range(q):
            if (a, b) == (0, 0):
                continue
            count = sum(trace[mul[a][t] ^ mul[b][mul[t][t]]] == 0 for t in range(1, q))
            assert c*(count+1) <= 2*q
            if count > worst:
                worst, chosen = count, (a, b)
    print(f'field {q}, core {c}: {q*q-1} nontrivial characters, '
          f'largest annihilated direction fraction {Fraction(worst, q-1)}')
    return chosen


def groups(field, c):
    q = field.order
    subfield = [a for a in range(q) if field.power(a, c) == a]
    assert len(subfield) == c and q % (2*c) == 0
    for t in range(1, q):
        subspace = [field.product[t][a] for a in subfield]
        remaining = set(range(q))
        cosets = []
        while remaining:
            representative = min(remaining)
            coset = sorted(representative ^ a for a in subspace)
            cosets.append(coset)
            remaining.difference_update(coset)
        half = len(cosets)//2
        for intercept in range(q):
            points = [x*q + (field.product[t][x] ^ intercept) for x in range(q)]
            petals = tuple(points[x] for coset in cosets[half:] for x in coset)
            for coset in cosets[:half]:
                yield tuple(points[x] for x in coset), petals


def build_control(field, c):
    n = field.order**2
    dag = Circuit(n)
    used, cores, signals = set(), [], []
    for core, petals in groups(field, c):
        rows = []
        for w in petals:
            edges = [(u, v) for x in core for u, v in ((x, w), (w, x))]
            assert used.isdisjoint(edges)
            used.update(edges)
            rows.append(dag.fold('or', (dag.inputs[e] for e in edges)))
        signals.append(dag.fold('and', rows))
        cores.append(core)
    remaining = [dag.inputs[e] for e in dag.edges if e not in used]
    bare = remaining[:n-2]
    tail = dag.fold('or', remaining[n-2:])
    assert len(remaining) >= n and len(signals) % 2 == 0
    first_layer = [xor_gate(dag, g, h) for g, h in zip(signals[::2], signals[1::2])]
    out = reduce(lambda g, h: xor_gate(dag, g, h), first_layer + bare + [tail])
    parity_inputs = len(signals) + len(bare) + 1
    gates, uses = live_wires(dag, out)
    assert len(gates) == len(dag.edges) + 3*parity_inputs - 4
    assert all(uses[g] == 2 for g in signals)
    assert sum(uses[w]-1 for w in dag.inputs.values()) == n-2
    # No direct NOT reads a raw arc, so these are the whole raw-literal fees.
    raw = set(dag.inputs.values())
    assert all(dag.nodes[g][0] != 'not' or dag.nodes[g][1] not in raw for g in gates)
    internal = len(gates) - len(raw) + 1 - len(bare)
    assert internal == 3*len(signals) + 2*(n-2) and 5*len(signals) > internal
    return dag, out, cores, signals


def check_control(field, c, character):
    dag, out, cores, signals = build_control(field, c)
    q = field.order
    a, b = character
    character_side = [v for v in range(dag.order)
                      if field.trace(field.product[a][v//q] ^ field.product[b][v % q], 2) == 0]
    rng = Random(379)
    counts = []
    for side in [character_side] + [rng.sample(range(dag.order), dag.order//2) for _ in range(5)]:
        left = set(side)
        right = sorted(set(range(dag.order))-left)
        rng.shuffle(right)
        pairs = tuple(zip(side, right))
        small, image = dag.contract(pairs)
        monochrome = [all(v in left for v in core) or all(v not in left for v in core) for core in cores]
        assert c*sum(monochrome) <= 4*len(cores)
        alive = set()
        for g, mono in zip(signals, monochrome):
            assert image[g] != 1 and (image[g] >= 2 or mono)
            if image[g] >= 2:
                assert image[g] not in alive
                alive.add(image[g])
        # Take the AND reader in each four-gate XOR as the extra slot.
        paid = sum(image[g] < 2 or image[signals[i ^ 1]] == 0 for i, g in enumerate(signals))
        assert c*paid <= 8*len(signals)
        rows = [rng.getrandbits(small.order) & ~(1 << i) for i in range(small.order)]
        assert small.values(rows)[image[out]] == dag.values(lift_graph(rows, pairs))[out]
        counts.append(paid)
    print(f'{dag.order} vertices: {dag.size(out)} gates in the exact-size control, {len(cores)} '
          f'marked shared sources, sampled charged slots {counts}')


if __name__ == '__main__':
    small_field = BinaryField(16, 0b10011)
    character = check_characters(small_field, 4)
    check_control(small_field, 4, character)
    check_characters(BinaryField(64, 0b1000011), 8)
