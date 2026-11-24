"""Face-choice contraction, and two independent physical switches per Hamiltonian arc."""
from face_multiplicity import equality_lines, line
from free_direction_coloring import lines3
from hamiltonian_boards import BoardFamily, check_bits, cycle_masks, geometry, sat_solver
from cycle_cover_queries import original
from paired_contraction import Circuit


def external_words(lines, ports):
    points = sorted({p for row in lines for p in row})
    index = {p: i for i, p in enumerate(points)}
    rows = [sum(1 << index[p] for p in row) for row in lines]
    answers = set()
    for word in range(1 << len(points)):
        if all((word & r).bit_count() == 1 for r in rows):
            answers.add(''.join(str(word >> index[p] & 1) for p in ports))
    return answers, len(points)


def check_two_faces():
    a, b, c, d = 4, 8, 16, 32
    main = [line(a, c), line(b, d)]
    ports = (c, a ^ c, d, b ^ d)
    loose, _ = external_words(main, ports)
    tied, n = external_words(main + equality_lines(a, b, 64, 128, 256), ports)
    quotient, _ = external_words([line(a, c), line(a, d)], (c, a ^ c, d, a ^ d))
    assert len(loose) == 9 and n == 16
    assert tied == quotient == {'0000', '0101', '0110', '1001', '1010'}
    print(f'11 boards to 2: all {2**n} choices, same five external words')


class DoubleShutters(BoardFamily):
    def __init__(self, m):
        super().__init__(m)
        self.old_dimension = self.dimension
        self.old_switches = self.switches
        self.switches = []
        self.second = []
        self.connectors = []
        self.extra_forces = []
        self.retract = {}
        for p, port, toggle in self.old_switches:
            alias, t, f, j = self.axis(), self.axis(), self.axis(), self.axis()
            self.connectors.extend((1, 2, u, v) for u, v, _ in equality_lines(port, alias, t, f, j))
            new_p, new_f, new_j, new_toggle = self.axis(), self.axis(), self.axis(), self.axis()
            self.extra_forces.extend((1, 2, u, v) for u, v, w in lines3((new_p, new_f, new_j))
                                     if (u, v, w) != line(new_p, new_f))
            # The original four private axes are consecutive in BoardFamily.
            assert toggle == p << 3
            self.retract.update({alias: port, new_p: p, new_f: p << 1, new_j: p << 2,
                                 new_toggle: toggle})
            self.switches.append((p, alias, toggle))
            self.second.append((new_p, alias, new_toggle))

    @staticmethod
    def switched(ports, mask):
        return [(1, 2, p, port ^ (toggle if mask >> i & 1 else 0))
                for i, (p, port, toggle) in enumerate(ports)]

    def boards(self, word):
        n = len(self.edges)
        if not 0 <= word < 1 << (2*n):
            raise ValueError('expected two edge masks')
        return (self.fixed + self.connectors + self.extra_forces + self.switched(self.switches, word)
                + self.switched(self.second, word >> n) + self.attachment)

    def bit_positions(self):
        start = len(self.fixed) + len(self.connectors) + len(self.extra_forces)
        return [(4*(start+i)+3)*8*self.field_bytes + toggle.bit_length()-1
                for i, (_, _, toggle) in enumerate(self.switches+self.second)]

    def map_vector(self, v):
        x = v & ((1 << self.old_dimension)-1)
        high = v ^ x
        while high:
            bit = high & -high
            x ^= self.retract[bit]
            high ^= bit
        return x

    def contracted(self, word, diagonal):
        # Drop the nine equality boards before taking the quotient. The
        # neutral second switch is private; on the diagonal its copy coincides.
        n = len(self.edges)
        mask = word & ((1 << n)-1)
        second_mask = word >> n
        if second_mask != (mask if diagonal else (1 << n)-1):
            raise ValueError('input outside the specified restriction')
        charts = self.fixed + self.switched(self.switches, mask) + self.attachment
        if diagonal:
            charts += self.extra_forces + self.switched(self.second, second_mask)
        return {tuple(self.map_vector(v) for v in board) for board in charts}


def check_shutters(m, solver):
    small, big = BoardFamily(m), DoubleShutters(m)
    n = len(small.edges)
    high = (1 << n)-1
    assert len(big.boards(0)) == len(small.boards(0)) + 16*n
    assert big.dimension == small.dimension + 8*n
    check_bits(big)
    tours = cycle_masks(m)
    words = range(1 << (2*n)) if m == 2 else [0, high, high << n, high | high << n,
              tours[0] | (tours[-1] << n), tours[0] | (tours[0] << n)]
    for word in words:
        common = word & (word >> n) & high
        assert geometry(big, word, solver, check_tables=(m == 2 and common == high)) == {
            t for t in tours if t & common == t}
    for x in range(high+1):
        expected = set(small.boards(x))
        assert big.contracted(x | (x << n), True) == expected
        assert big.contracted(x | (high << n), False) == expected
    print(f'm={m}: {len(big.boards(0))} -> {len(small.boards(0))} boards; '
          f'{2*n} distinct raw switch bits, both quotients checked on {high+1} masks')


def check_three_point_diagonal():
    # The two directed 3-tours partition the six arc variables. Make the
    # two copies of each variable nonadjacent in its six-leaf AND chain.
    small, big = Circuit(3), Circuit(4)
    n = len(small.edges)
    slots = list(big.inputs.values())
    tours = cycle_masks(3)
    terms = []
    for tour in tours:
        indices = [i for i in range(n) if tour >> i & 1]
        terms.append(big.fold('and', [slots[i] for i in indices] + [slots[n+i] for i in indices]))
    out = big.fold('or', terms)
    assert big.size(out) == 2*n-1
    source = original(4)
    for word in range(1 << (2*n)):
        common = word & (word >> n)
        assert big.values(source.graph(word))[out] == any(common & t == t for t in tours)
    kept = list(small.inputs.values())
    for second, expected in ((kept, 2*n-1), ([1]*n, n-1)):
        image = big.replay(small, dict(zip(big.edges, kept+second)))
        assert small.size(image[out]) == expected
    print('full H3 with double switches: 4096 masks, optimal 11 gates; diagonal 11, neutral 5')


if __name__ == '__main__':
    check_two_faces()
    check_three_point_diagonal()
    engine = sat_solver()
    check_shutters(2, engine)
    check_shutters(3, engine)
