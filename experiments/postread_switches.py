"""Post-read operations on cyclic routes, and coverage of forced decision pairs."""
from itertools import combinations, permutations, product
from math import comb, factorial

from cycle_cover_queries import evaluate, original, query_bits, with_hubs


def one_orbit(successor):
    seen, u = set(), 0
    while u not in seen:
        seen.add(u)
        u = successor[u]
    return len(seen) == len(successor) and u == 0


def routing(width, layers, word):
    """Each layer independently keeps all tracks or rotates them by one."""
    return [width*((j+1) % layers) + (track + ((word >> j) & 1)) % width
            for j in range(layers) for track in range(width)]


def check_routes():
    masks = 0
    for layers in range(2, 10):
        for width in (2, 3):
            for word in range(1 << layers):
                residue = word & 1
                steps = 0
                for j in range(1, layers-1):
                    residue = (residue + ((word >> j) & 1)) % width
                    steps += 1
                answer = (residue + (word >> (layers-1))) % width != 0
                assert steps+1 == layers-1
                assert one_orbit(routing(width, layers, word)) == answer == (word.bit_count() % width != 0)
                masks += 1
        # A pair of free switches always gives a genuinely two-variable decision.
        for shift in range(3):
            square = [[(shift+a+b) % 3 != 0 for b in range(2)] for a in range(2)]
            assert square[0] != square[1] and any(row[0] != row[1] for row in square)
    print(f'{masks} actual two- and three-track masks, all three residual two-switch tables')


def check_one_step(n):
    words = list(range(1 << n))
    unary = {tuple(((s >> i) & 1) ^ sign for s in words)
             for i in range(n) for sign in range(2)}
    unary.update([(0,)*len(words), (1,)*len(words)])
    faces = [[s for s in words if ((s >> i) & 1) == b] for i in range(n) for b in range(2)]
    allowed = [{tuple(reg[s] for s in face) for reg in unary} for face in faces]
    checks = 0
    for a, b, op in product(unary, unary, range(16)):
        out = [op >> (u + 2*v) & 1 for u, v in zip(a, b)]
        assert any(tuple(out[s] for s in face) in good for face, good in zip(faces, allowed))
        checks += 1
    # Every satisfiable conjunction of unary Boolean tests is a cube.
    for req in product((None, 0, 1), repeat=n):
        out = [all(v is None or ((s >> i) & 1) == v for i, v in enumerate(req)) for s in words]
        assert any(len({out[s] for s in face}) == 1 for face in faces)
    print(f'{checks} two-input gates on unary registers and {3**n} consistent conjunctions')


def check_sign_pairs(n):
    perms = list(permutations(range(n)))
    sign = {p: sum(a > b for a, b in combinations(p, 2)) % 2 for p in perms}
    rows = set()
    covered = [0, 0]
    total = 0
    target = (n-1) % 2
    for left in perms:
        answers = []
        for right in perms:
            yes = one_orbit(tuple(right[i] for i in left))
            answers.append(yes)
            if not yes:
                continue
            for u, v in combinations(range(n), 2):
                other = list(left)
                other[u], other[v] = other[v], other[u]
                other = tuple(other)
                assert not one_orbit(tuple(right[i] for i in other))
                assert (sign[left] ^ sign[right]) == target != (sign[other] ^ sign[right])
                assert sign[left] != sign[other]
                covered[sign[left]] += 1
                total += 1
        rows.add(tuple(answers))
    assert len(rows) == factorial(n)
    assert total == factorial(n)*factorial(n-1)*comb(n, 2)
    assert covered[0] == covered[1] == total//2
    print(f'n={n}: {len(rows)} different continuation functions; one sign bit decides all {total} pairs')


def check_ring_queries(m):
    source = original(m)
    ring = [(u, (u+1) % m) for u in range(m)]
    for k in range(1, m+1):
        inner = with_hubs(source, k)
        batches = []
        for start in range(0, m, k):
            request = [(2*u+1, 2*(m if v == 0 else v)) for u, v in ring[start:start+k]]
            batches.append(query_bits(inner, request))
        assert len(batches) == (m+k-1)//k
        for word in range(1 << m):
            graph = sum(1 << source.labels[e] for i, e in enumerate(ring) if (word >> i) & 1)
            assert all(evaluate(bits, graph) for bits in batches) == (word == (1 << m)-1)
    print(f'{m}-vertex fixed ring: all widths, all masks, ceiling(m/k) grouped queries')


if __name__ == '__main__':
    check_routes()
    check_one_step(4)
    for n in range(2, 6):
        check_sign_pairs(n)
        check_ring_queries(n)
