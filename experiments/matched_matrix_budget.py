"""Audit alternating Hamiltonian circuits on one matching and the ordered matrix probes."""
from collections import Counter
from fractions import Fraction
from functools import lru_cache
from itertools import combinations, permutations, product
from math import ceil
from types import SimpleNamespace

from absorbing_readers import ReaderProfile, masked_circuit
from alternating_cut import cut_graph
from boolean_sweep import affine_rebuild, live_gates, rewrite_windows, xor_gate
from cycle_cover_queries import tour_count
from paired_contraction import Circuit, held_karp, pairings


def rooted_cycle(m, vertices, reverse=False):
    step = list(range(m))
    cycle = [0] + sorted(vertices, reverse=reverse)
    for u, v in zip(cycle, cycle[1:]+cycle[:1]):
        step[u] = v
    return tuple(step)


def components(forward, backward):
    unseen = set(range(len(forward)))
    count = 0
    while unseen:
        v = next(iter(unseen))
        while v in unseen:
            unseen.remove(v)
            v = backward[forward[v]]
        count += 1
    return count


def all_subsets(items):
    return [frozenset(group) for k in range(len(items)+1) for group in combinations(items, k)]


def check_ordered_probes(m):
    rest = frozenset(range(1, m))
    words = all_subsets(rest)
    first = {s: rooted_cycle(m, s) for s in words}
    queries = {t: rooted_cycle(m, rest-t, reverse=True) for t in words}
    for s, forward in first.items():
        for t, backward in queries.items():
            assert components(forward, backward) == 1+len(s ^ t)
    upper = {(i, j) for i in rest for j in rest if i < j}
    fixed = {(i, i) for i in range(m)} | {(0, i) for i in rest} | {(i, 0) for i in rest}
    supported = {p for p in permutations(range(m)) if set(enumerate(p)) <= fixed | upper}
    assert supported == set(first.values())
    for e in upper:
        unique = [p for p in supported if components(p, queries[frozenset(e)]) == 1]
        assert len(unique) == 1 and (set(enumerate(unique[0])) - fixed) == {e}
    print(f'{m}+{m}: {len(words)**2:,} exact cycle counts, {len(upper)} independent upper cells')


def check_flexible_marking(m):
    """Turning on all optional arcs is the hardest rejection, turning them off the hardest acceptance."""
    cells = [(i, j) for i in range(m) for j in range(m)]
    bits = {(i, j): 1 << (m*i+j) for i, j in cells}
    upper = sum(bits[i, j] for i, j in cells if 0 < i < j)
    diagonal = sum(bits[i, i] for i in range(m))
    perms = list(permutations(range(m)))
    masks = {p: sum(bits[e] for e in enumerate(p)) for p in perms}
    identity = tuple(range(m))
    rest = set(range(1, m))
    checked = 0
    for i, j in cells:
        bit = bits[i, j]
        forward = set(enumerate(identity))
        if i == j:
            back = rooted_cycle(m, rest)
        elif i == 0 or j == 0:
            forward.add((j, i))
            back = rooted_cycle(m, rest-{i, j}, reverse=True)
        else:
            forward.update(((0, i), (j, 0)))
            back = rooted_cycle(m, rest-{i, j}, reverse=True)
        small = sum(bits[e] for e in forward) | bit
        large = (small | upper) ^ bit
        allowed = [mask for p, mask in masks.items() if components(p, back) == 1]
        assert any(mask & small == mask for mask in allowed)
        assert not any(mask & large == mask for mask in allowed)
        checked += 1
        # Opposite-matrix target. A single opposite permutation forces its marked row.
        forward_perm = list(identity)
        if i == j:
            other = 0 if i else 1
            forward_perm[i], forward_perm[other] = other, i
        witness = next(p for p in perms if p[i] == j and components(forward_perm, p) == 1)
        front = diagonal | masks[tuple(forward_perm)]
        assert components(forward_perm, witness) == 1
        assert front & masks[tuple(forward_perm)] == masks[tuple(forward_perm)]
        assert all(mask & (masks[witness] ^ bit) != mask for mask in masks.values())
        checked += 1
    print(f'{m}+{m}: {checked} raw pivots with the other upper-triangular switches free')


def matching_ledger(m, pairs):
    large = Circuit(2*m)
    output = held_karp(large, 2*m)
    left = {u for u, _ in pairs}
    stage = Circuit(2*m)
    wires = {e: stage.inputs[e] for e in large.edges if (e[0] in left) != (e[1] in left)}
    root = large.replay(stage, wires)[output]
    live = set(live_gates(stage, root))
    small, image = stage.contract(pairs)
    win, wr = rewrite_windows(small, image[root])
    aff, ar = affine_rebuild(win, wr)
    residual = min(small.size(image[root]), win.size(wr), aff.size(ar))
    constant = {w for w in live if image[w] < 2}
    keep, ports, raw = cut_graph(stage, root, constant)
    dead = live-keep-constant
    hidden = len(wires)-len(raw)
    fixed = ports | {w for w in raw if image[w] < 2}
    neutral = [v for v in keep if any(w in fixed for w in stage.nodes[v][1:])]
    credit = len(constant)+len(dead)+len(ports)-hidden
    extra_uses = len(neutral)-len(fixed)
    extra_rewrites = len(keep)-len(neutral)-residual
    assert len(live)-residual == m*m+m+credit+extra_uses+extra_rewrites
    return (len(live), residual, len(constant), len(dead), len(ports), hidden,
            credit, extra_uses, extra_rewrites)


def audited_profile(dag, root):
    live = live_gates(dag, root)
    raw = {w for g in live for w in dag.nodes[g][1:] if dag.nodes[w][0] == 'input'}
    inputs = {e: w for e, w in dag.inputs.items() if w in raw}
    view = SimpleNamespace(edges=list(inputs), inputs=inputs, nodes=dag.nodes, size=dag.size)
    return ReaderProfile(view, root)


def component_ledger(profile, selected, fixed, target, image, support_bound, small_expected=0):
    dag = profile.dag
    stems = {profile.head[e] for e in selected}
    active, leaves = profile.reachable_after_cut(stems)
    assert leaves == stems | {wire for e, wire in dag.inputs.items() if e not in selected}
    raw = set(dag.inputs.values())
    pruned = profile.gates - active - stems
    direct_not = {g for g in pruned if dag.nodes[g][0] == 'not' and dag.nodes[g][1] in raw}
    pending = set(pruned-direct_not)
    tickets = Counter(g for e, g in profile.repeated_tickets if e in fixed and g in pending)
    exceptions = 0
    small = 0
    largest = 0
    while pending:
        component = set()
        stack = [pending.pop()]
        while stack:
            g = stack.pop()
            component.add(g)
            for w in (*dag.nodes[g][1:], *profile.reads[g]):
                if w in pending:
                    pending.remove(w)
                    stack.append(w)
        hits = sum(tickets[g] for g in component)
        assert hits <= len(component)+1
        if hits > len(component):
            assert any(reader in stems for g in component for reader in profile.reads[g])
            raw_sources = {e for e, g in profile.repeated_tickets if e in fixed and g in component}
            if len(raw_sources) < support_bound:
                sources = {dag.inputs[e] for e in raw_sources}
                signs = {a for g in component for a in dag.nodes[g][1:] if a not in component}
                assert any(a in sources and any(dag.nodes[v] == ('not', a) for v in signs)
                           for a in signs)
                small += 1
            exceptions += 1
            largest = max(largest, len(component))
    _, _, actual = profile.check_cut(selected, fixed, target, image)
    fee = sum(profile.fees[e] for e in fixed)
    assert actual >= len(fixed)+len(stems)+fee-exceptions
    assert small == small_expected
    assert small <= sum(max(0, profile.fees[e]-1) for e in fixed)
    assert support_bound*(exceptions-small) <= 2*fee
    return exceptions, largest


def check_semantic_constant(m):
    original = Circuit(2*m)
    tour = held_karp(original, 2*m)
    dag = Circuit(2*m)
    active = {e: v for e, v in dag.inputs.items() if (e[0]^e[1]) & 1}
    e = (0, 1)
    w = active[2, 3]
    contradictory = dag.gate('and', w, dag.neg(w))
    active[e] = dag.gate('or', active[e], contradictory)
    root = original.replay(dag, active)[tour]
    profile = audited_profile(dag, root)
    pairs = tuple((2*i, 2*i+1) for i in range(m))
    target, image = dag.contract(pairs)
    fixed = {edge for edge in active if image[dag.inputs[edge]] < 2}
    assert component_ledger(profile, {e}, fixed, target, image, m-1, small_expected=1) == (1, 1)
    print(f'{m}+{m}: one pruned gate loses both signs of the same variable in a nonminimum circuit')


def check_stage_components(m):
    dag, root = masked_circuit(2*m, False)
    profile = audited_profile(dag, root)
    vertices = set(range(2*m))
    examined = 0
    for left in combinations(sorted(vertices), m):
        left = set(left)
        right = vertices-left
        inside = set(permutations(left, 2))
        other = set(permutations(right, 2))
        fixed = inside | other
        target = Circuit(2*m)
        cross = {e: w for e, w in target.inputs.items() if e not in fixed}
        for safe_left, safe_right in product(inside, other):
            movable, zero = inside-{safe_left}, other-{safe_right}
            selected = {e for e, h in profile.head.items() if e in movable or
                        (e in zero and dag.nodes[h][0] == 'and')}
            opened = {e: 1 for e in selected if dag.nodes[profile.head[e]][0] == 'or'}
            image = dag.replay(target, cross | opened)
            component_ledger(profile, selected, fixed, target, image, 2*m-2)
            examined += 1
    print(f'{2*m} vertices: {examined} full-to-alternating cuts on a mixed private-reader circuit')


def check_alternating_components(m):
    n = 2*m
    original = Circuit(n)
    big = held_karp(original, n)
    dag = Circuit(n)
    active = {e: w for e, w in dag.inputs.items() if (e[0]^e[1]) & 1}
    tour = [(2*i, 2*((i+1) % m)+1) for i in range(m)] + [(2*i+1, 2*i) for i in range(m)]
    guard = dag.fold('and', (active[e] for e in tour))
    active[0, 1] = dag.gate('or', active[0, 1], guard)
    root = original.replay(dag, active)[big]
    profile = audited_profile(dag, root)
    examined = exceptional = largest = 0
    orderings = list(permutations(range(m))) if m <= 4 else [tuple(range(m))]
    for left, right, reverse in product(orderings, orderings, (False, True)):
        pairs = [(2*i, 2*j+1) for i, j in zip(left, right)]
        if reverse:
            pairs = [(b, a) for a, b in pairs]
        matching = set(pairs)
        flex = {(pairs[i][0], pairs[j][1]) for i in range(1, m) for j in range(i+1, m)}
        lower = {(pairs[j][0], pairs[i][1]) for i in range(1, m) for j in range(i+1, m)}
        selected = {e for e, h in profile.head.items() if e in flex or
                    (e in lower and dag.nodes[h][0] == 'and') or
                    (e in matching and dag.nodes[h][0] == 'or')}
        target = Circuit(m)
        free = {(pairs[i][1], pairs[j][0]): target.inputs[i, j] for i, j in target.edges}
        fixed = set(active) - set(free)
        ones = matching | {e for e in selected & flex if dag.nodes[profile.head[e]][0] == 'or'}
        image = dag.replay(target, free | {e: 1 for e in ones})
        count, length = component_ledger(profile, selected, fixed, target, image, m-1)
        exceptional += count
        largest = max(largest, length)
        examined += 1
    assert largest == 2*m-1
    print(f'{m}+{m}: {examined} alternating-to-small cuts, {exceptional} exceptional components, '
          f'largest has {largest} gates and {largest+1} lost literal reads')


def actual_bound(m, size):
    n = 2*m
    inputs = n*(n-1)
    k = m//2
    H = (21*k-18)*inputs - (10*k-8)*size - (16*k-14)
    gamma = Fraction(3*m*m-5*m-2, inputs)
    return 3*m*m + ceil(gamma*max(0, H)/(13*k-14))


def check_product_fibre(m):
    n = 2*m
    blocks = [(2, 1, 4), (3, 0, 5)] + [(i,) for i in range(6, n)]
    fixed = ({(a, 1) for a in range(0, n, 2)} | {(1, a) for a in range(0, n, 2)} |
             {(b, 0) for b in range(1, n, 2)} | {(0, b) for b in range(1, n, 2)})
    free = [(i, j) for i in range(len(blocks)) for j in range(len(blocks)) if i != j]
    wiring = [(blocks[i][-1], blocks[j][0]) for i, j in free]
    assert fixed.isdisjoint(wiring) and len(set(wiring)) == len(free)
    maximum = fixed | set(wiring)
    for u, v, w in blocks[:2]:
        assert [b for a, b in maximum if a == u] == [v]
        assert [a for a, b in maximum if b == w] == [v]
    for side, hub in ((0, 1), (1, 0)):
        assert all((i, hub) in fixed and (hub, j) in fixed
                   for i in range(side, n, 2) for j in range(side, n, 2))
    if len(free) <= 12:
        words = range(1 << len(free))
    else:
        words = [0, (1 << len(free))-1]
        for order in permutations(range(1, len(blocks))):
            cycle = (0, *order)
            mask = sum(1 << free.index(e) for e in zip(cycle, cycle[1:]+cycle[:1]))
            words.extend((mask, mask & (mask-1)))
    for word in words:
        small = [0]*len(blocks)
        rows = [0]*n
        for u, v in fixed:
            rows[u] |= 1 << v
        for pos, ((i, j), (u, v)) in enumerate(zip(free, wiring)):
            if word >> pos & 1:
                small[i] |= 1 << j
                rows[u] |= 1 << v
        assert tour_count(rows) == tour_count(small)
    print(f'{n} vertices: both Boolean products complete, {len(words):,} full-graph tour counts preserved')


def check_parity_fibre():
    m = 2
    width = m*m

    def matprod(y, x):
        return sum((sum(((y >> (i*m+j)) & (x >> (j*m+k)) & 1) for j in range(m)) % 2)
                   << (i*m+k) for i in range(m) for k in range(m))

    outcomes = []
    identity, swap = 9, 6
    for word in range(1 << (2*width)):
        y, x = word >> width, word & 15
        yes = (y & identity == identity and x & swap == swap) or (y & swap == swap and x & identity == identity)
        outcomes.append((matprod(y, x), yes))
    count = 0
    for pattern in product((0, 1, 2), repeat=2*width):
        if 2 not in pattern:
            continue
        base = sum(1 << j for j, value in enumerate(pattern) if value == 1)
        words = [base]
        for j, value in enumerate(pattern):
            if value == 2:
                words += [w | (1 << j) for w in words]
        if len({outcomes[w][0] for w in words}) == 1:
            assert all(not outcomes[w][1] for w in words)
            count += 1
    print(f'2+2: all ternary restrictions, {count} nontrivial constant-parity-product cubes, all negative')


def check_linear_cut(m):
    n = 2*m
    base = Circuit(n)
    output = held_karp(base, n)
    dag = Circuit(n)
    raw = {e: w for e, w in dag.inputs.items() if (e[0]^e[1]) & 1}
    chosen = [(2*i, 2*j+1) for i in range(m) for j in range(m) if i != j]
    target, *others = chosen
    rest = 0
    for edge in others:
        rest = xor_gate(dag, rest, raw[edge])
    form = xor_gate(dag, raw[target], rest)
    control = dag.gate('and', raw[1, 0], raw[3, 0])
    port = xor_gate(dag, form, control)
    raw[target] = xor_gate(dag, xor_gate(dag, port, control), rest)
    root = base.replay(dag, raw)[output]
    pairs = [(2*i, 2*i+1) for i in range(m)]
    small, image = dag.contract(pairs)
    live = live_gates(dag, root)
    paid, ports, remaining = cut_graph(dag, root, {port})
    g = len(live)-len(paid)
    hidden = {dag.inputs[e] for e in raw}-remaining
    assert ports == {port} and hidden == {dag.inputs[target]} and image[port] == 0
    assert len(live)-small.size(image[root]) >= m*m+m+g
    print(f'{m}+{m}: mixed parity port cuts {g} gates with one hidden bit, all {g} credited beyond pins')


def in_out(k):
    """Glynn, Haythorpe and Moeini, Section 3 (the paper labels from one)."""
    if k < 4:
        raise ValueError('this construction uses k >= 4')
    even = k % 2 == 0
    # Each listed undirected edge is represented by both directed arcs.
    edges = set()
    for i in range(1, (k-1)//2+1):
        for u in range(4*i-2, 4*i+1):
            edges.update(((u, u+1), (u+1, u)))
    for i in range(1, (k-3)//2+1):
        edges.update(((4*i-2, 4*i+5), (4*i+1, 4*i+2)))
    edges.add((1, 2))
    exits = [0]*k
    for j in range(1, (k-3)//2+1):
        exits[2*j-1], exits[2*j] = 4*j+3, 4*j-3
    if even:
        edges.update(((2*k-6, 2*k-1), (2*k-3, 2*k-2), (2*k-2, 1), (2*k-2, 5), (2*k-1, 2*k-2)))
        exits[0], exits[-3], exits[-2], exits[-1] = 3, 2*k-1, 2*k-7, 2*k-3
    else:
        edges.update(((2*k-4, 1), (2*k-2, 5)))
        exits[0], exits[-2], exits[-1] = 2*k-1, 3, 2*k-5
    incoming = tuple(2*j for j in range(k))
    outgoing = tuple(x-1 for x in exits)
    assert set(incoming) == set(outgoing) and all(i != j for i, j in zip(incoming, outgoing))
    return 2*k-1, {(u-1, v-1) for u, v in edges}, incoming, outgoing


def check_disjointness(k, l):
    n1, left, lin, lout = in_out(k)
    n2, right, rin, rout = in_out(l)
    n = n1+n2
    fixed = left | {(u+n1, v+n1) for u, v in right}
    variable = {}
    for i in range(k):
        for j in range(l):
            pos = l*i+j
            variable[lout[i], n1+rin[j]] = 2*pos
            variable[n1+rout[j], lin[i]] = 2*pos+1
    assert len(variable) == 2*k*l and fixed.isdisjoint(variable)
    assert all((u^v) & 1 for u,v in fixed | variable.keys())
    neighbours = [[] for _ in range(n)]
    for u,v in fixed | variable.keys():
        mark = 0 if (u,v) in fixed else 1 << variable[u,v]
        neighbours[u].append((v, mark))

    @lru_cache(None)
    def supports(u, remaining):
        if not remaining:
            return frozenset(mark for v, mark in neighbours[u] if v == 0)
        return frozenset(mark | suffix for v, mark in neighbours[u] if remaining >> v & 1
                         for suffix in supports(v, remaining ^ (1 << v)))

    observed = supports(0, (1 << n)-2)
    assert observed == {3 << (2*i) for i in range(k*l)}
    print(f'{k}+{l} in-out ports: {n} vertices, all Hamiltonian supports give the '
          f'{k*l} paired terms on {2*k*l} independent arc switches')


def check_separated_cuts():
    # Conditioning on one participating forward cell leaves a uniform choice
    # of the opposite tail and head, each avoiding just its own endpoint.
    m = 7
    backward = {(i, i) for i in range(m)}
    hidden = {(i, j) for i in range(m) for j in range(m) if (3*i+2*j) % 5 != 0}
    both = sum(sum(v != i and u != j for u, v in backward) for i, j in hidden)
    density = Fraction(16, m*m)
    expected = density*(len(hidden)+len(backward)-2*Fraction(both, (m-1)**2))
    eta = density*(1-Fraction(2*m, (m-1)**2))
    assert expected >= eta*(len(hidden)+len(backward))
    # Exactly count the images of the four distinct same-side port labels.
    # Each ordered pair of different endpoints has the same number of full
    # permutation completions on its side.
    endpoints = list(permutations(range(m), 2))
    separated = sum(((a, b) in hidden) != ((b2, a2) in backward)
                    for a, a2 in endpoints for b, b2 in endpoints)
    assert Fraction(16*separated, len(endpoints)**2) == expected


def check_opposite_readers(m):
    source = Circuit(2*m)
    full = held_karp(source, 2*m)
    dag = Circuit(2*m)
    active = {e: w for e, w in dag.inputs.items() if (e[0]^e[1]) & 1}
    forward = {e for e in active if e[0] % 2 == 0}
    # A zero backward row precludes every alternating tour, for every Y.
    guard = dag.neg(dag.fold('or', (active[1, 2*i] for i in range(m))))
    guarded = active | {e: dag.gate('or', active[e], guard) for e in forward}
    out = source.replay(dag, guarded)[full]
    live = set(live_gates(dag, out))
    keep, ports, raw = cut_graph(dag, out, {guard})
    assert raw == set(active.values()) and ports == {guard}
    assert all(guarded[e] in keep for e in forward)
    removed = len(live)-len(keep)
    minimum_extra = removed+len(forward)
    for order in permutations(range(m)):
        pairs = tuple((2*i+1, 2*j) for i, j in enumerate(order))
        small, image = dag.contract(pairs)
        assert image[guard] == 0
        assert len(live)-small.size(image[out]) >= m*m+m+minimum_extra
    print(f'{m}+{m}: {len(forward)} distinct single readers, {removed} opposite-matrix gates, '
          f'at least {minimum_extra} extra deletions on every reverse matching')


def check_full_cross_pivots(m):
    n = 2*m
    # By independent relabelling it suffices to audit the pivot A_0 -> B_0.
    # Open that pivot as A_0's sole outgoing edge, and list all tours using it.
    spans = 1 << (m*m)
    possible = bytearray(spans)
    for tail in permutations(range(2, n)):
        path = (0, 1)+tail+(0,)
        mask = sum(1 << ((u//2)*m+v//2) for u,v in zip(path, path[1:])
                   if u % 2 and not v % 2)
        possible[mask] = 1
    for j in range(m*m):
        bit = 1 << j
        for base in range(0, spans, 2*bit):
            for mask in range(base, base+bit):
                possible[mask+bit] |= possible[mask]
    first_row = (1 << m)-1
    first_col = sum(1 << (i*m) for i in range(m))
    for mask, observed in enumerate(possible):
        assert bool(observed) == bool(mask & ~first_row and mask & ~first_col)
    print(f'{m}+{m}: all {spans:,} reverse matrices audited for the full-graph pivot criterion')


def check_mixed_guard():
    # The two presentations of f are equal. Matching propagation reaches their
    # conjunction with opposite signs, although the unrestricted guard uses data.
    m = 4
    dag = Circuit(2*m)
    def pos(i, j):
        return dag.inputs[2*i, 2*j+1]

    def neg(i, j):
        return dag.inputs[2*i+1, 2*j]

    variables = [pos(i,j) for i,j in ((1,0), (2,0), (1,2), (3,1))]
    a,b,c,d = variables
    f = dag.gate('and', dag.gate('or', a,b), dag.gate('or', c,d))
    distributed = dag.fold('or', (dag.gate('and', x,y) for x in (a,b) for y in (c,d)))
    different_col = dag.fold('or', (neg(i,j) for i in range(m) for j in range(1,m)))
    with_return = dag.gate('or', different_col, neg(0,0))
    guard = dag.gate('and', dag.gate('or', dag.neg(different_col), f),
                     dag.gate('or', dag.neg(with_return), dag.neg(distributed)))
    pairs = [(2*i+1, 2*i) for i in range(m)]
    small, image = dag.contract(pairs)
    out = image[guard]
    win, wr = rewrite_windows(small, out)
    aff, ar = affine_rebuild(win, wr)
    sizes = (small.size(out), win.size(wr), aff.size(ar))
    assert min(sizes) > 0
    source = Circuit(2*m)
    full = held_karp(source, 2*m)
    pivot = (0,3)
    guarded = source.replay(dag, dag.inputs | {pivot: dag.gate('or', pos(0,1), guard)})[full]
    assert dag.size(guarded) > source.size(full)
    base, plain_image = source.contract(pairs)
    control, control_output = rewrite_windows(base, plain_image[full])
    control_aff, control_ar = affine_rebuild(control, control_output)
    reference = min(base.size(plain_image[full]), control.size(control_output), control_aff.size(control_ar))
    smaller, guarded_image = dag.contract(pairs)
    root = guarded_image[guarded]
    windows, windows_root = rewrite_windows(smaller, root)
    affine, affine_root = affine_rebuild(windows, windows_root)
    full_sizes = (smaller.size(root), windows.size(windows_root), affine.size(affine_root))
    assert min(full_sizes) > reference
    for mask in range(1 << len(small.edges)):
        rows = [0]*m
        for index, (u,v) in enumerate(small.edges):
            if mask >> index & 1:
                rows[u] |= 1 << v
        assert small.values(rows)[out] == win.values(rows)[wr] == aff.values(rows)[ar] == 0
        expected = base.values(rows)[plain_image[full]]
        assert smaller.values(rows)[root] == windows.values(rows)[windows_root] == affine.values(rows)[affine_root] == expected
    print(f'4+4: mixed source {dag.size(guarded)} versus plain source {source.size(full)}; '
          f'guard always neutral on all 4,096 small graphs, '
          f'R0/window/affine keep {sizes} gates at its output, '
          f'{full_sizes} at the Hamiltonicity output versus {reference} with the raw input')
    def remaining(circuit, root, pairing):
        small, image = circuit.contract(pairing)
        win, wr = rewrite_windows(small, image[root])
        aff, ar = affine_rebuild(win, wr)
        return min(small.size(image[root]), win.size(wr), aff.size(ar))

    margins = Counter()
    orientation = Counter()
    for pairing in pairings(m):
        cost = remaining(dag, guarded, pairing)
        extra = cost-remaining(source, full, pairing)
        margins[extra] += 1
        if all(u % 2 for u,v in pairing):
            orientation[extra] += 1
            returns = {dag.inputs[v,u] for u,v in pairing}
            data_free = returns.isdisjoint(set(variables) | {dag.inputs[pivot]})
            assert extra == (11 if data_free else 0)
    assert sum(margins.values()) == 1680 and sum(orientation.values()) == 24
    print(f'4+4: extra surviving gates on all ordered pairings {sorted(margins.items())}; '
          f'on reverse matchings of this split {sorted(orientation.items())}')


def check_monotone_shared_guard(m):
    n = 2*m
    dag = Circuit(n)
    tour = {(i, (i+1) % n) for i in range(n)}
    owners = set(dag.edges)-tour
    guard = dag.fold('and', (dag.inputs[e] for e in sorted(tour)))
    source = Circuit(n)
    full = held_karp(source, n)
    guarded = dag.inputs | {e: dag.gate('or', dag.inputs[e], guard) for e in owners}
    root = source.replay(dag, guarded)[full]
    profile = audited_profile(dag, root)
    hits = trials = 0
    for pairs in pairings(m):
        target, image = dag.contract(pairs)
        trials += 1
        if not owners.intersection(pairs):
            continue
        hits += 1
        assert image[guard] == 0
        fixed = [e for e in dag.edges if image[dag.inputs[e]] < 2]
        credit = len(owners)-1
        assert len(profile.gates)-target.size(image[root]) >= len(fixed)+sum(profile.fees[e] for e in fixed)+credit
    d = len(owners)
    bound = Fraction(d*(n-3), (n-1)*(2*(n-3)+d-1))
    assert Fraction(hits, trials) >= bound and trials-hits == 2
    print(f'{n} vertices: one monotone guard with {d} distinct single readers, '
          f'{hits}/{trials} pairings certify its {d-1} extra uses')


def check_bipartite_or(k, extra_pairs=0):
    m = 3*k+extra_pairs
    pools = [list(range(2*k+side, 2*m, 2)) for side in (0, 1)]
    regular = []
    for direction in (0, 1):
        for _ in range(k-1):
            regular.append([pools[direction].pop(), pools[1-direction].pop()])
    reversible = [pools[i % 2].pop() for i in range(4)]
    for _ in range(extra_pairs):
        regular[0].extend([pools[0].pop(), pools[1].pop()])
    assert not any(pools)
    rows = [0]*(2*m)
    def attach(path):
        for u,v in zip(path, path[1:]):
            rows[u] |= 1 << v
        for u in range(2*k):
            if (u ^ path[0]) & 1:
                rows[u] |= 1 << path[0]
            if (u ^ path[-1]) & 1:
                rows[path[-1]] |= 1 << u
    for path in regular:
        attach(path)
    attach(reversible)
    attach(reversible[::-1])
    assert tour_count(rows) == 0
    for u in range(2*k):
        for v in range(1-u%2, 2*k, 2):
            rows[u] |= 1 << v
            assert tour_count(rows) > 0
            rows[u] ^= 1 << v
    print(f'{m}+{m}: one background reads the OR of any subset of {2*k*k} internal cross arcs')


if __name__ == '__main__':
    for order in (3, 4, 5, 6, 7, 8):
        check_ordered_probes(order)
    for order in (3, 4, 5, 6):
        check_flexible_marking(order)
    for size in (3, 4, 5, 6):
        fixed = tuple((2*i, 2*i+1) for i in range(size))
        print(f'Held-Karp second stage {2*size}: {matching_ledger(size, fixed)}')
    check_stage_components(3)
    for size in (3, 4, 5):
        check_alternating_components(size)
        check_product_fibre(size)
    check_parity_fibre()
    check_linear_cut(4)
    for ports in ((4,4), (4,5), (5,5), (4,6), (6,6)):
        check_disjointness(*ports)
    check_separated_cuts()
    check_semantic_constant(4)
    check_opposite_readers(4)
    for size in (2, 3, 4):
        check_full_cross_pivots(size)
    check_mixed_guard()
    check_monotone_shared_guard(3)
    for width, padding in ((2,0), (2,1), (3,0), (3,1), (4,0)):
        check_bipartite_or(width, padding)
    for size in range(16, 123):
        inputs = 2*size*(2*size-1)
        baseline = 3*size*size+size-2
        covered = 14*(actual_bound(size, 2*inputs)-baseline) >= 3*inputs//2-baseline
        assert covered == (size >= 92)
    for size in (92, 123, 242, 1024):
        n = 2*size
        s = 2*n*(n-1)
        target = (3*s+3)//4
        baseline = 3*size*size+size-2
        certified = actual_bound(size, s)
        assert 14*(certified-baseline) >= target-baseline
        print(f'm={size}, s=2N: certified {certified:,}, quarter target {target:,}, gap {target-certified:,}')
