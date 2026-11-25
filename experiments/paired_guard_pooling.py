"""Audit the OR normal form of a mixed Hamiltonicity guard and the cost of short restrictions."""
from collections import Counter
from fractions import Fraction
from itertools import combinations, permutations, product

from absorbing_readers import ReaderProfile
from alternating_cut import cut_graph
from boolean_sweep import affine_rebuild, live_gates, rewrite_windows, xor_gate
from cycle_cover_queries import tour_count
from matched_matrix_budget import actual_bound
from paired_contraction import Circuit, allowed, held_karp, pairings


def shared_guard(m, canonical, owners=2):
    """Two observable mixed signals, both invariant under pooling the rectangle."""
    dag = Circuit(2*m)
    q = [(2*i+1, 2*j) for i in range(1,m) for j in range(1,m)]
    tagged = [(0,1), (0,3)]
    # The second guard requires absence outside column 0 when it fires.
    # Add the remainder of that column-complement to the protected rectangle.
    other = [(1, 2*j) for j in range(1,m)]
    z, w = dag.inputs[2,1], dag.inputs[4,1]
    pooled = dag.fold('or', (dag.inputs[e] for e in q))
    if canonical:
        present = pooled
    else:
        # A data-dependent parity representation of the same disjunction.
        mixed = [xor_gate(dag, dag.inputs[e], z) for e in q]
        when_zero = dag.gate('and', dag.neg(z), dag.fold('or', mixed))
        when_one = dag.gate('and', z, dag.neg(dag.fold('and', mixed)))
        present = dag.gate('or', when_zero, when_one)
    absent = dag.neg(dag.fold('or', [present, *(dag.inputs[e] for e in other)]))
    guards = [dag.gate('and', absent, z), dag.gate('and', absent, w)]
    proxies = {e: dag.gate('or', dag.inputs[e], b) for e,b in zip(tagged[:owners], guards)}
    base = Circuit(2*m)
    root = held_karp(base, 2*m)
    output = base.replay(dag, dag.inputs | proxies)[root]
    return dag, output, set(q), pooled, set(guards)


def cut_fee(dag, root, group, pool, pairs, profile):
    matching, free = allowed(pairs)
    fixed = set(dag.inputs)-free
    fee = sum(profile.fees[e] for e in fixed)
    target, image = dag.contract(pairs)
    actual = len(profile.gates)-target.size(image[root])
    assert actual >= len(fixed)+fee
    if not matching.intersection(group):
        return False, 0, actual
    assert image[pool] == 1
    retained, ports, raw = cut_graph(dag, root, {pool})
    assert ports == {pool} and raw == set(dag.inputs.values())
    assert len(profile.gates)-len(retained) == len(group)-1
    loose = len(group & free)
    assert actual >= len(fixed)+fee+loose
    return True, loose, actual


def joint_charge(m, owners):
    dag, root, group, pool, _ = shared_guard(m, True, owners)
    profile = ReaderProfile(dag, root)
    assert all(profile.fees[e] >= 1 for e in group)
    pool_gates = set(live_gates(dag, pool))
    assert len(pool_gates) == len(group)-1
    samples = triggers = loose_sum = 0
    status = Counter()
    totals = Counter()
    for pairs in pairings(m):
        trigger, loose, actual = cut_fee(dag, root, group, pool, pairs, profile)
        matching, free = allowed(pairs)
        fixed = set(dag.inputs)-free
        left, right = zip(*pairs)
        rectangle = set(product(left, right))
        selected = {e for e,g in profile.head.items()
                    if (e in matching and dag.nodes[g][0] == 'or') or
                    (e in rectangle-matching and dag.nodes[g][0] == 'and')}
        stops = {profile.head[e] for e in selected}
        active, leaves = profile.reachable_after_cut(stops)
        assert leaves == stops | {w for e,w in dag.inputs.items() if e not in selected}
        dead = profile.gates-active-stops
        removed = pool_gates <= dead
        assert removed or pool_gates <= active
        fee = sum(profile.fees[e] for e in fixed)
        lost = sum(e in fixed and g in dead for e,g in profile.repeated_tickets)
        base = len(fixed)+fee+len(stops)+len(dead)-lost
        bonus = loose if trigger and not removed else 0
        assert actual >= base+bonus
        if trigger and removed:
            tree_lost = sum(e in fixed and g in pool_gates for e,g in profile.repeated_tickets)
            assert len(pool_gates)-tree_lost == loose-1
        status[trigger, removed] += 1
        triggers += trigger
        loose_sum += loose
        samples += 1
        totals['free'] += len(group & free)
    assert totals['free']*2*(2*m-1) == samples*len(group)*(m-1)
    if owners == 1:
        assert status[True,True] > 0
    print(f'{2*m} vertices, {owners} owner(s), {len(group)} pooled cells: {samples} pairings, '
          f'{triggers} hits, mean free credit {Fraction(loose_sum,samples)}, '
          f'(hit, pruned before projection) counts {sorted(status.items())}')
    return triggers, samples


def check_guard_semantics(m):
    original, out, group, _, ports = shared_guard(m, False)
    new, new_out, _, _, new_ports = shared_guard(m, True)
    def port_vectors(dag, signals, rows):
        values = dag.values(rows)
        return tuple(values[w] for w in sorted(signals))
    q = sorted(group)
    extras = [(1,2*j) for j in range(1,m)] + [(2,1), (4,1)]
    tests = 0
    for data in range(1 << (len(q)+len(extras))):
        rows = [0]*(2*m)
        for i,(a,b) in enumerate(q+extras):
            if data >> i & 1:
                rows[a] |= 1 << b
        compressed = list(rows)
        for a,b in q:
            compressed[a] &= ~(1 << b)
        if data & ((1 << len(q))-1):
            a,b = q[0]
            compressed[a] |= 1 << b
        v = port_vectors(original, ports, rows)
        assert v == port_vectors(original, ports, compressed) == port_vectors(new, new_ports, rows)
        tests += 1
    assert new.size(new_out) <= original.size(out)
    print(f'{2*m} vertices: {tests} exhaustive vector cofactors, two shared boundary outputs; '
          f'sizes {original.size(out)} and {new.size(new_out)}')


def protected_blocks(n, assignments):
    adj = [set() for _ in range(n)]
    for a,b in assignments:
        adj[a].add(b)
        adj[b].add(a)
    spare = [v for v in range(n) if not adj[v]]
    touched = set(range(n))-set(spare)
    blocks = []
    while touched:
        part = {touched.pop()}
        stack = list(part)
        while stack:
            fresh = adj[stack.pop()] & touched
            touched.difference_update(fresh)
            part.update(fresh)
            stack.extend(fresh)
        order = min(permutations(sorted(part)),
                    key=lambda xs: sum(assignments.get(e, 1) == 0 for e in zip(xs,xs[1:])))
        path = [order[0]]
        for a,b in zip(order,order[1:]):
            if assignments.get((a,b),1) == 0:
                path.append(spare.pop())
            path.append(b)
        blocks.append(path)
    return blocks+[[v] for v in spare]


def check_pin_projection(n, limit):
    arcs = list(permutations(range(n),2))
    cases = queries = 0
    for k in range(1,limit+1):
        for chosen in combinations(arcs,k):
            for bits in product((0,1),repeat=k):
                pins = dict(zip(chosen,bits))
                blocks = protected_blocks(n,pins)
                small_n = len(blocks)
                assert small_n >= n-k
                base = [0]*n
                for (u,v), value in pins.items():
                    base[u] |= value << v
                for block in blocks:
                    for u,v in zip(block,block[1:]):
                        base[u] |= 1 << v
                # All small graphs when possible, otherwise spanning tours
                # with one arc removed, the empty graph, and the complete graph.
                cells = list(permutations(range(small_n),2))
                tour = sum(1 << cells.index((i,(i+1)%small_n)) for i in range(small_n))
                masks = range(1 << len(cells)) if small_n <= 3 else [
                    0,tour,tour & (tour-1),(1 << len(cells))-1]
                for mask in masks:
                    rows = list(base)
                    small = [0]*small_n
                    for i,(a,b) in enumerate(cells):
                        if mask >> i & 1:
                            small[a] |= 1 << b
                            rows[blocks[a][-1]] |= 1 << blocks[b][0]
                    assert all((rows[u] >> v) & 1 == value for (u,v),value in pins.items())
                    assert bool(tour_count(rows)) == bool(tour_count(small))
                    queries += 1
                cases += 1
    print(f'{n} vertices: {cases} signed restrictions, {queries} embedded decisions')


def example_bounds(m):
    n = 2*m
    inputs = n*(n-1)
    s = 2*inputs
    q = (m-1)**2
    fixed = 3*m*m-m
    hit = Fraction(q*(n-3), (n-1)*(2*(n-3)+q-1))
    bonus = max(0, Fraction(q*(m-1), 2*(n-1))-q*(1-hit)-1)
    base = actual_bound(m,s)
    print(f'm={m}: fixed-orientation certificate {fixed+q:,}, '
          f'quarter gap {(3*s+3)//4-fixed-q:,}; '
          f'uniform additional free receipts >= {int(bonus):,}, '
          f'baseline integer bound {base:,}')


def is_matching(arcs):
    return len({a for a,b in arcs}) == len(arcs) == len({b for a,b in arcs})


def pins_all_reverse(m, extra):
    forward = {(a//2,b//2) for a,b in extra if a % 2 == 0 and b % 2}
    if is_matching(forward):
        return True
    for a,b in product(range(m),repeat=2):
        if any(v == 2*a and u % 2 == 0 or u == 2*b+1 and v % 2
               for u,v in extra):
            continue
        remaining = {(i,j) for i,j in forward if i != a and j != b}
        if is_matching(remaining):
            return True
    return False


def check_pair_criterion(m):
    n = 2*m
    reverse = {(u,v) for u in range(1,n,2) for v in range(0,n,2)}
    extras = sorted(set(permutations(range(n),2))-reverse)
    fixed_sets = [set(extras)-free for pairs in pairings(m)
                  for _,free in [allowed(pairs)] if reverse.isdisjoint(free)]
    inverse = {edge: sum(1 << j for j,fixed in enumerate(fixed_sets) if edge in fixed)
               for edge in extras}
    tested = 0
    forward = [e for e in extras if e[0] % 2 == 0 and e[1] % 2 == 1]
    for pool,limit in ((extras,3),(forward,5)):
        for k in range(1,limit+1):
            for chosen in combinations(pool,k):
                matches = (1 << len(fixed_sets))-1
                for e in chosen:
                    matches &= inverse[e]
                assert matches and pins_all_reverse(m,chosen)
                tested += 1
    mixed_bad = {(0,1),(0,3),(0,5),(2,0)}
    assert not pins_all_reverse(m,mixed_bad) and not any(mixed_bad <= f for f in fixed_sets)
    if m >= 3:
        forward_bad = {(2*i,2*j+1) for i in range(2) for j in range(3)}
        assert not pins_all_reverse(m,forward_bad) and not any(forward_bad <= f for f in fixed_sets)
    print(f'{n} vertices: {tested} support tests against all {len(fixed_sets)} '
          f'pairings pinning every reverse arc; four- and six-arc obstructions verified')


def check_index(m):
    n = 2*m
    forward = {(2*i,2*j+1) for i,j in ((0,0),(0,1),(0,2),(1,1),(2,2))}
    blocked = forward | {(0,2),(1,3)}
    tests = 0
    for u,v in product(range(1,n,2),range(0,n,2)):
        back = next((a,b) for a in range(0,n,2) for b in range(1,n,2)
                    if a != v and b != u and (a,b) not in blocked)
        paths = []
        for start,end in ((v,back[0]), (back[1],u)):
            interior = sorted(set(range(start%2,n,2))-{start,end})
            path = next(p for mid in permutations(interior) for p in [(start,*mid,end)]
                        if all(e not in blocked for e in zip(p,p[1:])))
            paths.extend(zip(path,path[1:]))
        for maximum, bit in product((False,True),repeat=2):
            rows = [0]*n
            for a,b in [*paths,back]:
                rows[a] |= 1 << b
            if maximum:
                for a,b in product(range(1,n,2),range(0,n,2)):
                    rows[a] |= 1 << b
            rows[u] = (rows[u] & ~(1 << v)) | (int(bit) << v)
            assert all(not (rows[a] >> b & 1) for a,b in blocked)
            assert bool(tour_count(rows)) == bit
            tests += 1
    print(f'{n} vertices: {tests} matrix INDEX endpoint checks with all seven nuisance bits zero')


def check_shared_cut(m):
    n = 2*m
    original = Circuit(n)
    full = held_karp(original,n)
    dag = Circuit(n)
    rectangle = {(u,v) for u in range(1,n,2) for v in range(0,n,2)}
    extra = {(0,1),(0,3),(0,5),(2,3),(4,5)}
    common = dag.fold('or', (dag.inputs[e] for e in sorted(extra)))
    encoded = {e: xor_gate(dag, dag.inputs[e], common) for e in sorted(rectangle)}
    decoded = {e: xor_gate(dag, w, common) for e,w in encoded.items()}
    output = original.replay(dag, dag.inputs | decoded)[full]
    live = set(live_gates(dag,output))
    active, ports, raw = cut_graph(dag,output,set(encoded.values()))
    hidden = {e for e,w in dag.inputs.items() if w not in raw}
    assert hidden == rectangle and len(ports) == len(hidden)
    removed = len(live)-len(active)
    checks = 0
    for pairs in pairings(m):
        _,free = allowed(pairs)
        if free.intersection(rectangle | extra):
            continue
        small, image = dag.contract(pairs)
        assert all(image[w] < 2 for w in ports)
        assert len(live)-small.size(image[output]) >= len(dag.inputs)-len(free)+removed
        checks += 1
    assert checks
    print(f'{n} vertices: {checks} paired cuts expose {len(ports)} shared XOR outputs '
          f'holding {len(hidden)} hidden matrix bits; all {removed} cut gates clear the raw baseline')


def check_star_pivots(m):
    star = [(0,2*j+1) for j in range(m-1)]
    last = 2*m-1
    tested = 0
    for bits in range(1 << len(star)):
        open_y = [e for j,e in enumerate(star) if bits >> j & 1]
        for head in range(2,2*m,2):
            ret = open_y[0] if open_y else (next(v for v in range(2,2*m,2) if v != head),1)
            arcs = open_y or [ret]
            a,b = ret
            path_a = [head,*(v for v in range(0,2*m,2) if v not in (head,a)),a]
            path_b = [b,*(v for v in range(1,2*m,2) if v not in (b,last)),last]
            for dense,bit in product((False,True),repeat=2):
                rows = [0]*(2*m)
                for u,v in [*arcs,*zip(path_a,path_a[1:]),*zip(path_b,path_b[1:])]:
                    rows[u] |= 1 << v
                if dense:
                    for u,v in product(range(1,2*m,2),range(0,2*m,2)):
                        rows[u] |= 1 << v
                rows[last] = (rows[last] & ~(1 << head)) | (int(bit) << head)
                assert bool(tour_count(rows)) == bit
                tested += 1
    print(f'{2*m} vertices: {tested} endpoint checks with every value of the forward star')


def check_six_bit_hazard(m):
    n = 2*m
    dag = Circuit(n)
    extra = {(2*i,2*j+1) for i in (1,2) for j in range(3)}
    reverse = {(2*i+1,2*j) for i,j in product(range(m),repeat=2)}
    far = dag.fold('or', (dag.inputs[e] for e in sorted(reverse) if e[1] != 0))
    wider = dag.gate('or',far,dag.inputs[1,0])
    parity = 0
    for e in sorted(extra):
        parity = xor_gate(dag,parity,dag.inputs[e])
    guard = dag.gate('and',dag.gate('or',dag.neg(far),parity),
                     dag.gate('or',dag.neg(wider),dag.neg(parity)))
    cases = visible = 0
    remaining = Counter()
    for pairs in pairings(m):
        _,free = allowed(pairs)
        if not reverse.isdisjoint(free):
            continue
        small, image = dag.contract(pairs)
        assert image[far] == 1 and len(extra & free) > 0 and image[guard] >= 2
        win, wr = rewrite_windows(small,image[guard])
        aff, ar = affine_rebuild(win,wr)
        assert ar == 0
        visible += wr == 0
        remaining[len(extra & free)] += 1
        cases += 1
    print(f'{n} vertices: six-bit guard hidden from R0 in {cases}/{cases} pin-all-X pairings, '
          f'window resolves {visible}, affine resolves {cases}; remaining variables {sorted(remaining.items())}')


def batch_affine_records(families,cap):
    records = []
    total = 0
    for description in families:
        if description is None:
            continue
        start = total
        total += 1 << len(description[1])
        if total > cap:
            return None
        records.append((start,0,description))
    records.extend((index,1,None) for index in range(cap))
    output = []
    for index,kind,description in sorted(records):
        if kind == 0:
            start = index
            origin,basis = description
        elif index < total:
            value = origin
            for j,vector in enumerate(basis):
                if (index-start) >> j & 1:
                    value ^= vector
            output.append(value)
    output.sort()
    return tuple(v for i,v in enumerate(output) if i == 0 or output[i-1] != v)


def check_batches():
    descriptions = (None,(2,()),(1,(2,)),(0,(1,2)),(3,(2,4)))
    cases = 0
    for families in product(descriptions,repeat=4):
        emitted = []
        for description in families:
            if description is not None:
                start,basis = description
                solutions = [start]
                for row in basis:
                    solutions += [x ^ row for x in solutions]
                emitted.extend(solutions)
        for cap in (0,3,8,16):
            expected = None if len(emitted)>cap else tuple(sorted(set(emitted)))
            assert batch_affine_records(families,cap) == expected
            cases += 1
    print(f'{cases} sorted batches agree on affine solutions, multiplicity cutoff and deduplication')


if __name__ == '__main__':
    check_guard_semantics(3)
    for order, owners in ((3,1),(3,2),(4,1),(4,2)):
        joint_charge(order,owners)
    check_pin_projection(5,2)
    for order in (3,4):
        check_pair_criterion(order)
    for order in (4,5,6):
        check_index(order)
    check_shared_cut(4)
    check_star_pivots(5)
    check_six_bit_hazard(4)
    check_batches()
    example_bounds(1024)
