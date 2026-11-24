"""Trace negative-distinguishing signals and the gate-loss budget on one pairing at a time."""
from collections import Counter, defaultdict
from fractions import Fraction
from itertools import permutations
from math import ceil

from joint_pair_support import small_negative_words
from oriented_contraction import de_morgan_circuit, zero_pin_values
from pair_certificate import all_inputs, tables
from paired_contraction import Circuit, held_karp, pairings
from paired_fanout import live_wires
from staged_contraction import protect_inputs


def control(dag):
    """Finite reference circuit. Enumerating covers is sufficient for the four-vertex audit."""
    vs = range(dag.order)
    reach = [[1 if u == v else dag.inputs[u, v] for v in vs] for u in vs]
    for k in vs:
        reach = [[dag.gate('or', reach[u][v], dag.gate('and', reach[u][k], reach[k][v]))
                  for v in vs] for u in vs]
    cover = dag.fold('or', (dag.fold('and', (dag.inputs[u, v] for u, v in enumerate(perm)))
                            for perm in permutations(vs) if all(u != v for u, v in enumerate(perm))))
    return dag.gate('and', cover, dag.fold('and', (w for row in reach for w in row)))


def check_monitors(dag, out):
    ones, columns = all_inputs(dag)
    q = control(dag)
    truth = tables(dag, ones, columns)
    disagreement = truth[q] ^ truth[out]
    assert disagreement == sum(1 << w for w in small_negative_words(dag.order))
    gates, uses = live_wires(dag, out)
    pin = {g: int(bool(truth[g] & disagreement)) for g in gates
           if truth[g] & disagreement in (0, disagreement)}
    assert pin[out] == 0
    replay = {w: w for w in dag.inputs.values()}
    folded = absorbing = paid_nots = dependent = 0
    for g in sorted(gates):
        op, *args = dag.nodes[g]
        supplied = [pin.get(a, replay[a]) for a in args]
        dependent += g in pin and any(a in pin for a in args)
        folded += any(w < 2 for w in supplied)
        if op == 'not':
            paid_nots += supplied[0] < 2
            replay[g] = dag.neg(supplied[0])
        else:
            replay[g] = dag.gate(op, *supplied)
            absorbing += sum(w < 2 for w in supplied) == 1 and replay[g] < 2
        if replay[g] < 2:
            assert replay[g] == pin[g]
    constant_monitors = sum(replay[g] < 2 for g in pin)
    slots = sum(uses[g] for g in pin)
    assert folded == slots-constant_monitors+absorbing+paid_nots
    high = dag.fold('or', (replay[g] for g in pin if pin[g] == 0))
    low = dag.fold('and', (replay[g] for g in pin if pin[g] == 1))
    mismatch = dag.gate('or', high, dag.neg(low))
    repaired = dag.gate('and', q, mismatch)
    true_high = dag.fold('or', (g for g in pin if pin[g] == 0))
    true_low = dag.fold('and', (g for g in pin if pin[g] == 1))
    true_mismatch = dag.gate('or', true_high, dag.neg(true_low))
    truth = tables(dag, ones, columns)
    assert truth[mismatch] == truth[true_mismatch] and truth[repaired] == truth[out]
    surplus = slots-(len(pin)-1)
    assert dag.size(repaired) <= len(gates)-surplus-absorbing-paid_nots+dag.size(q)+2
    print(f'global replay: {len(gates)} gates, {len(pin)} monitored, {dependent} monitored '
          'gates directly use another; all 4096 truth values agree')
    return dependent


def path_columns(dag):
    """Every bidirected spanning path at even order is a strongly connected cover negative."""
    columns = {e: 0 for e in dag.edges}
    bit = 1
    for order in permutations(range(dag.order)):
        if order[0] > order[-1]:
            continue
        for u, v in zip(order, order[1:]):
            columns[u, v] |= bit
            columns[v, u] |= bit
        bit <<= 1
    return bit-1, [columns[e] for e in dag.edges]


def weights_and_triggers(dag, out, varies):
    gates, uses = live_wires(dag, out)
    raw = {w: uses[w]-1 for w in dag.inputs.values()}
    weight = {}
    for g in gates:
        op, *args = dag.nodes[g]
        if op == 'not' and args[0] in raw:
            raw[args[0]] += uses[g]
        else:
            weight[g] = max(0, uses[g]-1)+int(op == 'not')
    assert sum(raw.values())+sum(weight.values()) == len(gates)-len(raw)+1
    zero, one = zero_pin_values(dag)
    outgoing = defaultdict(list)
    for h in gates:
        op, *args = dag.nodes[h]
        for i, g in enumerate(args):
            if g not in weight or not varies[g] or uses[g] <= 1:
                continue
            pins = zero[g] | one[g]
            if op != 'not':
                sibling = args[1-i]
                pins |= zero[sibling] if op == 'and' else one[sibling]
            outgoing[g].append(pins)
    tokens = []
    for g, choices in outgoing.items():
        assert len(choices) == uses[g]
        # Reserve the weakest use, one per source, for the wire-count identity.
        choices.sort(key=int.bit_count)
        tokens.extend(choices[1:])
    for g in weight:
        if dag.nodes[g][0] == 'not' and varies[g]:
            tokens.append(zero[g] | one[g])
    return raw, weight, Counter(tokens)


def trace_pair(dag, out, small, image, raw, weight, tokens, varies):
    m = small.order
    gates, _ = live_wires(dag, out)
    fixed = 3*m*m-m
    literal = sum(w for g, w in raw.items() if image[g] < 2)
    negative = sum(w for g, w in weight.items() if varies[g] and image[g] < 2)
    other = sum(w for g, w in weight.items() if not varies[g] and image[g] < 2)
    absorbing = 0
    for g in gates:
        if len(dag.nodes[g]) == 3 and image[g] < 2:
            _, a, b = dag.nodes[g]
            absorbing += (image[a] < 2) != (image[b] < 2)
    surviving = small.size(image[out])
    merge_loss = len(gates)-surviving-fixed-literal-negative-other-absorbing
    assert merge_loss >= 0
    zeroes = sum(1 << i for i, e in enumerate(dag.edges) if image[dag.inputs[e]] == 0)
    triggered = sum(count for pins, count in tokens.items() if pins & zeroes)
    assert triggered <= negative+absorbing
    return (fixed, literal, negative, other, absorbing, merge_loss, surviving, triggered)


def check_paired_negatives():
    n = 8
    base = Circuit(n)
    source, out = de_morgan_circuit(base, held_karp(base, n))
    guarded, _, embedded = protect_inputs(source)
    wrapped = embedded[out]
    ones, columns = path_columns(source)
    paths = tables(source, ones, columns)
    hidden_paths = tables(guarded, ones, columns)
    gates, uses = live_wires(source, out)
    shared = sorted(g for g in gates if uses[g] > 1 and source.nodes[g][0] != 'not')
    assert all(0 < paths[g] < ones and paths[g] == hidden_paths[embedded[g]] for g in shared)
    print(f'{len(shared)} shared internal signals distinguish bidirected path negatives, '
          f'carrying {sum(uses[g]-1 for g in shared)} extra uses')
    small_source = Circuit(n//2)
    words = small_negative_words(n//2)
    cols = [sum(((w >> i) & 1) << j for j, w in enumerate(words)) for i in range(len(small_source.edges))]
    all_words = (1 << len(words))-1
    assert len(words) == 144

    data = []
    for dag, root, vals in ((source, out, paths), (guarded, wrapped, hidden_paths)):
        varies = [0 < v < ones for v in vals]
        raw, weight, tokens = weights_and_triggers(dag, root, varies)
        w1 = sum(count for pins, count in tokens.items() if pins.bit_count() == 1)
        w2 = sum(count for pins, count in tokens.items() if pins.bit_count() >= 2)
        mean_bound = 44+Fraction(11, 14)*sum(raw.values())+Fraction(5, 7)*w1+Fraction(5, 6)*w2
        print(f'{dag.size(root)} gates: F={sum(raw.values())}, single/double triggers={w1}/{w2}, '
              f'common-pair expectation certifies >= {ceil(mean_bound)} deletions')
        data.append((dag, root, raw, weight, tokens, varies))
    traces = [[], []]
    kill_counts, kill_weights, still_vary = [], [], []
    public = tuple((2*i, 2*i+1) for i in range(n//2))
    for pairs in pairings(n//2):
        signatures = []
        for i, (dag, root, raw, weight, tokens, varies) in enumerate(data):
            small, image = dag.contract(pairs)
            row = trace_pair(dag, root, small, image, raw, weight, tokens, varies)
            if pairs == public:
                print(f'public pairing at {dag.size(root)} gates: {row}')
            traces[i].append(row)
            values = tables(small, all_words, cols)
            if i == 0:
                killed = [g for g in shared if image[g] < 2]
                kill_counts.append(len(killed))
                kill_weights.append(sum(uses[g]-1 for g in killed))
                sig = [values[image[g]] for g in shared]
                still_vary.append(sum(v not in (0, all_words) for v in sig))
                if pairs == public:
                    print(f'public pairing: {len(killed)} shared sources become constants, '
                          f'{still_vary[-1]} still distinguish paired negatives')
            else:
                active, _ = live_wires(small, image[root])
                old = {image[embedded[g]] for g in gates}
                assert len(old) == len(gates) and old <= active
                sig = [values[image[embedded[g]]] for g in shared]
            signatures.append(sig)
        assert signatures[0] == signatures[1]
    for (dag, root, raw, weight, tokens, _), rows in zip(data, traces):
        count = len(rows)
        assert count == 1680
        assert sum(r[1] for r in rows) == count*Fraction(11, 14)*sum(raw.values())
        rate = sum(Fraction(5, 7)*v if k.bit_count() == 1 else Fraction(5, 6)*v
                   for k, v in tokens.items() if k)
        assert sum(r[-1] for r in rows) >= count*rate
        size = dag.size(root)
        print(f'{size} gates: surviving {min(r[6] for r in rows)}..{max(r[6] for r in rows)}, '
              f'best excess over integer quarter {min(r[6] for r in rows)-size//4}')
    print(f'ordinary circuit killed {min(kill_counts)}..{max(kill_counts)} of these shared signals, '
          f'weight {min(kill_weights)}..{max(kill_weights)}; {min(still_vary)}..{max(still_vary)} '
          'still distinguish negatives inside each pairing in BOTH circuits')


if __name__ == '__main__':
    assert not small_negative_words(2) and not small_negative_words(3)
    core = Circuit(4)
    circuit, root = de_morgan_circuit(core, held_karp(core, 4))
    check_monitors(circuit, root)
    encoded, _, mapping = protect_inputs(circuit)
    assert check_monitors(encoded, mapping[root]) > 0
    check_paired_negatives()
