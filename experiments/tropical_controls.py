"""Exact finite checks for the MWIS tangent and a signed arithmetic bypass.

The flow circuit is a straight-line unrolling of Hertrich and Sering,
arXiv:2102.06635, Algorithms 2 and 3. All loop bounds and neighbors depend
on the fixed graph. Capacities are independent inputs reused across gates.
"""
from fractions import Fraction
from itertools import combinations, product


def direct_energy(edges, costs, color):
    return sum(color[a] == color[b] for a, b in edges) + sum(h[z] for h, z in zip(costs, color))


def tangent_check(n, edges, weights):
    degree = [sum(v in e for e in edges) for v in range(n)]
    step = Fraction(1, 1 + sum(abs(w) for w in weights))
    costs = [(1, 1 + d - step*w) for d, w in zip(degree, weights)]
    assert all(min(pair) >= 0 for pair in costs)
    optimum, best_weight = None, 0
    for z in product((0, 1), repeat=n):
        inside = sum(z[a] and z[b] for a, b in edges)
        weight = sum(w for w, bit in zip(weights, z) if bit)
        val = direct_energy(edges, costs, z)
        assert val == len(edges) + n + 2*inside - step*weight
        if inside == 0:
            best_weight = max(best_weight, weight)
        optimum = val if optimum is None else min(val, optimum)
    assert (len(edges)+n-optimum)/step == best_weight


class Circuit:
    def __init__(self, inputs):
        self.inputs = inputs
        self.gates = []

    def gate(self, kind, a, b=0):
        self.gates.append((kind, a, b))
        return self.inputs + len(self.gates) - 1

    def run(self, inputs, out):
        values = list(inputs)
        for op, a, b in self.gates:
            if op == 'const':
                values.append(a)
            elif op == '+':
                values.append(values[a]+values[b])
            elif op == '-':
                values.append(values[a]-values[b])
            else:
                values.append(min(values[a], values[b]))
        return values[out]


def flow_circuit(n, edges, side):
    source, sink = n, n+1
    count = n+2
    gates = Circuit(2*n)
    zero = gates.gate('const', 0)
    unit = gates.gate('const', 1)
    add = lambda a,b: gates.gate('+', a, b)
    sub = lambda a,b: gates.gate('-', a, b)
    low = lambda a,b: gates.gate('min', a, b)

    def high(a, b):
        return sub(add(a,b), low(a,b))

    cap = {}
    for u, v in edges:
        assert side[u] != side[v]
        cap[u,v] = cap[v,u] = unit
    for u in range(n):
        # y=true denotes source side; t-links charge the two unary prices.
        cap[source,u], cap[u,source] = 2*u + side[u], zero
        cap[u,sink], cap[sink,u] = 2*u + 1-side[u], zero
    nbr = [sorted(w for v,w in cap if v == u) for u in range(count)]
    pairs = sorted((u,v) for u,v in cap if u < v)
    value = zero
    # Extra zero-capacity reverses are part of the fixed directed topology.
    for k in range(1, count):
        for _ in range(len(cap)):
            z = dict.fromkeys(cap, zero)
            excess = [[zero]*count for _ in range(k+1)]
            fat = [[zero]*count for _ in range(k+1)]
            for v in nbr[sink]:
                fat[1][v] = cap[v,sink]
            for level in range(2,k+1):
                for v in range(count-1):
                    best = zero
                    for w in nbr[v]:
                        if w != sink:
                            best = high(best, low(fat[level-1][w],cap[v,w]))
                    fat[level][v] = best
            excess[k][source] = fat[k][source]
            for level in range(k,1,-1):
                for v in range(count-1):
                    for w in nbr[v]:
                        if w != sink:
                            room = sub(fat[level-1][w],excess[level-1][w])
                            push = low(excess[level][v],low(cap[v,w],room))
                            z[v,w] = add(z[v,w],push)
                            excess[level][v] = sub(excess[level][v],push)
                            excess[level-1][w] = add(excess[level-1][w],push)
            for v in nbr[sink]:
                z[v,sink] = excess[1][v]
                excess[1][v] = zero
            for level in range(2,k):
                for w in reversed(range(count-1)):
                    for v in reversed(nbr[w]):
                        if v != sink:
                            back = low(excess[level][w],z[v,w])
                            z[v,w] = sub(z[v,w],back)
                            excess[level][w] = sub(excess[level][w],back)
                            excess[level+1][v] = add(excess[level+1][v],back)
            for u,v in pairs:
                augment = sub(z[u,v],z[v,u])
                cap[u,v] = sub(cap[u,v],augment)
                cap[v,u] = add(cap[v,u],augment)
            for v in nbr[sink]:
                value = add(value, z[v,sink])
    return gates, value


def main():
    trials = 0
    for n in (1,2,3,4):
        pairs = list(combinations(range(n),2))
        for select in product((False,True), repeat=len(pairs)):
            edges = [edge for edge, used in zip(pairs, select) if used]
            for offset in range(4):
                weights = [Fraction((3*v+offset)%7-3, v+1) for v in range(n)]
                tangent_check(n, edges, weights)
                trials += 1
    print(f'{trials} signed rational derivative checks, including isolated vertices.')
    edges = [(0,1),(1,2),(2,3),(3,0)]
    dag, out = flow_circuit(4, edges, [0,1,0,1])
    for seed in range(12):
        prices = [((i*3+seed)%7, (i*i+2*seed)%9) for i in range(4)]
        target = min(direct_energy(edges,prices,z) for z in product((0,1), repeat=4))
        assert dag.run([c for pair in prices for c in pair],out) == target
    prices = [(Fraction(1,2),Fraction(3,7)),(4,0),(0,Fraction(8,3)),(1,0)]
    assert dag.run([c for pair in prices for c in pair],out) == min(
        direct_energy(edges,prices,z) for z in product((0,1), repeat=4))
    print(f'One fixed {len(dag.gates)}-gate min/add/subtract circuit on the 2x2 grid, 13 unary-price inputs checked.')


if __name__ == '__main__':
    main()
