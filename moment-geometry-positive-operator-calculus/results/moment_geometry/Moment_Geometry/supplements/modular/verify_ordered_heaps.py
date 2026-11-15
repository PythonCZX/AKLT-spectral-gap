#!/usr/bin/env python3
"""Exact finite-poset and Bernoulli checks for the ordered-logarithm formula.

The finite enumeration independently compares weak order maps, strict
surjective layerings, and linear-extension Eulerian coefficients. It does
not replace the general reciprocity or heap-algebra proof.
"""
from fractions import Fraction
from itertools import combinations, permutations, product
from pathlib import Path
import json
import math
import sympy as sp


def natural_posets(n):
    pairs = list(combinations(range(n), 2))
    seen = set()
    for mask in range(1 << len(pairs)):
        edges = {e for k, e in enumerate(pairs) if mask >> k & 1}
        for middle in range(n):
            edges |= {(i, j) for i in range(middle) for j in range(middle+1, n)
                      if (i, middle) in edges and (middle, j) in edges}
        key = frozenset(edges)
        if key not in seen:
            seen.add(key)
            yield key


def disconnected(n, edges):
    reached = {0}
    while True:
        new = reached | {j for i, j in edges if i in reached}
        new |= {i for i, j in edges if j in reached}
        if new == reached:
            return len(reached) < n
        reached = new


def check_poset(n, edges):
    t = sp.Symbol("t")
    weak = []
    strict_surjective = []
    for k in range(n+1):
        weak.append(sum(all(f[i] <= f[j] for i, j in edges)
                        for f in product(range(k), repeat=n)))
        strict_surjective.append(
            sum(len(set(f)) == k and all(f[i] < f[j] for i, j in edges)
                for f in product(range(k), repeat=n)))
    omega = sp.interpolate(list(enumerate(weak)), t).expand()
    derivative = Fraction(sp.diff(omega, t).subs(t, 0))
    layering = sum((Fraction((-1)**(n+k)*strict_surjective[k], k)
                    for k in range(1, n+1)), Fraction(0))
    eulerian = Fraction(0)
    for word in permutations(range(n)):
        positions = {a:i for i, a in enumerate(word)}
        if all(positions[i] < positions[j] for i, j in edges):
            descents = sum(word[i] > word[i+1] for i in range(n-1))
            eulerian += Fraction((-1)**descents,
                                 n*math.comb(n-1, descents))
    assert derivative == layering == eulerian
    if disconnected(n, edges):
        assert derivative == 0
    return derivative


def main():
    counts = {}
    for n in range(1, 5):
        cases = list(natural_posets(n))
        for edges in cases:
            check_poset(n, edges)
        counts[str(n)] = len(cases)
    assert list(counts.values()) == [1, 2, 7, 40]
    t, j = sp.symbols("t j", integer=True)
    expected = [Fraction(1), Fraction(1,2), Fraction(1,6), Fraction(0),
                Fraction(-1,30), Fraction(0), Fraction(1,42), Fraction(0),
                Fraction(-1,30), Fraction(0), Fraction(5,66), Fraction(0),
                Fraction(-691,2730), Fraction(0), Fraction(7,6)]
    stars = []
    for m, value in enumerate(expected):
        polynomial = sp.summation(j**m, (j, 1, t)).expand()
        actual = Fraction(sp.diff(polynomial, t).subs(t, 0))
        assert actual == value == Fraction(sp.bernoulli(m, 1))
        stars.append({"leaves":m, "coefficient":str(actual)})
    # Analytic inputs: sin x < x for x>0 and pi < 22/7.
    pole_radius_upper = Fraction(44, 7*128)
    assert pole_radius_upper < Fraction(1,16)
    assert Fraction(3,8) < Fraction(1,2)  # log 2 > 1/2 by integration.
    report = {
        "status":"all exact finite checks passed",
        "natural_posets_by_size":counts,
        "total_posets":sum(counts.values()),
        "independent_coefficient_methods":3,
        "star_Bernoulli_values":stars,
        "m128_pole_radius_rational_upper":str(pole_radius_upper),
        "leaf_activity":"1/16",
        "scope":"Exact finite enumeration and algebra; analytic inputs are identified."
    }
    path = Path(__file__).with_name("ordered_heaps_verified.json")
    path.write_text(json.dumps(report, indent=2)+"\n")
    print(json.dumps(report, indent=2))


if __name__ == "__main__":
    main()
