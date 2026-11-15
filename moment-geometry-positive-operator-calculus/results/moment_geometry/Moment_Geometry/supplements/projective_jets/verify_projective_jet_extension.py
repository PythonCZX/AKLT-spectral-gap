#!/usr/bin/env python3
"""Exact finite-dimensional stress tests beyond the surface case."""

from collections import Counter
from fractions import Fraction
from itertools import product
import json
from math import factorial, prod
from pathlib import Path


def monomials(D, M):
    if D == 1:
        yield (M,)
    else:
        for a in range(M + 1):
            for rest in monomials(D - 1, M - a):
                yield (a,) + rest


def norm(beta):
    return Fraction(prod(factorial(b) for b in beta), factorial(sum(beta)))


def audit(d, M):
    D = d + 1
    alphas = list(monomials(D, M))
    N = len(alphas)
    assert N % D == 0
    quota = N // D
    S = sum(M - max(a) for a in alphas)
    fixed = [[] for _ in range(D)]
    ties = []
    for alpha in alphas:
        choices = [i for i in range(D) if alpha[i] == max(alpha)]
        if len(choices) == 1:
            i = choices[0]
            fixed[i].append(alpha[:i] + alpha[i + 1:])
        else:
            ties.append((alpha, choices))
    support = {}
    enumerated = 0
    for assignment in product(*(choices for _, choices in ties)):
        enumerated += 1
        counts = Counter(assignment)
        if any(counts[i] + len(fixed[i]) != quota for i in range(D)):
            continue
        groups = [list(group) for group in fixed]
        for (alpha, _), i in zip(ties, assignment):
            groups[i].append(alpha[:i] + alpha[i + 1:])
        key = tuple(tuple(sorted(group)) for group in groups)
        assert key not in support
        assert sum(sum(beta) for group in key for beta in group) == S
        weight = prod((norm(beta) for group in key for beta in group), start=Fraction(1))
        support[key] = weight
    assert support
    total = sum(support.values(), Fraction(0))
    coordinate_moments = [[Fraction(0) for _ in range(d)] for _ in range(D)]
    nonzero_root_images = zero_root_images = 0
    for key, weight in support.items():
        for i, group in enumerate(key):
            for p in range(d):
                coordinate_moments[i][p] += weight * sum(beta[p] for beta in group)
            for index, beta in enumerate(group):
                for p in range(d):
                    for q in range(d):
                        if p == q or beta[q] == 0:
                            continue
                        changed = list(beta)
                        changed[p] += 1
                        changed[q] -= 1
                        changed = tuple(changed)
                        assert beta[q] * norm(changed) == (beta[p] + 1) * norm(beta)
                        group2 = list(group)
                        group2[index] = changed
                        if len(set(group2)) != quota:
                            zero_root_images += 1
                            continue
                        nonzero_root_images += 1
                        key2 = list(key)
                        key2[i] = tuple(sorted(group2))
                        assert tuple(key2) not in support
    expected = Fraction(S, D * d)
    assert all(x == expected * total for row in coordinate_moments for x in row)
    return {
        "complex_dimension": d,
        "centers": D,
        "degree": M,
        "section_dimension": N,
        "quota": quota,
        "S_M": S,
        "all_tie_assignments": enumerated,
        "nonzero_balanced_minors": len(support),
        "vector_squared_norm": str(total),
        "normalized_coordinate_moments": [[str(x / total) for x in row]
                                          for row in coordinate_moments],
        "expected_coordinate_moment": str(expected),
        "nonzero_root_images": nonzero_root_images,
        "wedge_zero_root_images": zero_root_images,
        "root_support_overlaps": 0,
        "all_assertions_passed": True,
    }


def main():
    records = [audit(d, M) for d, M in [(3, 3), (3, 5), (4, 2), (4, 3)]]
    output = Path(__file__).with_name("projective_jet_extension_exact.json")
    output.write_text(json.dumps({"arithmetic": "exact rational", "cases": records}, indent=2) + "\n")
    for record in records:
        print(f"d={record['complex_dimension']}, M={record['degree']}, "
              f"support={record['nonzero_balanced_minors']}, "
              f"coordinate-moment={record['expected_coordinate_moment']}, "
              "all-root-overlaps=0 PASS")
    print(output)


if __name__ == "__main__":
    main()
