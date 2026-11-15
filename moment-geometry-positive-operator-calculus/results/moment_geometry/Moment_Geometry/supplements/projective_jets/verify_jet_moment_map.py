#!/usr/bin/env python3
"""Exact audit of the three-center minimal-jet moment map.

All arithmetic is integral or fractions.Fraction.  The tested vector is the
actual exterior-power vector of Taylor coefficients of the unnormalized global
monomial basis.  Its nonzero coefficients are signs, so its coordinate squared
norms are products of a! b! / (a+b)! from the invariant Sym^ell(C^2) norm.

This independently checks the finite-dimensional assertion in Section 3 of
Three_Center_Jet_GIT_Theorem.md.  It is evidence for the general proof, not a
replacement for that proof and not an explicit construction of a semi-invariant.
"""

from __future__ import annotations

import argparse
from collections import Counter
from fractions import Fraction
from itertools import product
import json
from math import comb, factorial
from pathlib import Path


def monomials(M: int) -> list[tuple[int, int, int]]:
    return [(a, b, M - a - b) for a in range(M + 1)
            for b in range(M - a + 1)]


def row_label(alpha: tuple[int, int, int], i: int) -> tuple[int, int]:
    return tuple(alpha[j] for j in range(3) if j != i)


def sym_norm(a: int, b: int) -> Fraction:
    return Fraction(factorial(a) * factorial(b), factorial(a + b))


def dim_nonnegative_triples(total: int) -> int:
    return comb(total + 2, 2) if total >= 0 else 0


def independent_S(M: int, N: int) -> int:
    # Sum max(alpha) by its superlevel sets and inclusion-exclusion.
    sum_max = sum(3 * dim_nonnegative_triples(M - t)
                  - 3 * dim_nonnegative_triples(M - 2 * t)
                  + dim_nonnegative_triples(M - 3 * t)
                  for t in range(1, M + 1))
    return M * N - sum_max


def audit(M: int) -> dict:
    alphas = monomials(M)
    N = len(alphas)
    assert N % 3 == 0, (M, N)
    n = N // 3
    S = sum(M - max(alpha) for alpha in alphas)
    assert S == independent_S(M, N)

    fixed: list[list[tuple[int, int]]] = [[], [], []]
    ties = []
    for alpha in alphas:
        choices = tuple(i for i in range(3) if alpha[i] == max(alpha))
        if len(choices) == 1:
            i = choices[0]
            fixed[i].append(row_label(alpha, i))
        else:
            ties.append((alpha, choices))

    # Every nonzero minimal-order balanced minor is exactly one such assignment.
    support = {}
    enumerated = 0
    for assigned in product(*(choices for _, choices in ties)):
        enumerated += 1
        counts = Counter(assigned)
        if any(len(fixed[i]) + counts[i] != n for i in range(3)):
            continue
        rows = [list(group) for group in fixed]
        for (alpha, _), i in zip(ties, assigned):
            rows[i].append(row_label(alpha, i))
        key = tuple(tuple(sorted(group)) for group in rows)
        assert key not in support
        assert all(len(group) == len(set(group)) == n for group in key)
        assert sum(a + b for group in key for a, b in group) == S

        # Recover all global labels and verify their determinant is a permutation.
        recovered = []
        for i, group in enumerate(key):
            others = [j for j in range(3) if j != i]
            for a, b in group:
                alpha = [0, 0, 0]
                alpha[i] = M - a - b
                alpha[others[0]], alpha[others[1]] = a, b
                recovered.append(tuple(alpha))
        assert sorted(recovered) == sorted(alphas)

        squared_norm = Fraction(1)
        for group in key:
            for a, b in group:
                squared_norm *= sym_norm(a, b)
        support[key] = squared_norm

    assert support, (M, "balanced maximum-coordinate assignment missing")
    total_norm = sum(support.values(), Fraction(0))
    cartan = [Fraction(0), Fraction(0), Fraction(0)]
    central = [Fraction(0), Fraction(0), Fraction(0)]
    root_nonzero_images = 0
    root_wedge_zero_images = 0
    root_support_overlaps = 0

    for key, squared_norm in support.items():
        for i, group in enumerate(key):
            cartan[i] += squared_norm * sum(a - b for a, b in group)
            central[i] += squared_norm * sum(a + b for a, b in group)
            for row_index, (a, b) in enumerate(group):
                for delta_a, delta_b, coefficient in ((1, -1, b), (-1, 1, a)):
                    if coefficient == 0:
                        continue
                    changed_row = (a + delta_a, b + delta_b)
                    changed_group = list(group)
                    changed_group[row_index] = changed_row
                    if len(set(changed_group)) != n:
                        root_wedge_zero_images += 1
                        continue
                    root_nonzero_images += 1
                    changed_key = list(key)
                    changed_key[i] = tuple(sorted(changed_group))
                    changed_key = tuple(changed_key)
                    if changed_key in support:
                        root_support_overlaps += 1

    assert cartan == [0, 0, 0], (M, cartan)
    assert central == [Fraction(S, 3) * total_norm] * 3, (M, central)
    assert root_support_overlaps == 0, (M, root_support_overlaps)

    # Check the chosen metric really makes the raising/lowering maps adjoint.
    for ell in range(M + 1):
        for a in range(ell + 1):
            b = ell - a
            if b:
                assert b * sym_norm(a + 1, b - 1) == (a + 1) * sym_norm(a, b)

    return {
        "M": M,
        "N": N,
        "quota": n,
        "S_M": S,
        "S_over_MN": str(Fraction(S, M * N)),
        "anticanonical_threshold": None if S == 0 else str(Fraction(2 * M * N, 3 * S)),
        "number_of_tied_monomials": len(ties),
        "assignments_enumerated": enumerated,
        "nonzero_balanced_minors": len(support),
        "vector_squared_norm": str(total_norm),
        "normalized_local_cartan_expectations": [str(x / total_norm) for x in cartan],
        "normalized_center_degree_expectations": [str(x / total_norm) for x in central],
        "expected_center_degree": str(Fraction(S, 3)),
        "root_nonzero_images": root_nonzero_images,
        "root_wedge_zero_images": root_wedge_zero_images,
        "root_support_overlaps": root_support_overlaps,
        "all_assertions_passed": True,
    }


def cayley_hyperdet(tensor: dict) -> int:
    a = lambda i, j, k: tensor.get((i, j, k), 0)
    return (
        a(0, 0, 0)**2 * a(1, 1, 1)**2
        + a(0, 0, 1)**2 * a(1, 1, 0)**2
        + a(0, 1, 0)**2 * a(1, 0, 1)**2
        + a(1, 0, 0)**2 * a(0, 1, 1)**2
        - 2 * (
            a(0, 0, 0) * a(0, 0, 1) * a(1, 1, 0) * a(1, 1, 1)
            + a(0, 0, 0) * a(0, 1, 0) * a(1, 0, 1) * a(1, 1, 1)
            + a(0, 0, 0) * a(1, 0, 0) * a(0, 1, 1) * a(1, 1, 1)
            + a(0, 0, 1) * a(0, 1, 0) * a(1, 0, 1) * a(1, 1, 0)
            + a(0, 0, 1) * a(1, 0, 0) * a(0, 1, 1) * a(1, 1, 0)
            + a(0, 1, 0) * a(1, 0, 0) * a(0, 1, 1) * a(1, 0, 1))
        + 4 * (
            a(0, 0, 0) * a(0, 1, 1) * a(1, 0, 1) * a(1, 1, 0)
            + a(0, 0, 1) * a(0, 1, 0) * a(1, 0, 0) * a(1, 1, 1)))


def audit_M2_hyperdeterminant() -> dict:
    alphas = monomials(2)
    index = {alpha: i for i, alpha in enumerate(alphas)}
    tensor = {}
    # Basis bit 0 is the first tangent coordinate, bit 1 the second.
    for bits in product((0, 1), repeat=3):
        columns = []
        for i, bit in enumerate(bits):
            constant = [0, 0, 0]
            constant[i] = 2
            mixed = [0, 0, 0]
            mixed[i] = 1
            others = [j for j in range(3) if j != i]
            mixed[others[bit]] = 1
            columns.extend([index[tuple(constant)], index[tuple(mixed)]])
        if len(set(columns)) == 6:
            inversions = sum(columns[i] > columns[j]
                             for i in range(6) for j in range(i + 1, 6))
            tensor[bits] = (-1)**inversions
    assert len(tensor) == 2
    keys = list(tensor)
    assert all(keys[0][i] + keys[1][i] == 1 for i in range(3))
    invariant = cayley_hyperdet(tensor)
    assert invariant == 1

    matrices = [((2, 1), (1, 1)), ((1, 2), (3, 4)), ((2, -1), (1, 3))]
    transformed = {}
    for out in product((0, 1), repeat=3):
        transformed[out] = sum(value * matrices[0][out[0]][old[0]]
                               * matrices[1][out[1]][old[1]]
                               * matrices[2][out[2]][old[2]]
                               for old, value in tensor.items())
    determinant_product = 1
    for matrix in matrices:
        determinant_product *= matrix[0][0] * matrix[1][1] - matrix[0][1] * matrix[1][0]
    transformed_invariant = cayley_hyperdet(transformed)
    assert transformed_invariant == determinant_product**2 * invariant
    return {
        "tensor_coordinates": {"".join(map(str, key)): value for key, value in tensor.items()},
        "Cayley_hyperdeterminant": invariant,
        "invariant_degree": 4,
        "determinant_character_at_each_center": 2,
        "predicted_character_qS_over_6": str(Fraction(4 * 3, 6)),
        "exact_nondiagonal_change_of_basis_hyperdeterminant": transformed_invariant,
        "exact_expected_transformed_hyperdeterminant": determinant_product**2,
        "all_assertions_passed": True,
    }


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--degrees", type=int, nargs="+", default=[1, 2, 4, 5, 7, 8, 10, 11, 14])
    parser.add_argument("--output", type=Path,
                        default=Path(__file__).with_name("jet_moment_map_exact.json"))
    args = parser.parse_args()
    result = {
        "arithmetic": "exact integers and rational fractions",
        "coordinate_norm": "a! b! / (a+b)!",
        "tested_assertion": "zero moment map after determinant twist S_M/6 at each GL(2) factor",
        "cases": [audit(M) for M in args.degrees],
        "M2_explicit_semi_invariant": audit_M2_hyperdeterminant(),
    }
    args.output.write_text(json.dumps(result, indent=2) + "\n", encoding="utf-8")
    for case in result["cases"]:
        print(f"M={case['M']:2d}: N={case['N']:3d}, S={case['S_M']:4d}, "
              f"support={case['nonzero_balanced_minors']:4d}, "
              f"central={case['expected_center_degree']}, "
              f"root-overlap={case['root_support_overlaps']} PASS")
    print("M=2: explicit Cayley hyperdeterminant = 1; GL(2)^3 character check PASS")
    print(f"Exact audit saved to {args.output}")


if __name__ == "__main__":
    main()
