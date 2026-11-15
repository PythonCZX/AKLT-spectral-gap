#!/usr/bin/env python3
"""Exact nonlinear-chain and complementary-minor checks for the jet lemma."""

from itertools import combinations
import json
from math import comb
from pathlib import Path
import sympy as sp

s, t, h, k = sp.symbols("s t h k")


def rows(m):
    return [(a, ell - a) for ell in range(m + 1) for a in range(ell + 1)]


def audit(m, F):
    labels = rows(m)
    K = len(labels)
    R = m * (m + 1) * (m + 2) // 6
    jacobian = sp.factor(sp.det(sp.Matrix(F).jacobian([s, t])))
    substitutions = {s: s + h, t: t + k}
    increments = [sp.expand(f.subs(substitutions, simultaneous=True) - f) for f in F]
    columns = []
    for a, b in labels:
        polynomial = sp.Poly(sp.expand(increments[0]**a * increments[1]**b), h, k)
        columns.append([polynomial.coeff_monomial(h**u * k**v) for u, v in labels])
    T = sp.Matrix(K, K, lambda i, j: columns[j][i])
    chain_determinant = sp.Integer(1)
    for ell in range(m + 1):
        block = [i for i, beta in enumerate(labels) if sum(beta) == ell]
        chain_determinant *= T.extract(block, block).det(method="domain-ge")
    assert all(T[i, j] == 0 for i in range(K) for j in range(K)
               if sum(labels[i]) < sum(labels[j]))
    assert sp.factor(chain_determinant - jacobian**R) == 0
    B = sp.diag(*(s**a * t**b for a, b in labels)) * T
    determinant = (s * t * jacobian)**R
    assert sp.factor(s**R * t**R * chain_determinant - determinant) == 0
    all_indices = set(range(K))
    count = 0
    for point in ({s: 2, t: 3}, {s: 3, t: 5}):
        exact_matrix = B.subs(point)
        inverse = exact_matrix.inv()
        exact_determinant = determinant.subs(point)
        assert exact_matrix.det() == exact_determinant
        for quota in sorted({1, 2, K - 1, K} & set(range(1, K + 1))):
            selections = list(combinations(range(K), quota))
            # Deterministic spread, including off-diagonal complementary minors.
            chosen = sorted(set([0, len(selections) // 3, 2 * len(selections) // 3,
                                 len(selections) - 1]))
            for ia in chosen:
                for ib in chosen:
                    I, J = selections[ia], selections[ib]
                    Ic, Jc = sorted(all_indices - set(I)), sorted(all_indices - set(J))
                    lhs = inverse.extract(I, J).det()
                    complementary = exact_matrix.extract(Jc, Ic).det()
                    rhs = (-1)**(sum(I) + sum(J)) * complementary / exact_determinant
                    assert lhs == rhs
                    count += 1
    return {
        "order": m,
        "chart": [str(f) for f in F],
        "jet_dimension": K,
        "determinant_exponent_R": R,
        "jacobian": str(jacobian),
        "chain_determinant": str(jacobian**R),
        "scaled_determinant": str(determinant),
        "complementary_minor_identities_checked": count,
        "complementary_minor_evaluation_points": [[2, 3], [3, 5]],
        "all_assertions_passed": True,
    }


def main():
    cases = []
    for chart in [(s, s*s*(t+s)), (s*t, s*t*t)]:
        for m in (1, 2, 3):
            cases.append(audit(m, chart))
    thresholds = []
    for m in range(1, 101):
        N = comb(3*m+2, 2)
        R = m*(m+1)*(m+2)//6
        exact = sp.Rational(m*N, 9*R)
        formula = sp.Rational(9*m*(m+1)+2, 3*(m+1)*(m+2))
        assert exact == formula
        assert exact < 3
        thresholds.append({"m": m, "threshold": str(exact)})
    output = Path(__file__).with_name("truncated_jet_chain_exact.json")
    output.write_text(json.dumps({"arithmetic": "exact symbolic rational",
                                 "charts": cases,
                                 "finite_thresholds": thresholds}, indent=2) + "\n")
    for case in cases:
        print(f"m={case['order']}, chart={case['chart']}: "
              f"R={case['determinant_exponent_R']}, "
              f"{case['complementary_minor_identities_checked']} complementary minors PASS")
    print("All finite threshold identities m=1,...,100 PASS")
    print(output)


if __name__ == "__main__":
    main()
