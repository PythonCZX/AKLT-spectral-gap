"""Certify a finite bound for the angular mean of a Slater energy.

The assignment is proposed numerically, then certified using rational
multiplicative dual variables. Arb encloses the remaining logarithms.
No angular sampling or determinant simulation enters the certificate.
The input coordinates are positive rational squared moduli, one row per
section of O(m) on CP^q; m must be a multiple of q+1.
"""
from __future__ import annotations
import argparse
from fractions import Fraction as F
from itertools import permutations
import json
import math
from pathlib import Path


def compositions(total, parts):
    if parts == 1:
        yield (total,)
    else:
        for first in range(total + 1):
            for tail in compositions(total - first, parts - 1):
                yield (first,) + tail


def weights(points, exponents):
    return [[math.prod(p[j] ** a[j] for j in range(len(p)))
             for a in exponents] for p in points]


def exact_assignment_dual(w, assignment):
    """Return positive rational u,v with w_ij <= u_i v_j and equality
    on the proposed permutation, or reject it. No floating tolerance.
    """
    n = len(w)
    assert sorted(assignment) == list(range(n))
    gain = [[w[i][assignment[j]] / w[i][assignment[i]]
             for j in range(n)] for i in range(n)]
    potential = [F(1)] * n
    for _ in range(n - 1):
        updated = [max([potential[j]] +
                       [potential[i] * gain[i][j] for i in range(n)])
                   for j in range(n)]
        if updated == potential:
            break
        potential = updated
    if any(potential[i] * gain[i][j] > potential[j]
           for i in range(n) for j in range(n)):
        raise ValueError("Proposed matching is not exactly optimal.")
    v = [F(0)] * n
    for j in range(n):
        v[assignment[j]] = potential[j]
    u = [w[i][assignment[i]] / potential[i] for i in range(n)]
    assert all(w[i][j] <= u[i] * v[j]
               for i in range(n) for j in range(n))
    assert all(w[i][assignment[i]] == u[i] * v[assignment[i]]
               for i in range(n))
    return u, v


def certify(q, m, coordinates, precision=160):
    import numpy as np
    from scipy.optimize import linear_sum_assignment
    from flint import arb, ctx
    if q < 1 or m < 1 or m % (q + 1):
        raise ValueError("Require q >= 1 and positive m divisible by q+1.")
    exponents = list(compositions(m, q + 1))
    points = [[F(x) for x in row] for row in coordinates]
    n, k = len(exponents), m // (q + 1)
    if len(points) != n or any(len(p) != q + 1 or sum(p) != 1 or
                              min(p) <= 0 for p in points):
        raise ValueError("Need exactly binom(m+q,q) positive rational simplex rows.")
    log_scores = np.array([[sum(a[j] * (math.log(p[j].numerator) - math.log(p[j].denominator))
                                for j in range(q + 1))
                           for a in exponents] for p in points])
    rows, columns = linear_sum_assignment(-log_scores)
    assignment = [int(j) for j in columns]
    assert list(rows) == list(range(n))
    w = weights(points, exponents)
    u, v = exact_assignment_dual(w, assignment)
    ctx.prec = precision
    def arbf(x):
        return arb(x.numerator) / arb(x.denominator)
    cost = arb(0)
    for i, j in enumerate(assignment):
        for ell, count in enumerate(exponents[j]):
            if count:
                a = F(count, m)
                cost += arbf(a) * (arbf(a).log() - arbf(points[i][ell]).log())
    cost /= n
    upper = (q + 1) * cost
    lower = upper - arb(n).log() / k - arb(math.factorial(n)).log() / (k * n)
    return {
        "status": "certified", "evidence_class": "certified_arithmetic",
        "q": q, "m": m, "k": k, "N": n,
        "coordinates": [[str(x) for x in p] for p in points],
        "exponents": exponents, "assignment": assignment,
        "multiplicative_dual": {"u": [str(x) for x in u],
                                 "v": [str(x) for x in v]},
        "dual_inequalities_checked": n * n,
        "precision_bits": precision,
        "assignment_KL_cost_interval": str(cost),
        "lower_bound_interval": str(lower),
        "upper_bound_interval": str(upper),
        "phase_mean_energy_enclosure": str(lower.union(upper)),
        "meaning": "The phase-averaged energy lies between the exact lower and upper expressions enclosed above. The union ball encloses the entire guaranteed interval. This is not a bound for each angular configuration or an attractive partition function.",
    }


def finite_checks():
    # Every assignment is exposed: exhaustive six-point Newton-polytope check.
    a = list(compositions(2, 3))
    vertices, gaps = 0, []
    for perm in permutations(range(len(a))):
        lhs = sum(sum(x*x for x in row[1:]) for row in a)
        lhs -= sum(sum(a[i][j]*a[perm[i]][j] for j in (1, 2))
                   for i in range(len(a)))
        rhs = sum(sum((a[i][j]-a[perm[i]][j])**2 for j in (1, 2))
                  for i in range(len(a)))
        assert 2*lhs == rhs
        assert lhs >= 0
        assert (lhs == 0) == (perm == tuple(range(len(a))))
        vertices += 1
        if lhs:
            gaps.append(lhs)
    # Exact multinomial mode inequality, including boundary types.
    modal_cases = 0
    for d in (2, 3, 4):
        for m in range(1, 7):
            types = list(compositions(m, d))
            for alpha in types:
                p = [F(x, m) for x in alpha]
                values = [F(math.factorial(m), math.prod(math.factorial(x) for x in b))
                          * math.prod(p[j]**b[j] for j in range(d)) for b in types]
                own = values[types.index(alpha)]
                assert own == max(values)
                assert F(1, len(types)) <= own <= 1
                modal_cases += 1
    # Rational dual against exhaustive six-by-six assignment products.
    points = [[F(x + 1, 5) for x in row] for row in a]
    w = weights(points, a)
    identity = list(range(len(a)))
    u, v = exact_assignment_dual(w, identity)
    optimum = math.prod(w[i][i] for i in range(len(a)))
    assert all(math.prod(w[i][p[i]] for i in range(len(a))) <= optimum
               for p in permutations(range(len(a))))
    assert math.prod(u) * math.prod(v) == optimum
    # Verify that a strictly inferior matching is rejected.
    bad = identity.copy(); bad[0], bad[-1] = bad[-1], bad[0]
    try:
        exact_assignment_dual(w, bad)
    except ValueError:
        pass
    else:
        raise AssertionError("An inferior matching was accepted.")
    return {"exposure_assignments": vertices, "minimum_positive_exposure_gap": min(gaps),
            "exact_multinomial_modes": modal_cases,
            "exhaustive_assignment_comparisons": math.factorial(len(a)),
            "incorrect_assignment_rejected": True}


def main():
    if not __debug__:
        raise RuntimeError("Run without -O: exact certificate assertions must remain enabled.")
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--input", type=Path, help="JSON with q, m, coordinates.")
    parser.add_argument("--output", type=Path,
                        default=Path(__file__).with_name("toric_assignment_certificate.json"))
    parser.add_argument("--verify", action="store_true")
    args = parser.parse_args()
    if args.input:
        data = json.loads(args.input.read_text())
    else:
        q, m = 2, 3
        data = {"q": q, "m": m,
                "coordinates": [[str(F(x+1, m+q+1)) for x in a]
                                for a in compositions(m, q+1)]}
    out = certify(data["q"], data["m"], data["coordinates"])
    out["example_kind"] = "user-supplied" if args.input else "deterministic rational illustration"
    if args.verify:
        out["finite_checks"] = finite_checks()
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(out, indent=2) + "\n")
    print(json.dumps({"status": out["status"], "N": out["N"],
                      "phase_mean_energy_enclosure": out["phase_mean_energy_enclosure"],
                      "finite_checks": out.get("finite_checks"),
                      "output": str(args.output)}, indent=2))


if __name__ == "__main__":
    main()
