#!/usr/bin/env python3
"""Exact finite-dimensional identities used by the cubic classification.

This verifies polynomial identities, not the external Kempf--Ness or
Vinberg theorems.  No floating-point tolerance is used.
"""
from collections import Counter
from itertools import product
import json
from pathlib import Path

import sympy as s

OUT = Path(__file__).with_name("cubic_classification_verified.json")
report = {}


def monomial(positive, negative):
    # The barred and unbarred matrix entries are independent formal variables.
    return tuple(sorted(positive)), tuple(sorted(negative))


def check_haar_identity(n, d):
    """Compare all formal coefficient monomials after the two Haar contractions."""
    lhs, rhs = Counter(), Counter()
    coefficient = n - 1
    for a, b, c, e, i, k in product(
        range(n), range(n), range(n), range(n), range(d), range(d)
    ):
        pos = ((i, a, c), (k, b, e))
        # (n-1) tr(A^2), two fourth-moment contractions.
        lhs[monomial(pos, ((i, b, c), (k, a, e)))] += coefficient
        lhs[monomial(pos, ((k, b, c), (i, a, e)))] += coefficient
        # -(tr A)^2, two fourth-moment contractions.
        lhs[monomial(pos, ((i, a, c), (k, b, e)))] -= 1
        lhs[monomial(pos, ((k, a, c), (i, b, e)))] -= 1
        # (n-1) tr(R^2).
        rhs[monomial(pos, ((i, b, c), (k, a, e)))] += coefficient
        # (n-1) tr(C^2).
        rhs[monomial(((i, a, e), (k, b, c)), ((i, a, c), (k, b, e)))] += coefficient
        # -tr(T^2).
        rhs[monomial(pos, ((k, a, c), (i, b, e)))] -= 1
        # -S^2.
        rhs[monomial(pos, ((i, a, c), (k, b, e)))] -= 1
    lhs = {k: v for k, v in lhs.items() if v}
    rhs = {k: v for k, v in rhs.items() if v}
    assert lhs == rhs, (n, d)
    return len(lhs)


report["haar_coefficient_identities"] = {
    f"{n}x{n}x{d}": check_haar_identity(n, d)
    for n in range(2, 5) for d in range(2, 5)
}

x, y, z, a, b, c, aa, bb, cc = s.symbols("x y z a b c aa bb cc")
moore = s.Matrix([[a*x, b*z, c*y], [c*z, a*y, b*x], [b*y, c*x, a*z]])
assert s.expand(moore.det() - ((a**3+b**3+c**3)*x*y*z-a*b*c*(x**3+y**3+z**3))) == 0
report["moore_determinant"] = True

node = s.Matrix([[x, 0, y], [0, y, x], [-c*y, -a*x, z]])
assert s.expand(node.det() - (x*y*z+a*x**3+c*y**3)) == 0
cusp = s.Matrix([[x,y,0],[0,x,z],[-y,0,x]])
assert s.expand(cusp.det()-(x**3-y**2*z)) == 0
report["all_singular_irreducible_representations"] = True

coefficients = [moore.diff(v) for v in (x, y, z)]
bar_sub = {a: aa, b: bb, c: cc}
adjoints = [M.xreplace(bar_sub).T for M in coefficients]
R = sum((M*A for M,A in zip(coefficients, adjoints)), s.zeros(3))
C = sum((A*M for M,A in zip(coefficients, adjoints)), s.zeros(3))
T = s.Matrix(3,3,lambda i,j:s.trace(coefficients[i]*adjoints[j]))
scalar = a*aa+b*bb+c*cc
for marginal in (R,C,T):
    assert all(s.expand(v)==0 for v in marginal-scalar*s.eye(3))
report["cartan_all_three_marginals_scalar"] = True

omega = (-1+s.sqrt(3)*s.I)/2
factor = (x+y+z)*(x+omega*y+omega**2*z)*(x+omega**2*y+omega*z)
assert s.simplify(s.expand(factor-(x**3+y**3+z**3-3*x*y*z))) == 0
fourier = s.Matrix([[1,1,1],[1,omega,omega**2],[1,omega**2,omega]])
assert all(s.simplify(v)==0 for v in fourier*fourier.conjugate().T-3*s.eye(3))
report["singular_hesse_orthogonal_triangle"] = True

# Phase averaging encodes the required vanishing first and second Fourier modes.
phase = s.symbols("phase", nonzero=True)
triangle_moment = s.zeros(6)
for zero in range(3):
    p = [s.Integer(0)]*3
    slots = [j for j in range(3) if j != zero]
    p[slots[0]] = 1/s.sqrt(2)
    p[slots[1]] = phase/s.sqrt(2)
    v = s.Matrix([p[0]**2,p[1]**2,p[2]**2,
                  s.sqrt(2)*p[0]*p[1],s.sqrt(2)*p[0]*p[2],
                  s.sqrt(2)*p[1]*p[2]])
    vbar = v.xreplace({phase:1/phase})
    Q = v*vbar.T
    average = Q.applyfunc(lambda h:s.expand(h).coeff(phase,0))
    triangle_moment += average/3
assert triangle_moment == s.eye(6)/6
report["triangle_first_two_fourier_conditions_suffice"] = True

# The nine Hesse projectors supply the required converse.
points = []
for zero in range(3):
    for j in range(3):
        p = [s.Integer(0)]*3
        slots = [i for i in range(3) if i != zero]
        p[slots[0]] = 1/s.sqrt(2)
        p[slots[1]] = -omega**j/s.sqrt(2)
        points.append(s.Matrix(p))
moment = s.zeros(6)
for p in points:
    v = s.Matrix([p[0]**2,p[1]**2,p[2]**2,
                  s.sqrt(2)*p[0]*p[1],s.sqrt(2)*p[0]*p[2],
                  s.sqrt(2)*p[1]*p[2]])
    moment += v*v.conjugate().T/9
assert all(s.simplify(h)==0 for h in moment-s.eye(6)/6)
report["hesse_nine_exact_second_moment"] = True

integer_pairs = [(n,d) for n in range(2,101) for d in range(2,101)
                 if n*(d-1)==2*d]
assert integer_pairs == [(3,3),(4,2)]
report["critical_integer_pairs_through_100"] = integer_pairs
report["critical_integer_pair_exhaustion"] = "(n-2)(d-1)=2"
report["status"] = "All exact checks passed."
OUT.write_text(json.dumps(report, indent=2)+"\n")
print(json.dumps(report, indent=2))
