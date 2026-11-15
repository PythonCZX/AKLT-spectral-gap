"""Exact checks of the finite-dimensional identities in the analytic packet.

This does not numerically test compactness or PDE regularity. It independently
integrates all 36 matrix-unit inputs of the coherent frame, compares the
partial-trace formula, and verifies the repair/dilution arithmetic.
"""
from itertools import product
from pathlib import Path
import json
import math
import sympy as s

ROOT = Path(__file__).resolve().parent
alphas = [(2, 0, 0), (1, 1, 0), (1, 0, 1),
          (0, 2, 0), (0, 1, 1), (0, 0, 2)]
coeff = [s.sqrt(s.factorial(2) /
                s.prod(s.factorial(a) for a in alpha))
         for alpha in alphas]
U = s.zeros(9, 6)
for j, alpha in enumerate(alphas):
    slots = [i for i, count in enumerate(alpha) for _ in range(count)]
    a, b = slots
    if a == b:
        U[3*a+b, j] = 1
    else:
        U[3*a+b, j] = 1/s.sqrt(2)
        U[3*b+a, j] = 1/s.sqrt(2)
assert U.T * U == s.eye(6)

def partial_trace(H):
    full = U * H * U.T
    return s.Matrix(3, 3, lambda a, b:
                    sum(full[3*a+j, 3*b+j] for j in range(3)))

def leg(A):
    return s.simplify(U.T * (s.kronecker_product(A, s.eye(3)) +
                            s.kronecker_product(s.eye(3), A)) * U)

def haar_moment(a, b):
    if a != b:
        return s.S.Zero
    return s.Rational(2 * math.prod(math.factorial(x) for x in a),
                      math.factorial(sum(a)+2))

frame = s.zeros(36, 36)
for a, b, g, d in product(range(6), repeat=4):
    z_exp = tuple(alphas[a][i] + alphas[d][i] for i in range(3))
    bar_exp = tuple(alphas[b][i] + alphas[g][i] for i in range(3))
    frame[6*a+b, 6*g+d] = s.simplify(
        coeff[a]*coeff[b]*coeff[g]*coeff[d] * haar_moment(z_exp, bar_exp))

for g, d in product(range(6), repeat=2):
    H = s.zeros(6)
    H[g, d] = 1
    rhs = (H + 2*leg(partial_trace(H)) + s.trace(H)*s.eye(6))/90
    lhs = s.Matrix(6, 6, lambda a, b: frame[6*a+b, 6*g+d])
    assert s.simplify(lhs-rhs) == s.zeros(6), (g, d)

eigenvalues = frame.eigenvals()
assert eigenvalues == {s.Rational(1, 6): 1,
                       s.Rational(1, 15): 8,
                       s.Rational(1, 90): 27}
P = s.diag(1, 0, 0)
Q = s.diag(1, 0, 0, 0, 0, 0)
B = 90*Q - 30*leg(P) + 5*s.eye(6)
assert s.trace(B) == 0
assert s.trace(B*B) == 2550
B_frame = s.Matrix(6, 6, list(frame * s.Matrix(list(B))))
assert s.simplify(B_frame - Q + s.eye(6)/6) == s.zeros(6)
assert 2550 < 51**2

c, A, D = s.symbols("c A D", real=True)
J = (2*A+D)/3
Jc = c**2*((3-c)*A+c*D)/3
energy_remainder = s.factor(c**2*(3-c)*J/2 - Jc)
assert s.simplify(energy_remainder - c**2*(1-c)*D/2) == 0

delta = s.symbols("delta", positive=True)
p = 1/(1+102*delta)
assert s.simplify(p - (1-p)/(102*delta)) == 0
alpha = s.symbols("alpha")
C = 2/((1-3*alpha)*(2-3*alpha))
assert s.diff(C, alpha).subs(alpha, 0) == s.Rational(9, 2)
assert C.subs(alpha, s.Rational(1, 6)) == s.Rational(8, 3)

result = {
    "all_36_matrix_unit_haar_contractions_match": True,
    "frame_eigenvalues": {str(k): int(v) for k, v in eigenvalues.items()},
    "centered_inverse_frame_diagonal": list(map(int, B.diagonal())),
    "centered_inverse_frame_squared_HS_norm": 2550,
    "centered_inverse_frame_identity_checked": True,
    "repair_exact_moment_cancellation": True,
    "dilution_nonnegative_remainder": str(energy_remainder),
    "normalized_psh_L1_bound": "9/2",
    "global_entropy_energy_bound": "E <= 6 H + 6 log(8/3)",
    "scope": "Exact algebra only; analytic theorems are proved and sourced in the packet."
}
(ROOT/"analytic_constants_verified.json").write_text(
    json.dumps(result, indent=2) + "\n")
print(json.dumps(result, indent=2))
