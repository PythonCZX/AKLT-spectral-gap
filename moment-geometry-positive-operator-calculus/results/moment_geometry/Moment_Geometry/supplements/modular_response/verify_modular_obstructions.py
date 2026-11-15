#!/usr/bin/env python3
"""Independent finite-dimensional checks for the modular obstruction addendum.

Requirements: Python 3, NumPy.  The proofs, rather than these numerical
checks, establish the all-size and arbitrary-parameter statements.
"""
from __future__ import annotations

import json
import math
from fractions import Fraction
from pathlib import Path

import numpy as np


HERE = Path(__file__).resolve().parent


def kron_all(*xs: np.ndarray) -> np.ndarray:
    ans = np.array([[1.0]], dtype=complex)
    for x in xs:
        ans = np.kron(ans, x)
    return ans


def herm_function(a: np.ndarray, function) -> np.ndarray:
    vals, vecs = np.linalg.eigh(a)
    return (vecs * function(vals)) @ vecs.conj().T


def opnorm(a: np.ndarray) -> float:
    return float(np.linalg.norm(a, ord=2))


def delete(a: np.ndarray, site: int, dimension: int) -> np.ndarray:
    """Normalized partial trace, reinserted in the original three-site order."""
    reshaped = a.reshape([dimension] * 6)
    marginal = np.trace(reshaped, axis1=site, axis2=site + 3)
    answer = np.zeros_like(a)
    for row in np.ndindex((dimension,) * 3):
        for col in np.ndindex((dimension,) * 3):
            if row[site] == col[site]:
                r = tuple(row[j] for j in range(3) if j != site)
                c = tuple(col[j] for j in range(3) if j != site)
                answer[np.ravel_multi_index(row, (dimension,) * 3),
                       np.ravel_multi_index(col, (dimension,) * 3)] = (
                    marginal[r + c] / dimension
                )
    return answer


def f_scalar(x: float) -> float:
    return x / math.sinh(x) if x else 1.0


def spectral_map(k: np.ndarray, h: np.ndarray, function) -> np.ndarray:
    vals, vecs = np.linalg.eigh(k)
    hh = vecs.conj().T @ h @ vecs
    differences = vals[:, None] - vals[None, :]
    multiplier = np.vectorize(function)(differences)
    return vecs @ (multiplier * hh) @ vecs.conj().T


def verify_bs(dimension: int, s: Fraction, t: Fraction) -> dict:
    d = dimension
    eye = np.eye(d)
    x = np.zeros((d, d))
    x[0, 1] = x[1, 0] = 1
    z = np.diag([1, -1] + [0] * (d - 2))
    sf, tf = float(s), float(t)
    sigma = (eye + tf * x) / d
    half = herm_function(sigma, np.sqrt)
    inverse_half = np.linalg.inv(half)
    half_lift = kron_all(eye, half, eye)
    u = np.eye(d**3) + sf * kron_all(z, z, eye)
    v = np.eye(d**3) + sf * kron_all(eye, z, z)
    rho = half_lift @ u @ v @ half_lift / d**2
    assert abs(np.trace(rho) - 1) < 2e-14
    assert np.linalg.eigvalsh(rho)[0] > 0
    assert opnorm(rho.imag) < 1e-14
    ea, ec = delete(rho, 0, d), delete(rho, 2, d)
    eb = delete(rho, 1, d)
    # The density matrices of marginals are embedded with identity,
    # whereas normalized deletion inserts I/d.
    rho_ab = d * ec
    rho_bc = d * ea
    sigma_lift = kron_all(eye, sigma, eye)
    recovery_error = opnorm(rho_ab @ np.linalg.inv(sigma_lift) @ rho_bc - rho)
    ratio_a = rho @ np.linalg.inv(ea)
    predicted_ratio = half_lift @ u @ kron_all(eye, inverse_half, eye)
    ratio_error = opnorm(ratio_a - predicted_ratio)
    assert recovery_error < 5e-14
    assert ratio_error < 5e-14

    log_rho = herm_function(rho, np.log)
    log_ea = herm_function(ea, np.log)
    p = kron_all(z, x, z)
    denom = np.trace(p @ p).real
    coefficient = float(np.trace(p @ log_rho).real / denom)
    difference_coefficient = float(np.trace(p @ (log_rho - log_ea)).real / denom)
    vv = math.sqrt(tf**2 + 4 * sf**2 * (1 - tf**2) / (1 + sf**2)**2)
    exact_function = tf * (math.atanh(vv) / vv - math.atanh(tf) / tf) / 2
    rational_lower = 2 * t * s**2 * (1 - t**2) / (3 * (1 + s**2)**2)
    assert abs(coefficient - exact_function) < 3e-14
    assert abs(difference_coefficient - exact_function) < 3e-14
    assert coefficient > float(rational_lower) > 0
    ratio_norms = []
    right_remainder_norms = []
    for deleted in (ea, eb, ec):
        y = rho @ np.linalg.inv(deleted)
        ratio_norms.append(opnorm(y - np.eye(d**3)))
        right_remainder_norms.append(opnorm(np.eye(d**3) - np.linalg.inv(y)))

    return {
        "local_dimension": d,
        "s": str(s),
        "t": str(t),
        "minimum_eigenvalue": float(np.linalg.eigvalsh(rho)[0]),
        "BS_recovery_error": recovery_error,
        "local_ratio_identity_error": ratio_error,
        "log_three_body_coefficient": coefficient,
        "closed_formula_coefficient": exact_function,
        "Hermitian_conditional_log_coefficient": difference_coefficient,
        "positive_rational_lower_bound": str(rational_lower),
        "positive_rational_lower_bound_decimal": float(rational_lower),
        "ratio_minus_identity_norms_A_B_C": ratio_norms,
        "right_remainder_norms_A_B_C": right_remainder_norms,
    }


def verify_cp_block(n: int, weight: float, a: float, b: float) -> dict:
    x = np.array([[0.0, 1.0], [1.0, 0.0]])
    y = np.array([[0.0, -1.0j], [1.0j, 0.0]])
    z = np.diag([1.0, -1.0])
    e = a / weight
    k = b * z + e * x
    h = n * z
    r = math.hypot(b, e)
    phi_h = spectral_map(k, h, f_scalar)
    predicted_entry = n * b * e / r**2 * (1 - f_scalar(2 * r))
    assert abs(phi_h[0, 1] - predicted_entry) < 2e-12
    odd = spectral_map(k, h, lambda u: math.tanh(u / 2))
    predicted_odd = -1j * n * e / r * math.tanh(r) * y
    assert opnorm(odd - predicted_odd) < 2e-12
    q = h + odd
    rho = herm_function(k, np.exp)
    assert opnorm(q.conj().T - np.linalg.solve(rho, q @ rho)) < 5e-12
    tangent = q @ rho
    assert opnorm(tangent - tangent.conj().T) < 5e-12
    uniform_lower = n * a * b / (a*a + b*b) * (1 - f_scalar(2*b))
    weighted_actual_lower = weight * abs(phi_h[0, 1])
    assert weighted_actual_lower + 2e-12 >= uniform_lower
    return {
        "n": n,
        "weight_w_n": weight,
        "a": a,
        "b": b,
        "K_interaction_norm_upper": a + b/n,
        "H_interaction_norm": 1,
        "Phi_H_full_support_weighted_lower": float(weighted_actual_lower),
        "uniform_linear_lower": uniform_lower,
        "compatible_Q_full_support_weighted_lower": float(weight * abs(q[0, 1])),
    }


def full_matrix_block_check(n: int) -> dict:
    """Confirm that the reducing-block computation matches the full system."""
    eye = np.eye(2)
    x = np.array([[0.0, 1.0], [1.0, 0.0]])
    z = np.diag([1.0, -1.0])
    d = sum(kron_all(*(z if j == i else eye for j in range(n))) for i in range(n))
    v = kron_all(*(x for _ in range(n)))
    weight, a, b = math.exp(0.3 * n), 0.07, 0.11
    k = (b / n) * d + (a / weight) * v
    answer = spectral_map(k, d, f_scalar)
    rr = math.hypot(b, a/weight)
    formula = n*b*(a/weight)/(rr*rr)*(1-f_scalar(2*rr))
    error = abs(answer[0, -1] - formula)
    assert error < 3e-13
    return {"n": n, "full_matrix_formula_error": float(error)}


def main() -> None:
    bs = [verify_bs(d, Fraction(1, q), Fraction(1, q))
          for d in (2, 3) for q in (10, 100)]
    blocks = [verify_cp_block(n, w, 0.07, 0.11)
              for n in (4, 16, 64, 256)
              for w in (1.0, float(n*n), math.exp(n/10))]
    full = [full_matrix_block_check(n) for n in (2, 3, 4, 5)]
    report = {
        "status": "all independent numerical identities passed",
        "scope": "The addendum contains the exact all-size proofs; this file checks formulas independently.",
        "BS_family": bs,
        "CP_filter_blocks": blocks,
        "full_matrices": full,
        "critical_qualification": "The CP obstruction concerns arbitrary Hermitian inputs. Its corresponding full KMS-compatible right response is already large; the physical full-response reconstruction question remains open.",
    }
    path = HERE / "modular_obstructions_verification.json"
    path.write_text(json.dumps(report, indent=2) + "\n")
    print(json.dumps(report, indent=2))


if __name__ == "__main__":
    main()
