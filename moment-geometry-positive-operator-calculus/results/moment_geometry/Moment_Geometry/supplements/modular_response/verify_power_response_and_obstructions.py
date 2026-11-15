#!/usr/bin/env python3
"""Independent finite-dimensional checks of the exact power-response theorem.

Requires NumPy and SciPy. The accompanying mathematical proofs establish
the all-parameter and all-size claims. This script also checks the obstruction examples by importing the supplied
sibling module. All imports stay inside this supplemental distribution.
"""
from __future__ import annotations

import importlib.util
import json
import math
from fractions import Fraction
from pathlib import Path

import numpy as np
from scipy.integrate import quad

HERE = Path(__file__).resolve().parent
ROOT = HERE.parent


def norm(a):
    return float(np.linalg.norm(a, ord=2))


def sinh_ratio(x, r):
    return r if x == 0 else math.sinh(r*x)/math.sinh(x)


def psi_kernel(t, r):
    # Equivalent stable form avoiding overflow in cosh(pi*t).
    z = math.exp(-math.pi*abs(t))
    return math.sin(math.pi*r)*z/(1+z*z+2*math.cos(math.pi*r)*z)


def fourier_checks():
    out = []
    for r in (0.1, 0.25, 0.5, 0.9, 0.99):
        for x in (0.0, 0.3, 1.5, 6.0):
            integral, error = quad(
                lambda t: 2*psi_kernel(t, r)*math.cos(t*x),
                0, np.inf, epsabs=2e-12, epsrel=2e-12, limit=300,
            )
            expected = sinh_ratio(x, r)
            assert abs(integral-expected) < 1e-10
            out.append({"r":r, "x":x, "error":abs(integral-expected),
                        "quadrature_error_estimate":error})
    return out


def herm_function(a, function):
    vals, vecs = np.linalg.eigh(a)
    return (vecs*function(vals))@vecs.conj().T


def power_derivative(rho, tangent, r):
    vals, vecs = np.linalg.eigh(rho)
    dd = vecs.conj().T@tangent@vecs
    divided = np.empty((len(vals), len(vals)))
    for i, a in enumerate(vals):
        for j, b in enumerate(vals):
            if i == j:
                divided[i,j] = r*a**(r-1)
            else:
                divided[i,j] = b**r*math.expm1(r*math.log(a/b))/(a-b)
    return vecs@(divided*dd)@vecs.conj().T


def log_derivative(rho, tangent):
    vals, vecs = np.linalg.eigh(rho)
    dd = vecs.conj().T@tangent@vecs
    divided = np.empty((len(vals), len(vals)))
    for i, a in enumerate(vals):
        for j, b in enumerate(vals):
            divided[i,j] = 1/a if i == j else math.log(a/b)/(a-b)
    return vecs@(divided*dd)@vecs.conj().T


def matrix_checks():
    rng = np.random.default_rng(20261115)
    out = []
    for dim in (2, 3, 5, 8):
        raw = rng.normal(size=(dim,dim))+1j*rng.normal(size=(dim,dim))
        k = (raw+raw.conj().T)/(3*math.sqrt(dim))
        rho = herm_function(k, np.exp)
        raw = rng.normal(size=(dim,dim))+1j*rng.normal(size=(dim,dim))
        tangent = (raw+raw.conj().T)/(2*math.sqrt(dim))
        q = tangent@np.linalg.inv(rho)
        h = (q+q.conj().T)/2
        a = (q-q.conj().T)/2
        kvals, basis = np.linalg.eigh(k)
        diff = kvals[:,None]-kvals[None,:]
        hh, aa = basis.conj().T@h@basis, basis.conj().T@a@basis
        dotk = log_derivative(rho, tangent)
        for r in (0., 1e-4, 0.1, 0.25, 0.5, 0.9, 1.):
            rho_r_inverse = herm_function(rho, lambda x: x**(-r))
            qr = power_derivative(rho, tangent, r)@rho_r_inverse
            hr, ar = (qr+qr.conj().T)/2, (qr-qr.conj().T)/2
            psi = np.vectorize(lambda x:sinh_ratio(float(x), r))(diff)
            chi = np.vectorize(lambda x:sinh_ratio(float(x)/2, r)**2)(diff)
            predicted_h = basis@(psi*hh)@basis.conj().T
            predicted_a = basis@(chi*aa)@basis.conj().T
            herr, aerr = norm(hr-predicted_h), norm(ar-predicted_a)
            assert max(herr,aerr) < 2e-12
            assert norm(hr) <= r*norm(h)+3e-12
            assert norm(ar) <= r*r*norm(a)+3e-12
            # For a diagonal modular generator these are Schur multipliers;
            # their Choi positivity is equivalent to these Gram PSD checks.
            min_psi = float(np.linalg.eigvalsh(psi)[0])
            min_chi = float(np.linalg.eigvalsh(chi)[0])
            assert min(min_psi,min_chi) > -3e-12
            item = {"dimension":dim, "r":r, "H_formula_error":herr,
                    "A_formula_error":aerr,
                    "H_norm_bound_slack":r*norm(h)-norm(hr),
                    "A_norm_bound_slack":r*r*norm(a)-norm(ar),
                    "psi_Gram_min_eigenvalue":min_psi,
                    "chi_Gram_min_eigenvalue":min_chi}
            if r == 1e-4:
                item["rescaled_response_to_log_derivative_error"] = norm(qr/r-dotk)
                assert norm(ar/r) <= r*norm(a)+3e-8
            out.append(item)
        for x in (0., 0.2, 2., 5.):
            for r,s in ((0.1,0.3),(0.5,0.5),(0.9,0.8)):
                assert abs(sinh_ratio(r*x,s)*sinh_ratio(x,r)
                           -sinh_ratio(x,r*s)) < 2e-15
            assert abs(sinh_ratio(x,.25)
                       -1/(4*math.cosh(x/4)*math.cosh(x/2))) < 2e-15
            assert abs(sinh_ratio(x/2,.25)**2
                       -1/(16*math.cosh(x/8)**2*math.cosh(x/4)**2)) < 2e-15
    return out


def obstruction_checks():
    prior = HERE/'verify_modular_obstructions.py'
    spec = importlib.util.spec_from_file_location('prior_obstructions', prior)
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return {
        "BS_family":[module.verify_bs(d,Fraction(1,q),Fraction(1,q))
                     for d in (2,3) for q in (10,100)],
        "CP_filter_blocks":[module.verify_cp_block(n,w,.07,.11)
                            for n in (4,16,64,256)
                            for w in (1.,float(n*n),math.exp(n/10))],
        "full_matrices":[module.full_matrix_block_check(n)
                         for n in (2,3,4,5)],
    }


def main():
    report = {
        "status":"all independent formula and obstruction checks passed",
        "scope":"Exact mathematical proofs establish all-r and all-size statements; numerical checks audit formulas only.",
        "fourier_checks":fourier_checks(),
        "matrix_checks":matrix_checks(),
        "prior_obstructions":obstruction_checks(),
        "spatial_locality_claim":False,
    }
    path = HERE/'power_response_and_obstructions_verified.json'
    path.write_text(json.dumps(report,indent=2)+'\n')
    print(json.dumps({"status":report["status"],
                      "fourier_checks":len(report["fourier_checks"]),
                      "matrix_checks":len(report["matrix_checks"]),
                      "prior_obstruction_checks":sum(map(len,report["prior_obstructions"].values())),
                      "report":str(path)},indent=2))


if __name__ == '__main__':
    main()
