"""Exact scalar checks used in Qutrit_Proof_Packet.

This is not a finite-sample verification of the universal contact conjecture.
The geometric and compactness arguments remain the written proofs.
"""
from pathlib import Path
import json
import sympy as s

root = Path(__file__).resolve().parent
r, x, beta = s.symbols("r x beta", positive=True)
M=s.Matrix([[251,-13,-13],[-13,20,-7],[-13,-7,20]])/3888
lower=s.factor(4*M.det()/s.trace(M)**2)
kappa=s.factor(lower/(s.Rational(19,12)))
assert lower==s.Rational(325,338724)
assert kappa==s.Rational(325,536313)
binary=s.integrate(6*x*(1-x),(x,1-1/s.sqrt(3),1))
assert s.simplify(binary-(1-2/(3*s.sqrt(3))))==0
half=s.integrate(2*(1-r)*(-s.Rational(5,36)+3*r/4),(r,0,s.Rational(3,7)))
half+=s.integrate(2*(1-r)*(s.Rational(11,18)-r),(r,s.Rational(3,7),1))
assert s.factor(half)==s.Rational(1,441)
S=2/beta*s.log(24/beta)
tail=s.simplify(6*(S+2)*s.exp(-beta*S))
assert s.simplify(tail-beta*(s.log(24/beta)+beta)/48)==0

# Energy-dilution review: the coefficient comparison is exactly 3(1-c)/2.
c=s.symbols("c")
assert s.simplify(((3-c)/2-c)-3*(1-c)/2)==0

report={
    "status":"Exact symbolic equalities verified; no numerical proof claims",
    "basis_Gram_lower_bound":str(lower),
    "kappa":str(kappa),
    "binary_tail_moment":str(s.simplify(binary)),
    "naive_qubit_support_loss":str(s.factor(half)),
    "Gaussian_tail_expression":str(tail),
    "energy_dilution_coefficient_difference":str(s.factor((3-c)/2-c))
}
(root/"exact_verification.json").write_text(json.dumps(report,indent=2)+"\n")
print(json.dumps(report,indent=2))
