"""Exact algebra checks for the four-ray flagged contact theorem.

These checks supplement the geometric and calculus proofs in
Four_Ray_Flag_Closure.md. They do not replace those arguments.
"""
from pathlib import Path
import json
import sympy as S

ROOT = Path(__file__).resolve().parent
a, b, c, t, p = S.symbols("a b c t p", real=True)
h, s, edge, r = S.symbols("h s edge r", real=True)
z, kap = S.symbols("z kap", positive=True)
out = {}

def zero(name, expression):
    value = S.factor(expression)
    assert value == 0, (name, value)
    out[name] = True

# Adjacent-facet distance inequality before division by positive factors.
lhs = (s*edge + h*r)**2 - h**2*((s+h)**2+(r-edge)**2)
rhs = (s+h)*((s-h)*edge**2+2*h*edge*r-h**2*(s+h))
zero("adjacent_facet_squared_identity", lhs-rhs)

# Vertical contribution to the lifted deficit.
A = a+b+2*c
vertical = (a+b-2*c)**2+t**2*(a-b)**2-A**2
zero("lifted_vertical_deficit", vertical-(t**2*(a-b)**2-8*c*(a+b)))

# Pair the two deficits at the endpoints of the unique large gap.
fa, fb, fc, ga, gb, gc = S.symbols("fa fb fc ga gb gc")
Di = t**2*(b-c)**2+b*c*gb+4*a*(b*(fa-2*p)+c*(fc-2*p))
Dj = t**2*(a-c)**2+a*c*gc+4*b*(a*(fa-2*p)+c*(fb-2*p))
summed = (t**2*((a-c)**2+(b-c)**2)
          +8*a*b*(fa-2*p)+a*c*(gc+4*fc-8*p)
          +b*c*(gb+4*fb-8*p))
zero("paired_deficit_identity", Di+Dj-summed)

lower = S.Rational(81,100)*((a-c)**2+(b-c)**2)-a*b/25+c*(a+b)/25
sos = S.Rational(79,200)*(a+b-2*c)**2+S.Rational(83,200)*(a-b)**2+c**2/25
zero("final_sum_of_squares", lower-sos)

# Derivative of q(z), after using kappa'= (1-2z)/(2kappa).
q = z+(1-z)/(1+2*kap)
dq = S.diff(q,z)+S.diff(q,kap)*(1-2*z)/(2*kap)
N = (1-z)*(4*z-1)+4*kap**3
num = S.together(dq-N/(kap*(1+2*kap)**2))
zero("q_derivative_sign_identity", S.factor(num).subs(kap**2,z*(1-z)))
dN = S.diff(N,z)+S.diff(N,kap)*(1-2*z)/(2*kap)
zero("N_derivative", dN-(5-8*z+6*kap*(1-2*z)))

# Purely rational comparisons used in the calculus argument.
assert S.Rational(1,100)+S.Rational(99,118) < S.Rational(17,20)
assert S.Rational(2,3) < S.Rational(17,20)
assert S.Rational(81,100)*S.Rational(15,16) > S.Rational(17,20)**2
assert S.Rational(81,100)*S.Rational(3,4) > S.Rational(3,4)**2
assert S.Rational(10009,5000000) < S.Rational(1,200)
assert S.Rational(9,10)**2 > S.Rational(3,4)
assert 388800 > 388129
out["coefficient_comparisons"] = True

# Middle-gap coefficient subtraction with sines and cosines as formal variables.
sn, cs = S.symbols("sn cs")
tt=S.Rational(9,10)
H=8*tt*sn-2*(3-tt**2)-2*(1+tt**2)*cs
upper_p=(S.sqrt(3)*sn-1-cs)/4
middle=(S.Rational(36,5)-2*S.sqrt(3))*sn-S.Rational(119,50)-S.Rational(81,50)*cs
zero("middle_gap_coefficient", H-8*upper_p-middle)
endpoint=S.simplify(middle.subs({sn:S.sqrt(3)/2,cs:S.Rational(1,2)}))
zero("middle_gap_endpoint", endpoint-(18*S.sqrt(3)/5-S.Rational(619,100)))
assert S.sign(endpoint-S.Rational(1,25)) == 1
out["middle_gap_strict_margin"] = str(endpoint-S.Rational(1,25))

# Optional polynomial form of the two-large-gap monotonicity certificate.
x=S.symbols("x")
zero("two_large_gap_polynomial",
     2*(3-x)*(3-2*x)**2-(3*x+x**3)
     -3*(1-x)*(3*x**2-13*x+18))
out["two_large_gap_quadratic_discriminant"] = 169-216
assert 169-216 < 0

# Certified available assignment coefficient.
K=S.Rational(19,162)+S.Rational(37,972)*S.Rational(7,22)
zero("radial_K_rational_bound", K-S.Rational(2767,21384))
available=36*K/5
assert available > S.Rational(9,10)
out["available_t_lower_bound"] = str(available)
out["margin_above_nine_tenths"] = str(available-S.Rational(9,10))
out["all_checks_passed"] = True
out["scope"] = "Exact algebra only; geometric signs and analytic inequalities are proved in the companion note."
path=ROOT/"four_ray_flag_exact_verification.json"
path.write_text(json.dumps(out,indent=2)+"\n")
print(json.dumps(out,indent=2))

