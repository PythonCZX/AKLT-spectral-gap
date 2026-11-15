"""Exact identities for the full three-ray flagged-contact proof."""
from pathlib import Path
import json
import sympy as s

root=Path(__file__).resolve().parent
a,b,c,t=s.symbols("a b c t", real=True)
ca,cb,cg,sa,sb,sg=s.symbols("ca cb cg sa sb sg",real=True)
T=a*b*sa+b*c*sb+c*a*sg
w2=a*a+b*b+4*c*c+2*a*b*ca-4*b*c*cb-4*c*a*cg
v2=a*a+b*b-2*a*b*ca
D=s.expand(w2+t*t*v2+4*t*T-(a+b+2*c)**2)
f=lambda co,si:t*si-1-co
g=lambda co,si:4*t*si-2*(1-t*t)*(1-co)
expected=t*t*(a-b)**2+a*b*g(ca,sa)+4*c*(a*f(cg,sg)+b*f(cb,sb))
assert s.expand(D-expected)==0

# Deficits at the two endpoints of alpha, whose opposite pairs are bc and ca.
Di=t*t*(b-c)**2+b*c*g(cb,sb)+4*a*(b*f(ca,sa)+c*f(cg,sg))
Dj=t*t*(a-c)**2+a*c*g(cg,sg)+4*b*(a*f(ca,sa)+c*f(cb,sb))
h=lambda co,si:g(co,si)+4*f(co,si)
summed=t*t*((b-c)**2+(a-c)**2)+8*a*b*f(ca,sa)+a*c*h(cg,sg)+b*c*h(cb,sb)
assert s.expand(Di+Dj-summed)==0
hbound=s.factor(4*(t**4+3*t*t-2)/(1+t*t))
assert hbound.subs(t,s.Rational(3,4))==s.Rational(1,100)
Kl=s.Rational(19,162)+s.Rational(37,972)/s.Rational(22,7)
assert Kl==s.Rational(2767,21384)
tl=36*Kl/5
assert tl==s.Rational(2767,2970)>s.Rational(9,10)>s.Rational(3,4)

u=s.symbols("u",positive=True)
chord=s.Rational(101,216)-s.Rational(37,108)*u
assert chord.subs(u,s.Rational(1,2))==s.Rational(8,27)
assert chord.subs(u,1)==s.Rational(1,8)
A=s.pi/16
B=s.pi/32+s.Rational(1,24)
Il=s.simplify(s.Rational(2,3)*(A-(s.Rational(101,216)*A-s.Rational(37,108)*B)))
assert s.simplify(Il-(19*s.pi/648+s.Rational(37,3888)))==0
report={
  "status":"All symbolic identities and rational margins passed",
  "pair_deficit_identity":True,
  "endpoint_sum_identity":True,
  "middle_angle_margin":str(hbound.subs(t,s.Rational(3,4))),
  "I_lower_bound":str(Il),
  "K_rational_lower_bound":str(Kl),
  "available_geometric_coefficient_lower_bound":str(tl),
  "required_geometric_coefficient":"3/4",
  "coefficient_margin":str(tl-s.Rational(3,4))
}
(root/"three_ray_flag_exact_verification.json").write_text(json.dumps(report,indent=2)+"\n")
print(json.dumps(report,indent=2))
