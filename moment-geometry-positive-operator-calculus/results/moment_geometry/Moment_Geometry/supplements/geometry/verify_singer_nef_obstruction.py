"""Exact audit of the Singer ten-point nef-coupling obstruction."""
from fractions import Fraction as F
from pathlib import Path
import json
import sympy as s

x,y,z,t=s.symbols("x y z t")
polys=[x**3-y*z**2,y**3-x**2*z,z**3-x*y**2]
G=x*x*y+x*x*z+x*y*y+y*y*z+x*z*z+y*z*z+x*y*z
chars=[0,2,6,1,3,4]
assert len(set(chars))==6
amp2=[s.Rational(1,9)]*3+[s.Rational(2,9)]*3
M=s.diag(*[s.Rational(3,4)*a+(s.Rational(1,12) if i<3 else 0)
            for i,a in enumerate(amp2)])
assert M==s.eye(6)/6
for f in polys:
    assert s.rem(s.expand(f.subs({x:1,y:t,z:t**3})),t**7-1,t)==0
basis=[{x:1,y:0,z:0},{x:0,y:1,z:0},{x:0,y:0,z:1}]
cusps=[1,2,0]
for i,f in enumerate(polys):
    assert f.subs(basis[i])==1
    for j in range(3):
        if j!=i: assert f.subs(basis[j])==0
    assert all(s.diff(f,v).subs(basis[cusps[i]])==0 for v in [x,y,z])
assert s.rem(s.expand(G.subs({x:1,y:t,z:t**3})),t**7-1,t)==sum(t**i for i in range(7))
smooth=[]
for name,f in [("torus_omission_cubic",G),("basis_pencil_member",polys[1]+polys[2])]:
    grads=[s.diff(f,v) for v in [x,y,z]]
    for v in [x,y,z]:
        other=[w for w in [x,y,z] if w!=v]
        gb=s.groebner([h.subs(v,1) for h in grads],*other,domain=s.QQ)
        assert list(gb)==[1],(name,str(v),gb)
        smooth.append([name,str(v),"unit gradient ideal"])
# Divisor classes dH - sum multiplicities E.
classes=[
    [3,0,2,1]+[1]*7,
    [3,1,0,2]+[1]*7,
    [3,2,1,0]+[1]*7]
intersection=lambda a,b:a[0]*b[0]-sum(u*v for u,v in zip(a[1:],b[1:]))
gram=[[intersection(a,b) for b in classes] for a in classes]
assert gram==[[-3,0,0],[0,-3,0],[0,0,-3]]
assert [sum(c[j] for c in classes) for j in range(11)]==[9]+[3]*10
# Threshold mixture.
t0=F(20,21); wa=F(4,7); wb=F(3,7)
basis_marginal=(wa+wb/F(3))/9
torus_marginal=(wa*F(6,7)+wb)/9
haar_marginal=wb/9
assert basis_marginal==t0/F(12)
assert torus_marginal==t0*F(3,28)
assert haar_marginal==1-t0
assert F(27,4)*t0==6+9*(1-t0)
record={
    "exact_second_moment":str(M),
    "symmetric_square_characters_mod_7":chars,
    "cuspidal_cubics":[str(f) for f in polys],
    "torus_omission_cubic":str(G),
    "smooth_chart_checks":smooth,
    "cubic_intersection_matrix":gram,
    "haar_dilution_threshold":str(1-t0),
    "boundary_mixture_weights":[str(wa),str(wb)],
    "boundary_marginals":{"each_basis":str(basis_marginal),
                          "each_torus":str(torus_marginal),
                          "haar":str(haar_marginal)},
    "distinct_coupling_bad_mass":str(F(3,4)),
    "arbitrary_coupling_minimum_bad_mass":str(F(1,4)),
    "status":"all exact checks passed"}
out=Path(__file__).with_name("singer_nef_obstruction_exact.json")
out.write_text(json.dumps(record,indent=2)+"\n")
print(json.dumps(record,indent=2))

