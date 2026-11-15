#!/usr/bin/env python3
"""Exact algebra audits for microscopic moment repair and the H4 obstruction.

These finite computations verify the coherent repair frame, the Hesse
two-design identity, and the all-degree radial-order formula. They do not
replace the probabilistic and asymptotic proofs in the companion notes.
"""
from pathlib import Path
from fractions import Fraction
import json
import math
import sympy as sp

HERE=Path(__file__).resolve().parent
z=sp.symbols('z0:3')
b=sp.symbols('b0:3')
variables=z+b
eye3=sp.eye(3)
v=sp.Matrix([z[0]**2,z[1]**2,z[2]**2,
             sp.sqrt(2)*z[0]*z[1],sp.sqrt(2)*z[0]*z[2],sp.sqrt(2)*z[1]*z[2]])
vb=sp.Matrix([b[0]**2,b[1]**2,b[2]**2,
              sp.sqrt(2)*b[0]*b[1],sp.sqrt(2)*b[0]*b[2],sp.sqrt(2)*b[1]*b[2]])
P=sp.Matrix(z)*sp.Matrix(b).T
T=v*vb.T
W=sp.zeros(9,6)
for j in range(3): W[3*j+j,j]=1
for col,(i,j) in enumerate(((0,1),(0,2),(1,2)),3):
    W[3*i+j,col]=W[3*j+i,col]=1/sp.sqrt(2)
LP=W.T*(sp.kronecker_product(P,eye3)+sp.kronecker_product(eye3,P))*W
B=90*T-30*LP+5*sp.eye(6)

def haar(poly):
    total=sp.S(0)
    for exps, coefficient in sp.Poly(sp.expand(poly),*variables).terms():
        az,ab=exps[:3],exps[3:]
        if az==ab:
            total += coefficient*sp.Rational(
                2*math.prod(math.factorial(n) for n in az),
                math.factorial(sum(az)+2))
    return sp.simplify(total)

for i in range(6):
    for j in range(6):
        assert haar(B[j,i])==0
        for p in range(6):
            for q in range(6):
                actual=haar(B[j,i]*T[p,q])
                target=sp.Integer(p==i and q==j)-sp.Rational(int(i==j and p==q),6)
                assert actual==target,(i,j,p,q,actual,target)

omega=(-1+sp.sqrt(3)*sp.I)/2
points=[]
for r in range(3):
    points.extend([sp.Matrix([0,1,-omega**r])/sp.sqrt(2),
                   sp.Matrix([-omega**r,0,1])/sp.sqrt(2),
                   sp.Matrix([1,-omega**r,0])/sp.sqrt(2)])
moment=sp.zeros(6)
for point in points:
    symbol=v.subs(dict(zip(z,point)))
    moment += symbol*sp.conjugate(symbol).T/9
moment=moment.applyfunc(sp.simplify)
assert moment==sp.eye(6)/6

k=sp.symbols('k',positive=True,integer=True)
j=sp.symbols('j',integer=True)
J=9*sp.summation(j*(j+1),(j,0,k-2))+8*k*(k-1)+k*(k+1)
assert sp.simplify(J-(3*k**3-k))==0
N=(3*k+2)*(3*k+1)/2
energy_slope=sp.factor(2*J/(k*N))
assert sp.limit(energy_slope,k,sp.oo)==sp.Rational(4,3)
assert Fraction(3,2)*Fraction(8,3)==4


report={
    'status':'all exact algebra audits passed',
    'repair_mean_identities':36,
    'repair_frame_matrix_identities':1296,
    'Hesse_second_moment':'I_6/6 exactly',
    'radial_multiplicity':str(sp.factor(J)),
    'radial_energy_slope':str(energy_slope),
    'radial_energy_slope_limit':'4/3',
    'conditional_inverse_base':'(3/2)*(8/3)=4',
    'scope':'Exact finite algebra plus a symbolic all-degree identity; no numerical LDP claim.',
}
(HERE/'microscopic_repair_verified.json').write_text(json.dumps(report,indent=2)+'\n')
print(json.dumps(report,indent=2))
