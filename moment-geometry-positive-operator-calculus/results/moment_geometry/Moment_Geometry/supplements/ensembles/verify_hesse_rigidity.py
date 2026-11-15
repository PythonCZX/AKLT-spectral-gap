"""Exact symbolic verification of the Hesse rigidity matrix identities."""
from pathlib import Path
import json
import sympy as s

a = s.symbols("a0:3")
ac = s.symbols("ac0:3")
z = s.symbols("z0:3")
zc = s.symbols("zc0:3")
conjugate = dict(zip(a+ac+z+zc, ac+a+zc+z))
def adjoint(matrix):
    return matrix.T.xreplace(conjugate)
def matrix(v,w):
    return s.Matrix([
        [v[0]*w[0],v[1]*w[2],v[2]*w[1]],
        [v[2]*w[2],v[0]*w[1],v[1]*w[0]],
        [v[1]*w[1],v[2]*w[0],v[0]*w[2]],
    ])
def invariants(v,vc):
    norm = sum(v[i]*vc[i] for i in range(3))
    r = sum(v[i]**2*vc[i]**2 for i in range(3))-norm**2/2
    d = sum(v[i]**2*vc[(i+1)%3]*vc[(i+2)%3] for i in range(3))
    return norm,r,d
M = matrix(a,z)
B = M*adjoint(M)
na,ra,da = invariants(a,ac)
nz,rz,dz = invariants(z,zc)
det_expected = sum(x**3 for x in a)*s.prod(z)-s.prod(a)*sum(x**3 for x in z)
kernel_expected = 4*ra*rz+4*(da*dz.xreplace(conjugate)+da.xreplace(conjugate)*dz)
checks = {
    "Moore_determinant_identity": s.expand(M.det()-det_expected)==0,
    "Frobenius_trace_identity": s.expand(s.trace(B)-na*nz)==0,
    "acute_kernel_identity": s.expand(
        2*s.trace(B*B)-s.trace(B)**2-kernel_expected)==0,
}

omega = -s.Rational(1,2)+s.I*s.sqrt(3)/2
points = []
for omitted in range(3):
    occupied = [i for i in range(3) if i!=omitted]
    for j in range(3):
        zz = [s.Integer(0)]*3
        zz[occupied[0]] = 1/s.sqrt(2)
        zz[occupied[1]] = -omega**j/s.sqrt(2)
        points.append(s.Matrix(zz))
overlaps = [s.simplify((u.conjugate().T*v)[0]*
                      (v.conjugate().T*u)[0])
            for i,u in enumerate(points) for j,v in enumerate(points) if i<j]
checks["all_36_SIC_overlaps_equal_one_quarter"] = all(x==s.Rational(1,4) for x in overlaps)
def qvector(zz):
    x,y,w = zz
    return s.Matrix([x*x,y*y,w*w,s.sqrt(2)*x*y,s.sqrt(2)*x*w,s.sqrt(2)*y*w])
qpoints = [qvector(zz) for zz in points]
moment = sum((q*q.conjugate().T for q in qpoints),s.zeros(6))/9
checks["uniform_Hesse_measure_exact_second_design"] = all(
    s.simplify(x)==0 for x in moment-s.eye(6)/6)
p0,p1,p2 = s.symbols("p0 p1 p2")
heron = 2*(p0*p1+p1*p2+p2*p0)-(p0*p0+p1*p1+p2*p2)
checks["Heron_identity"] = s.expand(
    heron-((p0+p1+p2)**2-2*(p0*p0+p1*p1+p2*p2)))==0
b0,b1 = s.symbols("b0 b1")
b2 = -b0-b1
checks["degenerate_triangle_cubic_identity"] = s.expand(
    b0**3+b1**3+b2**3-3*b0*b1*b2)==0
assert all(checks.values()), checks
record = {"all_exact_checks_pass": True, **checks,
          "scope":"Algebraic identities and SIC moment; measure-theoretic implication is proved in the companion note."}
Path(__file__).with_name("hesse_rigidity_verified.json").write_text(
    json.dumps(record,indent=2)+"\n")
print(json.dumps(record,indent=2))

