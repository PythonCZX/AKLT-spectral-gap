#!/usr/bin/env python3
"""Exact algebra checks and separately labeled numerical probes for the Hesse certificate."""
from __future__ import annotations
import argparse
import itertools
import json
import math
from pathlib import Path

import numpy as np
import sympy as sp


def simplify_matrix(m):
    return m.applyfunc(sp.simplify)


def occupation(k):
    return [(a, b, k-a-b) for a in range(k, -1, -1)
            for b in range(k-a, -1, -1)]


def coherent(z, k):
    return sp.Matrix([
        sp.sqrt(sp.factorial(k) / sp.prod(sp.factorial(e) for e in alpha))
        * sp.prod(z[j]**alpha[j] for j in range(3))
        for alpha in occupation(k)
    ])


def exact_checks():
    omega = (-1 + sp.I*sp.sqrt(3))/2
    H = [sp.Matrix(v)/sp.sqrt(2) for v in
         [(0,1,-omega**j) for j in range(3)]
         + [(1,0,-omega**j) for j in range(3)]
         + [(1,-omega**j,0) for j in range(3)]]
    columns = {k: sp.Matrix.hstack(*(coherent(z,k) for z in H)) for k in (1,2,3,4)}
    moments = {k: simplify_matrix(v*v.conjugate().T/9) for k,v in columns.items()}
    occ3=occupation(3)
    f=sp.zeros(10,1)
    for j,alpha in enumerate(occ3):
        if 3 in alpha:
            f[j]=1/sp.sqrt(3)
    t=sp.zeros(10,1); t[occ3.index((1,1,1))]=1
    Q=f*f.T+t*t.T
    W=sp.diag(*[sp.Rational(1,2)-sp.Rational(sum(n*(n-1) for n in alpha),6) for alpha in occ3])
    W+=3*f*f.T
    results={}
    def check(name,condition):
        value=bool(condition)
        results[name]=value
        if not value:
            raise AssertionError(name)
    check("M1_is_I3_over_3", moments[1]==sp.eye(3)/3)
    check("M2_is_I6_over_6", moments[2]==sp.eye(6)/6)
    check("Q_is_rank_two_projector", Q*Q==Q and Q.rank()==2)
    check("M3_is_IminusQ_over_8", simplify_matrix(moments[3]-(sp.eye(10)-Q)/8)==sp.zeros(10))
    check("fourth_moment_rank_nine", moments[4].rank()==9)
    gram=simplify_matrix(columns[3].conjugate().T*columns[3])
    projector_gram=gram.applyfunc(lambda x:sp.simplify(x*sp.conjugate(x)))
    check("third_projector_gram", projector_gram==(63*sp.eye(9)+sp.ones(9))/64)
    check("third_vector_frame_rank_eight",gram.rank()==8)
    check("witness_spectrum", W.eigenvals()=={sp.Rational(-1,2):2,sp.Rational(1,6):6,
                                            sp.Rational(1,2):1,sp.Rational(5,2):1})
    # Formal homogeneous symbol, using independent conjugate variables.
    z=sp.symbols("z0:3")
    zb=sp.symbols("zb0:3")
    v=coherent(z,3); vb=coherent(zb,3)
    p=[z[j]*zb[j] for j in range(3)]
    n=sum(p); F=sum(zz**3 for zz in z); Fb=sum(zz**3 for zz in zb)
    check("witness_symbol",sp.expand((vb.T*W*v)[0]-(n**3/2-n*sum(x*x for x in p)+F*Fb))==0)
    check("projector_symbol",sp.expand((vb.T*Q*v)[0]-(F*Fb/3+6*sp.prod(p)))==0)
    tt,y,a,c,u=sp.symbols("t y a c u",real=True)
    check("binary_cubic_factorization",
          sp.expand(1-sp.Rational(3,4)*tt**2-y**3+sp.Rational(3,4)*tt**2*y
                    -(1-y)*(1+y+y*y-sp.Rational(3,4)*tt**2))==0)
    check("binary_nonnegative_remainder",
          sp.expand(y+y*y-sp.Rational(3,4)*tt**2
                    -(y-tt/2)*(y+tt/2+1)-tt*(1-tt)/2)==0)
    check("large_coordinate_projector_constant",
          sp.expand(9*(2*a-1)**2-(3-a)-(4*a-3)*(9*a-2))==0)
    check("small_coordinate_h_identity",
          sp.expand(c-2*c*c-2*u*c+2*u*u-(c-sp.Rational(5,2)*c*c+2*(u-c/2)**2))==0)
    check("small_coordinate_h_margin",
          sp.expand(c-sp.Rational(5,2)*c*c-c/3
                    -(c/24+sp.Rational(5,2)*c*(sp.Rational(1,4)-c)))==0)
    check("small_coordinate_projector_margin",
          sp.Rational(27,4)*6-sp.Rational(40,3)==sp.Rational(163,6))
    check("h_distance_constant",
          sp.Rational(11,8)*3+sp.Rational(27,16)*2==sp.Rational(15,2))
    check("SIC_tomography_constant",16*sp.Rational(3,4)==12)
    results["moment_ranks"]={str(k):moments[k].rank() for k in (1,2,3,4)}
    results["witness_spectrum_exact"]={str(k):v for k,v in W.eigenvals().items()}
    results["Q_occupation_basis"]=[list(x) for x in occ3]
    results["Q_matrix"]=[[str(Q[i,j]) for j in range(10)] for i in range(10)]
    return results


def numerical_probes(samples,seed):
    rng=np.random.default_rng(seed)
    omega=np.exp(2j*np.pi/3)
    H=np.array([(0,1,-omega**j) for j in range(3)]
               +[(1,0,-omega**j) for j in range(3)]
               +[(1,-omega**j,0) for j in range(3)],complex)/np.sqrt(2)
    z=rng.normal(size=(samples,3))+1j*rng.normal(size=(samples,3))
    z/=np.linalg.norm(z,axis=1,keepdims=True)
    p=abs(z)**2
    f2=abs(np.sum(z**3,axis=1))**2
    h=.5-np.sum(p*p,axis=1)+f2
    q=f2/3+6*np.prod(p,axis=1)
    d2=1-np.max(abs(z@H.conj().T)**2,axis=1)
    margins={
        "h_nonnegative":float(np.min(h)),
        "twice_h_minus_F_squared":float(np.min(2*h-f2)),
        "three_h_minus_min_probability":float(np.min(3*h-np.min(p,axis=1))),
        "15h_over_2_minus_distance_squared":float(np.min(7.5*h-d2)),
        "27q_over_4_minus_distance_squared":float(np.min(6.75*q-d2)),
    }
    if any(v < -1e-11 for v in margins.values()):
        raise AssertionError(margins)
    # Also check noisy finite ensembles and solve their actual W1 transport.
    from scipy.optimize import linprog
    cases=[]
    for perturb in (0.0,0.002,0.02,0.1,0.3):
        noise=rng.normal(size=H.shape)+1j*rng.normal(size=H.shape)
        Z=H+perturb*noise
        Z/=np.linalg.norm(Z,axis=1,keepdims=True)
        weights=np.ones(9)/9
        if perturb:
            weights=rng.dirichlet(np.full(9,1/(perturb*perturb)))
        prob=abs(Z)**2
        qv=abs(np.sum(Z**3,axis=1))**2/3+6*np.prod(prob,axis=1)
        eps=float(weights@qv)
        M1=(Z.T*weights)@Z.conj()
        delta=float(np.linalg.norm(M1-np.eye(3)/3))
        # The projector difference avoids square-root amplification of
        # inner-product roundoff when two rays coincide exactly.
        PZ=np.einsum('ia,ib->iab',Z,Z.conj())
        PH=np.einsum('ia,ib->iab',H,H.conj())
        dist=np.linalg.norm(PZ[:,None]-PH[None,:],axis=(2,3))/np.sqrt(2)
        Aeq=np.zeros((18,81))
        for i in range(9):
            Aeq[i,9*i:9*i+9]=1
        for j in range(9):
            Aeq[9+j,j::9]=1
        lp=linprog(dist.ravel(),A_eq=Aeq,b_eq=np.r_[weights,np.ones(9)/9],
                   bounds=(0,None),method="highs")
        if not lp.success:
            raise RuntimeError(lp.message)
        bound=(1+3/np.sqrt(2))*np.sqrt(27*eps/4)+1.5*delta
        if lp.fun>bound+1e-7:
            raise AssertionError((lp.fun,bound))
        cases.append({"perturbation":perturb,"Q_probability":eps,"M1_HS_error":delta,
                      "actual_discrete_W1":float(lp.fun),"theorem_bound":float(min(1,bound))})
    return {"status":"diagnostic_only_not_a_proof","seed":seed,"samples":samples,
            "minimum_margins":margins,"max_observed_d2_over_h":float(np.max(d2/h)),
            "max_observed_d2_over_q":float(np.max(d2/q)),"transport_checks":cases}


def main():
    ap=argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--exact-only",action="store_true",
                    help="Skip every floating diagnostic.")
    ap.add_argument("--samples",type=int,default=0,
                    help="Explicitly enable this many random-ray diagnostic samples.")
    ap.add_argument("--seed",type=int,default=20261115)
    ap.add_argument("--output",type=Path,default=Path(__file__).with_name("hesse_ensemble_certification_verified.json"))
    args=ap.parse_args()
    if args.samples < 0:
        ap.error("--samples must be nonnegative")
    run_samples = args.samples if not args.exact_only else 0
    result={"exact":exact_checks(),
            "numerical":numerical_probes(run_samples,args.seed) if run_samples else
                        {"status":"not_run","samples":0,"seed":args.seed}}
    args.output.write_text(json.dumps(result,indent=2)+"\n")
    print(json.dumps({"exact_checks_passed":sum(v is True for v in result["exact"].values()),
                      "numerical_minimum_margins":result["numerical"].get("minimum_margins"),
                      "output":str(args.output)},indent=2))


if __name__=="__main__":
    main()

