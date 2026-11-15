"""From finite ferromagnetic magnetization cumulants to CP Gamma rules.

This is an operator-computational extraction of classical Lee--Yang,
Schoenberg and van Dantzig theory; those scalar connections are not new.
The exact moment compiler avoids finding the partition-function zeros.
Its current Ising input enumerator costs O(2**n * |E|), and is not a
general efficient partition-function algorithm.
"""
from fractions import Fraction as F
from math import factorial
from pathlib import Path
from itertools import product
from collections import defaultdict
import json
import argparse
import numpy as np

from finite_arithmetic_certificate import isolate_moment_rule


def magnetization_distribution(n,edges,q=F(2)):
    """Zero-field Ising distribution with q=exp(2J)>=1.

    A configuration has weight q**(number of agreeing edges), which
    differs from exp(J sum sigma_i sigma_j) by a common normalizer.
    """
    assert q>=1
    raw=defaultdict(F)
    for sigma in product([-1,1],repeat=n):
        agreements=sum(sigma[i]==sigma[j] for i,j in edges)
        raw[F(sum(sigma),n)]+=q**agreements
    total=sum(raw.values())
    return {m:w/total for m,w in sorted(raw.items())}


def thorinary_moments(distribution,maximum):
    """Recover zero power sums exactly from magnetization cumulants.

    log E exp(xM)=sum_{k>=1} ell_k x**(2k), and
    m_k=(-1)**(k+1)*k*ell_k.  Positivity is supplied by Lee--Yang.
    """
    a=[F(1)]+[sum(p*m**(2*k) for m,p in distribution.items())/factorial(2*k)
               for k in range(1,maximum+1)]
    ell=[F(0)]
    for n in range(1,maximum+1):
        ell.append(a[n]-sum((k*ell[k]*a[n-k] for k in range(1,n)),F(0))/n)
    return [None]+[(-1)**(k+1)*k*ell[k] for k in range(1,maximum+1)]


def midpoint(interval):return float((interval[0]+interval[1])/2)
def rule_value(rule,x):
    exponent=midpoint(rule['drift'])*x*x
    for c,a in zip(rule['nodes'],rule['shapes']):
        exponent+=midpoint(a)*np.log1p(midpoint(c)*x*x)
    return np.exp(-exponent)


def exact_counterexample():
    # Two antiferromagnetic spins: P(M=1)=P(M=-1)=1/20,
    # P(M=0)=9/10.  The corresponding power mixture is operator monotone,
    # but its inverse modular kernel is not CP on a three-level register.
    # At h=log2, cosh h=5/4, cosh2h=17/8, so all entries are rational.
    c1=F(40,41);c2=F(80,89)
    C=[[F(1),c1,c2],[c1,F(1),c1],[c2,c1,F(1)]]
    v=[1,-2,1]
    witness=sum(v[i]*C[i][j]*v[j] for i in range(3) for j in range(3))
    assert witness==F(-26,3649)
    return dict(distribution={'-1':'1/20','0':'9/10','1':'1/20'},
                representing_mean='(t^0+t^1)/20 + 9*t^(1/2)/10',
                log_rho_eigenvalues_up_to_scalar=['-2*log(2)','0','2*log(2)'],
                modular_half_generator_eigenvalues=['-log(2)','0','log(2)'],
                kernel=[[str(x) for x in row] for row in C],
                rational_witness_vector=v,quadratic_form=str(witness),
                conclusion='A valid power-mixture Petz metric need not have a CP relative-score filter. The Lee--Yang condition supplies additional content.')


def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--exact-only",action="store_true",
                        help="Skip frequency-grid diagnostics; retain exact isolation.")
    args=parser.parse_args()
    n=8
    graphs={'path':[(i,i+1) for i in range(n-1)],
            'cycle':[(i,(i+1)%n) for i in range(n)],
            'complete':[(i,j) for i in range(n) for j in range(i+1,n)]}
    rows=[]
    for name,edges in graphs.items():
        for q in [F(1),F(2),F(5)]:
            law=magnetization_distribution(n,edges,q)
            moments=thorinary_moments(law,11)
            assert all(v>0 for v in moments[1:])
            xgrid=np.linspace(0,8,161)
            exact=(np.array([1/sum(float(p)*np.cosh(float(m)*x)
                                  for m,p in law.items()) for x in xgrid])
                   if not args.exact_only else None)
            records=[]
            for r in range(1,5):
                lower=isolate_moment_rule(moments,r,'radau')
                upper=isolate_moment_rule(moments,r,'gauss')
                lv=uv=None
                if not args.exact_only:
                    lv=rule_value(lower,xgrid);uv=rule_value(upper,xgrid)
                    assert np.min(exact-lv)>-1e-12
                    assert np.min(uv-exact)>-1e-12
                records.append(dict(order=r,
                                    max_bracket_width=float(max(uv-lv)) if lv is not None else None,
                                    error_at_x4=(float(rule_value(upper,4)-1/sum(float(p)*np.cosh(float(m)*4) for m,p in law.items()))
                                                 if not args.exact_only else None),
                                    gauss_error_coefficient=str(upper['coefficient']),
                                    radau_error_coefficient=str(lower['coefficient']),
                                    nodes_positive=True,weights_positive=True,
                                    exact_rational_root_isolation=True))
            rows.append(dict(graph=name,spins=n,q=str(q),
                             variance=str(2*moments[1]),
                             first_four_zero_power_sums=[str(v) for v in moments[1:5]],
                             distribution={str(m):str(p) for m,p in law.items()},
                             rules=records))
    result=dict(ferromagnets=rows,antiferromagnetic_adverse_control=exact_counterexample(),
                floating_frequency_grid_run=not args.exact_only,
                known_scalar_sources=['Lee and Yang1952; Schoenberg1951',
                    'Konstantopoulos, Patie and Sarkar2024, DOI10.5802/aif.3600'],
                scope='Lee--Yang supplies global positive divisibility. Exact rational moments and Sturm isolation certify rule parameters/error constants. Frequency-grid comparisons are numerical diagnostics, not proof of global positivity. Input enumeration is exponential.')
    p=Path(__file__).with_suffix('.json');p.write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps(dict(output=str(p),models=len(rows),
                          selected=rows[4],adverse=result['antiferromagnetic_adverse_control']),indent=2))


if __name__=='__main__':main()
