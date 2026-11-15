"""Exact quadrature isolation, rounding budgets, and a local order chooser.

The certificate uses rational moments, rational Sturm root intervals, and
rational interval arithmetic.  Its conclusions therefore do not depend on
the floating-point Jacobi eigensolver in positive_bessel_filters.py.
Arb is used only for the final two-eigenvalue Fisher example.
"""
from fractions import Fraction as F
from pathlib import Path
import json
import argparse
from functools import lru_cache
import sympy as sp

from positive_bessel_filters import rayleigh_moments, inner, build_rule
from local_commutator_certificate import certificate


def add(a,b):return a[0]+b[0],a[1]+b[1]
def neg(a):return -a[1],-a[0]
def sub(a,b):return add(a,neg(b))
def mul(a,b):
    p=[x*y for x in a for y in b]
    return min(p),max(p)
def div(a,b):
    assert b[0]*b[1]>0
    return mul(a,(1/b[1],1/b[0]))
def const(a):return F(a),F(a)
def interval_poly(coeffs,x):
    out=const(0)
    for c in coeffs[::-1]:out=add(mul(out,x),const(c))
    return out
def max_distance(interval,number):
    return max(abs(interval[0]-number),abs(interval[1]-number))
def frac_from_sympy(x):return F(int(sp.numer(x)),int(sp.denom(x)))


def monic_orthogonal(moments,order):
    polys=[[F(1)]];norms=[moments[0]]
    for n in range(order):
        p=polys[-1];h=norms[-1]
        a=inner([F(0)]+p,p,moments)/h
        b=F(0) if n==0 else h/norms[-2]
        nxt=[F(0)]*(len(p)+1)
        for j,x in enumerate(p):nxt[j+1]+=x;nxt[j]-=a*x
        if n:
            for j,x in enumerate(polys[-2]):nxt[j]-=b*x
        hn=inner(nxt,nxt,moments)
        assert hn>0
        for k in range(n+1):
            assert inner(nxt,[F(0)]*k+[F(1)],moments)==0
        polys.append(nxt);norms.append(hn)
    return polys,norms


@lru_cache(maxsize=None)
def isolate_rule(nu=F(1,2),order=2,kind='gauss',digits=55):
    """Return exact rational enclosing intervals for an ideal Gaussian rule."""
    assert isinstance(nu,F) and nu>-1
    assert kind in ['gauss','radau'] and order>=0
    assert kind=='radau' or order>0
    m=rayleigh_moments(nu,2*order+3)
    out=isolate_moment_rule(m,order,kind,digits)
    out['nu']=nu
    return out


def isolate_moment_rule(m,order=2,kind='gauss',digits=55):
    """Compile any supplied exact positive Thorin power-sum sequence.

    m[j]=sum lambda_k**j, j>=1.  A theorem about the input source must
    establish positivity of its underlying measure; finite moment checks
    alone do not establish a global Lee--Yang property.
    """
    assert kind in ['gauss','radau'] and order>=0
    assert kind=='radau' or order>0
    moments=m[1:] if kind=='gauss' else m[2:]
    polys,norms=monic_orthogonal(moments,order)
    nodes=[];weights=[];shapes=[]
    if order:
        x=sp.Symbol('x');p=polys[-1]
        poly=sp.Poly(sum(sp.Rational(c.numerator,c.denominator)*x**j
                         for j,c in enumerate(p)),x)
        roots=sp.polys.polytools.intervals(poly,eps=sp.Rational(1,10**digits))
        assert sum(mult for _,mult in roots)==order
        dp=[j*p[j] for j in range(1,len(p))]
        for (lohi,mult) in roots:
            assert mult==1
            c=tuple(frac_from_sympy(z) for z in lohi)
            assert c[0]>0
            denom=mul(interval_poly(dp,c),interval_poly(polys[-2],c))
            w=div(const(norms[-2]),denom)
            assert w[0]>0
            if kind=='radau':w=div(w,c)
            nodes.append(c);weights.append(w);shapes.append(div(w,c))
    drift=const(0)
    if kind=='radau':
        drift=const(m[1])
        for w in weights:drift=sub(drift,w)
        assert drift[0]>0
    power=2*order+1 if kind=='gauss' else 2*order+2
    return dict(order=order,kind=kind,nodes=nodes,weights=weights,
                shapes=shapes,drift=drift,coefficient=norms[-1]/power,
                derivative_order=2*power,root_interval_digits=digits)


def rounding_certificate(ideal,rounded):
    """d controls generator rounding by d*||ad_K^2(A)||.

    This certifies the actual binary64 scales/shapes/drift supplied to a
    sampler as exact dyadic parameters.  PRNG/statistical errors and the
    numerical error of Hamiltonian simulation are separate budgets.
    """
    assert rounded.head==0
    d=max_distance(ideal['drift'],F.from_float(rounded.drift))
    for c,a,cf,af in zip(ideal['nodes'],ideal['shapes'],rounded.scales,rounded.shapes):
        cc=F.from_float(float(cf));aa=F.from_float(float(af))
        assert cc>0 and aa>0
        d+=max_distance(a,aa)*c[1]+aa*max_distance(c,cc)
    return d


@lru_cache(maxsize=None)
def _local_certificate(spins,max_derivative):
    return certificate(spins,max_derivative)


def order_chooser(spins=32,max_derivative=14,nu=F(1,2),beta=F(1),
                  tolerance=F(1,10**6),tau=F(1)):
    """Choose the cheapest certified candidate, or explicitly return failure.

    Cost orders Gamma draws first, then local derivative degree.  This is
    a classical sampling-cost proxy, not a Hamiltonian-simulation runtime.
    The finite budget prevents claims of arbitrary-temperature efficiency.
    """
    local={r['derivative_order']:r for r in _local_certificate(spins,max_derivative)}
    candidates=[]
    for order in range((max_derivative-2)//4+1):
        for kind in ['gauss','radau']:
            degree=4*order+(2 if kind=='gauss' else 4)
            if degree>max_derivative or (order==0 and kind=='gauss'):continue
            ideal=isolate_rule(nu,order,kind)
            rule=build_rule(float(nu),order,kind)
            derivative=F(local[degree]['exact_operator_norm_upper_bound'])*beta**degree
            d2=F(local[2]['exact_operator_norm_upper_bound'])*beta**2
            rounding=rounding_certificate(ideal,rule)
            bound=tau*(ideal['coefficient']*derivative+rounding*d2)
            candidates.append(dict(kind=kind,order=order,gamma_draws=order,
                                   derivative_order=degree,
                                   pauli_terms=local[degree]['pauli_terms'],
                                   support_sites=local[degree]['support_sites'],
                                   bound=float(bound),bound_exact=str(bound),
                                   rounding_generator_budget=float(rounding),
                                   certified=bound<=tolerance))
    passing=[r for r in candidates if r['certified']]
    selected=min(passing,key=lambda r:(r['gamma_draws'],r['derivative_order'])) if passing else None
    return dict(spins=spins,beta=str(beta),tau=str(tau),nu=str(nu),
                tolerance=str(tolerance),max_derivative=max_derivative,
                selected=selected,status='certified' if selected else 'budget not certified',
                candidates=candidates)


def arb_scalar_example(max_order=8):
    """Certified fixed-state Fisher intervals for the depolarized Slater line.

    The supplied pure-state QFI is 12/(1+3*zeta^2)^2 at zeta=1/3.
    Only that analytic tangent norm is required; no 84x84 matrices are built.
    """
    from flint import arb,ctx
    ctx.prec=230
    def arbf(q):return arb(q.numerator)/arb(q.denominator)
    def arbi(v):return arbf(v[0]).union(arbf(v[1]))
    def scalar_filter(q,x):
        s=x*x;g=arbi(q['drift'])*s
        for c,a in zip(q['nodes'],q['shapes']):
            g+=arbi(a)*(1+arbi(c)*s).log()
        return (-g).exp()
    a=F(757,840);b=F(1,840);c=a-b;pure=F(27,4)
    x=arb(757).log()/2
    # g_nu = c^2 QFI_pure/(2 sqrt(a*b))*phi_nu(log(a/b)/2).
    prefactor=arbf(c*c*pure/2)/arbf(a*b).sqrt()
    exact_sld=arbf(c*c*pure/(a+b))
    exact_bkm=arbf(c*pure/2)*arb(757).log()
    out=[]
    for nu,name,exact in [(F(-1,2),'SLD',exact_sld),(F(1,2),'BKM',exact_bkm)]:
        for r in range(1,max_order+1):
            lo=prefactor*scalar_filter(isolate_rule(nu,r,'radau'),x)
            hi=prefactor*scalar_filter(isolate_rule(nu,r,'gauss'),x)
            assert lo.upper()<exact.lower()
            assert hi.lower()>exact.upper()
            out.append(dict(metric=name,order=r,
                            lower_endpoint=lo.lower().str(35,radius=False),
                            upper_endpoint=hi.upper().str(35,radius=False),
                            exact_metric_ball=exact.str(45),
                            bracket_width_upper=(hi.upper()-lo.lower()).upper().str(12,radius=False)))
    return dict(dimension=84,depolarization='1/10',zeta='1/3',
                eigenvalues=[str(a),str(b)],eigenvalue_ratio=757,
                pure_QFI=str(pure),input_tangent_FS_norm_squared='27/16',
                interval_engine='Exact rational root isolation and python-flint Arb at230 bits',
                brackets=out)


def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--skip-arb",action="store_true",
                        help="Explicitly omit the optional python-flint interval example.")
    parser.add_argument("--arb-max-order",type=int,default=8)
    args=parser.parse_args()
    if args.arb_max_order<1:
        parser.error("--arb-max-order must be positive")
    audit=[]
    for nu in [F(-1,2),F(0),F(1,2),F(3,2)]:
        for kind in ['gauss','radau']:
            for r in [1,2,3,4]:
                ideal=isolate_rule(nu,r,kind);rule=build_rule(float(nu),r,kind)
                budget=rounding_certificate(ideal,rule)
                audit.append(dict(nu=str(nu),kind=kind,order=r,
                                  exact_error_coefficient=str(ideal['coefficient']),
                                  rounded_generator_error_budget=float(budget),
                                  rational_root_intervals_verified=True))
    choices=[order_chooser(beta=beta,tolerance=tol)
             for beta in [F(1,2),F(1),F(2),F(4),F(8)]
             for tol in [F(1,1000),F(1,10**6),F(1,10**9)]]
    result=dict(rational_isolation_audit=audit,order_choices=choices,
                depolarized_slater_example=(arb_scalar_example(args.arb_max_order)
                    if not args.skip_arb else
                    {"status":"not_run","reason":"Explicit --skip-arb option"}),
                scope='The operator bounds combine exact rational algebra and a proved analytic theorem. Rounded sampling parameters have a separate certified perturbation budget. Statistical sampling and unitary simulation errors are external.')
    p=Path(__file__).with_suffix('.json');p.write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps(dict(output=str(p),rational_isolation_cases=len(audit),
                          choices=[{k:c[k] for k in ['beta','tolerance','status','selected']} for c in choices],
                          slater=result['depolarized_slater_example']),indent=2))


if __name__=='__main__':main()
