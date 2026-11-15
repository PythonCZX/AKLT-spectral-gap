"""Positive Bessel modular filters, Gamma compression, and local certificates.

The scalar Gauss/Gamma construction is classical and, for Bessel clocks,
is the subject of Clark (2026), arXiv:2610.19233.  This module exposes its
operator lift: every generated rule is a CP semigroup; the accompanying
derivative certificate is an observable-norm bound, not a diamond bound.

Two Gaussian quadratures are supported.  ``gauss`` compresses the Thorin
measure and gives an upper spectral multiplier.  ``radau`` adds the zero
node and gives a lower multiplier.  Their differences are generally NOT
positive maps, even though they bracket quadratic information metrics.
"""
from dataclasses import dataclass
from fractions import Fraction
from math import factorial
from pathlib import Path
import argparse
import json

import mpmath as mp
import numpy as np
from scipy.linalg import eigh
from scipy.special import ive, gammaln


@dataclass
class Rule:
    nu: float
    head: int
    order: int
    kind: str
    drift: float
    scales: np.ndarray
    shapes: np.ndarray  # shapes per unit semigroup time tau
    error_coefficient: float  # multiply tau*||ad_K^derivative_order A||
    derivative_order: int
    scalar_moment_residual: float

    def to_json(self):
        return dict(nu=self.nu, head=self.head, order=self.order, kind=self.kind,
                    drift=self.drift, scales=self.scales.tolist(),
                    shapes=self.shapes.tolist(),
                    error_coefficient=self.error_coefficient,
                    derivative_order=self.derivative_order,
                    scalar_moment_residual=self.scalar_moment_residual)


def inner(p, q, moments):
    return sum(a*b*moments[i+j] for i,a in enumerate(p) for j,b in enumerate(q))


def gauss_from_moments(moments, order):
    """High-precision positive Gaussian rule; return nodes, weights, h_order.

    The moment source must be a positive measure, as it is here.  The proof
    gives positivity; numerical checks detect insufficient arithmetic precision.
    """
    if order == 0:
        return [], [], moments[0]
    polys=[[mp.mpf(1)]]; norms=[moments[0]]; alpha=[]; beta=[]
    for n in range(order):
        p=polys[-1]; h=norms[-1]
        a=inner([mp.mpf(0)]+p,p,moments)/h
        b=mp.mpf(0) if n==0 else h/norms[-2]
        alpha.append(a)
        if n: beta.append(b)
        nxt=[mp.mpf(0)]*(len(p)+1)
        for j,x in enumerate(p):nxt[j+1]+=x;nxt[j]-=a*x
        if n:
            for j,x in enumerate(polys[-2]):nxt[j]-=b*x
        polys.append(nxt);norms.append(inner(nxt,nxt,moments))
    J=mp.matrix(order)
    for j in range(order):J[j,j]=alpha[j]
    for j,b in enumerate(beta):J[j,j+1]=J[j+1,j]=mp.sqrt(b)
    nodes,U=mp.eigsy(J)
    weights=[moments[0]*U[0,j]**2 for j in range(order)]
    return list(nodes),weights,norms[-1]


def rayleigh_moments(nu, maximum):
    """m_j=sum_k j_{nu,k}^{-2j}, exact recursion from the Bessel ODE.

    m_1=1/(4(nu+1)); (nu+n)m_n=sum_{i=1}^{n-1} m_i*m_{n-i}.
    Rational nu can be passed as a Fraction, yielding exact rational output.
    """
    one=Fraction(1) if isinstance(nu,Fraction) else mp.mpf(1)
    out=[None,one/(4*(nu+1))]
    for n in range(2,maximum+1):
        out.append(sum(out[i]*out[n-i] for i in range(1,n))/(nu+n))
    return out


def build_rule(nu=.5, order=2, kind='gauss', head=0, dps=90):
    """Compile a CP semigroup rule from <=2*order+3 scalar moments.

    A nonzero head is currently exposed only at nu=1/2, whose zeros are pi*j.
    For head=0 every rational nu has an exact rational moment recurrence.
    """
    assert nu>-1 and order>=0 and kind in {'gauss','radau'}
    assert order>0 or kind=='radau'
    assert head>=0 and (head==0 or nu==.5)
    with mp.workdps(dps):
        nnu=mp.mpf(str(nu)); maximum=2*order+3
        if head:
            sums=[None]+[mp.zeta(2*j,head+1)/mp.pi**(2*j) for j in range(1,maximum+1)]
        else:
            sums=rayleigh_moments(nnu,maximum)
        moments=sums[1:]
        if kind=='gauss':
            nodes,weights,h=gauss_from_moments(moments,order)
            drift=mp.mpf(0);degree=2*order+1;coefficient=h/degree
            exact_degree=2*order-1
        else:
            nodes,wtilde,h=gauss_from_moments(moments[1:],order)
            weights=[w/c for w,c in zip(wtilde,nodes)]
            drift=moments[0]-sum(weights)
            degree=2*order+2;coefficient=h/degree
            exact_degree=2*order
        assert all(c>0 for c in nodes)
        assert all(w>0 for w in weights)
        assert drift>=0
        residual=mp.mpf(0)
        for k in range(exact_degree+1):
            got=sum(w*c**k for w,c in zip(weights,nodes))+(drift if k==0 else 0)
            residual=max(residual,abs(got-moments[k])/moments[k])
        assert residual<mp.mpf('1e-60'),residual
        return Rule(float(nu),head,order,kind,float(drift),
                    np.array([float(c) for c in nodes]),
                    np.array([float(w/c) for w,c in zip(weights,nodes)]),
                    float(coefficient),2*degree,float(residual))


def exact_multiplier(x,nu=.5,tau=1.):
    if nu<=-1 or tau<0:raise ValueError('Require nu>-1 and tau>=0')
    x=np.abs(np.asarray(x,dtype=float));out=np.ones_like(x)
    mask=x>1e-8; y=x[mask]
    # ive = exp(-|x|)*I_nu(x), avoiding hyperbolic overflow.
    lognorm=gammaln(nu+1)+nu*np.log(2/y)+np.log(ive(nu,y))+y
    out[mask]=np.exp(-tau*lognorm)
    # Taylor control for small x avoids cancellation at the removable zero.
    out[~mask]=np.exp(-tau*x[~mask]**2/(4*(nu+1)))
    return out


def rule_multiplier(x,rule,tau=1.):
    if tau<0:raise ValueError('Require tau>=0')
    x=np.asarray(x,dtype=float); L=x*x
    exponent=rule.drift*L
    for scale,shape in zip(rule.scales,rule.shapes):
        exponent=exponent+shape*np.log1p(scale*L)
    for j in range(1,rule.head+1):exponent=exponent+np.log1p(L/(np.pi*j)**2)
    return np.exp(-tau*exponent)


def sample_times(rule,size,tau=1.,rng=None):
    """Sample one real evolution time per channel use; O(head+order) draws.

    Unconditionally, U_T (.) U_T* implements the compiled CP channel.
    This does not estimate/learn an unknown K; Hamiltonian simulation access
    and any state preparation cost are external requirements.
    """
    if tau<0:raise ValueError('Require tau>=0')
    rng=np.random.default_rng() if rng is None else rng
    if tau==0:return np.zeros(size)
    S=np.full(size,tau*rule.drift)
    for j in range(1,rule.head+1):S+=rng.gamma(tau,1/(np.pi*j)**2,size)
    for scale,shape in zip(rule.scales,rule.shapes):S+=rng.gamma(tau*shape,scale,size)
    return rng.normal(size=size)*np.sqrt(2*S)


def exact_rational_certificates(max_order=8):
    """Check the closed Jacobi recurrence and moment optimality exactly."""
    records=[]
    for nu in [Fraction(-1,2),Fraction(0),Fraction(1,2),Fraction(1),Fraction(3,2)]:
        m=rayleigh_moments(nu,2*max_order+2)
        polys=[[Fraction(1)]];norms=[m[1]]
        for n in range(max_order):
            p=polys[-1];h=norms[-1]
            a=inner([Fraction(0)]+p,p,m[1:])/h
            b=Fraction(0) if n==0 else h/norms[-2]
            def A(j):return Fraction(0) if j==0 else 1/(4*(nu+j)*(nu+j+1))
            assert a==A(2*n)+A(2*n+1)
            if n:assert b==A(2*n-1)*A(2*n)
            nxt=[Fraction(0)]*(len(p)+1)
            for j,x in enumerate(p):nxt[j+1]+=x;nxt[j]-=a*x
            if n:
                for j,x in enumerate(polys[-2]):nxt[j]-=b*x
            hn=inner(nxt,nxt,m[1:]);assert hn>0
            for k in range(n+1):assert inner(nxt,[Fraction(0)]*k+[Fraction(1)],m[1:])==0
            polys.append(nxt);norms.append(hn)
            records.append(dict(nu=str(nu),order=n+1,
                                generator_error_coefficient=str(hn/(2*n+3)),
                                derivative_order=4*n+6,
                                exact_orthogonality=True,closed_jacobi_recurrence=True))
    return records


I=np.eye(2,dtype=complex);X=np.array([[0,1],[1,0]],complex)
Y=np.array([[0,-1j],[1j,0]],complex);Z=np.diag([1.,-1.]).astype(complex)

def tensor(ops):
    out=np.ones((1,1),complex)
    for op in ops:out=np.kron(out,op)
    return out

def local(n,items):return tensor([items.get(k,I) for k in range(n)])

def comm(K,A):return K@A-A@K


def benchmark(spins=(3,5,7,8)):
    records=[]
    for n in spins:
        base=sum(.37*local(n,{j:Z,j+1:Z}) for j in range(n-1))
        base+=sum(.29*local(n,{j:X})+.13*local(n,{j:Z}) for j in range(n))
        A=local(n,{n//2:Z})
        for beta in [.5,1.,2.]:
            K=beta*base;ev,U=eigh(K);Ae=U.conj().T@A@U
            differences=ev[:,None]-ev[None,:]
            deriv={0:A}
            for j in range(1,15):deriv[j]=comm(K,deriv[j-1])
            dn={j:float(np.linalg.norm(deriv[j],2)) for j in [4,6,8,10,12,14]}
            for nu in [-.5,.5,1.5]:
                for tau in [.5,1.]:
                    target=exact_multiplier(differences,nu,tau)*Ae
                    for q,kind in [(0,'radau'),(1,'gauss'),(1,'radau'),(2,'gauss'),(2,'radau'),(3,'gauss')]:
                        rule=build_rule(nu,q,kind)
                        approx=rule_multiplier(differences,rule,tau)*Ae
                        err=float(np.linalg.norm(approx-target,2))
                        bound=tau*rule.error_coefficient*dn[rule.derivative_order]
                        assert err<=bound+8e-13,(n,beta,nu,tau,q,kind,err,bound)
                        records.append(dict(spins=n,beta=beta,nu=nu,tau=tau,q=q,kind=kind,
                                            error=err,derivative_norm=dn[rule.derivative_order],
                                            derivative_order=rule.derivative_order,
                                            analytic_bound=bound))
    return records


def metric_checks():
    rng=np.random.default_rng(20261114);records=[]
    for dimension in [3,7,12]:
        K=np.diag(np.linspace(-3,2,dimension));p=np.exp(np.diag(K));p/=sum(p)
        sr=np.sqrt(p);relative=[]
        for j in range(5):
            a=rng.normal(size=(dimension,dimension))+1j*rng.normal(size=(dimension,dimension))
            a=(a+a.conj().T)/2;a-=np.dot(p,np.diag(a))*np.eye(dimension)
            relative.append(a/np.linalg.norm(a,2))
        diff=(np.diag(K)[:,None]-np.diag(K)[None,:])/2
        def gram(mult):
            return np.array([[np.sum(sr[:,None]*sr[None,:]*a.conj()*b*mult).real
                              for b in relative] for a in relative])
        for nu in [-.5,0.,.5,1.5,5.]:
            exact=gram(exact_multiplier(diff,nu))
            for q in [1,2,3]:
                upper=gram(rule_multiplier(diff,build_rule(nu,q,'gauss')))
                lower=gram(rule_multiplier(diff,build_rule(nu,q,'radau')))
                eig_lower=np.linalg.eigvalsh(exact-lower)
                eig_upper=np.linalg.eigvalsh(upper-exact)
                assert eig_lower[0]>-1e-13 and eig_upper[0]>-1e-13
                records.append(dict(dimension=dimension,parameters=5,nu=nu,q=q,
                                    exact_min_eigenvalue=float(np.linalg.eigvalsh(exact)[0]),
                                    lower_slack=float(eig_lower[0]),upper_slack=float(eig_upper[0]),
                                    bracket_width=float(np.linalg.norm(upper-lower,2))))
    # A CP-order adverse control: unequal unital maps cannot dominate each other.
    delta=float(rule_multiplier(np.array([1.]),build_rule(.5,1,'gauss'))[0]-exact_multiplier(np.array([1.]))[0])
    adverse=dict(off_diagonal_multiplier_difference=delta,
                 difference_on_plus_state_eigenvalues=[-delta/2,delta/2],
                 difference_choi_nonzero_eigenvalues=[-delta,delta],
                 interpretation='Spectral/quadratic-form order does not imply positive-map or CP order.')
    return records,adverse


def stochastic_checks(samples=2000):
    rng=np.random.default_rng(193618);out=[]
    for nu in [-.5,.5,1.5]:
        for kind in ['gauss','radau']:
            r=build_rule(nu,2,kind); t=sample_times(r,samples,tau=.5,rng=rng)
            frequencies=np.array([.4,1.,2.])
            measured=np.mean(np.cos(t[:,None]*frequencies),axis=0)
            wanted=rule_multiplier(frequencies,r,.5)
            out.append(dict(nu=nu,kind=kind,samples=len(t),
                            empirical_variance=float(np.var(t)),
                            expected_variance=.5/(2*(nu+1)),
                            characteristic_error=float(max(abs(measured-wanted))),
                            three_frequency_hoeffding_radius=float(np.sqrt(2*np.log(6/.01)/len(t)))))
    return out


def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--exact-only",action="store_true",
                        help="Only exact rational recurrence certificates.")
    parser.add_argument("--quick",action="store_true",
                        help="Limit dense diagnostic chains to three and five spins.")
    parser.add_argument("--monte-carlo-samples",type=int,default=0,
                        help="Optional samples per clock; zero disables Monte Carlo.")
    parser.add_argument("--output",type=Path,default=Path(__file__).with_suffix('.json'))
    args=parser.parse_args()
    if args.monte_carlo_samples<0:
        parser.error("--monte-carlo-samples must be nonnegative")
    exact=exact_rational_certificates()
    if args.exact_only:
        result=dict(exact_rational=exact,
                    scope="Exact rational recurrence and orthogonality identities only.",
                    floating_diagnostics_run=False,monte_carlo_samples=0)
        args.output.write_text(json.dumps(result,indent=2)+'\n')
        print(json.dumps(dict(output=str(args.output),exact_recurrences=len(exact),
                              floating_diagnostics_run=False),indent=2))
        return
    rules=[build_rule(nu,q,kind).to_json() for nu in [-.5,.5,1.5]
           for q,kind in [(0,'radau'),(1,'gauss'),(1,'radau'),(2,'gauss'),(2,'radau'),(3,'gauss')]]
    tests=benchmark((3,5) if args.quick else (3,5,7,8));metrics,adverse=metric_checks()
    result=dict(exact_rational=exact,rules=rules,benchmarks=tests,metrics=metrics,
                cp_order_adverse_control=adverse,
                stochastic=stochastic_checks(args.monte_carlo_samples)
                           if args.monte_carlo_samples else [],
                monte_carlo_samples=args.monte_carlo_samples,
                scope='Exact scalar rational recurrence certificates; mathematical operator error proof in accompanying note. Dense-matrix checks are numerical diagnostics, not formal operator-norm certificates.')
    path=args.output;path.write_text(json.dumps(result,indent=2)+'\n')
    selected=[r for r in tests if r['spins']==8 and r['beta']==1 and r['nu']==.5 and r['tau']==1]
    print(json.dumps(dict(output=str(path),exact_recurrences=len(exact),benchmark_cases=len(tests),
                          metric_cases=len(metrics),selected=selected,adverse=adverse),indent=2))


if __name__=='__main__':main()
