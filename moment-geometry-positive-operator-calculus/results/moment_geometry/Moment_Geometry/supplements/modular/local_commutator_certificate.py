"""Exact local Pauli derivative bounds without building a Hilbert matrix.

The Hamiltonian is sum (37 ZZ +29 X+13 Z)/100 on an open chain.
We propagate i^-r ad_(100K)^r(Z_center) as integer Pauli coefficients.
Cancellation is retained before taking the l1 bound.  Runtime depends on
the generated local Pauli supports, not on 2^n.  Growth with derivative
order is real and is reported explicitly.
"""
from collections import defaultdict
from fractions import Fraction
from pathlib import Path
from time import perf_counter
import json


def terms(n):
    out=[]
    for j in range(n):
        out.append(((1<<j,0),29));out.append(((0,1<<j),13))
    for j in range(n-1):out.append(((0,(1<<j)+(1<<(j+1))),37))
    return out


def step(A,H):
    B=defaultdict(int)
    for (x,z),c in A.items():
        for (u,v),h in H:
            if ((x&v).bit_count()+(z&u).bit_count())%2==0:continue
            # H*A multiplication phase, in P(x,z)=i^(x.z) X^x Z^z.
            xx,zz=x^u,z^v
            power=((u&v).bit_count()+(x&z).bit_count()-(xx&zz).bit_count()+2*(v&x).bit_count())%4
            assert power in [1,3]
            B[(xx,zz)]+=2*(1 if power==1 else -1)*h*c
    return {p:c for p,c in B.items() if c}


def certificate(n,order=14):
    A={(0,1<<(n//2)):1};H=terms(n);out=[];start=perf_counter()
    for r in range(1,order+1):
        A=step(A,H)
        if r%2==0:
            support=0
            for x,z in A:support|=x|z
            b=Fraction(sum(abs(c) for c in A.values()),100**r)
            out.append(dict(spins=n,derivative_order=r,pauli_terms=len(A),
                            support_sites=support.bit_count(),
                            exact_operator_norm_upper_bound=str(b),
                            bound_float=float(b),elapsed_seconds=perf_counter()-start))
    return out


def independent_dense_check():
    """Compare the bit algebra with exact 8x8 matrix commutators once."""
    import sympy as s
    X=s.Matrix([[0,1],[1,0]]);Z=s.diag(1,-1);I=s.eye(2)
    def dense(p):
        x,z=p;factors=[]
        for j in range(3):
            local=I
            if x>>j&1:local=local*X
            if z>>j&1:local=local*Z
            factors.append(local)
        return s.I**((x&z).bit_count())*s.kronecker_product(*factors)
    H=sum((c*dense(p) for p,c in terms(3)),s.zeros(8))
    paulis={(0,2):1};matrix=dense((0,2))
    for order in range(1,7):
        paulis=step(paulis,terms(3));matrix=(H*matrix-matrix*H)/s.I
        from_sparse=sum((c*dense(p) for p,c in paulis.items()),s.zeros(8))
        assert matrix==from_sparse
    return dict(spins=3,orders_checked=list(range(1,7)),
                method='Independent exact SymPy matrix commutators',passed=True)


def main():
    rows=certificate(8)+certificate(16)+certificate(32)
    a={r['derivative_order']:r for r in rows if r['spins']==16}
    b={r['derivative_order']:r for r in rows if r['spins']==32}
    for k in a:
        assert a[k]['exact_operator_norm_upper_bound']==b[k]['exact_operator_norm_upper_bound']
        assert a[k]['pauli_terms']==b[k]['pauli_terms']
    out=dict(hamiltonian='(37 sum ZZ +29 sum X +13 sum Z)/100',
             observable='Z at center',rows=rows,
             sixteen_and_thirtytwo_site_local_certificates_identical=True,
             independent_dense_validation=independent_dense_check(),
             scope='Exact rational Pauli l1 bounds. These are genuine upper bounds on operator derivatives; no dense diagonalization or norm estimation is used.')
    p=Path(__file__).with_suffix('.json');p.write_text(json.dumps(out,indent=2)+'\n')
    print(json.dumps(out,indent=2))


if __name__=='__main__':main()
