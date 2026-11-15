#!/usr/bin/env python3
"""Adversarial numerical checks of the two-port CP-order Schur-angle theorem.

No numerical output is a universal proof. Independent matrix formulations are
compared, including rank-one cores, entangled retained legs, arbitrary Choi
perturbations, arbitrary reference projection ranks, and microscopic AKLT stars.
"""
from __future__ import annotations
import argparse
import itertools
import json
from pathlib import Path
import numpy as np
import scipy.linalg as la


def cp_super_from_choi(J,d=2):
    return J.reshape(d,d,d,d).transpose(0,2,1,3)


def apply_super(X,S,axis,dims):
    n=len(dims)
    labels=list(range(2*n))
    out=labels.copy();out[axis]=2*n;out[n+axis]=2*n+1
    val=np.einsum(S,[2*n,2*n+1,axis,n+axis],
                  X.reshape(*dims,*dims),labels,out,optimize=True)
    return val.reshape(X.shape)


def hermitian(X):
    return (X+X.conj().T)/2


def invsqrt(X):
    w,v=la.eigh(hermitian(X))
    if w[0]<=0:
        raise ValueError(("not positive",float(w[0])))
    return (v/np.sqrt(w))@v.conj().T


def core(rng,r,mode):
    dim=4*r
    if mode=="pure":
        v=rng.normal(size=dim)+1j*rng.normal(size=dim)
        C=np.outer(v,v.conj())
    elif mode=="nearly_pure":
        v=rng.normal(size=dim)+1j*rng.normal(size=dim)
        C=np.outer(v,v.conj())+1e-12*np.eye(dim)
    elif mode=="flat_spectrum":
        V=rng.normal(size=(dim,dim))+1j*rng.normal(size=(dim,dim))
        U,_=la.qr(V)
        ev=np.geomspace(1,1e-12,dim)
        C=(U*ev)@U.conj().T
    elif mode=="GHZ":
        v=np.zeros(dim,complex)
        v[0]=1
        v[((1*2+1)*r)+(r-1)]=1
        C=np.outer(v,v.conj())+1e-10*np.eye(dim)
    else:
        X=rng.normal(size=(dim,dim))+1j*rng.normal(size=(dim,dim))
        C=X@X.conj().T
    # Exact-reference whitening: (Psi_i tensor Psi_j)(C)=I.
    Ct=C.reshape(2,2,r,2,2,r)
    R=np.einsum("abkabl->kl",Ct)
    V=np.kron(np.eye(4),invsqrt(R))
    C=4*hermitian(V@C@V)
    return C


def random_map(rng,delta,mode):
    J0=np.eye(4)/2
    if mode=="depolarizing":
        # Centered AKLT-like error, allowing both transfer signs.
        beta=delta/3*(1 if rng.random()<.5 else -1)
        vec=np.eye(2).reshape(4)
        J=J0+beta*(np.outer(vec,vec)-J0)
    else:
        Z=rng.normal(size=(4,4))+1j*rng.normal(size=(4,4))
        Z=hermitian(Z);Z/=np.linalg.norm(Z,2)
        J=J0+delta*Z/2
    S=cp_super_from_choi(J)
    return S,float(np.linalg.norm(2*J-np.eye(4),2))


def random_projection_basis(rng,rank):
    X=rng.normal(size=(4,4))+1j*rng.normal(size=(4,4))
    U,_=la.qr(X)
    return U[:,:rank],U[:,rank:]


def quotient_angle(G,p,pc,q,qc,r,direct=False):
    I=np.eye(r)
    W=np.kron(np.kron(p,I),q)
    U=np.kron(np.kron(p,I),qc)
    V=np.kron(np.kron(pc,I),q)
    GW=W.conj().T@G@W
    UW=U.conj().T@G@W
    WV=W.conj().T@G@V
    SUV=U.conj().T@G@V-UW@la.solve(GW,WV,assume_a="pos")
    SUU=U.conj().T@G@U-UW@la.solve(GW,UW.conj().T,assume_a="pos")
    SVV=V.conj().T@G@V-WV.conj().T@la.solve(GW,WV,assume_a="pos")
    c=float(np.linalg.norm(invsqrt(SUU)@SUV@invsqrt(SVV),2))
    discrepancy=0.0
    if direct:
        vals,vecs=la.eigh(hermitian(G))
        sqrtG=(vecs*np.sqrt(vals))@vecs.conj().T
        def projector(X):
            B=la.orth(X)
            return B@B.conj().T
        PM=projector(sqrtG@np.column_stack([W,U]))
        PN=projector(sqrtG@np.column_stack([W,V]))
        PW=projector(sqrtG@W)
        c2=float(np.linalg.norm(PM@PN-PW,2))
        discrepancy=abs(c-c2)
    return c,discrepancy,float(min(la.eigvalsh(SUU)[0],la.eigvalsh(SVV)[0]))


def stress_test(trials,seed):
    rng=np.random.default_rng(seed)
    Psi=cp_super_from_choi(np.eye(4)/2)
    modes=["pure","nearly_pure","flat_spectrum","GHZ","Wishart"]
    samples=[];worst=0;min_slack=1;max_identity=0;max_direct=0;max_ratio_core=0
    for trial in range(trials):
        r=(1,2,4)[trial%3]
        mode=modes[(trial//3)%len(modes)]
        C=core(rng,r,mode)
        di=(.005,.02,.08,.15,.25)[(trial//15)%5]
        dj=(.006,.03,.09,.17,.23)[(trial//75)%5]
        Si,di_actual=random_map(rng,di,"general")
        Sj,dj_actual=random_map(rng,dj,"general")
        dims=[2,2,r]
        ref=apply_super(apply_super(C,Psi,0,dims),Psi,1,dims)
        G=apply_super(apply_super(C,Si,0,dims),Sj,1,dims)
        A=apply_super(apply_super(C,Si-Psi,0,dims),Psi,1,dims)
        B=apply_super(apply_super(C,Psi,0,dims),Sj-Psi,1,dims)
        cross=apply_super(apply_super(C,Si-Psi,0,dims),Sj-Psi,1,dims)
        identity=float(np.linalg.norm(ref-np.eye(4*r),2))
        max_identity=max(max_identity,identity)
        residual=float(np.linalg.norm(G-(ref+A+B+cross),2))
        a=float(np.linalg.norm(A,2));b=float(np.linalg.norm(B,2));cc=float(np.linalg.norm(cross,2))
        tolerance=max(1e-9,30*identity)
        if a>di+tolerance or b>dj+tolerance or cc>di*dj+tolerance or residual>tolerance:
            raise AssertionError(("CP decomposition",trial,a,b,cc,di,dj,identity,residual))
        G=hermitian(G.reshape(2,2,r,2,2,r).transpose(0,2,1,3,5,4).reshape(4*r,4*r))
        fullG=np.kron(np.kron(np.eye(2),G),np.eye(2))
        rp=1+((trial//5)%3);rq=1+((trial//7)%3)
        p,pc=random_projection_basis(rng,rp)
        q,qc=random_projection_basis(rng,rq)
        c,discrepancy,diag_min=quotient_angle(fullG,p,pc,q,qc,r,direct=(trial%30==0))
        max_direct=max(max_direct,discrepancy)
        m=(1-di)*(1-dj)
        bound=2*di*dj*(1+di*dj)/(m*m)
        ratio=c/bound
        min_slack=min(min_slack,bound-c)
        if c>bound+tolerance or diag_min<m-tolerance or discrepancy>2e-8:
            raise AssertionError(("angle",trial,c,bound,diag_min,m,discrepancy))
        if ratio>worst:
            worst=ratio
            samples.append({"trial":trial,"core_mode":mode,"retained_dimension":r,
                "reference_ranks":[rp,rq],"delta_i":di,"delta_j":dj,
                "angle":c,"bound":bound,"ratio":ratio,
                "A_norm":a,"B_norm":b,"Cij_norm":cc,"reference_whitening_error":identity})
    return {"status":"all numerical tests passed; not a universal proof","trials":trials,"seed":seed,
            "largest_angle_bound_ratio":worst,"minimum_angle_bound_slack":min_slack,
            "maximum_reference_whitening_error":max_identity,
            "maximum_direct_projection_vs_Schur_error":max_direct,
            "record_worst_cases":samples[-6:]}


def spin_symmetrizer(d):
    A=np.zeros((d+1,2**d),complex)
    for index,bits in enumerate(itertools.product(range(2),repeat=d)):
        A[sum(bits),index]=1/math_sqrt_binom(d,sum(bits))
    return A


def math_sqrt_binom(d,k):
    import math
    return math.sqrt(math.comb(d,k))


def microscopic_star_checks():
    # Physical virtual-spin construction: normalized singlets and symmetric
    # Clebsch-Gordan map at every core and every spin-one wire vertex.
    eps=np.array([[0,1],[-1,0]],complex)/np.sqrt(2)
    S=np.zeros((3,2,2),complex)
    S[0,0,0]=1;S[1,0,1]=S[1,1,0]=1/np.sqrt(2);S[2,1,1]=1
    one=np.einsum("al,plb->pab",eps,S)
    cases=[]
    for ell in (1,2):
        W=one
        for _ in range(ell-1):
            W=np.einsum("pac,qcb->pqab",W,one).reshape(-1,2,2)
        # Rescale the local wire amplitudes to the TP transfer gauge.
        W=W*(2/np.sqrt(3))**ell
        K=W.conj().transpose(0,2,1)
        CP=np.einsum("pua,pvb->uvab",K,K.conj())
        beta=(-1/3)**ell
        vec=np.eye(2).reshape(4)
        expected=cp_super_from_choi(np.eye(4)/2+beta*(np.outer(vec,vec)-np.eye(4)/2))
        map_error=float(np.linalg.norm(CP-expected))
        if map_error>1e-12:
            raise AssertionError(("microscopic wire",ell,map_error))
        for degree in (2,3,4):
            A=spin_symmetrizer(degree)
            C=A.conj().T@A
            dims=[2]*degree
            gram_cp=C.copy()
            for axis in range(degree):
                gram_cp=apply_super(gram_cp,CP,axis,dims)
            # Form the actual physical map by independent contractions.
            # A[h,a0,...], W[p_i,a_i,b_i].
            # Integer-index einsum permits arbitrary degree without hand-built strings.
            tensors=[A.reshape(degree+1,*([2]*degree)),[0]+list(range(1,degree+1))]
            for j in range(degree):
                tensors.extend([W,[degree+1+j,1+j,2*degree+1+j]])
            output=[0]+list(range(degree+1,2*degree+1))+list(range(2*degree+1,3*degree+1))
            T=np.einsum(*tensors,output,optimize=True).reshape(-1,2**degree)
            gram_direct=T.conj().T@T
            error=float(np.linalg.norm(gram_direct-gram_cp)/np.linalg.norm(gram_cp))
            if error>2e-12:
                raise AssertionError(("microscopic star Gram",degree,ell,error))
            cases.append({"degree":degree,"half_wire_length":ell,
                          "physical_block_dimension":int(T.shape[0]),"boundary_dimension":2**degree,
                          "relative_direct_vs_CP_Gram_error":error,"wire_transfer_error":map_error,
                          "minimum_Gram_eigenvalue":float(la.eigvalsh(gram_direct)[0])})
    return {"normalization":"one normalized singlet per internal bond; each half-wire scaled by (2/sqrt(3))^ell",
            "cases":cases,"all_passed":True}


def main():
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument("--trials",type=int,default=600)
    p.add_argument("--seed",type=int,default=2026111507)
    p.add_argument("--output",type=Path,default=Path(__file__).with_name("two_port_schur_adversarial_checks.json"))
    args=p.parse_args()
    result={"adversarial":stress_test(args.trials,args.seed),"microscopic_AKLT":microscopic_star_checks()}
    args.output.write_text(json.dumps(result,indent=2)+"\n")
    print(json.dumps({"stress":{k:v for k,v in result["adversarial"].items() if k!="record_worst_cases"},
                     "microscopic_AKLT":result["microscopic_AKLT"],"output":str(args.output)},indent=2))


if __name__=="__main__":
    main()

