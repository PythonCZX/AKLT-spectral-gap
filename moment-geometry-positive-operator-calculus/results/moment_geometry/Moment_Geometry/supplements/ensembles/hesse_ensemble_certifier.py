#!/usr/bin/env python3
"""Trusted matched-replica Hesse-ensemble confidence calculator.

Examples:
  python hesse_ensemble_certifier.py budget --epsilon 0.1 --alpha 0.01
  python hesse_ensemble_certifier.py simulate --rotation 0.01 --q-trials 1000000 --single-trials 1000000
  python hesse_ensemble_certifier.py certify --q-trials 10000 --q-clicks 0 --sic-counts 1000,1000,1000,1000,1000,1000,1000,1000,1000
The confidence statement assumes independent source requests, exact matched replicas
within a request, trusted measurements and qutrit dimension, and sample sizes
chosen independently of the observed outcomes. See the accompanying proof.
"""
from __future__ import annotations

import argparse
import json
import math
from pathlib import Path

import numpy as np
from scipy.stats import beta

K=1+3/math.sqrt(2)
CQ=27/4


def hesse_vectors():
    omega=np.exp(2j*np.pi/3)
    return np.array([(0,1,-omega**j) for j in range(3)]
                    +[(1,0,-omega**j) for j in range(3)]
                    +[(1,-omega**j,0) for j in range(3)],complex)/np.sqrt(2)


def binomial_upper(clicks,trials,failure):
    if trials<=0 or clicks<0 or clicks>trials:
        raise ValueError("Require 0 <= clicks <= trials and trials > 0.")
    if clicks==trials:
        return 1.0
    if clicks==0:
        return -math.expm1(math.log(failure)/trials)
    return float(beta.ppf(1-failure,clicks+1,trials-clicks))


def certificate(q_trials,q_clicks,sic_counts,alpha):
    if not 0<alpha<1:
        raise ValueError("alpha must lie strictly between zero and one.")
    counts=np.array(sic_counts,dtype=np.int64)
    if counts.shape!=(9,) or np.any(counts<0) or counts.sum()<=0:
        raise ValueError("Supply nine nonnegative SIC counts with positive total.")
    N1=int(counts.sum())
    p=counts/N1
    q_upper=binomial_upper(q_clicks,q_trials,alpha/2)
    delta_hat=float(math.sqrt(12)*np.linalg.norm(p-np.ones(9)/9))
    radius=math.sqrt(12)*(1+math.sqrt(math.log(2/alpha)))/math.sqrt(N1)
    delta_upper=min(math.sqrt(2/3),delta_hat+radius)
    rms=min(1.0,math.sqrt(CQ*q_upper))
    tv=min(1.0,math.sqrt(3)*delta_upper+math.sqrt(6)*rms)
    bound=min(1.0,K*rms+1.5*delta_upper)
    return {
        "confidence_at_least":1-alpha,
        "metric":"W1 with cost 0.5*trace_norm(P-Q)",
        "W1_upper":bound,
        "localization_RMS_trace_distance_upper":rms,
        "nearest_Hesse_weights_TV_from_uniform_upper":tv,
        "Q_probability_upper":q_upper,
        "mean_state_HS_error_estimate":delta_hat,
        "mean_state_HS_error_upper":delta_upper,
        "tomography_HS_radius":radius,
        "q_trials":int(q_trials),"q_clicks":int(q_clicks),
        "single_copy_trials":N1,"physical_copies":3*int(q_trials)+N1,
        "sic_counts":[int(x) for x in counts],
        "assumptions":["independent source requests","same pure hidden ray within each replica block",
                       "trusted Q projector and calibrated SIC POVM","trusted qutrit dimension and reference basis",
                       "fixed sample sizes, not arbitrary outcome-dependent stopping"],
        "not_a_device_independent_claim":True,
    }


def budget(epsilon,alpha):
    if not 0<epsilon<1 or not 0<alpha<1:
        raise ValueError("epsilon and alpha must lie strictly between zero and one.")
    N3=math.ceil(27*K*K*math.log(2/alpha)/(epsilon*epsilon))
    N1=math.ceil(432*(1+math.sqrt(math.log(2/alpha)))**2/(epsilon*epsilon))
    return {"target_W1":epsilon,"failure_probability":alpha,"q_triples":N3,
            "single_copy_tomography_samples":N1,"total_physical_copies":3*N3+N1,
            "acceptance_rule":{"Q_clicks":0,"tomography_HS_error_estimate_at_most":epsilon/6},
            "ideal_source_acceptance_probability_at_least":1-alpha/2}


def simulation(rotation,weight_skew,q_trials,single_trials,alpha,seed):
    if not 0<=weight_skew<1 or single_trials<=0:
        raise ValueError("weight_skew must be in [0,1); single_trials must be positive.")
    rng=np.random.default_rng(seed)
    H=hesse_vectors()
    phases=np.exp(1j*np.array([rotation,-rotation,0]))
    Z=H*phases
    weights=np.ones(9)*(1-weight_skew)/9
    weights[0]+=weight_skew
    prob=abs(Z)**2
    qvalues=abs(np.sum(Z**3,axis=1))**2/3+6*np.prod(prob,axis=1)
    true_q=float(weights@qvalues)
    overlap=abs(Z@H.conj().T)**2
    povm_p=weights@overlap/3
    povm_p/=povm_p.sum()
    clicks=int(rng.binomial(q_trials,true_q))
    counts=rng.multinomial(single_trials,povm_p)
    cert=certificate(q_trials,clicks,counts,alpha)
    M1=(Z.T*weights)@Z.conj()
    from scipy.optimize import linprog
    PZ=np.einsum('ia,ib->iab',Z,Z.conj())
    PH=np.einsum('ia,ib->iab',H,H.conj())
    costs=np.linalg.norm(PZ[:,None]-PH[None,:],axis=(2,3))/np.sqrt(2)
    A=np.zeros((18,81))
    for i in range(9):
        A[i,9*i:9*i+9]=1
    for j in range(9):
        A[9+j,j::9]=1
    lp=linprog(costs.ravel(),A_eq=A,b_eq=np.r_[weights,np.ones(9)/9],
               bounds=(0,None),method="highs")
    if not lp.success:
        raise RuntimeError(lp.message)
    return {
        "simulation_only":True,"seed":seed,"rotation_radians":rotation,"weight_skew":weight_skew,
        "true_Q_probability":true_q,
        "true_M1_HS_error":float(np.linalg.norm(M1-np.eye(3)/3)),
        "W1_from_floating_point_discrete_transport":float(lp.fun),
        "certificate":cert,
        "reproduce_certificate_command":
            "python hesse_ensemble_certifier.py certify --q-trials "
            +str(q_trials)+" --q-clicks "+str(clicks)+" --sic-counts "
            +",".join(str(int(x)) for x in counts)+" --alpha "+str(alpha),
    }


def main():
    ap=argparse.ArgumentParser(description=__doc__,formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("--output",type=Path,help="Optional JSON output path.")
    sub=ap.add_subparsers(dest="command",required=True)
    p=sub.add_parser("certify",help="Calculate a bound from actual observed counts.")
    p.add_argument("--q-trials",type=int,required=True)
    p.add_argument("--q-clicks",type=int,required=True)
    p.add_argument("--sic-counts",required=True,help="Nine comma-separated integer counts.")
    p.add_argument("--alpha",type=float,default=0.01)
    p=sub.add_parser("budget",help="Plan a zero-click acceptance test.")
    p.add_argument("--epsilon",type=float,required=True)
    p.add_argument("--alpha",type=float,default=0.01)
    p=sub.add_parser("simulate",help="Generate and certify an explicit rotated Hesse source.")
    p.add_argument("--rotation",type=float,default=0.01)
    p.add_argument("--weight-skew",type=float,default=0.0)
    p.add_argument("--q-trials",type=int,default=1000000)
    p.add_argument("--single-trials",type=int,default=1000000)
    p.add_argument("--alpha",type=float,default=0.01)
    p.add_argument("--seed",type=int,default=20261115)
    args=ap.parse_args()
    try:
        if args.command=="certify":
            result=certificate(args.q_trials,args.q_clicks,
                               [int(x) for x in args.sic_counts.split(",")],args.alpha)
        elif args.command=="budget":
            result=budget(args.epsilon,args.alpha)
        else:
            result=simulation(args.rotation,args.weight_skew,args.q_trials,args.single_trials,args.alpha,args.seed)
    except ValueError as exc:
        ap.error(str(exc))
    encoded=json.dumps(result,indent=2)+"\n"
    if args.output:
        args.output.write_text(encoded)
    print(encoded,end="")


if __name__=="__main__":
    main()

