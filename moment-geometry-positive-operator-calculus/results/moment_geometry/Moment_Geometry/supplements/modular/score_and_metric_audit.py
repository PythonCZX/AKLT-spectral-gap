"""Normalization, beta/Bessel identity, and data-processing adverse controls."""
from pathlib import Path
import json
import mpmath as mp
import numpy as np
from positive_bessel_filters import exact_multiplier, build_rule, rule_multiplier


def main():
    rng=np.random.default_rng(4104);scores=[]
    for d in [2,5,9]:
        energies=np.linspace(-3,2,d);p=np.exp(energies);p/=sum(p)
        A=rng.normal(size=(d,d))+1j*rng.normal(size=(d,d));A=(A+A.conj().T)/2
        A-=np.dot(p,np.diag(A))*np.eye(d)
        sqrtp=np.sqrt(p);dotrho=sqrtp[:,None]*sqrtp[None,:]*A
        diff=energies[:,None]-energies[None,:]
        div=np.ones((d,d));mask=abs(diff)>1e-12
        div[mask]=diff[mask]/(p[:,None]-p[None,:])[mask]
        np.fill_diagonal(div,1/p)
        logscore=dotrho*div
        sld=2*dotrho/(p[:,None]+p[None,:])
        elog=float(np.linalg.norm(exact_multiplier(diff/2,.5)*A-logscore))
        esld=float(np.linalg.norm(exact_multiplier(diff/2,-.5)*A-sld))
        assert max(elog,esld)<2e-12
        scores.append(dict(dimension=d,bkm_log_derivative_error=elog,sld_equation_error=esld))
    beta=[]
    with mp.workdps(60):
        for nu in [mp.mpf('-.25'),mp.mpf(0),mp.mpf('.5'),mp.mpf('1.5'),mp.mpf(5)]:
            alpha=nu+mp.mpf('.5')
            for t in [mp.mpf('.1'),mp.mpf(2),mp.mpf(10)]:
                y=mp.log(t)/2
                # Series avoids phase conventions for negative y.
                norm=mp.hyper([],[nu+1],y*y/4)
                bessel=mp.sqrt(t)*norm
                integral=mp.quad(lambda s:mp.power(t,s)*mp.power(s*(1-s),alpha-1),[0,.5,1])/mp.beta(alpha,alpha)
                error=abs(bessel-integral)
                assert error<mp.mpf('2e-15')
                beta.append(dict(nu=float(nu),t=float(t),identity_error=float(error)))
    # Invalid metric parameter: positivity of the filter alone is insufficient.
    p=.8;eps=.1;gap=.5*np.log(p/(1-p))
    classical=4*eps**2
    quantum=2*eps**2/np.sqrt(p*(1-p))*float(exact_multiplier(np.array([gap]),-.75)[0])
    assert quantum<classical
    # Even a valid metric's CP quadrature need not itself remain a Petz metric.
    logt=24.;rule=build_rule(.5,0,'radau')
    log_mean=logt/2+rule.drift*logt**2/4
    log_arithmetic=np.logaddexp(0.,logt)-np.log(2)
    assert log_mean>log_arithmetic
    out=dict(score_normalizations=scores,beta_identity_checks=beta,
             invalid_nu_control=dict(nu=-.75,rho_diagonal=[p,1-p],tangent_off_diagonal=eps,
                                     input_quadratic_form=quantum,x_measurement_classical_fisher=classical,
                                     data_processing_violation=classical-quantum),
             quadrature_is_not_a_new_monotone_metric=dict(valid_target_nu=.5,kind='radau mean-only',
                                     log_eigenvalue_ratio=logt,log_approximant_mean=log_mean,
                                     log_arithmetic_mean=log_arithmetic,
                                     conclusion='Fixed-state Loewner brackets are valid; global CPTP data processing of approximant metrics is not asserted.'))
    Path(__file__).with_suffix('.json').write_text(json.dumps(out,indent=2)+'\n')
    print(json.dumps(out,indent=2))


if __name__=='__main__':main()
