# Fractional-power response: unchecked proof package

## Status

`response_proofs.tex` is an expanded mathematical proof insertion. It is **uncompiled and unverified**. No proof-assistant compilation, numerical experiment, test, or verification run was performed for this handoff. It is not Lean source and must not be described as kernel-checked. No `sorry`, target-theorem axiom, or assumed target Fourier identity is introduced: the document provides ordinary analytic proofs of the missing identities.

The source scope is the report's “Positive modular response calculus,” in `publication_package/proofs/quantum_results.tex`: Theorem `q:thm-powers`, the KMS compatibility display, and Proposition `q:prop-rotation` (report Section 13). The document is independent of the presentation.

## What has been supplied

| Local ID | Exact assertion established in mathematical text | Principal argument |
|---|---|---|
| R1 | A differentiable faithful matrix path has differentiable logarithm, with the resolvent derivative | Scalar log integral, spectral theorem, resolvent identity; explicit remainder at most `||E||²/m²` |
| R2 | The actual derivative of the exponential is the Duhamel integral | Uniformly summable derivatives of the exponential series; integer beta integral |
| R3 | The actual derivative of `rho^r` has the report's Hermitian and anti-Hermitian spectral multipliers | R2, one fixed-time diagonalization, adjoints, elementary hyperbolic identities |
| F1 | Exact Fourier integral for `1/(cosh u + cos alpha)` | Explicit pole locations, residues, rectangle side bounds, continuity at frequency zero |
| F2 | `p_r` transforms to `sinh(rx)/sinh x`, with mass `r`; convolution kernel for `chi_r`; logistic limit for `f` | F1, change of variables, Fubini, an explicit integrable dominating function |
| F3 | Complete positivity and exact completely bounded norms at every finite ancilla | Positive integral of unitary conjugations; norm attained at the identity |
| C1 | The coth partial-fraction identity previously treated as an input | Explicit cosine coefficients of periodic `cosh(a t)` and Fejér convergence; no assumed Mittag–Leffler identity |
| C2 | Positive rational series for the rotation multiplier `h`, including `h(0)=1/3` | Locally uniform differentiation of C1 and elementary Taylor expansions |
| C3 | Exact nonnegative rotation density, transform, mass, closed form, and exponential weighted masses | Elementary Laplace integrals and Tonelli; no assumed scalar Fourier formula |
| K1 | KMS compatibility of the actual derivative | Adjoint identity and inversion of the positive spectral multiplier `1+exp(-x)` |
| K2 | Positive rotation generator, norm `1/3`, exact rotation equation, and optional unitary ODE | F3/C3 argument, K1 and R3, product rule |

## Dependency graph for machine translation

1. Standard finite-dimensional Hermitian spectral theorem and scalar logarithm integration → **R1**.
2. Derivative of finite products, convergence of exponential power series, integer beta integration → **R2**.
3. R1 + R2 + fixed-basis matrix-unit calculus → **R3**.
4. Standard residue theorem + explicit contour estimates → **F1**.
5. F1 + dominated convergence + Fubini/Tonelli → **F2**.
6. F2 + tensor-product unitary conjugations → **F3**.
7. Standard Fourier coefficient integration and Fejér convergence → **C1**.
8. C1 + termwise differentiation + elementary exponential Taylor remainder → **C2**.
9. C2 + elementary exponential integration + Tonelli → **C3**.
10. Matrix adjoints and fixed-basis functional calculus → **K1**.
11. R3 + C3 + K1 → **K2**.

The contour Fourier transform and coth series are now conclusions proved in this package, rather than imported analytic assumptions. General-purpose calculus, integration, the residue theorem, Fejér convergence, and the finite-dimensional spectral theorem remain standard mathematical dependencies to instantiate from the formal library.

## Translation interfaces and exact proof obligations

### R1: matrix logarithm

- Domain: a finite-dimensional complex Hilbert space, a positive definite Hermitian `X`, Hermitian perturbations `E`, and a lower bound `m > 0` with `m I ≤ X`.
- First establish the scalar integral for `log a` from its truncated antiderivative. Apply spectral functional calculus to obtain the matrix identity.
- Use the **ordered** resolvent identity `R' - R = -R E R'`. No matrices are commuted.
- The remainder integrand is exactly `-R E R E R'`. Its norm is dominated by `2 ||E||²/(m+s)^3`.
- To compose with a differentiable path, use `rho(lambda+h)-rho(lambda)=h dotrho + o(h)`; local faithfulness follows from the spectral lower bound and the norm perturbation inequality.
- Required output is the Fréchet derivative on the real vector space of Hermitian matrices, which is enough for all path statements.

### R2: exponential derivative

- Use the real Fréchet derivative of the complex matrix exponential (or its complex derivative followed by restriction).
- The uniform derivative bound on a norm ball is `n R^(n-1) ||L||`; its exponential-series sum is finite.
- Both exponential series under the integral converge uniformly and absolutely; termwise multiplication and integration are justified by the bound `exp(||K||)||L||`.
- The integer beta integral is proved by integration by parts in the text, and is not assumed as a response identity.
- Preserve the order `exp((1-u)K) L exp(uK)`. Right multiplication by `exp(-rK)` and `s=r(1-u)` give the required right logarithmic derivative.

### R3: spectral identification

- Diagonalize only at the parameter being evaluated. Do not require or assert a differentiable eigenbasis, particularly at repeated eigenvalues.
- Define every quotient by its continuous value at zero, preferably using integral definitions for `F_r`, `S_r`, `T_r` first.
- The anti-Hermitian multiplier is harmless at zero because `T_1(0)=T_r(0)=0`; do not divide by `T_1(0)`.
- `Q_r/r → dotK` follows from convergence on finitely many eigenvalue differences, not from a merely formal expansion.

### F1: contour computation

- Parameters: `0 < alpha < pi`, initially `k > 0`.
- Rectangle: `[-R,R] + i[0,2pi]`, counterclockwise, for sufficiently large positive `R`.
- Poles: `i(pi-alpha)` and `i(pi+alpha)`, both strictly inside and simple. The exponential substitution proves there are no other poles in the strip.
- Side bound: each vertical integral has modulus at most `2pi/(sinh R - 1)`.
- Top integral: `-exp(-2pi k)` times the bottom, including the orientation minus sign.
- Zero frequency is obtained by dominated convergence, not by dividing by `sinh 0`. Negative frequencies use evenness and the vanishing sine integral.

### F2/F3: transforms and positivity

- For `0 < r ≤ 1/2`, the dominating density is `pi/(2 cosh(pi t))`; this proves `p_r/r → p_0` in `L1`.
- The rescaled density for `psi_r(x/2)` is `2 p_r(2t)`; the convolution is of that rescaled density with itself.
- Fourier representation of a matrix map only requires the scalar forward-transform identity at finitely many spectral differences. No additional Fourier inversion theorem is needed.
- At each ancilla, integrate conjugations by `exp(itK) tensor I`. Positivity, the norm upper bound, and attainment on the identity are elementary.
- Handle `r=0` and `r=1` as zero and identity maps, respectively. There is no ordinary endpoint `p_1` density.

### C1/C2: coth without an assumed Mittag–Leffler expansion

- The periodic extension of `cosh(a t)` from `[-pi,pi]` is continuous because its endpoints agree. It need not have a continuous periodic derivative.
- The cosine coefficients decay as `n^-2`, so their series converges absolutely and uniformly.
- Fejér convergence identifies the sum with the original continuous periodic function. This is the one general Fourier-series theorem used in this route.
- Local uniform derivative bounds are `4R²/(2pi n)²` and `8R/(2pi n)²`. They permit termwise differentiation of `x coth(x/2)`.
- Extend the resulting `h` series through zero by domination. The scalar Taylor coefficient proves the total mass `1/3`; an imported Basel-sum identity is unnecessary.

### C3: positive density and exponential weights

- The series defining `k` diverges at `t=0`. Set `k(0)=0` or any finite value; every theorem is unaffected by this null-set modification.
- For `a > 0`, prove the transforms of `exp(-a|t|)` and `|t| exp(-a|t|)` by explicit antiderivatives on the two half-lines.
- The `n`th positive density has mass `8/(2pi n)²`. Tonelli gives `L1` membership and permits the Fourier-series interchange.
- Closed form uses the geometric series and its integrated logarithmic series only for `0 < exp(-2pi|t|) < 1`.
- For `0 ≤ v < 2pi`, use `2pi n-v ≥ (2pi-v)n` to dominate the weighted-mass series by `n^-2`. Negative `v` are automatic from the unweighted result.

### K1/K2: signs and ODE

- `A=(Q-Q*)/2`, `J=-iA`, and `D(X)=[K,X]`. These conventions are fixed.
- `Q*=rho^-1 Q rho`, and therefore `A=tanh(D/2)H`.
- `i[C,K]=-i D h(D)J=-(1-f(D))H`; this sign is necessary for `dotK=H+i[C,K]`.
- The optional ODE is `dotU=i C U`, so `d(U* K U)/dlambda=U*(dotK-i[C,K])U`.
- A standard linear ODE existence theorem is only needed to construct the optional frame `U`; it is not needed for the response or rotation identities themselves.

## Scope exclusions

This package does not formalize the locality-obstruction examples, the decorated-network gap proof, the modular clock/Bessel quadrature section, measurement simulation, or any attractive-LDP statement. It also does not assert spatial locality from a completely bounded norm estimate. Those are separate blocks. No complete Lean implementation is supplied: presenting an uncompiled fragment with unverifiable library names as a completed proof would obscure the exact remaining task. The mathematical identities and analytic limits listed above have explicit proof text ready for translation.
