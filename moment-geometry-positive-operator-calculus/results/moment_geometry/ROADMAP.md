# MomentGeometry — formalization roadmap and coverage ledger

Source: *Moment geometry and positive operator calculus* and its
**Formalization and reproducibility guide**, supplied by the person.
The supplied distribution itself states **proof_assistant_verified=false** for all
74 records. Statement labels in that distribution are not Lean declaration names.

## Current scope

* **74** source contract records, **1** fully source-contract verified.
* **9** record has an integrated verified component (`op:hyperbolic-clock`).
* **64** source contracts remain assigned.
* The registry's two separate future problems are not part of this source-completion target.
* Ultramath is stopped under the person's explicit instruction. The main project is built directly using the shared `/opt/lean/bin/lean` 4.33.1 and installed `/opt/mathlib`.

**No proof of a nonzero spectral gap for the spin-3/2 hexagonal AKLT model is claimed.**
The guide instead contains decorated-network transfer and finite finite-patch interfaces.

## Main build

```sh
OPENBLAS_NUM_THREADS=1 OMP_NUM_THREADS=1 python3 scripts/check_lean_moment_geometry.py
```

The latest integrated run passes twenty-eight modules and 201 audited theorem reports, all using only
`propext`, `Classical.choice`, and `Quot.sound`.

## Ordering from the guide

1. Finite interfaces: coherent moments, rational polynomial identities, graph cofactors,
   Choi positivity, exact quadrature transcripts.
2. Finite-dimensional general lemmas: entropy projection, operator divided differences,
   completely positive functional calculus, subspace angles, coupling inequalities.
3. All-degree combinatorics, local graph asymptotic, and variational convergence.
4. Heavy geometric/analytic results with explicit external-theorem interfaces, not
   unproven assumptions hidden in a headlined final theorem.

## Per-contract ledger

“Integrated component” is not equivalent to a completed registry entry. No theorem
count or compilation count substitutes for checking that a declaration matches its
source contract, including quantifiers, external hypotheses, and normalization.

### `prop:repair` — Positive repair

* Source proof: `sections/coherent_foundations.tex`
* Review status: **integrated_component**
* Dependencies: none.
* External inputs: Unitary-invariant projective tensor integration / symmetric-power Haar moments.
* Scope limits: none listed.
* Verified Lean modules: `MomentGeometry/Repair/Frame.lean`.
* Verified component: Reviewed prop:repair finite frame algebra: moment map linearity, density bounds [1/2,3/2], normalization, the (1-p)k=p scalar law and exact moment cancellation at p=(1+102δ)^{-1}. Rebuilt both independently and main-tree.
* Missing relative to contract: eq:repairframe Haar fourth moments and its Hilbert--Schmidt norm bound, the Borel probability-measure lift, and the convex relative-entropy inequality.
* Provenance: Integrated from accepted scoped integration smwi6zlvo/m8/d6, with an independently rebuilt coverage_74_audit.json.

### `an:frame-spectrum` — Exact coherent covariance spectrum

* Source proof: `sections/coherent_foundations.tex`
* Review status: **assigned**
* Dependencies: none.
* External inputs: Unitary-invariant projective tensor integration / symmetric-power Haar moments.
* Scope limits: none listed.
* Pending: Complete source-contract formalization remains pending.

### `an:dilution` — Energy retained by positive dilution

* Source proof: `sections/equilibria.tex`
* Review status: **assigned**
* Dependencies: `prop:repair`.
* External inputs: Finite-energy Monge--Ampere variational theory and convex duality.
* Scope limits: none listed.
* Pending: Complete source-contract formalization remains pending.

### `geo:sharp` — Sharp balanced entropy threshold

* Source proof: `proofs/geometry_results.tex`
* Review status: **assigned**
* Dependencies: none.
* External inputs: Kempf--Ness moment-map criterion and existence of a nonvanishing invariant for semistable vectors; Resolution of ideals, discrepancy transformation, and complex singularity exponents; Zhang Proposition 4.1 Hilbert-geodesic comparison; exact fixed-degree specialization proved in the paper; Finite-energy Monge--Ampere variational theory and convex duality.
* Scope limits: No endpoint boundedness claim.; No identification of the higher-design sharp threshold.; Balanced basis-ideal valuations are not a theorem about all singular strata of the many-particle determinant..
* Pending: Complete source-contract formalization remains pending.

### `geo:basis-lct` — Balanced basis-ideal singularity bound

* Source proof: `proofs/geometry_results.tex`
* Review status: **assigned**
* Dependencies: none.
* External inputs: Kempf--Ness moment-map criterion and existence of a nonvanishing invariant for semistable vectors; Resolution of ideals, discrepancy transformation, and complex singularity exponents.
* Scope limits: none listed.
* Pending: Complete source-contract formalization remains pending.

### `geo:exact-quantization` — Exact fixed-degree Hilbert comparison

* Source proof: `proofs/geometry_results.tex`
* Review status: **assigned**
* Dependencies: none.
* External inputs: Zhang Proposition 4.1 Hilbert-geodesic comparison; exact fixed-degree specialization proved in the paper; Finite-energy Monge--Ampere variational theory and convex duality.
* Scope limits: The epsilon-free conclusion uses constant Bergman density and the endpoint derivative argument; it is not the general asymptotic theorem..
* Pending: Complete source-contract formalization remains pending.

### `an:entropy-projection` — Exact constrained entropy projection

* Source proof: `sections/equilibria.tex`
* Review status: **assigned**
* Dependencies: `an:frame-spectrum`.
* External inputs: Finite-energy zero-Lelong-number exponential integrability; Finite-energy Monge--Ampere variational theory and convex duality.
* Scope limits: none listed.
* Pending: Complete source-contract formalization remains pending.

### `an:equilibrium` — Smooth constrained equilibria

* Source proof: `sections/equilibria.tex`
* Review status: **assigned**
* Dependencies: `geo:sharp`, `an:entropy-projection`, `an:dilution`.
* External inputs: Finite-energy Monge--Ampere variational theory and convex duality; Finite-energy zero-Lelong-number exponential integrability; Complex Monge--Ampere Lp, Holder, and higher elliptic regularity.
* Scope limits: Every minimizer is smooth, but uniqueness of the minimizer is not asserted.; Uniform estimates require a compact gamma range and uniformly controlled smooth W..
* Pending: Complete source-contract formalization remains pending.

### `an:lower-comparison` — Lower comparison with explicit finite-test error

* Source proof: `sections/equilibria.tex`
* Review status: **assigned**
* Dependencies: `geo:exact-quantization`.
* External inputs: Finite-energy Monge--Ampere variational theory and convex duality.
* Scope limits: One-sided lower energy comparison; not an attractive pressure upper bound..
* Pending: Complete source-contract formalization remains pending.

### `geo:cubic` — Complete cubic-support classification

* Source proof: `proofs/geometry_cubic.tex`
* Review status: **assigned**
* Dependencies: none.
* External inputs: Unitary-invariant projective tensor integration / symmetric-power Haar moments; Kempf--Ness moment-map criterion and existence of a nonvanishing invariant for semistable vectors; Closed-orbit / Cartan classification for complex 3-qutrit tensors and the E6 order-three grading; Hesse normal form for smooth plane cubics.
* Scope limits: Classification is unitary rather than arbitrary projective equivalence.; Smooth case has unique Hesse measure; triangle case permits the specified continuous phase measures..
* Pending: Complete source-contract formalization remains pending.

### `geo:hesse-bound` — Robust Hesse ensemble certificate

* Source proof: `proofs/geometry_hesse.tex`
* Review status: **assigned**
* Dependencies: none.
* External inputs: Unitary-invariant projective tensor integration / symmetric-power Haar moments.
* Scope limits: none listed.
* Pending: Complete source-contract formalization remains pending.

### `geo:hesse-third` — Hesse third moment and exposed coherent face

* Source proof: `proofs/geometry_hesse.tex`
* Review status: **assigned**
* Dependencies: none.
* External inputs: none.
* Scope limits: none listed.
* Pending: Complete source-contract formalization remains pending.

### `geo:confidence` — Finite-sample Hesse confidence certificate

* Source proof: `proofs/geometry_hesse.tex`
* Review status: **assigned**
* Dependencies: `geo:hesse-bound`.
* External inputs: none.
* Scope limits: Not device independent.; Independent copies of the averaged density do not give matched replica access.; SciPy quantile evaluation is numerical, not an interval-certified implementation..
* Pending: Complete source-contract formalization remains pending.

### `geo:general-cert` — General support-and-weight ensemble certificate

* Source proof: `proofs/geometry_hesse.tex`
* Review status: **assigned**
* Dependencies: `geo:hesse-bound`.
* External inputs: none.
* Scope limits: The global support estimate and injective weight map must be supplied for a new ensemble..
* Pending: Complete source-contract formalization remains pending.

### `geo:singer-nef` — An exact coupling obstruction and repair threshold

* Source proof: `proofs/geometry_singer.tex`
* Review status: **assigned**
* Dependencies: none.
* External inputs: Known weighted ten-point projective-toric design; new claims concern its geometry.
* Scope limits: The underlying ten-point design is attributed to the literature..
* Pending: Complete source-contract formalization remains pending.

### `geo:k3-lattice` — The lattice of the design cover

* Source proof: `proofs/geometry_singer.tex`
* Review status: **assigned**
* Dependencies: `geo:singer-nef`.
* External inputs: Symplectic and non-symplectic prime-order K3 automorphism lattices.
* Scope limits: none listed.
* Pending: Complete source-contract formalization remains pending.

### `geo:flag-theorem` — Arbitrary contacts on a flagged qutrit frame

* Source proof: `proofs/geometry_qutrit.tex`
* Review status: **assigned**
* Dependencies: none.
* External inputs: Haar steering body and projective-simulable POVM convex geometry.
* Scope limits: Geometric flagged support is required..
* Pending: Complete source-contract formalization remains pending.

### `geo:cusp` — A negative cusp for pinched clusters

* Source proof: `proofs/geometry_qutrit.tex`
* Review status: **assigned**
* Dependencies: `geo:flag-theorem`.
* External inputs: none.
* Scope limits: The coefficient margin is not a numerical neighborhood radius..
* Pending: Complete source-contract formalization remains pending.

### `geo:operational` — Uniform operational neighborhoods

* Source proof: `proofs/geometry_qutrit.tex`
* Review status: **assigned**
* Dependencies: `geo:flag-theorem`, `geo:cusp`.
* External inputs: Haar steering body and projective-simulable POVM convex geometry.
* Scope limits: Radius is qualitative and depends on d,m.; Qutrit extension is around conv(reducible POVMs), not every irreducible qutrit POVM.; Zero labelled effects are allowed..
* Pending: Complete source-contract formalization remains pending.

### `geo:boundary` — Exact boundary within the center classes

* Source proof: `proofs/geometry_qutrit.tex`
* Review status: **assigned**
* Dependencies: `geo:operational`, `geo:flag-theorem`, `geo:cusp`.
* External inputs: none.
* Scope limits: none listed.
* Pending: Complete source-contract formalization remains pending.

### `lem:coherent-graph-integral` — The local graph integral

* Source proof: `proofs/coherent_gram.tex`
* Review status: **assigned**
* Dependencies: none.
* External inputs: Directed matrix-tree theorem and accretive complex Gaussian integral.
* Scope limits: none listed.
* Pending: Complete source-contract formalization remains pending.

### `thm:coherent-spectral-law` — Coherent spectral law

* Source proof: `proofs/coherent_gram.tex`
* Review status: **assigned**
* Dependencies: `lem:coherent-graph-integral`.
* External inputs: Directed matrix-tree theorem and accretive complex Gaussian integral.
* Scope limits: Almost sure convergence requires sum_m 1/n_m<infinity.; Conditioning extension requires fixed bounded moment family and n_m epsilon_m^2->infinity.; No exponentially small eigenvalue or log determinant control..
* Pending: Complete source-contract formalization remains pending.

### `lem:tree-one-noncrossing` — The noncrossing layer

* Source proof: `proofs/coherent_gram.tex`
* Review status: **assigned**
* Dependencies: none.
* External inputs: Directed matrix-tree theorem and accretive complex Gaussian integral; Noncrossing partitions, Kreweras complementation, and Marchenko--Pastur moments.
* Scope limits: none listed.
* Pending: Complete source-contract formalization remains pending.

### `thm:coherent-free-limit` — Support, exponential moments, and the free limit

* Source proof: `proofs/coherent_gram.tex`
* Review status: **assigned**
* Dependencies: `thm:coherent-spectral-law`, `lem:tree-one-noncrossing`.
* External inputs: Noncrossing partitions, Kreweras complementation, and Marchenko--Pastur moments.
* Scope limits: Support is unbounded for every finite q; compact support is asserted only for the limiting Marchenko--Pastur law as q tends to infinity..
* Pending: Complete source-contract formalization remains pending.

### `eq:coherent-finite-moments` — Finite-degree coherent Gram trace identities

* Source proof: `proofs/coherent_gram.tex`
* Review status: **integrated_component**
* Dependencies: `lem:coherent-graph-integral`.
* External inputs: none.
* Scope limits: none listed.
* Verified Lean modules: `MomentGeometry/Coherent/Moments.lean`, `MomentGeometry/Coherent/CycleCofactor.lean`, `MomentGeometry/Coherent/UnitDensity.lean`.
* Verified component: Exact finite expected second/third/fourth trace books (definitions plus rational denominator algebra), including the independent-source-moment and finite-sample corrections and cubic limit expansion. Verified smwi6zlvo/m1/d2 adds asymptotic D-ratio forms with Dprime/D -> 2^q, quotient cycle outdegree Laplacians retaining parallel edges/discarding loops, restricted-growth partition words, and explicit order-<=(4) cofactor checks, τ hist {1:14,2:1}, noncrossing equivalence, root-independence and positivity. The m1 scoped review passed both new modules and 16 standard-axiom reports; current direct eight-module build passes 117 reports (including the independent headline audit module). No overall asymptotic spectral law is accepted.
* Missing relative to contract: Haar tensor moment construction; random coherent Gram matrices and their empirical laws; local graph integral, arbitrary-order cofactor-support formula, moment/variance and convergence with conditioned laws. Exact finite formulas do not certify any of these.
* Provenance: Written against proofs/coherent_gram.tex; it does not upgrade a symbolic finite check to the spectral-law theorem.

### `lem:conditional-replacement` — Conditional replacement estimate

* Source proof: `proofs/probability_repulsive.tex`
* Review status: **assigned**
* Dependencies: none.
* External inputs: none.
* Scope limits: The one-coordinate exponent does not reach the attractive target near gamma=1..
* Pending: Complete source-contract formalization remains pending.

### `prop:microscopic-moment-repair` — Entropy-controlled repair of microscopic moments

* Source proof: `proofs/probability_repulsive.tex`
* Review status: **assigned**
* Dependencies: `lem:conditional-replacement`, `an:frame-spectrum`.
* External inputs: Unitary-invariant projective tensor integration / symmetric-power Haar moments.
* Scope limits: none listed.
* Pending: Complete source-contract formalization remains pending.

### `thm:repulsive-design-ldp` — Shrinking-design pressure and large deviations

* Source proof: `proofs/probability_repulsive.tex`
* Review status: **assigned**
* Dependencies: `prop:microscopic-moment-repair`, `an:lower-comparison`.
* External inputs: Unrestricted positive-temperature LDP for polarized compact complex manifolds; Sanov theorem, entropy variational formula, and the bounded-continuous Laplace/LDP equivalence on a compact state space.
* Scope limits: Repulsive sign only.; Does not establish attractive pressure or attractive LDP near gamma=1..
* Pending: Complete source-contract formalization remains pending.

### `op:heap` — The order-polynomial logarithm

* Source proof: `sections/positive_calculus.tex`
* Review status: **assigned**
* Dependencies: none.
* External inputs: Cartier--Foata inversion, heap order polynomials, and Eulerian descent expansion.
* Scope limits: none listed.
* Pending: Complete source-contract formalization remains pending.

### `op:root-response` — Ordered root-response obstruction

* Source proof: `sections/positive_calculus.tex`
* Review status: **assigned**
* Dependencies: `op:heap`.
* External inputs: none.
* Scope limits: none listed.
* Pending: Complete source-contract formalization remains pending.

### `op:hyperbolic-clock` — Positive hyperbolic clock and local error

* Source proof: `sections/positive_calculus.tex`
* Review status: **integrated_component**
* Dependencies: none.
* External inputs: Infinite divisibility of the hyperbolic product and Gamma subordination.
* Scope limits: Norm contraction does not imply an interaction-norm locality bound..
* Verified Lean modules: `MomentGeometry/Operator/CP/Base.lean`, `MomentGeometry/Operator/CP/Closure.lean`, `MomentGeometry/Operator/Clock.lean`.
* Verified component: Choi-style multiplier criterion; CP of matrix conjugation; PSD Gaussian/resolvent kernels; Euler sine-product convergence; complete positivity of the hyperbolic clock kernel for every real exponent >=0 (dense identity at 0, actual CP at tau>0).
* Missing relative to contract: Gamma-subordinated heat-channel identity and its full functional-calculus realization; fourth-nested-commutator error bound; full contract in proofs/positive_calculus.tex.
* Provenance: Copied from reviewed scoped packages results/coherent_continuation/review_smwhh7nna_m2/lean/{ModularCPBase,ModularCPClosure}.lean, with namespace/import adaptation and fresh build. Inherited declarations are not a certificate of the whole registered result.

### `op:metric-range` — Exact metric range

* Source proof: `sections/positive_calculus.tex`
* Review status: **assigned**
* Dependencies: none.
* External inputs: Petz correspondence between symmetric operator means and monotone quantum metrics.
* Scope limits: none listed.
* Pending: Complete source-contract formalization remains pending.

### `op:quadrature-theorem` — Finite positive quadrature with local certificates

* Source proof: `sections/positive_calculus.tex`
* Review status: **assigned**
* Dependencies: `op:hyperbolic-clock`.
* External inputs: Positive Gaussian/Radau quadrature and Peano-kernel Hermite interpolation remainder.
* Scope limits: Degenerate finite-support rules terminate exactly.; Scalar multiplier order is not positive-map order.; Implementation must add independently certified rounding error..
* Pending: Complete source-contract formalization remains pending.

### `op:information-bracket` — Fixed-state information-matrix bracket

* Source proof: `sections/positive_calculus.tex`
* Review status: **assigned**
* Dependencies: `op:quadrature-theorem`, `op:metric-range`.
* External inputs: Petz correspondence between symmetric operator means and monotone quantum metrics.
* Scope limits: Finite approximants are not claimed to define globally monotone metrics for every state..
* Pending: Complete source-contract formalization remains pending.

### `op:one-clock` — One-node positive hyperbolic approximation

* Source proof: `sections/positive_calculus.tex`
* Review status: **assigned**
* Dependencies: `op:quadrature-theorem`.
* External inputs: none.
* Scope limits: none listed.
* Pending: Complete source-contract formalization remains pending.

### `q:lem-schur` — A quotient-metric estimate

* Source proof: `proofs/quantum_results.tex`
* Review status: **assigned**
* Dependencies: none.
* External inputs: none.
* Scope limits: none listed.
* Pending: Complete source-contract formalization remains pending.

### `q:thm-wire-gap` — Two-port CP gap criterion

* Source proof: `proofs/quantum_results.tex`
* Review status: **integrated_component**
* Dependencies: `q:lem-schur`.
* External inputs: Choi criterion for complete positivity.
* Scope limits: Gap refers to the sum of norm-one blocked complement projections.; Core dimension and core condition number do not enter the bound..
* Verified Lean modules: `MomentGeometry/Network/CPOrder.lean`, `MomentGeometry/Network/WireGap.lean`, `MomentGeometry/Network/GapAssembly.lean`, `MomentGeometry/Network/GapSpectral.lean`, `MomentGeometry/Network/GapSpectral.lean`.
* Verified component: Finite CP order algebra, conflict/Rayleigh matrix assembly and true finite-dimensional spectral proof of blocked gap from hcross and the full-ground-space projector. Rebuilt 14 standard-axiom declarations.
* Missing relative to contract: Full-Schmidt-rank CP transport, injectivity, CP-tensor sandwich, whitening/signed cancellation and physical edge-subspace identification. hcross is an explicit remaining input, not the finished Schur estimate.
* Provenance: Accepted at finite matrix step, smwi6zlvo/m5/d5; unsupported angle/transport assumptions are not discharged.

### `q:lem-seed` — Finite-patch comparison

* Source proof: `proofs/quantum_results.tex`
* Review status: **source_contract_verified**
* Dependencies: `q:thm-wire-gap`.
* External inputs: none.
* Scope limits: The finite-patch kernel and positive gap are hypotheses to verify in a new model..
* Verified Lean modules: `MomentGeometry/Swarm/Seed.lean`.
* Verified component: Complete operator-level q:lem-seed at its full assumptions: coverage reindexing, exact common kernel, (g/m)H_block ≤ H_micro, and every gap certificate γ transfers to g_*γ/m. The numerical gap is represented faithfully by its lower-bound certificates, not by an undefined gap functional.
* Missing relative to contract: Physical patch instantiations including AKLT tensor-image/kernel and actual g_*(Δ,ℓ)>0. These are separate q:cor-aklt obligations, not a missing clause of the operator-level seed theorem.
* Provenance: Independently rebuilt smwi6zlvo/m6/d3 and integrated. Source hypotheses and coverage are preserved; no physical nonzero gap is inferred from this algebraic comparison alone.

### `q:cor-aklt` — Logarithmic sufficient decoration

* Source proof: `proofs/quantum_results.tex`
* Review status: **integrated_component**
* Dependencies: `q:thm-wire-gap`, `q:lem-seed`.
* External inputs: AKLT valence-bond representation and decorated-parent tensor conventions.
* Scope limits: Decorated networks; no universal undecorated AKLT gap theorem.; Physical lower bound retains the positive finite-patch factor g_*(Delta,ell)..
* Verified Lean modules: `MomentGeometry/AKLT/Wire.lean`, `MomentGeometry/AKLT/Radius.lean`, `MomentGeometry/AKLT/Decoration.lean`, `MomentGeometry/AKLT/Finite.lean`, `MomentGeometry/AKLT/Bridge.lean`.
* Verified component: Spin-one normalized wire/iteration algebra, centered transfer radius and bounds, two-port cosine arithmetic, minimal-level decoration inequalities, positive finite patch minima, dimension arithmetic, coprime product divisibility. 57 audited declarations in independent review.
* Missing relative to contract: Pauli/Kraus identity and Choi spectrum, edge-bracket irreducibility/nonassociativity, SU(2) regional tensor image, actual finite patch gaps and wire/seed input obligations.
* Provenance: Arithmetic only, smwi6zlvo/m7/d7. g_*>0 stays a side condition; no undecorated spin-3/2 hexagonal gap is claimed.

### `q:thm-oblique` — A compatible-idempotent certificate

* Source proof: `proofs/quantum_results.tex`
* Review status: **integrated_component**
* Dependencies: none.
* External inputs: none.
* Scope limits: none listed.
* Verified Lean modules: `MomentGeometry/Swarm/Oblique.lean`.
* Verified component: Defect-matrix assembly from hcos and Rayleigh hypotheses to (1-ρ)H≤H², complement projection version and row/column-sum criterion. Independently rebuilt with standard axioms.
* Missing relative to contract: Orthogonalizer, adjoint-commutator bound, quotient construction of cosine matrix and input perturbation ODE/locality facts.
* Provenance: Finite assembly only, smwi6zlvo/m6/d3. hcos remains an interface, not a supplied cosine theorem.

### `q:cor-filtered` — Filtered commuting-projector models

* Source proof: `proofs/quantum_results.tex`
* Review status: **integrated_component**
* Dependencies: `q:thm-oblique`.
* External inputs: none.
* Scope limits: Locality is supplied by product filters and bounded original supports..
* Verified Lean modules: `MomentGeometry/Swarm/Filtered.lean`, `MomentGeometry/Swarm/Oblique.lean`.
* Verified component: Similarity/filter transport of idempotence and commutativity, common kernel, and gap inequality from the conditional hcos and row/column defect inputs.
* Missing relative to contract: Product-filter locality and the perturbation bound ||P_i-E_i||≤exp(2sε)-1 used to instantiate the defect matrix; no physical nonzero gap is asserted from the arithmetic alone.
* Provenance: Accepted with those explicit input obligations, smwi6zlvo/m6/d3.

### `q:thm-powers` — Exact response of fractional powers

* Source proof: `proofs/quantum_results.tex`
* Review status: **integrated_component**
* Dependencies: none.
* External inputs: Positive-definite hyperbolic quotient functions and Schur multiplier inequalities.
* Scope limits: Hermitian and anti-Hermitian inputs obey the KMS compatibility relation.; Power is not renormalized to trace one..
* Verified Lean modules: `MomentGeometry/Operator/KMS.lean`.
* Verified component: Regular scalar Hermitian and anti-Hermitian response functions with limiting values r and r^2 and the exact square-ratio for chi_r. Component only.
* Missing relative to contract: The matrix exponential-divided-difference representation of fractional powers, actual H_r/A_r matrix parts, CP amplification and masses r and r², and derivative-limit assembly.
* Provenance: Registry matching validated by smwi6zlvo/m8/d6; scalar functions are not the final matrix theorem.

### `q:kms-compatibility` — KMS-compatible tangent relation

* Source proof: `proofs/quantum_results.tex`
* Review status: **integrated_component**
* Dependencies: `q:thm-powers`.
* External inputs: none.
* Scope limits: none listed.
* Verified Lean modules: `MomentGeometry/Operator/KMS.lean`.
* Verified component: Regular scalar Hermitian and anti-Hermitian divided-difference ratios (values r and r^2 at zero), auxilliary half-angle identities, and chi_r(x)*tanh(x/2)=tanh(r*x/2)*psi_r(x). The wrong earlier scalar identity was corrected before integration.
* Missing relative to contract: Matrix-valued divided-difference integral representation, right-derivative KMS compatibility, and complete-power response Q_r. Those are differential/functional-calculus obligations, not scalar arithmetic.
* Provenance: Written for the new source contract; not an inference from the separate hyperbolic-clock kernel.

### `q:prop-rotation` — A positive rotation generator

* Source proof: `proofs/quantum_results.tex`
* Review status: **assigned**
* Dependencies: `q:thm-powers`, `q:kms-compatibility`.
* External inputs: Positive-definite hyperbolic quotient functions and Schur multiplier inequalities.
* Scope limits: none listed.
* Pending: Complete source-contract formalization remains pending.

### `q:prop-ratio-obstruction` — Exact local ratios, nonlocal log difference

* Source proof: `proofs/quantum_results.tex`
* Review status: **assigned**
* Dependencies: none.
* External inputs: none.
* Scope limits: Failure of exact log-difference locality does not rule out decay with additional assumptions..
* Pending: Complete source-contract formalization remains pending.

### `q:prop-filter-obstruction` — No generic same-norm modular bound

* Source proof: `proofs/quantum_results.tex`
* Review status: **assigned**
* Dependencies: `q:thm-powers`.
* External inputs: none.
* Scope limits: Obstructs a generic locally bounded estimate in the same interaction norm; does not obstruct ordinary operator-norm CP contraction..
* Pending: Complete source-contract formalization remains pending.

### `att:coarse-entropy` — An exact coarse-graining bound

* Source proof: `proofs/attractive_high_temperature.tex`
* Review status: **assigned**
* Dependencies: none.
* External inputs: Product-reference entropy tensorization, chain rule, finite-alphabet type bounds, and entropy variational formula; needed inequalities are proved in the manuscript.
* Scope limits: none listed.
* Pending: Complete source-contract formalization remains pending.

### `att:entropy-chaos` — Entropy chaos from compact conditional densities

* Source proof: `proofs/attractive_high_temperature.tex`
* Review status: **assigned**
* Dependencies: `att:coarse-entropy`.
* External inputs: Product-reference entropy tensorization, chain rule, finite-alphabet type bounds, and entropy variational formula; needed inequalities are proved in the manuscript.
* Scope limits: The limiting empirical law may be a nontrivial mixture; this is not restricted to a deterministic directing measure..
* Pending: Complete source-contract formalization remains pending.

### `att:conditional-compactness` — Compact attractive conditionals

* Source proof: `proofs/attractive_high_temperature.tex`
* Review status: **assigned**
* Dependencies: none.
* External inputs: Compactness of normalized plurisubharmonic potentials, upper semicontinuity of extended Aubin--Mabuchi energy, and measure-energy duality.
* Scope limits: Compactness uses a strict exponent margin r*gamma<1/3 with r>1..
* Pending: Complete source-contract formalization remains pending.

### `att:quadratic-pressure` — A small-coupling exponential estimate

* Source proof: `proofs/attractive_high_temperature.tex`
* Review status: **assigned**
* Dependencies: none.
* External inputs: Product-reference entropy tensorization, chain rule, finite-alphabet type bounds, and entropy variational formula; needed inequalities are proved in the manuscript; Compactness of normalized plurisubharmonic potentials, upper semicontinuity of extended Aubin--Mabuchi energy, and measure-energy duality.
* Scope limits: Bound applies to both signs of sufficiently small t; constants are uniform in k and in references with the fixed Lp bound.; Negative-t conditionals need not have a uniform positive lower bound..
* Pending: Complete source-contract formalization remains pending.

### `att:general-product-energy` — Product-law mean energy from repulsive pressure

* Source proof: `proofs/attractive_high_temperature.tex`
* Review status: **assigned**
* Dependencies: `att:quadratic-pressure`, `an:lower-comparison`.
* External inputs: Unrestricted positive-temperature LDP for polarized compact complex manifolds.
* Scope limits: Only repulsive pressure is imported.; A change to a reference-adapted orthonormal basis changes energy by O(1/k)..
* Pending: Complete source-contract formalization remains pending.

### `att:directing-class` — A compact class for all directing densities

* Source proof: `proofs/attractive_high_temperature.tex`
* Review status: **assigned**
* Dependencies: `att:conditional-compactness`.
* External inputs: Compactness of normalized plurisubharmonic potentials, upper semicontinuity of extended Aubin--Mabuchi energy, and measure-energy duality.
* Scope limits: Arbitrary continuous tilts enter only after uniform approximation at the pressure level..
* Pending: Complete source-contract formalization remains pending.

### `att:smooth-net` — Uniform smooth reference approximation

* Source proof: `proofs/attractive_high_temperature.tex`
* Review status: **assigned**
* Dependencies: `att:directing-class`.
* External inputs: Positive smooth heat kernels for elliptic diffusions with prescribed smooth invariant probability, Lp contraction, and strong continuity; Compactness of normalized plurisubharmonic potentials, upper semicontinuity of extended Aubin--Mabuchi energy, and measure-energy duality.
* Scope limits: Reference Lr bounds and positive lower bounds remain uniform as the approximation net is refined..
* Pending: Complete source-contract formalization remains pending.

### `att:gibbs-energy-limit` — Entropy and energy limits of attractive Gibbs laws

* Source proof: `proofs/attractive_high_temperature.tex`
* Review status: **assigned**
* Dependencies: `att:entropy-chaos`, `att:directing-class`, `att:smooth-net`, `att:quadratic-pressure`, `att:general-product-energy`.
* External inputs: Product-reference entropy tensorization, chain rule, finite-alphabet type bounds, and entropy variational formula; needed inequalities are proved in the manuscript.
* Scope limits: Does not assert microscopic energy compactness for arbitrary symmetric laws with bounded entropy and energy.; Cell-conditioned laws need not retain the compact conditional-density property..
* Pending: Complete source-contract formalization remains pending.

### `att:good-rate` — Good rate and entropy-continuous energy recovery

* Source proof: `proofs/attractive_high_temperature.tex`
* Review status: **assigned**
* Dependencies: none.
* External inputs: Compactness of normalized plurisubharmonic potentials, upper semicontinuity of extended Aubin--Mabuchi energy, and measure-energy duality; Product-reference entropy tensorization, chain rule, finite-alphabet type bounds, and entropy variational formula; needed inequalities are proved in the manuscript.
* Scope limits: Relative entropy in the compact-potential dual is against an unnormalized finite reference measure.; Infinite entropy is assigned free energy +infinity; the Renyi coercivity proves that this equals the compact infimum..
* Pending: Complete source-contract formalization remains pending.

### `att:full-laplace` — Full attractive determinant Laplace principle

* Source proof: `proofs/attractive_high_temperature.tex`
* Review status: **assigned**
* Dependencies: `att:gibbs-energy-limit`, `att:general-product-energy`, `att:good-rate`.
* External inputs: Sanov theorem, entropy variational formula, and the bounded-continuous Laplace/LDP equivalence on a compact state space.
* Scope limits: The range is a strict subinterval of the scalar section integrability threshold..
* Pending: Complete source-contract formalization remains pending.

### `att:design-laplace` — Full attractive LDP on shrinking design tubes

* Source proof: `proofs/attractive_high_temperature.tex`
* Review status: **assigned**
* Dependencies: `att:full-laplace`, `att:general-product-energy`, `att:good-rate`.
* External inputs: Positive smooth heat kernels for elliptic diffusions with prescribed smooth invariant probability, Lp contraction, and strong continuity; Sanov theorem, entropy variational formula, and the bounded-continuous Laplace/LDP equivalence on a compact state space.
* Scope limits: The unconditioned LDP gives the upper bound on fixed closed tubes, followed by tube radius tending to zero.; The lower bound uses exact-design smooth product references and L1 energy convergence..
* Pending: Complete source-contract formalization remains pending.

### `att:polarized-extension` — Polarized manifolds and all projective dimensions

* Source proof: `proofs/attractive_high_temperature.tex`
* Review status: **assigned**
* Dependencies: `att:quadratic-pressure`, `att:gibbs-energy-limit`, `att:good-rate`, `att:full-laplace`, `att:design-laplace`.
* External inputs: Unrestricted positive-temperature LDP for polarized compact complex manifolds; Compactness of normalized plurisubharmonic potentials, upper semicontinuity of extended Aubin--Mabuchi energy, and measure-energy duality; Positive smooth heat kernels for elliptic diffusions with prescribed smooth invariant probability, Lp contraction, and strong continuity.
* Scope limits: Unrestricted full LDP on every stated polarized manifold.; Shrinking fixed-design constraints are asserted on CPq with anticanonical polarization and gamma<1/(q+1), using unitary averaging.; The general-manifold statement does not assert arbitrary moment-constrained recovery without an additional repair..
* Pending: Complete source-contract formalization remains pending.

### `att:haar-minimizer` — Zero pressure and the unique Haar equilibrium

* Source proof: `proofs/attractive_high_temperature.tex`
* Review status: **assigned**
* Dependencies: `att:gibbs-energy-limit`, `att:polarized-extension`, `att:full-laplace`, `att:design-laplace`, `ac:tubes`, `ac:concentration`.
* External inputs: none.
* Scope limits: Strict uniqueness uses exponential separation, not only convergence in probability..
* Pending: Complete source-contract formalization remains pending.

### `tor:vertices` — The assignment vertices

* Source proof: `proofs/toric_assignment.tex`
* Review status: **assigned**
* Dependencies: none.
* External inputs: One-variable Jensen formula, phase orthogonality, and the strong law; the assignment-vertex and modal-probability reductions are proved in the manuscript.
* Scope limits: Bounds concern the phase-averaged logarithm, not pointwise determinant values..
* Pending: Complete source-contract formalization remains pending.

### `tor:finite-certificate` — Finite assignment certificate

* Source proof: `proofs/toric_assignment.tex`
* Review status: **assigned**
* Dependencies: `tor:vertices`.
* External inputs: none.
* Scope limits: The energy error is at most log(N)/k + log(N!)/(kN), hence at most 2log(N)/k.; No phase inverse-moment estimate is asserted..
* Pending: Complete source-contract formalization remains pending.

### `tor:cost-limit` — Convergence of the unbounded assignment cost

* Source proof: `proofs/toric_assignment.tex`
* Review status: **assigned**
* Dependencies: none.
* External inputs: One-variable Jensen formula, phase orthogonality, and the strong law; the assignment-vertex and modal-probability reductions are proved in the manuscript; Toric Legendre/Monge--Ampere correspondence and Kantorovich duality; the unbounded-cost extension is proved with marginal tail control.
* Scope limits: Boundary singularities are controlled by a coupling-independent marginal logarithmic tail.; No uniform positive lower bound on all coordinates is assumed..
* Pending: Complete source-contract formalization remains pending.

### `tor:energy-transport` — Relative-entropy transport formula

* Source proof: `proofs/toric_assignment.tex`
* Review status: **assigned**
* Dependencies: none.
* External inputs: Toric Legendre/Monge--Ampere correspondence and Kantorovich duality; the unbounded-cost extension is proved with marginal tail control.
* Scope limits: Energy equals (q+1) times the KL optimal transport cost; both simplex marginals are probability measures..
* Pending: Complete source-contract formalization remains pending.

### `tor:mean-energy` — Actual Slater mean energy for toric reference laws

* Source proof: `proofs/toric_assignment.tex`
* Review status: **assigned**
* Dependencies: `tor:finite-certificate`, `tor:cost-limit`, `tor:energy-transport`.
* External inputs: none.
* Scope limits: L1 convergence for a general toric reference invokes deterministic lower comparison for its polarization.; For Haar reference the elementary universal lower bound alone gives L1 convergence in every dimension.; The theorem identifies product mean energy, not angular exponential inverse moments..
* Pending: Complete source-contract formalization remains pending.

### `ac:canonical-poincare` — Canonical-volume Poincar\'e inequality

* Source proof: `proofs/attractive_concentration.tex`
* Review status: **assigned**
* Dependencies: none.
* External inputs: Compact Kahler minimal L2 solution of dbar for positive line bundles, via Bochner--Kodaira curvature inequality.
* Scope limits: The norm uses the specified Hermitian metric G; top-form and background-volume factors cancel..
* Pending: Complete source-contract formalization remains pending.

### `ac:variance` — Attractive covariance and exponential tilts

* Source proof: `proofs/attractive_concentration.tex`
* Review status: **assigned**
* Dependencies: `ac:canonical-poincare`.
* External inputs: Compact Kahler minimal L2 solution of dbar for positive line bundles, via Bochner--Kodaira curvature inequality.
* Scope limits: Integrability is an explicit hypothesis beyond the independently supplied unconditional range.; Curvature comparison and covector norms use G=2pi omega0..
* Pending: Complete source-contract formalization remains pending.

### `ac:ward` — Sharp covariance of the first moment

* Source proof: `proofs/attractive_concentration.tex`
* Review status: **assigned**
* Dependencies: `ac:variance`.
* External inputs: Unitary-invariant projective tensor integration / symmetric-power Haar moments.
* Scope limits: Uses the exact projective SL(D) Jacobian and the determinant-one symmetric-power representation.; Finiteness in the attractive range forces gamma<1-1/N..
* Pending: Complete source-contract formalization remains pending.

### `ac:integrability` — Integrability by monomial degeneration

* Source proof: `proofs/attractive_concentration.tex`
* Review status: **assigned**
* Dependencies: none.
* External inputs: Resolution of ideals, discrepancy transformation, and complex singularity exponents.
* Scope limits: Gives complex singularity exponent at least 1/m by monomial degeneration.; For the anticanonical determinant it guarantees integrability for gamma<1/(q+1), not the near-one range..
* Pending: Complete source-contract formalization remains pending.

### `ac:concentration` — Attractive empirical concentration

* Source proof: `proofs/attractive_concentration.tex`
* Review status: **assigned**
* Dependencies: `ac:variance`, `ac:integrability`.
* External inputs: none.
* Scope limits: Unconditional for gamma<1/(q+1).; For larger gamma below one the partition finiteness must be established separately..
* Pending: Complete source-contract formalization remains pending.

### `ac:tubes` — Moment tubes and propagation of chaos

* Source proof: `proofs/attractive_concentration.tex`
* Review status: **assigned**
* Dependencies: `ac:concentration`.
* External inputs: none.
* Scope limits: Fixed-order projective moments only; constants may depend on q, gamma, and the moment order.; Propagation of chaos is for each fixed number of particle labels..
* Pending: Complete source-contract formalization remains pending.

### `cy:finite-convexity` — Convexity of the product mean energy

* Source proof: `proofs/nonlinear_green.tex`
* Review status: **assigned**
* Dependencies: none.
* External inputs: none.
* Scope limits: Rank-two pencil reduction is outside a proper analytic exceptional locus.; The coherent-moment Hessian identity is exact at fixed k; no convergence of the Hessians is asserted..
* Pending: Complete source-contract formalization remains pending.

### `cy:green-formula` — Nonlinear Green representation

* Source proof: `proofs/nonlinear_green.tex`
* Review status: **assigned**
* Dependencies: `cy:finite-convexity`, `att:general-product-energy`, `att:polarized-extension`.
* External inputs: Yau existence and uniqueness for the prescribed smooth positive Monge--Ampere probability volume, plus elliptic implicit-function differentiability modulo constants; Compactness of normalized plurisubharmonic potentials, upper semicontinuity of extended Aubin--Mabuchi energy, and measure-energy duality.
* Scope limits: Convergence in each finite Lp topology; no uniform-norm or metric-derivative convergence.; Solves the determinant instance of the cited mean-energy/Green representation questions, not the assertion for arbitrary singular Hamiltonians.; No complex zero-free partition-function assertion is made..
* Pending: Complete source-contract formalization remains pending.

### `cy:interpolation-sampling` — Random interpolation divisors and sampling error

* Source proof: `proofs/nonlinear_green.tex`
* Review status: **assigned**
* Dependencies: `cy:green-formula`.
* External inputs: Poincare--Lelong identity with dd^c=i partial barpartial/(2pi); basic Hilbert-space sample-variance identity; Compactness of normalized plurisubharmonic potentials, upper semicontinuity of extended Aubin--Mabuchi energy, and measure-energy duality.
* Scope limits: Zero-divisor currents converge weakly.; The explicit variance bound controls fixed-k sampling error, not the polynomial-level approximation bias.; Sample-only procedure assumes evaluation of sections and Hermitian norm, and independent sample access to mu; efficient sampling and finite-precision conditioning are not asserted..
* Pending: Complete source-contract formalization remains pending.

### `cy:hessian-hierarchy` — Finite Hessian as squared coherent-moment discrepancies

* Source proof: `proofs/nonlinear_green.tex`
* Review status: **assigned**
* Dependencies: `cy:finite-convexity`.
* External inputs: none.
* Scope limits: Finite-k identity only; truncated sums give nonnegative lower bounds on the Hessian..
* Pending: Complete source-contract formalization remains pending.

