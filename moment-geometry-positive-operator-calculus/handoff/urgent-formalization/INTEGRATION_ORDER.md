# Integration order

**Status:** unchecked mathematical proof expansion plus uncompiled partial Lean source. No full machine formalization is claimed.

## 1. Replace the opaque matrix-angle premise

Implement the producer in `cp_contracts.md`, following `cp_transport_proofs.tex` in order. It takes actual wire Kraus families and centered CP sandwiches, and returns the `hcross` inequality needed by the existing matrix-gap theorem. The Schur argument eliminates only the intersection subspace, not the fourth joint eigenspace. The physical-subspace identification uses an explicit reference filter and its polar factor.

## 2. Instantiate the producer for the microscopic AKLT model

Use `aklt_proofs.tex`, then `aklt_obligations.md`. Preserve the centered rank-one reference when reading the Choi radius. The bracket property is **nonassociateness**, not nonassociativity.

The new explicit lower bound is

`CΔ = lcm { binomial(r,s) : 0 ≤ s ≤ r ≤ Δ+2 }`,
`R = (Δ+1)^2 * 3^(2ℓΔ)`, `M = 2ℓΔ+1`,
`g_exp = CΔ^(-R) * M^(1-R) > 0`.

The conclusion is `g_exp ≤ g_*`, not an equality with the minimum patch gap. The matrices are rational in a nonorthonormal polynomial basis with an explicitly positive binomial Gram matrix. They are similar to Hermitian positive operators. Keep that basis/inner-product distinction when applying spectral theory.

A blocked certificate `c>0` yields the physical bound `c*g_exp/Δ`. The logarithmic-decoration corollary uses `c≥1/2`.

## 3. Replace the opaque oblique/locality premise

Use `oblique_proofs.tex`, then `oblique_obligations.md`. The orthogonalizer, adjoint commutator, quotient-angle estimate and complementary-projection step produce the actual `hcos`. The filter-locality proof supplies its input. Do not retain `hcos` as an assumed application theorem.

## 4. Close the analytic response definitions

Use `response_proofs.tex`, then `response_obligations.md`. First identify the actual derivative using log resolvents and the exponential Duhamel formula. Only then apply divided-difference algebra. The scalar Fourier and coth identities have their own proofs, including convergence and boundary estimates; they are not imported as unexplained transforms.

## Lean boundaries

`lean/SchurScalar.lean` covers scalar rational identities and comparison endpoints. `lean/AKLT.lean` covers elementary matrix/scalar ingredients. `lean/ObliqueAlgebra_uncompiled.lean` adds commutator, conjugation and scalar spectral proof scripts. The operator geometry, polynomial/SU(2) realization, and analytic transforms still need translation against the swarm's actual library interfaces. There was no Lean project or swarm source tree in this workspace to integrate with.

Standard infrastructure (finite-dimensional spectral theory, positive square roots, CP/Kraus equivalence, orthogonal projections, elementary polynomial algebra, integration and residue/Fourier theorems) is separated from application-specific results in the per-block obligation files. A completed target must derive its output from that infrastructure, not assume an equivalent certificate.
