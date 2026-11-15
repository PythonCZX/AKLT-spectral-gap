# CP and quotient-angle integration contracts

Status: mathematical proof expansion supplied; Lean scalar closures supplied but uncompiled. The matrix/operator proofs are not yet Lean code. No verification was run.

## Main producer the swarm should implement

`cp_transport_hcross`

Inputs:
- a finite simple graph and explicit finite-dimensional port spaces;
- nonzero core maps, nonzero full-Schmidt-rank edge vectors;
- wire Kraus families and the coordinate Gram identity;
- faithful rank-one reference maps;
- CP sandwiches with defects in [0,1).

Output, for each pair of edge-complement projections and every vector ξ:

`Re ⟪h_e ξ, h_f ξ⟫ ≥ -C[e,f] * ‖h_e ξ‖ * ‖h_f ξ‖`,

where C[e,f]=0 on disjoint edges and B(delta_i,delta_j) at a shared vertex.

This is the missing `hcross` argument to the existing matrix-gap theorem. It is a conclusion, not an input.

## Dependency order

1. Kraus tensor family → tensor CP order.
2. Faithful product reference → strictly positive Gram → injective block maps.
3. Four-sector decomposition of two commuting projections.
4. Coercive compression on the intersection W; explicit minimizing lift.
5. Schur cross Gram and exact normalized-angle identity.
6. CP mixed-defect identities → bounded whitened A,B,D.
7. Actual physical ranges L E_e; reference L0 E_e and L0 E_f have disjoint supports.
8. Polar factor of L L0^-1 → invoke the quotient-angle result.
9. Two-projection block argument → complement cross-term inequality.
10. Full physical-space image-sector decomposition.

Do not eliminate the fourth projection sector Z in the Schur complement. Do not whiten the entire core by a scalar product lower bound that grows with degree. Keep every unselected wire at its actual map.

## External foundational interfaces

Finite-dimensional spectral theorem; positive square root and inverse; orthogonal projection onto a subspace; finite Hilbert tensor product and Kraus/Choi equivalence. These are standard infrastructure. None encodes the desired application-specific angle estimate.

`lean/SchurScalar.lean` only closes the rational and scalar-order endpoints. It must not be cited as a formal proof of the geometric producer above.
