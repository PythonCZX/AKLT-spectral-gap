URGENT PROOF AND FORMALIZATION HANDOFF

Start with INTEGRATION_ORDER.md. All four requested blocks are included.

STATUS — READ FIRST
No compilation, tests, numerical checks, or mathematical verification pass was performed, as requested. The TeX files contain expanded mathematical proof drafts. The Lean files contain uncompiled algebraic/scalar proof code. This is NOT a complete Lean formalization of the operator, representation, polynomial, and analytic results. No kernel-checked completion is claimed.

The point of this handoff is to remove opaque target assumptions from the mathematical arguments before the swarm translates them. cp_transport_proofs.tex derives the angle certificate hcross from actual CP/Kraus data. oblique_proofs.tex derives hcos from oblique-idempotent and local-filter data. aklt_proofs.tex realizes the microscopic projectors and gives an explicit positive patch-gap lower bound. response_proofs.tex proves the actual derivative and scalar integral identities.

FILES
cp_transport_proofs.tex — CP tensor order, injectivity, quotient metric, whitening, physical edge ranges, and hcross.
aklt_proofs.tex — Pauli/Kraus realization, Choi multiplicities, SU(2) and polynomial kernels, prime brackets, regional images, and explicit patch-gap bound.
oblique_proofs.tex — orthogonalizer, commutator bounds, quotient separation, cosine matrix, hcos, and filter locality.
response_proofs.tex — actual derivatives and Duhamel identification, Fourier contour calculation, coth series, positive densities, and KMS/rotation consequences.
Each block has a separate contracts/obligations document listing its machine-translation boundary.
lean/ — unchecked Lean source for finite elementary endpoints; this folder does not discharge the full analytic proof graph.
source/ — original report source for label, normalization, and citation alignment.
proof_insertions.tex — optional combined TeX source, not compiled.
