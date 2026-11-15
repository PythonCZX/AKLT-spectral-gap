# Oblique/filter formalization handoff — unchecked

Prepared 2026-11-15. No compilation, proof-assistant checking, numerical verification, or automated testing was performed. The companion TeX is a detailed hand proof, not completed formal verification. No theorem is replaced by an axiom or a placeholder proof.

## Exact deliverable

oblique_proofs.tex expands the compatible-idempotent certificate and product-filter neighborhood theorem from publication_package/proofs/quantum_results.tex. It derives the pairwise cross-term hypothesis called hcos rather than taking it as an input.

## Statement order and dependencies

1. O1: idempotent block form [[I,A],[0,0]]; norm(P-P*)=norm A; norm P≤sqrt(1+a²).
2. O2: D=I-(P-P*)²=I+(P-P*)*(P-P*)≥I; invertibility and inverse norm≤1; actual range projection=P P* D⁻¹.
3. O3: product/inverse commutator expansion, yielding L=κ+2κ²a.
4. O4: compatibility and adjoints give norm[ΠP,ΠR]≤2 LP LR norm[P,R*]; adjoint-commutator norm is symmetric.
5. O5: quotient by the entire common range; induced idempotents have product zero and no larger norm. Minimize norm(u-tv)² to obtain c≤aP/κP and c≤aR/κR. This excludes almost-parallel ranges.
6. O6: diagonalize A B A on the reduced space. The top eigenvector gives norm[A,B]≥c sqrt(1-c²). O5 supplies a strictly positive lower bound for the square root. Combine with O4 to get the third term in b.
7. O7: complement cosines agree. The TeX proves the needed two-projection blocks explicitly by diagonalizing A B A; use an existing library theorem only if its conventions agree.
8. O8: derive hcos. Remove the common component of the two violation vectors and apply O7. For every ψ and i≠j, Re⟪Qiψ,Qjψ⟫≥-bij norm(Qiψ) norm(Qjψ).
9. O9: construct real symmetric nonnegative B explicitly. Expand norm(Hψ)², use hcos and the symmetric-matrix Rayleigh bound, then diagonalize H. Kernel is the entire common range.
10. O10: weighted positive-vector certificate B w≤r w gives spectral radius≤r by diagonal similarity and a maximal-modulus eigenvector coordinate.
11. O11: product-filter factors outside each support cancel. Orthogonalized projections retain the support. Disjoint supports force adjoint commutators and matrix entries to vanish.
12. O12: differentiate exp(tK) E exp(-tK) on the finite support and integrate; obtain δ=exp(2sε)-1 and a≤2δ.
13. O13: support incidence gives row sum≤2Mδ; invoke O9 for the physical-parent operator inequality.

## Suggested hcos signature

For orthogonal violations Q indexed by a finite type and real coefficients b, use:

For all distinct i,j and all vectors ψ,
-b(i,j)·norm(Qiψ)·norm(Qjψ) ≤ Re inner(Qiψ,Qjψ).

The equivalent doubled anticommutator inequality is also supplied. O9 constructs Q from orthogonalizers and proves this signature; no assumption is missing.

## Edge cases and definition choices

- Primary cosine definition: norm(ΠM ΠN−Πintersection), avoiding a supremum over an empty unit sphere.
- κ≥1. The square-root denominator in O6 is positive because O5 proves a lower bound, not merely because c≤1.
- Quotient norms and range identification are proved explicitly in O5.
- For P=0, norm P≤κ is correct; norm P=κ is not.
- Remove the entire intersection before discussing nontrivial angles.
- The filter generators need not be self-adjoint for the norm estimate. Positive filters may specialize to self-adjoint generators.
- State the final result as an operator inequality above the full kernel. It also covers the case with no excited eigenvalue.
- Handle empty index types explicitly or assume a nonempty index type.
- Nonzero site Hilbert spaces are assumed for tensor-product operator-norm equality.

## Machine obligations remaining

All thirteen lemmas need translation into the selected Hilbert-space or matrix API and kernel checking. Main library interfaces: orthogonal decomposition/range, quotient norms, finite-dimensional spectral theorem, operator norms, tensor locality, and matrix-exponential differentiation. The specialized mathematical arguments are supplied in full; these are implementation obligations rather than extra mathematical hypotheses.

No Lean file is claimed complete in this handoff. A superficially complete file obtained by postulating the missing analytic lemmas would not satisfy the request.

## Additional uncompiled Lean source

ObliqueAlgebra_uncompiled.lean contains actual proof scripts for the product, difference, square, and inverse commutator identities; conjugation preserves multiplication, idempotence, and commutativity; and the scalar nonnegative-eigenvalue gap implication. These scripts have not been compiled. They contain no placeholder axioms or incomplete-proof commands. They do not claim to formalize the remaining analytic lemmas.
