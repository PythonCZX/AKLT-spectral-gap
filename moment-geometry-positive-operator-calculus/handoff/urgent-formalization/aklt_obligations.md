# Decorated AKLT: explicit proof handoff

Status: mathematical proof text supplied; **not compiled, tested, or proof-assistant verified in this urgent pass**. The accompanying Lean file is unchecked source for elementary algebraic portions only. It does not purport to formalize the full microscopic theorem.

## Files and scope

- `aklt_proofs.tex` contains the complete coordinate arguments below. It is an input fragment, not a standalone TeX document.
- `AKLT.lean` contains proposed Lean proofs of the Pauli entry identity and positivity of the explicit denominator bound. No compilation has been attempted; API or syntax repair may be necessary.
- The independent CP quotient-angle argument is outside this module and is owned by the main proof handoff. No statement here establishes its validity by numerical evidence.

## Claims now reduced explicitly

1. **Actual spin-one tensor and Kraus channel.** Start with the triplet coefficient matrices, contract the antisymmetric virtual form, normalize by sqrt(2/3), and make the displayed unitary physical-basis change. This produces X/sqrt3, Y/sqrt3, Z/sqrt3. Conjugation/transposition conventions must be fixed at this stage, not inferred from an abstract channel.
2. **Pauli channel and powers.** Entrywise identity holds for every complex 2×2 matrix, not merely Hermitian ones. Complementary idempotents Psi and id−Psi give all powers.
3. **Choi spectrum and multiplicities.** Use unnormalized Omega=00+11, J(Psi)=I4/2. The relative Choi matrix is (1−beta)I4+4beta|omega><omega|, giving eigenvalue1+3beta once and1−beta three times. Center at (1+beta)Psi. The radius is2/(3^ell+(-1)^ell); ell≥2 is essential for a strict CP lower bound.
4. **Physical maximal-spin projector.** Binary degree-p monomials have squared norms1/binom(p,i). Multiplication m is a coisometry by Vandermonde; P=m*m is the actual orthogonal projector. Formula(urgent:projector-entries) supplies every rational matrix entry in a nonorthonormal basis. It is similar to a Hermitian matrix, not asserted Euclidean-Hermitian in that basis.
5. **SU(2) identification.** Multiplication is equivariant. Binary Sym^r is irreducible by the H,E,F monomial argument. The highest weight p+q has multiplicity one in Sym^p⊗Sym^q, identifying the image as maximal spin without requiring the whole Clebsch–Gordan decomposition.
6. **One-edge kernel.** Bracket multiplication is injective, lies in ker(m), and has the exact same dimension pq. Thus the projector kernel is precisely bracket divisibility.
7. **Irreducibility and nonassociateness.** “Nonassociativity” should be corrected to **nonassociate**. Regard b_vw as a primitive linear polynomial in y_w over the other-variable ring. Gauss implies irreducible; UFD implies prime. Vertex multidegrees distinguish unordered edges. Simple graph is essential (no loops or parallel edges).
8. **Regional image.** Pairwise nonassociate primes turn simultaneous divisibility into divisibility by the whole bracket product. Residual multidegrees are the omitted boundary degrees. Boundary symmetrization is surjective by monomials; linear combinations allow arbitrary correlated boundary tensors. For whole half-wire blocks each boundary endpoint has exactly one residual leg, so there is no extra symmetrization kernel.
9. **Finite patch types.** Type(d,e,ell) has2+ell(d+e)sites and1+ell(d+e)terms, physical dimension(d+1)(e+1)3^(ell(d+e)), and kernel dimension2^(d+e−2). At most Delta² ordered types occur.
10. **Actual positive seed constant.** Let C_Delta be the lcm of binomial coefficients with total≤Delta+2, R=(Delta+1)²3^(2ellDelta), M=2ellDelta+1. The explicit lower bound is

   g_exp = C_Delta^(−R) M^(1−R) > 0.

   Every patch matrix has entries in(1/C_Delta)Z, is similar to a positive Hermitian matrix, is nonzero, and has eigenvalues≤M. If rank=r, its lowest nonzero characteristic coefficient equals the product of positive eigenvalues and is a positive integer multiple of C_Delta^(−r). This proves the bound. **g_exp≤g_*; it is not an equality with the exact minimum.** No positive patch gap is assumed.
11. **Coverage.** Internal block terms occur between1andDelta times; interface terms once. Same kernels follow from positivity and coverage. A coarse gap c gives physical gap≥c g_exp/Delta with the norm-one microscopic normalization.

## Formalization dependency map

### Finite algebra

- Fin2 matrices, complex conjugation, matrix multiplication, trace.
- Kronecker products, normalized and unnormalized maximally entangled vectors, rank-one projections.
- Binomial identities, positive diagonal Gram matrices, adjoints in weighted inner products.
- Finite-variable polynomial ring over C, multigrading, integral domain, units, Gauss lemma, UFD primes, coprime product divisibility.
- Finite-dimensional tensor products and surjectivity of symmetrization.

### Representation bridge that still needs Lean development

Define the actual SU(2) action on binary polynomials. Prove its derivative formulas H,E,F; prove invariant subspaces are stable under those derivatives; isolate weights by Lagrange polynomials in H; use E,F to span all monomials. Formalize the unique highest-weight copy and identify the physical projector with m*m. The TeX supplies the complete argument, but the Lean file does not implement this representation API.

### Spectral bridge that still needs Lean development

Define patch Hamiltonians by the explicit rational projector formula and a positive diagonal coordinate Gram matrix. Prove similarity to a Hermitian positive matrix. Relate the characteristic coefficient at its rank to the product of positive eigenvalues and to principal minors. Formalize the denominator lattice C^(−r)Z, positivity of a nonzero integer numerator, and norm bound by the number of projectors. The resulting g_exp is explicit; importing this spectral bridge as an external lemma must expose its exact finite-dimensional hypotheses, not assume the desired patch gap.

### Graph bookkeeping

Construct subdivision with2ell added vertices per original edge, orient each core edge once, and assign exactlyell added vertices to each endpoint block. Whole-block regional subsets retain the original physical spins, including dangling boundary ports. Prove patch-type counts, boundary residual degrees, and coverage multiplicities. Disconnected or one-block regions need a separately stated convention; the present theorem covers connected regions of at least two blocks.

## Normalization traps

- Each microscopic interaction is an orthogonal projector of norm1.
- Full physical degree, not induced regional degree, determines spin.
- Use the centered reference(1+beta)Psi in the CP comparison.
- Choi uses unnormalized Omega; its squared norm is2.
- Bracket orientation changes a sign only.
- Rational polynomial coordinates are nonorthonormal; use the binomial Gram weights.
- The explicit seed bound is intentionally tiny. It supplies existence, not an optimized numerical gap.
- No verification or new numerical experiment was run for this handoff.
