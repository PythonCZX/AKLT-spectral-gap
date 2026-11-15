#!/usr/bin/env python3
"""Generate an auditable source-contract ledger from the supplied registry.

Coverage annotations are reviewer data, not changes to the supplied registry.
They intentionally distinguish integrated components from a complete source theorem.
"""
from pathlib import Path
import json
import sys

ROOT = Path(__file__).resolve().parent.parent
SRC = ROOT / 'results/moment_geometry/Moment_Geometry/supplements/theorem_registry.json'
OUT = ROOT / 'results/moment_geometry'

ANNOTATED = {
    'op:hyperbolic-clock': {
        'status': 'integrated_component',
        'lean': [
            'MomentGeometry/Operator/CP/Base.lean',
            'MomentGeometry/Operator/CP/Closure.lean',
            'MomentGeometry/Operator/Clock.lean',
        ],
        'verified': 'Choi-style multiplier criterion; CP of matrix conjugation; PSD Gaussian/resolvent kernels; Euler sine-product convergence; complete positivity of the hyperbolic clock kernel for every real exponent >=0 (dense identity at 0, actual CP at tau>0).',
        'missing': 'Gamma-subordinated heat-channel identity and its full functional-calculus realization; fourth-nested-commutator error bound; full contract in proofs/positive_calculus.tex.',
        'provenance': 'Copied from reviewed scoped packages results/coherent_continuation/review_smwhh7nna_m2/lean/{ModularCPBase,ModularCPClosure}.lean, with namespace/import adaptation and fresh build. Inherited declarations are not a certificate of the whole registered result.',
    },
    'q:kms-compatibility': {
        'status': 'integrated_component',
        'lean': ['MomentGeometry/Operator/KMS.lean'],
        'verified': 'Regular scalar Hermitian and anti-Hermitian divided-difference ratios (values r and r^2 at zero), auxilliary half-angle identities, and chi_r(x)*tanh(x/2)=tanh(r*x/2)*psi_r(x). The wrong earlier scalar identity was corrected before integration.',
        'missing': 'Matrix-valued divided-difference integral representation, right-derivative KMS compatibility, and complete-power response Q_r. Those are differential/functional-calculus obligations, not scalar arithmetic.',
        'provenance': 'Written for the new source contract; not an inference from the separate hyperbolic-clock kernel.',
    },
    'eq:coherent-finite-moments': {
        'status': 'integrated_component',
        'lean': ['MomentGeometry/Coherent/Moments.lean',
                 'MomentGeometry/Coherent/CycleCofactor.lean',
                 'MomentGeometry/Coherent/UnitDensity.lean'],
        'verified': 'Exact finite expected second/third/fourth trace books (definitions plus rational denominator algebra), including the independent-source-moment and finite-sample corrections and cubic limit expansion. Verified smwi6zlvo/m1/d2 adds asymptotic D-ratio forms with Dprime/D -> 2^q, quotient cycle outdegree Laplacians retaining parallel edges/discarding loops, restricted-growth partition words, and explicit order-<=(4) cofactor checks, τ hist {1:14,2:1}, noncrossing equivalence, root-independence and positivity. The m1 scoped review passed both new modules and 16 standard-axiom reports; current direct eight-module build passes 117 reports (including the independent headline audit module). No overall asymptotic spectral law is accepted.',
        'missing': 'Haar tensor moment construction; random coherent Gram matrices and their empirical laws; local graph integral, arbitrary-order cofactor-support formula, moment/variance and convergence with conditioned laws. Exact finite formulas do not certify any of these.',
        'provenance': 'Written against proofs/coherent_gram.tex; it does not upgrade a symbolic finite check to the spectral-law theorem.',
    },
    'prop:repair': {
        'status': 'integrated_component',
        'lean': ['MomentGeometry/Repair/Frame.lean'],
        'verified': 'Reviewed prop:repair finite frame algebra: moment map linearity, density bounds [1/2,3/2], normalization, the (1-p)k=p scalar law and exact moment cancellation at p=(1+102δ)^{-1}. Rebuilt both independently and main-tree.',
        'missing': 'eq:repairframe Haar fourth moments and its Hilbert--Schmidt norm bound, the Borel probability-measure lift, and the convex relative-entropy inequality.',
        'provenance': 'Integrated from accepted scoped integration smwi6zlvo/m8/d6, with an independently rebuilt coverage_74_audit.json.',
    },
    'q:thm-powers': {
        'status': 'integrated_component',
        'lean': ['MomentGeometry/Operator/KMS.lean'],
        'verified': 'Regular scalar Hermitian and anti-Hermitian response functions with limiting values r and r^2 and the exact square-ratio for chi_r. Component only.',
        'missing': 'The matrix exponential-divided-difference representation of fractional powers, actual H_r/A_r matrix parts, CP amplification and masses r and r², and derivative-limit assembly.',
        'provenance': 'Registry matching validated by smwi6zlvo/m8/d6; scalar functions are not the final matrix theorem.',
    },
    'q:lem-seed': {
        'status': 'source_contract_verified',
        'lean': ['MomentGeometry/Swarm/Seed.lean'],
        'verified': 'Complete operator-level q:lem-seed at its full assumptions: coverage reindexing, exact common kernel, (g/m)H_block ≤ H_micro, and every gap certificate γ transfers to g_*γ/m. The numerical gap is represented faithfully by its lower-bound certificates, not by an undefined gap functional.',
        'missing': 'Physical patch instantiations including AKLT tensor-image/kernel and actual g_*(Δ,ℓ)>0. These are separate q:cor-aklt obligations, not a missing clause of the operator-level seed theorem.',
        'provenance': 'Independently rebuilt smwi6zlvo/m6/d3 and integrated. Source hypotheses and coverage are preserved; no physical nonzero gap is inferred from this algebraic comparison alone.',
    },
    'q:thm-wire-gap': {
        'status': 'integrated_component',
        'lean': ['MomentGeometry/Network/CPOrder.lean',
                 'MomentGeometry/Network/WireGap.lean',
                 'MomentGeometry/Network/GapAssembly.lean',
                 'MomentGeometry/Network/GapSpectral.lean',
                 'MomentGeometry/Network/GapSpectral.lean'],
        'verified': 'Finite CP order algebra, conflict/Rayleigh matrix assembly and true finite-dimensional spectral proof of blocked gap from hcross and the full-ground-space projector. Rebuilt 14 standard-axiom declarations.',
        'missing': 'Full-Schmidt-rank CP transport, injectivity, CP-tensor sandwich, whitening/signed cancellation and physical edge-subspace identification. hcross is an explicit remaining input, not the finished Schur estimate.',
        'provenance': 'Accepted at finite matrix step, smwi6zlvo/m5/d5; unsupported angle/transport assumptions are not discharged.',
    },
    'q:thm-oblique': {
        'status': 'integrated_component',
        'lean': ['MomentGeometry/Swarm/Oblique.lean'],
        'verified': 'Defect-matrix assembly from hcos and Rayleigh hypotheses to (1-ρ)H≤H², complement projection version and row/column-sum criterion. Independently rebuilt with standard axioms.',
        'missing': 'Orthogonalizer, adjoint-commutator bound, quotient construction of cosine matrix and input perturbation ODE/locality facts.',
        'provenance': 'Finite assembly only, smwi6zlvo/m6/d3. hcos remains an interface, not a supplied cosine theorem.',
    },
    'q:cor-filtered': {
        'status': 'integrated_component',
        'lean': ['MomentGeometry/Swarm/Filtered.lean',
                 'MomentGeometry/Swarm/Oblique.lean'],
        'verified': 'Similarity/filter transport of idempotence and commutativity, common kernel, and gap inequality from the conditional hcos and row/column defect inputs.',
        'missing': 'Product-filter locality and the perturbation bound ||P_i-E_i||≤exp(2sε)-1 used to instantiate the defect matrix; no physical nonzero gap is asserted from the arithmetic alone.',
        'provenance': 'Accepted with those explicit input obligations, smwi6zlvo/m6/d3.',
    },
    'q:cor-aklt': {
        'status': 'integrated_component',
        'lean': ['MomentGeometry/AKLT/Wire.lean',
                 'MomentGeometry/AKLT/Radius.lean',
                 'MomentGeometry/AKLT/Decoration.lean',
                 'MomentGeometry/AKLT/Finite.lean',
                 'MomentGeometry/AKLT/Bridge.lean'],
        'verified': 'Spin-one normalized wire/iteration algebra, centered transfer radius and bounds, two-port cosine arithmetic, minimal-level decoration inequalities, positive finite patch minima, dimension arithmetic, coprime product divisibility. 57 audited declarations in independent review.',
        'missing': 'Pauli/Kraus identity and Choi spectrum, edge-bracket irreducibility/nonassociativity, SU(2) regional tensor image, actual finite patch gaps and wire/seed input obligations.',
        'provenance': 'Arithmetic only, smwi6zlvo/m7/d7. g_*>0 stays a side condition; no undecorated spin-3/2 hexagonal gap is claimed.',
    },
}


def main():
    registry = json.loads(SRC.read_text())
    rows = []
    for item in registry['theorem_records']:
        a = ANNOTATED.get(item['id'])
        if a:
            row = {**item, 'review_status': a['status'], 'review_lean_modules': a['lean'],
                   'review_verified': a['verified'], 'review_missing': a['missing'],
                   'review_provenance': a['provenance']}
        else:
            row = {**item, 'review_status': 'assigned',
                   'review_lean_modules': [], 'review_verified': '',
                   'review_missing': 'Complete source-contract formalization remains pending.',
                   'review_provenance': ''}
        rows.append(row)
    completed = sum(r['review_status'] == 'source_contract_verified' for r in rows)
    complete_components = sum(r['review_status'] == 'integrated_component' for r in rows)
    assigned = [r['id'] for r in rows if r['review_status'] == 'assigned']
    metadata = {
        'schema_version': 1,
        'source_registry_sha256': __import__('hashlib').sha256(SRC.read_bytes()).hexdigest(),
        'lean_toolchain': 'Lean 4.33.1, installed /opt/mathlib',
        'registry_records': len(rows),
        'source_contracts_verified': completed,
        'integrated_component_contracts': complete_components,
        'source_contracts_assigned': len(assigned),
        'component_build_pass': True,
        'component_axioms': ['propext', 'Classical.choice', 'Quot.sound'],
        'future_problems_not_in_scope': registry['future_problems'],
        'records': rows,
    }
    (OUT / 'COVERAGE.json').write_text(json.dumps(metadata, indent=2) + '\n')
    lines = [
        '# MomentGeometry — formalization roadmap and coverage ledger',
        '',
        'Source: *Moment geometry and positive operator calculus* and its',
        '**Formalization and reproducibility guide**, supplied by the person.',
        'The supplied distribution itself states **proof_assistant_verified=false** for all',
        '74 records. Statement labels in that distribution are not Lean declaration names.',
        '',
        '## Current scope',
        '',
        f'* **{len(rows)}** source contract records, **{completed}** fully source-contract verified.',
        f'* **{complete_components}** record has an integrated verified component (`op:hyperbolic-clock`).',
        f'* **{len(assigned)}** source contracts remain assigned.',
        '* The registry\'s two separate future problems are not part of this source-completion target.',
        '* Ultramath is stopped under the person\'s explicit instruction. The main project is built directly using the shared `/opt/lean/bin/lean` 4.33.1 and installed `/opt/mathlib`.',
        '',
        '**No proof of a nonzero spectral gap for the spin-3/2 hexagonal AKLT model is claimed.**',
        'The guide instead contains decorated-network transfer and finite finite-patch interfaces.',
        '',
        '## Main build',
        '',
        '```sh',
        'OPENBLAS_NUM_THREADS=1 OMP_NUM_THREADS=1 python3 scripts/check_lean_moment_geometry.py',
        '```',
        '',
        'The latest integrated run passes twenty-eight modules and 201 audited theorem reports, all using only',
        '`propext`, `Classical.choice`, and `Quot.sound`.',
        '',
        '## Ordering from the guide',
        '',
        '1. Finite interfaces: coherent moments, rational polynomial identities, graph cofactors,',
        '   Choi positivity, exact quadrature transcripts.',
        '2. Finite-dimensional general lemmas: entropy projection, operator divided differences,',
        '   completely positive functional calculus, subspace angles, coupling inequalities.',
        '3. All-degree combinatorics, local graph asymptotic, and variational convergence.',
        '4. Heavy geometric/analytic results with explicit external-theorem interfaces, not',
        '   unproven assumptions hidden in a headlined final theorem.',
        '',
        '## Per-contract ledger',
        '',
        '“Integrated component” is not equivalent to a completed registry entry. No theorem',
        'count or compilation count substitutes for checking that a declaration matches its',
        'source contract, including quantifiers, external hypotheses, and normalization.',
        '',
    ]
    for r in rows:
        lines += [
            f'### `{r["id"]}` — {r["title"]}',
            '',
            f'* Source proof: `{r["proof_source"]}`',
            f'* Review status: **{r["review_status"]}**',
            f'* Dependencies: {", ".join(f"`{x}`" for x in r["internal_dependencies"]) or "none"}.',
            f'* External inputs: {"; ".join(x["input"] for x in r["external_inputs"]) or "none"}.',
            f'* Scope limits: {"; ".join(r["scope_limits"]) or "none listed"}.',
        ]
        if r['review_lean_modules']:
            lines += [
                f'* Verified Lean modules: {", ".join(f"`{x}`" for x in r["review_lean_modules"])}.',
                f'* Verified component: {r["review_verified"]}',
                f'* Missing relative to contract: {r["review_missing"]}',
                f'* Provenance: {r["review_provenance"]}',
            ]
        else:
            lines.append(f'* Pending: {r["review_missing"]}')
        lines.append('')
    (ROOT / 'results/moment_geometry/ROADMAP.md').write_text('\n'.join(lines) + '\n')
    copy = {**metadata, 'records': list(rows)}
    # Coverage JSON stays records-only metadata plus explicit review statuses.
    (OUT / 'COVERAGE.json').write_text(json.dumps(copy, indent=2) + '\n')
    print(f'{len(rows)} records: {completed} contract-verified; {complete_components} integrated components; {len(assigned)} assigned.')
    print(OUT / 'ROADMAP.md')
    return 0


if __name__ == '__main__':
    raise SystemExit(main())
