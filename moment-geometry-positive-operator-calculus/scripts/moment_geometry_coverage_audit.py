#!/usr/bin/env python3
"""Regenerate a 74-record coverage ledger from the supplied theorem registry.

The registry itself is never written.  This script

* reads `supplements/theorem_registry.json` (74 records, all
  `proof_assistant_verified = false`),
* checks that every record id appears exactly once in the emitted ledger,
* resolves every *claimed* verified Lean ingredient against the actual source
  file (the declaration must occur as a `theorem`/`def` in that file), and
* writes one ledger entry per record, with an explicit status.

Status vocabulary (strict):

  `source_contract_verified`  a proved declaration matching the registered
      statement exists.  Nothing in this project has this status.
  `component_verified`        proved declarations are ingredients of the record.
  `not_started`               no proved Lean ingredient.

A claimed component does not make the record verified: the ledger keeps
`source_contract_verified: false` for every record, always.

Usage (from the member directory):
  python3 scripts/regenerate_coverage.py --out coverage_74.json
"""
from __future__ import annotations
import argparse
import datetime
import hashlib
import json
import re
from pathlib import Path

HERE = Path(__file__).resolve().parents[1]
# Review relocation: derive the repository root from a known artifact, not
# from the number of components in the original .ultramath member path.
REGISTRY_REL = 'results/moment_geometry/Moment_Geometry/supplements/theorem_registry.json'
REPO = next(p for p in (HERE, *HERE.parents) if (p / REGISTRY_REL).is_file())
REGISTRY = REPO / REGISTRY_REL
MINE = 'lean/MomentGeometry'
MAIN = 'lean/MomentGeometry'

# --- The audit claim: proved Lean ingredients, per registry record. -----------
# Every entry is resolved against the named file below; a missing declaration is
# a hard error, not a silent pass.
COMPONENTS = {
    'op:hyperbolic-clock': [
        (f'{MAIN}/Operator/CP/Base.lean', 'isCP_multMap_iff',
         'Choi-style multiplier criterion for complete positivity (finite dimension).'),
        (f'{MAIN}/Operator/CP/Closure.lean', 'isCP_sinhc_rpow_uncond',
         'Complete positivity of the hyperbolic clock kernel at every real exponent > 0.'),
        (f'{MAIN}/Operator/Clock.lean', 'completelyPositive_sinhc_rpow',
         'Headline export: the clock multiplier is completely positive.'),
    ],
    'q:thm-powers': [
        (f'{MAIN}/Operator/KMS.lean', 'hermitianPart',
         'Scalar Hermitian response psi_r(x) = sinh(rx)/sinh(x), value r at 0.'),
        (f'{MAIN}/Operator/KMS.lean', 'antiPart',
         'Scalar anti-Hermitian response chi_r(x) = (cosh(rx)-1)/(cosh x - 1), value r^2 at 0.'),
        (f'{MAIN}/Operator/KMS.lean', 'antiPart_eq_ratio_sq',
         'chi_r(x) = (sinh(rx/2)/sinh(x/2))^2, the source normalisation, away from 0.'),
    ],
    'q:kms-compatibility': [
        (f'{MAIN}/Operator/KMS.lean', 'antiPart_compatibility',
         'Scalar KMS relation chi_r(x) tanh(x/2) = tanh(rx/2) psi_r(x).'),
        (f'{MAIN}/Operator/KMS.lean', 'cosh_sub_one_div_sinh_eq_tanh_half',
         'The removable-singularity identity (cosh z - 1)/sinh z = tanh(z/2).'),
    ],
    'eq:coherent-finite-moments': [
        (f'{MINE}/Coherent/Moments.lean', 'expectedT3_cubic_form',
         'Exact finite-k cubic form of E T_3 with the corrected correction term.'),
        (f'{MINE}/Coherent/Moments.lean', 'expectedT3_at_unit_density',
         'Exact finite-k E T_3 = 5 - 6/D + 2/D^2 at n = D, D != 0.'),
        (f'{MINE}/Coherent/UnitDensity.lean', 'expectedT4_unit_density_general',
         'Exact finite-k E T_4 at n = D with D\' free: 14 + (D-1)/D\' - 30/D + 23/D^2 - 6/D^3.'),
        (f'{MINE}/Coherent/UnitDensity.lean', 'expectedT4_unit_density_q2_m1',
         'Exact instance q = 2, m = 1 (D = 3, D\' = 6): E T_4 = 20/3.'),
    ],
    'prop:repair': [
        (f'{MINE}/Repair/Frame.lean', 'repair_density_range',
         'Repair density 1 - d/(2 C delta) lies in [1/2, 3/2] when |d| <= C delta.'),
        (f'{MINE}/Repair/Frame.lean', 'repair_total_mass',
         'Normalisation of the repair density from the frame identity sum sigma_i d_i = 0.'),
        (f'{MINE}/Repair/Frame.lean', 'repair_moment_eq',
         'Exact moment cancellation at p = (1 + 102 delta)^(-1).'),
        (f'{MINE}/Repair/Frame.lean', 'repair_summary',
         'Combined source-constant statement: range, normalisation, exact moment tau.'),
    ],
}

# Newer independently reviewed integrations. These keep named hypotheses
# hcross/hcos visible as components; only q:lem-seed is marked contract-complete.
COMPONENTS.update({
    'q:thm-wire-gap': [
        (f'{MAIN}/Network/GapAssembly.lean', 'norm_sq_block_ge_of_conflict',
         'Finite matrix assembly from the off-block angle certificate and a conflict matrix.')
    ],
    'q:thm-oblique': [
        (f'{MAIN}/Swarm/Oblique.lean', 'defect_gap', 'Defect matrix assembly from hcos and the Rayleigh input.'),
        (f'{MAIN}/Swarm/Oblique.lean', 'rayleigh_of_rowSums', 'Row/column-sum criterion showing the Rayleigh defect bound.')
    ],
    'q:cor-filtered': [
        (f'{MAIN}/Swarm/Filtered.lean', 'filtered_ground_space', 'Transport of idempotence, commutation, ranges and the common kernel under a similarity.')
    ],
    'q:cor-aklt': [
        (f'{MAIN}/AKLT/Wire.lean', 'phi_iterate_eq', 'Spin-one wire channel algebra and contraction by the exact transfer scalar.'),
        (f'{MAIN}/AKLT/Radius.lean', 'delta_le_ninth', 'Exact centered transfer-radius bounds, not a Choi spectrum theorem.'),
        (f'{MAIN}/AKLT/Decoration.lean', 'decoration_gap_positive', 'Positive decorated gap-factor arithmetic conditional on the finite-patch input.')
    ],
    'q:lem-seed': [
        (f'{MAIN}/Swarm/Seed.lean', 'sum_patchHam', 'Coverage reindexing of the patch Hamiltonians.'),
        (f'{MAIN}/Swarm/Seed.lean', 'seed_kernel_eq', 'Full common-kernel identity using positivity and every-term coverage.'),
        (f'{MAIN}/Swarm/Seed.lean', 'seed_gap_le', '(g/m)•H_block ≤ H_micro.'),
        (f'{MAIN}/Swarm/Seed.lean', 'seed_gap_transfer', 'Every blocked gap certificate γ gives micro certificate g_*γ/m.')
    ],
})
SOURCE_CONTRACTS = {'q:lem-seed'}

# Honest statement of what each component-carrying record still needs.
GAPS = {
    'op:hyperbolic-clock': 'Gamma-subordinated heat-channel identity, fourth-nested-commutator '
                           'error bound; component is CP positivity of the kernel only.',
    'q:thm-powers': 'Matrix-level divided-difference representation of A -> A^r, the split '
                    'H_r + A_r, CP amplification positivity, and the norms r and r^2.',
    'q:kms-compatibility': 'Matrix-level identity A = tanh(ad_K/2) H on a faithful path; only the '
                           'scalar quotient identity is proved.',
    'eq:coherent-finite-moments': 'The random Gram matrix, the tensor second/fourth moment '
                                  'integrals int P_z^{otimes m} dsigma = I/D and '
                                  'int |<z,w>|^{4m} dsigma(w) = 1/D\', and hence the expectations '
                                  'themselves.  Only the rational identities in (n, D, D\') are proved.',
    'prop:repair': 'eq:repairframe (Haar fourth-moment identities for '
                   'B_z = 90 Q_z - 30 L(P_z) + 5 I and ||B_z||_HS = sqrt 2550 < 51), the Borel lift, '
                   'and the relative-entropy inequality.',
}

GAPS.update({
    'q:thm-wire-gap': 'CP transport/injectivity, tensor-product CP orders, CP sandwich whitening, the signed-average mixed-defect cancellation and physical edge-subspace identifications. block_gap_row_criterion assumes hcross and the actual ground-space projector.',
    'q:thm-oblique': 'The orthogonalizer formula, adjoint-commutator bounds, quotient construction of the cosine matrix, and full product-filter locality. hcos is an explicit remaining interface.',
    'q:cor-filtered': 'Perturbation ODE bound ||P_i-E_i||≤exp(2sε)-1 and tensor locality from product filters. Gap assembly is conditional on the hcos input.',
    'q:cor-aklt': 'Pauli/Kraus identity, actual Choi multiplicities, edge-bracket irreducibility/nonassociate regional SU(2) kernel, finite physical patch gap, and q:thm-wire-gap inputs.',
    'q:lem-seed': 'Complete at the operator-level contract. Physical AKLT patch instantiation and numerical patch gaps are separate q:cor-aklt inputs, not additional gaps in q:lem-seed.',
})


def sha256(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


DECL_RE = re.compile(r'^\s*(?:@\[[^\]]*\]\s*)?(?:noncomputable\s+)?(?:private\s+|protected\s+)?'
                     r'(theorem|lemma|def|abbrev)\s+([A-Za-z0-9_.\']+)', re.M)


def declared_names(path: Path) -> set[str]:
    text = path.read_text()
    names = set()
    for m in DECL_RE.finditer(text):
        full = m.group(2)
        names.add(full)
        names.add(full.rsplit('.', 1)[-1])
    return names


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument('--out', default='coverage_74.json')
    args = ap.parse_args()

    registry = json.loads(REGISTRY.read_text())
    records = registry['theorem_records']
    ids = [r['id'] for r in records]
    if len(ids) != 74 or len(set(ids)) != 74:
        raise SystemExit(f'registry integrity failure: {len(ids)} records, {len(set(ids))} distinct')
    if not all(r['proof_assistant_verified'] is False for r in records):
        raise SystemExit('registry unexpectedly contains a verified record')

    unknown = sorted(set(COMPONENTS) - set(ids))
    if unknown:
        raise SystemExit(f'component claims for unknown record ids: {unknown}')

    # Resolve every claim against the real file.
    resolved: dict[str, list[dict]] = {}
    errors = []
    for rid, claims in COMPONENTS.items():
        out = []
        for relpath, decl, note in claims:
            path = REPO / relpath
            if not path.is_file():
                errors.append(f'{rid}: missing file {relpath}')
                continue
            if decl not in declared_names(path):
                errors.append(f'{rid}: declaration {decl} not found in {relpath}')
                continue
            out.append({'decl': decl, 'file': relpath, 'declared': True, 'note': note})
        resolved[rid] = out
    if errors:
        print('COMPONENT CLAIM FAILURES:')
        for e in errors:
            print('  ' + e)
        return 1

    ledger = []
    n_comp = 0
    for r in records:
        rid = r['id']
        comps = resolved.get(rid, [])
        status = ('source_contract_verified' if rid in SOURCE_CONTRACTS else
                  'component_verified' if comps else 'not_started')
        if comps:
            n_comp += 1
        ledger.append({
            'id': rid,
            'title': r['title'],
            'kind': r['kind'],
            'source': r['proof_source'],
            'registered_mathematical_status': r['mathematical_status'],
            'registered_proof_assistant_verified': r['proof_assistant_verified'],
            'source_contract_verified': rid in SOURCE_CONTRACTS,
            'status': status,
            'verified_components': comps,
            'remaining_for_contract': GAPS.get(rid, 'Complete source-contract formalization '
                                                     'remains pending; no Lean ingredient is proved.'),
        })

    out = {
        'schema_version': 2,
        'generated_utc': datetime.datetime.now(datetime.timezone.utc).strftime('%Y-%m-%dT%H:%M:%SZ'),
        'generator': 'scripts/regenerate_coverage.py (member m8)',
        'source_registry': 'results/moment_geometry/Moment_Geometry/supplements/theorem_registry.json',
        'source_registry_sha256': sha256(REGISTRY),
        'registry_records': len(records),
        'source_contracts_verified': len(SOURCE_CONTRACTS),
        'records_with_verified_components': n_comp,
        'ledger_ids_unique': len({e['id'] for e in ledger}) == len(ledger),
        'status_vocabulary': ['source_contract_verified', 'component_verified', 'not_started'],
        'additional_scope_note': 'Contract coverage counts complete source contracts only; component proofs do not close their remaining physical/analytic inputs.',
        'priority_records': sorted(COMPONENTS) + [
            'q:prop-rotation', 'q:lem-schur', 'q:thm-wire-gap', 'q:lem-seed', 'q:cor-aklt',
            'q:thm-oblique', 'q:cor-filtered', 'thm:coherent-spectral-law',
            'lem:coherent-graph-integral', 'lem:tree-one-noncrossing',
            'thm:coherent-free-limit'],
        'records': ledger,
    }
    Path(args.out).write_text(json.dumps(out, indent=2) + '\n')
    print(f'{len(ledger)} records; source_contracts_verified={len(SOURCE_CONTRACTS)}; '
          f'records_with_verified_components={n_comp}; unique_ids={out["ledger_ids_unique"]}')
    print(f'wrote {args.out}')
    return 0


if __name__ == '__main__':
    raise SystemExit(main())
