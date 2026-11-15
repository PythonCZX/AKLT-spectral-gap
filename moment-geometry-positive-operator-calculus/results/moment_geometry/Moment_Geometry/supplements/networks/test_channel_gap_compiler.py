"""Exact adversarial and end-to-end checks for the supplemental compiler."""
from fractions import Fraction as F
from itertools import combinations
import json
from pathlib import Path

import sympy as sp

import channel_gap_compiler as compiler


def expect_failure(fn):
    try:
        fn()
    except compiler.CertificateError:
        return
    raise AssertionError("An invalid input was accepted")


def main():
    # Zero pivots are never silently skipped. This matrix is indefinite.
    bad = sp.Matrix([[0, sp.I], [-sp.I, 1]])
    assert not compiler.exact_psd(bad)["valid"]
    assert compiler.exact_psd(bad)["reason"] == "zero_diagonal_nonzero_row"
    assert not compiler.exact_psd(sp.Matrix([[1, 1], [0, 1]]))["valid"]
    assert compiler.exact_psd(sp.zeros(3))["valid"]
    assert not compiler.exact_psd(sp.zeros(3), positive_definite=True)["valid"]
    assert compiler.exact_psd(sp.diag(0, 2, 0, 3))["rank"] == 2

    # Compare the congruence algorithm with all principal minors on exact
    # complex rank-deficient Gram matrices and their negative perturbations.
    exact_cases = 0
    for rank in range(1, 5):
        A = sp.Matrix(4, rank, lambda i, j: (i + 1) ** j + sp.I * (i + 2) ** (j + 1))
        gram = (A * A.conjugate().T).applyfunc(sp.expand)
        for matrix in (gram, gram - 3 * sp.eye(4), gram + sp.eye(4)):
            minors_positive = all(sp.expand(matrix.extract(ids, ids).det()) >= 0
                for size in range(1, 5) for ids in combinations(range(4), size))
            assert compiler.exact_psd(matrix)["valid"] == minors_positive
            exact_cases += 1

    assert compiler.aklt_channel(2)["delta"] == "1/5"
    assert compiler.aklt_channel(3)["delta"] == "1/13"
    assert compiler.pair_bound(F(1, 5), F(1, 5)) == F(13, 64)
    assert compiler.pair_bound(F(1, 13), F(1, 13)) == F(85, 5184)
    assert compiler.uniform_aklt(3, 4)["coarse_gap_lower_bound"] == "3/16"
    assert compiler.uniform_aklt(31, 6)["coarse_gap_lower_bound"] == "7/432"
    assert compiler.plan_aklt(31, "1/100", 10)["decoration_per_original_edge"] == 6
    assert not compiler.plan_aklt(2, "1", 10)["certified"]
    expect_failure(lambda: compiler.uniform_aklt(3, 3))
    expect_failure(lambda: compiler.aklt_channel(1))
    expect_failure(lambda: compiler.rational(0.5))

    directory = Path(__file__).with_name("compiler_examples")
    choi = json.loads((directory / "complex_choi.json").read_text())
    channel = compiler.choi_channel(choi)
    assert channel["delta"] == "1/9"
    assert channel["exact_positivity_proofs"]["lower_residual"]["rank"] == 1
    false_sandwich = dict(choi, upper="1")
    expect_failure(lambda: compiler.choi_channel(false_sandwich))
    singular_reference = dict(choi, R=[[1, 0], [0, 0]])
    expect_failure(lambda: compiler.choi_channel(singular_reference))

    graph_data = json.loads((directory / "path4_aklt.json").read_text())
    graph = compiler.graph_certificate(graph_data, directory)
    spectral = graph["spectral_certificate"]
    assert spectral["certified"]
    assert spectral["spectral_radius_upper_bound"] == "169/512"
    assert spectral["coarse_gap_lower_bound"] == "343/512"
    assert graph["microscopic_gap_multiplier_for_g_seed"] == "343/1024"
    # The supplied certificate improves the maximum row sum, 13/32.
    assert F(spectral["spectral_radius_upper_bound"]) < F(13, 32)
    graph_data.pop("certificate_weights")
    automatic = compiler.graph_certificate(graph_data, directory)["spectral_certificate"]
    assert automatic["certified"]
    assert F(automatic["spectral_radius_upper_bound"]) < F(169, 512)
    mixed = compiler.graph_certificate(json.loads((directory / "mixed_channels.json").read_text()), directory)
    assert mixed["spectral_certificate"]["certified"]

    # A fake or nonpositive Perron vector can never turn an invalid
    # influence matrix into a certificate.
    C = [[F(0), F(2)], [F(2), F(0)]]
    assert not compiler.spectral_certificate(C, [F(1), F(100)])["certified"]
    expect_failure(lambda: compiler.spectral_certificate(C, [F(0), F(1)]))
    result = {"status": "all checks passed", "exact_principal_minor_cross_checks": exact_cases,
              "zero_pivot_adversarial_check": "passed",
              "complex_rank_one_sandwich": "passed",
              "automatic_and_supplied_rational_vector_checks": "passed",
              "uniform_AKLT_degree3_decoration4_gap": "3/16",
              "uniform_AKLT_degree31_decoration6_gap": "7/432",
              "path4_rational_spectral_gap": "343/512"}
    Path(__file__).with_name("channel_gap_compiler_verified.json").write_text(json.dumps(result, indent=2) + "\n")
    print(json.dumps(result, indent=2))


if __name__ == "__main__":
    main()
