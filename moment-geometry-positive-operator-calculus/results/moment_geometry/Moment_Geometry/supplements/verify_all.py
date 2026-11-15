#!/usr/bin/env python3
"""Run the finite checks accompanying the paper and write an evidence ledger.

The default suite performs exact algebra and certified interval checks.
Floating diagnostics and Monte Carlo are separately opt-in.  This runner
does not claim proof-assistant verification of the mathematical theorems.
"""
from __future__ import annotations

import argparse
from concurrent.futures import ThreadPoolExecutor, as_completed
from datetime import datetime, timezone
import hashlib
from importlib import metadata
import json
import os
from pathlib import Path
import platform
import shlex
import subprocess
import sys
import time


ROOT = Path(__file__).resolve().parent
THREAD_VARIABLES = (
    "OPENBLAS_NUM_THREADS", "MKL_NUM_THREADS", "OMP_NUM_THREADS",
    "NUMEXPR_NUM_THREADS", "BLIS_NUM_THREADS", "VECLIB_MAXIMUM_THREADS",
)
PACKAGES = ("numpy", "scipy", "sympy", "mpmath", "python-flint")


def digest(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def relative(path: Path) -> str:
    try:
        return path.resolve().relative_to(ROOT).as_posix()
    except ValueError:
        return str(path.resolve())


def task(name, script, artifact, evidence="exact_algebra", arguments=(), scope=""):
    return {
        "id": name, "script": script, "arguments": list(arguments),
        "artifacts": [artifact], "evidence_class": evidence, "scope": scope,
    }


def tasks(args, output_directory: Path):
    result_path = lambda name: str(output_directory / name)
    core = [
        task("cubic_classification", "ensembles/verify_cubic_classification.py",
             "ensembles/cubic_classification_verified.json",
             scope="Finite tensor, determinant, and Fourier identities; external orbit theorems remain analytic inputs."),
        task("hesse_rigidity", "ensembles/verify_hesse_rigidity.py",
             "ensembles/hesse_rigidity_verified.json"),
        task("hesse_certification_exact", "ensembles/verify_hesse_ensemble_certification.py",
             result_path("hesse_exact.json"), arguments=("--exact-only", "--output", result_path("hesse_exact.json")),
             scope="Eighteen exact identities for the positive three-copy witness and moment reconstruction."),
        task("coherent_frame_constants", "ensembles/verify_analytic_constants.py",
             "ensembles/analytic_constants_verified.json",
             scope="Coherent-frame contractions and repair arithmetic; not a numerical test of compactness or PDE regularity."),
        task("microscopic_moment_repair", "probability/verify_microscopic_repair.py",
             "probability/microscopic_repair_verified.json"),
        task("coherent_gram_combinatorics", "probability/verify_coherent_gram_moments.py",
             result_path("coherent_gram_exact.json"), arguments=("--exact-only", "--output", result_path("coherent_gram_exact.json")),
             scope="All set partitions through order nine and finite expectation identities through order four; no pressure or LDP inference."),
        task("coherent_spectral_extensions", "probability/verify_probability_extensions.py",
             "probability/probability_extensions_verified.json",
             scope="Independent crossing criterion, Narayana counts, pairing bounds, and aspect-ratio/dimension identities through order eight."),
        {**task("toric_assignment_certificate", "probability/toric_assignment_certificate.py",
             "probability/toric_assignment_certificate.json", evidence="certified_arithmetic",
             arguments=("--verify",),
             scope="Exact rational multiplicative assignment duals and finite Newton-vertex checks, with Arb logarithmic energy enclosures."),
         "requires_arb": True},
        task("projective_plane_jets", "projective_jets/verify_jet_moment_map.py",
             "projective_jets/jet_moment_map_exact.json"),
        task("higher_dimensional_jets", "projective_jets/verify_projective_jet_extension.py",
             "projective_jets/projective_jet_extension_exact.json"),
        task("nonlinear_jet_chain", "geometry/verify_truncated_jet_chain.py",
             "geometry/truncated_jet_chain_exact.json",
             scope="Finite nonlinear chart chain rules and threshold identities; not the conjectural constrained second-moment threshold."),
        task("singer_nef_coupling", "geometry/verify_singer_nef_obstruction.py",
             "geometry/singer_nef_obstruction_exact.json"),
        task("qutrit_contact_constants", "qutrit/verify_qutrit_packet.py",
             "qutrit/exact_verification.json"),
        task("qutrit_three_ray", "qutrit/verify_three_ray_flag.py",
             "qutrit/three_ray_flag_exact_verification.json"),
        task("qutrit_four_ray", "qutrit/verify_four_ray_flag.py",
             "qutrit/four_ray_flag_exact_verification.json"),
        task("ordered_heaps", "modular/verify_ordered_heaps.py",
             "modular/ordered_heaps_verified.json",
             scope="Fifty finite posets, three coefficient formulas, and fifteen Bernoulli values; general reciprocity is proved in the text."),
        task("bessel_rational_recurrences", "modular/positive_bessel_filters.py",
             result_path("bessel_exact.json"), arguments=("--exact-only", "--output", result_path("bessel_exact.json"))),
        task("finite_arithmetic_quadrature", "modular/finite_arithmetic_certificate.py",
             "modular/finite_arithmetic_certificate.json", evidence="certified_arithmetic",
             arguments=("--skip-arb",) if args.skip_arb else (),
             scope="Exact root isolation and dyadic rounding budgets; optional Arb enclosures. Floating proposals are validated by rational inequalities."),
        task("lee_yang_quadrature", "modular/lee_yang_compiler.py",
             "modular/lee_yang_compiler.json", arguments=("--exact-only",),
             scope="Exact partition-polynomial moments and positive quadrature certificates; the Lee--Yang theorem is an identified source assumption."),
        task("local_commutator_certificates", "modular/local_commutator_certificate.py",
             "modular/local_commutator_certificate.json"),
        task("channel_gap_compiler", "networks/test_channel_gap_compiler.py",
             "networks/channel_gap_compiler_verified.json", evidence="certified_arithmetic",
             scope="Exact Choi and rational graph bounds; any physical finite-block gap is a separate stated input."),
    ]
    if args.include_diagnostics or args.monte_carlo:
        core += [
            task("power_response_diagnostic", "modular_response/verify_power_response_and_obstructions.py",
                 "modular_response/power_response_and_obstructions_verified.json", evidence="floating_diagnostic",
                 scope="Numerical Fourier, matrix-response, and modular-obstruction checks at fixed sizes."),
            task("score_metric_diagnostic", "modular/score_and_metric_audit.py",
                 "modular/score_and_metric_audit.json", evidence="floating_diagnostic"),
            task("bessel_matrix_diagnostic", "modular/positive_bessel_filters.py",
                 result_path("bessel_diagnostic.json"), evidence="floating_diagnostic",
                 arguments=("--quick", "--output", result_path("bessel_diagnostic.json")),
                 scope="Dense three- and five-spin tests and finite metric checks; Monte Carlo disabled."),
            task("two_port_schur_diagnostic", "networks/verify_two_port_schur_angle.py",
                 result_path("two_port_schur_diagnostic.json"), evidence="floating_diagnostic",
                 arguments=("--trials", "24", "--seed", "2026111507", "--output", result_path("two_port_schur_diagnostic.json")),
                 scope="Twenty-four seeded adversarial random test matrices and six direct finite-star contractions, not statistical inference."),
        ]
    if args.monte_carlo:
        core += [
            task("hesse_monte_carlo", "ensembles/verify_hesse_ensemble_certification.py",
                 result_path("hesse_monte_carlo.json"), evidence="monte_carlo_diagnostic",
                 arguments=("--samples", "2000", "--seed", "20261115", "--output", result_path("hesse_monte_carlo.json"))),
            task("coherent_gram_monte_carlo", "probability/verify_coherent_gram_moments.py",
                 result_path("coherent_gram_monte_carlo.json"), evidence="monte_carlo_diagnostic",
                 arguments=("--monte-carlo", "--levels", "2", "4", "--repetitions", "4", "--seed", "20261115", "--output", result_path("coherent_gram_monte_carlo.json"))),
            task("bessel_clock_monte_carlo", "modular/positive_bessel_filters.py",
                 result_path("bessel_monte_carlo.json"), evidence="monte_carlo_diagnostic",
                 arguments=("--quick", "--monte-carlo-samples", "2000", "--output", result_path("bessel_monte_carlo.json"))),
        ]
    return core


def run_one(spec, args, directory, environment):
    command = [sys.executable, str(ROOT / spec["script"]), *spec["arguments"]]
    display = ["python", spec["script"], *[relative(Path(x)) if Path(x).is_absolute() else x for x in spec["arguments"]]]
    stdout = directory / "logs" / (spec["id"] + ".stdout.txt")
    stderr = directory / "logs" / (spec["id"] + ".stderr.txt")
    started = time.monotonic()
    if spec.get("requires_arb") and args.skip_arb:
        return {
            "id": spec["id"], "status": "skipped", "evidence_class": spec["evidence_class"],
            "scope": spec["scope"], "command_from_supplements": shlex.join(display), "argv": display,
            "exit_code": None, "elapsed_seconds": 0.0,
            "failure": None, "skip_reason": "Explicit --skip-arb: this complete suite requires Arb.",
            "script_sha256": digest(ROOT / spec["script"]), "stdout": None, "stderr": None,
            "artifacts": [],
        }
    failure = None
    try:
        with stdout.open("w", encoding="utf-8") as out, stderr.open("w", encoding="utf-8") as err:
            proc = subprocess.run(command, cwd=ROOT, env=environment, stdout=out,
                                  stderr=err, timeout=args.timeout, check=False)
        code = proc.returncode
    except subprocess.TimeoutExpired:
        code, failure = None, "subprocess timeout"
    except OSError as exc:
        code, failure = None, str(exc)
    artifacts = []
    for filename in spec["artifacts"]:
        path = Path(filename)
        if not path.is_absolute():
            path = ROOT / path
        exists = path.is_file()
        artifacts.append({"path": relative(path), "exists": exists,
                          "sha256": digest(path) if exists else None,
                          "bytes": path.stat().st_size if exists else None})
    passed = code == 0 and all(a["exists"] for a in artifacts)
    if code == 0 and not passed:
        failure = "expected output artifact missing"
    return {
        "id": spec["id"], "status": "passed" if passed else "failed",
        "evidence_class": spec["evidence_class"], "scope": spec["scope"],
        "command_from_supplements": shlex.join(display), "argv": display,
        "exit_code": code, "elapsed_seconds": round(time.monotonic()-started, 3),
        "failure": failure, "script_sha256": digest(ROOT / spec["script"]),
        "stdout": relative(stdout), "stderr": relative(stderr), "artifacts": artifacts,
    }


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--include-diagnostics", action="store_true",
                        help="Also run bounded floating and adversarial diagnostics.")
    parser.add_argument("--monte-carlo", action="store_true",
                        help="Explicitly add small seeded Monte Carlo runs; implies diagnostics.")
    parser.add_argument("--skip-arb", action="store_true",
                        help="Explicitly omit only the python-flint certified scalar example.")
    parser.add_argument("--jobs", type=int, choices=(1, 2), default=2)
    parser.add_argument("--timeout", type=float, default=900,
                        help="Time limit in seconds per subprocess (default 900).")
    parser.add_argument("--output", type=Path, default=ROOT / "results" / "verification_report.json")
    args = parser.parse_args()
    if not __debug__:
        parser.error("run without -O or -OO: assertions are part of the verification")
    if args.timeout <= 0:
        parser.error("--timeout must be positive")
    args.output = args.output.resolve()
    directory = args.output.parent
    (directory / "logs").mkdir(parents=True, exist_ok=True)
    versions = {}
    for package in PACKAGES:
        try:
            versions[package] = metadata.version(package)
        except metadata.PackageNotFoundError:
            versions[package] = None
    required = PACKAGES[:-1] if args.skip_arb else PACKAGES
    missing = [name for name in required if versions[name] is None]
    if missing:
        parser.error("missing dependencies: " + ", ".join(missing)
                     + "; install requirements.txt, or explicitly use --skip-arb for python-flint only")
    environment = os.environ.copy()
    environment.update({name: "1" for name in THREAD_VARIABLES})
    environment["PYTHONHASHSEED"] = "0"
    environment["PYTHONOPTIMIZE"] = "0"
    environment["PYTHONDONTWRITEBYTECODE"] = "1"
    specifications = tasks(args, directory)
    started = time.monotonic()
    started_utc = datetime.now(timezone.utc).isoformat()
    completed = []
    print(f"Running {len(specifications)} suites; at most {args.jobs} subprocesses; BLAS threads = 1.", flush=True)
    with ThreadPoolExecutor(max_workers=args.jobs) as executor:
        futures = [executor.submit(run_one, spec, args, directory, environment)
                   for spec in specifications]
        for future in as_completed(futures):
            item = future.result()
            completed.append(item)
            print(f"{item['status'].upper():6s} {item['id']} ({item['elapsed_seconds']:.2f}s)", flush=True)
    order = {spec["id"]: i for i, spec in enumerate(specifications)}
    completed.sort(key=lambda row: order[row["id"]])
    by_class = {}
    for item in completed:
        group = by_class.setdefault(item["evidence_class"], {"passed": 0, "failed": 0, "skipped": 0})
        group[item["status"]] += 1
    manifest_paths = sorted(ROOT.rglob("*.py")) + [ROOT / "requirements.txt"]
    manifest_paths += sorted((ROOT / "networks" / "compiler_examples").glob("*.json"))
    manifest = {relative(path): digest(path) for path in manifest_paths if path.is_file()}
    report = {
        "schema_version": 1,
        "status": ("failed" if any(item["status"] == "failed" for item in completed) else
                   "passed_with_skips" if any(item["status"] == "skipped" for item in completed) else "passed"),
        "started_utc": started_utc, "finished_utc": datetime.now(timezone.utc).isoformat(),
        "elapsed_seconds": round(time.monotonic()-started, 3),
        "environment": {"python": sys.version, "python_implementation": platform.python_implementation(),
                        "platform": platform.platform(), "packages": versions,
                        "blas_thread_environment": {key: environment[key] for key in THREAD_VARIABLES},
                        "python_hash_seed": "0"},
        "options": {"jobs": args.jobs, "timeout_seconds_per_suite": args.timeout,
                    "include_diagnostics": args.include_diagnostics or args.monte_carlo,
                    "monte_carlo": args.monte_carlo, "skip_arb": args.skip_arb},
        "summary_by_evidence_class": by_class,
        "theorem_scope": "Finite exact checks and certified enclosures support reproducibility; analytic arguments and external theorems are stated in the paper. No proof-assistant formalization is claimed. Floating and Monte Carlo diagnostics do not establish asymptotic theorems.",
        "suites": completed, "source_sha256_manifest": manifest,
    }
    args.output.write_text(json.dumps(report, indent=2) + "\n", encoding="utf-8")
    print(json.dumps({"status": report["status"], "summary": by_class,
                      "elapsed_seconds": report["elapsed_seconds"], "report": str(args.output)}, indent=2))
    return 0 if report["status"] != "failed" else 1


if __name__ == "__main__":
    raise SystemExit(main())
