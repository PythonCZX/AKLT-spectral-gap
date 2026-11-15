# Moment geometry and positive operator calculus

This curated package contains the supplied 99-page report **Moment geometry and
positive operator calculus**, its **12-page formalization and reproducibility
guide**, the executable computational supplements, the 13 figure PDFs,
bibliographic sources, and the current Lean 4 formalization evidence.

The original article's **proofs are mathematical prose**. Finite scripts,
numerical diagnostics, and independent Lean modules have different and separate
trust scopes. This package does **not** assert that the entire paper, an
unrestricted qutrit statement, or a nonzero spectral gap for the spin-3/2
undecorated hexagonal AKLT model has been formalized.

## Read or reproduce

### Article and formalization guide

- [Main report (99 pages)](Moment_Geometry/main.pdf)
- [Formalization and reproducibility guide (12 pages)](Moment_Geometry/formalization.pdf)
- [Formalization guide source](Moment_Geometry/supplements/formalization_guide.tex)
- [Theorem and dependency registry](Moment_Geometry/supplements/theorem_registry.json)
- [Figure-generation code](Moment_Geometry/code/make_figures.py) and [figure PDFs](Moment_Geometry/figures/)
- [Verification source and driver](Moment_Geometry/supplements/verify_all.py)
- [Exact and certified verification records](Moment_Geometry/supplements/results/)
- [Current Lean coverage status](status/COVERAGE.json) and [audit coverage](status/coverage_74_audit.json)

The source TeX is in `Moment_Geometry/`: `main.tex`, `sections/`, `proofs/`,
`code/`, and `data/`. Article paths used in the guide and registry retain the
original directory layout intentionally.

### Lean project

The `lean/MomentGeometry/` directory contains the direct finite interfaces
under construction. Run from the root of this package:

```sh
OPENBLAS_NUM_THREADS=1 OMP_NUM_THREADS=1 \
  python3 scripts/check_lean_moment_geometry.py
```

The scripted gate uses the pinned `/opt/lean/bin/lean` Lean 4.33.1 and installed
`/opt/mathlib`; it scans source tokens for `sorry`, `admit`, `axiom`,
`native_decide`, and `unsafe`, and checks `#print axioms` against **only**
`propext`, `Classical.choice`, and `Quot.sound`. It uses no custom Lake project.

Latest independently verified export: **28 modules, 201 directly printed
axiom reports**. That number refers to the declared print/theorem reports in the
modules, not every helper declaration and not 201 completed source theorems.

### Current formalization coverage

Read [status/ROADMAP.md](status/ROADMAP.md) for record-by-record gaps and
[status/coverage_74_audit.json](status/coverage_74_audit.json) for the machine
coverage table. At this export snapshot:

- **1 source contract (`q:lem-seed`) is completed at operator level**, with the
  registration's positivity, micro/patch kernels and coverage assumptions; the
  real nonzero finite-patch gap is a separate input and not glossed over.
- **9 additional registry records have proved components** (clock/KMS,
  coherent finite moments, repair, fractional-power response, conditional
  matrix gap, oblique/filter, AKLT arithmetic).
- **64 source records remain assigned**. Heavy analytic and geometric
  dependencies are not silently discharged by numeric checks.

In particular the fractional-power module proves a spectral divided-difference
response and CP bounds conditional on kernel positivity, **not yet** the full
Duhamel identification or Fourier transform. Network-gap modules have genuine
matrix/spectral assembly under explicit `hcross` angle inputs; they do not
prove the full physical CP tensor transport. The finite-patch comparison does
not itself instantiate a nonzero physical AKLT gap, still less an undecorated
hexagonal spectral-gap theorem. Those obligations are tracked, not hidden.

### Finite computational evidence

The supplied finite suite passes, in an isolated environment with the exact
requirements in `Moment_Geometry/supplements/requirements.txt`:

- **18 exact algebra**;
- **3 certified arithmetic/enclosure**;
- **4 bounded numerical diagnostics**.

See [independent verification report](status/verification_report.json).
These results reproduce finite identities and certified bounds. They are
**not universal proofs and not proof-assistant verification of the report**.

Recreate a project-local environment outside version control:

```sh
python3 -m venv .venv
.venv/bin/python -m pip install \
  -r Moment_Geometry/supplements/requirements.txt pypdf
export OPENBLAS_NUM_THREADS=1 OMP_NUM_THREADS=1
.venv/bin/python Moment_Geometry/supplements/verify_all.py \
  --jobs 1 --include-diagnostics \
  --output /tmp/moment-geometry-verification.json
.venv/bin/python Moment_Geometry/build.py
```

`pypdf` is required for the article build's page-count checks; a first isolated
run without it stopped at `ModuleNotFoundError: pypdf` and was repaired. The
successful render has **99 article pages + 12 guide pages**, with zero undefined
references and zero overfull boxes. Choose your own writable scratch/output path
rather than `/tmp` if you would like to retain logs.

See `.gitignore` before committing: virtual environments, `.olean`, generated
documentation and validation logs are excluded, not the legitimate supplied
computational reports.

## Maintenance and release status

This is a release export for review, not a certification of complete article
coverage and not an instruction to push everything from the source working
repository. The code and source materials in the supplied archive family have
been copied without modifying their mathematical text. Relevant new imports
under `MomentGeometry.Operator.*` are documented in the coverage files.

For a later release review: add newly verified modules by their fresh build
source paths, regenerate coverage with the two coverage programs below, and
retain explicit hypotheses for analytical or physical inputs such as tensor CP
whitening, Choi spectra, Fourier densities and regional tensor kernels.

```sh
python3 scripts/moment_geometry_coverage.py
python3 scripts/moment_geometry_coverage_audit.py \
  --out status/coverage_74_audit.json
```
