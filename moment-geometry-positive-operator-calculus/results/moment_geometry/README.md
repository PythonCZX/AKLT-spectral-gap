# MomentGeometry formalization programme

This main-project directory follows the person-supplied **Formalization and
reproducibility guide** for *Moment geometry and positive operator calculus*.
The main Lean source is `lean/MomentGeometry/`. The supplied distribution is
copied here for reading and independent reruns, not silently upgraded to proof
assistant results.

## Scope and status

The source registry contains 74 proved-on-paper contract records, all initially
`proof_assistant_verified=false`. This project makes no claim that these have
all been formalized. See [ROADMAP.md](ROADMAP.md) and machine-readable
[COVERAGE.json](COVERAGE.json) for record-specific status.

The verified component records are `op:hyperbolic-clock`, `q:thm-powers`
(scalar response functions only), `q:kms-compatibility`,
`eq:coherent-finite-moments`, and `prop:repair`. The operator-level finite-patch
comparison `q:lem-seed` is additionally contract-verified. Newer matrix steps
support `q:thm-wire-gap`, `q:thm-oblique`, `q:cor-filtered`, and
`q:cor-aklt`, with the angle inputs and physical kernel instantiation expressly
open. There is one contract-verified record, nine component-bearing records and
64 assigned records. The asymptotic
`thm:coherent-spectral-law` itself remains open; its finite moment and
order-≤4 cofactor inputs are components, not its proof. Other source contracts
remain assigned. In particular, no complete nonzero spectral
gap for the spin-3/2 hexagonal AKLT model is claimed. The attached decorated
AKLT transfer contract is different and retains its finite-patch gap factor.

Original supplied archives are unchanged. Repeated archives supplied with the
`-2` suffix are pairwise byte-identical; only one of each was used.

## Direct checks

```sh
OPENBLAS_NUM_THREADS=1 OMP_NUM_THREADS=1 \
  python3 scripts/check_lean_moment_geometry.py
python3 scripts/moment_geometry_coverage.py
```

The direct Lean build currently passes **28 modules and 201 audited theorem
reports** using only `propext`, `Classical.choice`, and `Quot.sound` on the
pinned `/opt/lean/bin/lean` 4.33.1 with installed `/opt/mathlib`.
Moment-limit refinements and the directed-cycle-cofactor finite model from
`smwi6zlvo/m1/d2` have been independently rebuilt and accepted **at their
scoped finite interface**. The separate member review has 16 further standard
axiom headline reports at `results/moment_geometry/review/smwi6zlvo_m1/revision1/`.
This does not complete the asymptotic spectral law.
The scanner rejects `sorry`, `admit`, `axiom`, `native_decide`, `unsafe` in
actual source tokens (comments are ignored). It also reruns all module-specific
`#print axioms` blocks. This is not a module-count proof of registry coverage.

Provenance declarations for the imported CP implementation are copied from
`results/coherent_continuation/review_smwhh7nna_m2/lean/ModularCPBase.lean` and
`ModularCPClosure.lean`, with imports adapted under `MomentGeometry.Operator.CP`
and freshly rebuilt. Conditional interfaces in the older base (Euler sine
product and conjugation positivity) are discharged in the closure module. An
unconditional clock theorem and the full fractional-power matrix response are
different objects; the latter remains pending.

## Supplied finite evidence

An isolated Python environment was created at `results/moment_geometry/.venv`
to respect the supplied pinned versions (`numpy 2.3.5`, `scipy 1.17.0`,
`sympy 1.14.0`, `mpmath 1.3.0`, `python-flint 0.9.0`) without changing the
shared environment. A fresh driver run passes **18 exact, 3 certified-arithmetic,
and 4 bounded numerical diagnostic suites, with none skipped or failed**.
See [fresh verification report](review/verification_report.json).
These computations support the mathematical interfaces; they do not prove the
analytic statements or prove a formal proof assistant certificate.

The supplied article build itself was also run. Its initial dependency boundary
was `ModuleNotFoundError: pypdf`; `pypdf` was installed into the isolated
environment and `results/moment_geometry/.venv/bin/python
results/moment_geometry/Moment_Geometry/build.py` then passed. The generated
outputs have **99 main-report pages and 12 guide pages**, with no undefined
references or overfull boxes. It is a document/layout check, not a new audit of
every mathematical assertion.

## Swarm status

All eight prior unrelated swarms were stopped under the earlier explicit
request. The person subsequently explicitly authorized swarm work for this
guide. The current formalization swarm is `smwi6zlvo`: eight members,
`deepseek/deepseek-v4.1-flash`, maximum reasoning, 100 steps each, a 1600-call
budget and a 180-minute deadline. Its roles cover fractional-power matrix
response, positive Fourier/KMS calculus, Schur/angle, network gap, finite-patch
and AKLT transfer, coherent moments, and integration. Reports are judged after
independent inspection; having many declarations is not evidence of global
completion.
