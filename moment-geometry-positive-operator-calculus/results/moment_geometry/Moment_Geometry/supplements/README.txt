COMPUTATIONAL SUPPLEMENT
========================

This directory contains independently runnable computations accompanying
the mathematical paper: exact identities, finite arithmetic certificates,
operational calculators, and explicitly labelled numerical diagnostics.
All data required by these programs are included. No original research
workspace, network service, external database, or SageMath installation is
required. The parent directory contains the paper and its proof sources.

The most immediately reusable components are:

  * ensembles/hesse_ensemble_certifier.py: a confidence calculator for
    certifying a qutrit ensemble using matched three-copy measurements;
  * modular/positive_bessel_filters.py and finite_arithmetic_certificate.py:
    positive modular-channel approximations, random-time samplers, exact
    quadrature isolation, and observable-dependent error budgets;
  * networks/channel_gap_compiler.py: exact small-channel and graph
    certificates for the primitive-wire spectral-gap theorem;
  * probability/verify_coherent_gram_moments.py: exact graph enumeration
    for coherent-state Gram moments, with optional simulation;
  * probability/toric_assignment_certificate.py: exact rational duals and
    certified intervals for phase-averaged Slater energies.


1. REPRODUCING THE CHECKS
-------------------------

Use Python 3.12 and install the supplied pinned dependencies. From this
directory, one possible setup is:

  python3 -m venv .venv
  .venv/bin/python -m pip install -r requirements.txt
  .venv/bin/python verify_all.py

On Windows, replace .venv/bin/python by .venv\Scripts\python.exe.
An existing environment with the listed dependencies is also sufficient.
The tested environment is CPython 3.12.14, NumPy 2.3.5, SciPy 1.17.0,
SymPy 1.14.0, mpmath 1.3.0, and python-flint 0.9.0.

The default runner executes 21 exact or certified-arithmetic suites. It
uses at most two concurrent subprocesses and sets BLAS/OpenMP thread
counts to one. All assertions remain enabled. Do not invoke the individual
verification scripts with Python's -O or -OO optimization flags.

To add the four bounded floating-point diagnostic suites:

  python verify_all.py --include-diagnostics

To explicitly add small seeded Monte Carlo experiments as well:

  python verify_all.py --monte-carlo

Monte Carlo is disabled in the default and --include-diagnostics runs.
Some adversarial floating diagnostics generate a fixed seeded collection
of test matrices; these are finite robustness checks, not Monte Carlo
estimates of physical quantities or asymptotic laws. The --monte-carlo
option adds 2,000 Hesse test rays, four coherent-Gram samples at each of
two small levels, and 2,000 draws per tested Bessel clock. Larger runs must
be requested directly through the corresponding module's command line.

For serial execution or a different per-program time budget:

  python verify_all.py --jobs 1 --timeout 900

The python-flint dependency supplies rigorous Arb real-ball arithmetic.
If it cannot be installed, the remaining suite can be run with:

  python verify_all.py --skip-arb

This option explicitly omits the Arb metric-bracketing example and skips
the complete toric-assignment suite, which requires Arb; the JSON report
records both omissions. Rational root isolation and rounding budgets in
the modular suite are still checked. A complete reproduction uses
python-flint and does not pass --skip-arb.

The aggregate record is results/verification_report.json. It contains:

  * Python, platform, dependency versions, thread limits, and run options;
  * each exact command, runtime, exit status, and evidence classification;
  * per-program stdout/stderr logs under results/logs/;
  * SHA-256 hashes of scripts, input examples, and generated certificates;
  * an explicit statement of the scope of the computational evidence.

Most programs write JSON next to their source. Programs accepting --output
are directed to results/ by the aggregate runner. An alternate aggregate
destination can be supplied with --output PATH. Scripts resolve their
inputs relative to their own location and can be run from any directory.


2. WHAT IS VERIFIED
--------------------

The evidence ledger distinguishes four categories.

EXACT ALGEBRA. Integer, rational, or symbolic-algebra identities are checked
at the listed finite degrees, sizes, and parameter values. Examples include
coherent-frame contractions, balanced-jet weights, partition tree counts,
and positive rational quadrature recurrences. Numerical approximations
printed alongside exact fractions are for display only.

CERTIFIED ARITHMETIC. Rational inequalities and rigorous enclosing
intervals validate the claimed finite certificate. Floating-point linear
algebra may propose a quadrature parameter or a graph weight, but the
accepted bound is checked by exact arithmetic. Arb provides outward
enclosures for the specified transcendental scalar example.

FLOATING DIAGNOSTICS. Fixed-size matrix, Fourier-transform, metric, and
adversarial checks test formulas and implementation consistency. Their
tolerances and dimensions are recorded by the individual programs. They
are not uniform operator bounds or proofs of infinite-size statements.

MONTE CARLO DIAGNOSTICS. Explicitly requested seeded samples illustrate
finite-size behavior. They are separated from algebraic certificates and
do not establish pressure limits, logarithmic uniform integrability,
large-deviation principles, or thermodynamic spectral gaps.

The general mathematical arguments and the external theorem inputs are
given in the paper and proof material. This package does not claim
proof-assistant formalization. Exact symbolic checks are also distinct
from a formal proof of the correctness of SymPy or the Python runtime.


3. QUTRIT ENSEMBLES AND POSITIVE WITNESSES
------------------------------------------

ensembles/hesse_ensemble_certifier.py

This calculator turns observed counts into a confidence upper bound for
the Wasserstein distance to the uniform Hesse ensemble, using the pure
state trace distance as transportation cost. The experiment combines the
positive rank-two projector Q on three matched copies with single-copy
SIC tomography. Its output also includes localization and weight bounds.

Plan a fixed-sample zero-click acceptance test:

  python ensembles/hesse_ensemble_certifier.py budget --epsilon 0.1 --alpha 0.01

Evaluate a synthetic count example (replace these counts by measurements):

  python ensembles/hesse_ensemble_certifier.py --output results/hesse_counts.json certify --q-trials 10000 --q-clicks 0 --sic-counts 1000,1000,1000,1000,1000,1000,1000,1000,1000 --alpha 0.01

Generate a seeded example with a rotated Hesse ensemble:

  python ensembles/hesse_ensemble_certifier.py simulate --rotation 0.01 --q-trials 100000 --single-trials 100000 --seed 20261115

The --output option precedes the subcommand. Parent directories for direct
CLI output files must already exist. The simulate subcommand is explicitly
a simulation, not experimental data.

The confidence theorem assumes independent source requests, the same pure
hidden state within each three-copy block, trusted qutrit dimension and
measurements, a calibrated reference basis, and sample sizes fixed before
observing outcomes. It is not device-independent certification. The
statistical formulas are justified in the paper; inverse beta quantiles
are evaluated numerically by SciPy and are not Arb interval enclosures.

Related exact verifiers:

  verify_cubic_classification.py checks determinant, tensor-marginal,
  invariant-theory, and phase-Fourier identities used in cubic support
  classification. It does not reprove the referenced closed-orbit theorem.

  verify_hesse_rigidity.py checks the finite Hesse algebra and moment data.

  verify_hesse_ensemble_certification.py --exact-only checks 18 identities
  behind the positive three-copy witness and reconstruction bounds. Its
  optional --samples N argument enables a separate seeded ray diagnostic;
  the default sample count is zero.

  verify_analytic_constants.py independently integrates all 36 matrix-unit
  inputs of the qutrit second coherent frame, verifies its three eigenvalue
  sectors, and checks moment-repair and energy-dilution arithmetic.


4. POSITIVE MODULAR CHANNELS AND METRICS
---------------------------------------

modular/positive_bessel_filters.py exposes the following reusable functions:

  rayleigh_moments(nu, maximum)
      Computes the Rayleigh sums from the Bessel differential equation.
      Passing fractions.Fraction for nu gives rational results.

  build_rule(nu, order, kind)
      Constructs a positive Gauss or zero-node Radau compression. The
      returned Rule gives the scales, Gamma shapes, heat drift, derivative
      order, and scalar error coefficient.

  rule_multiplier(x, rule, tau) and exact_multiplier(x, nu, tau)
      Evaluate the finite rule and the Bessel target at a scalar frequency.

  sample_times(rule, size, tau, rng)
      Samples Gaussian times with a Gamma-subordinator variance. Averaged
      unitary conjugation implements the compiled completely positive
      channel. Access to the specified Hamiltonian and state preparation
      are external operational requirements.

The scalar variable x is the frequency of ad_G. To implement a metric whose
argument is ad_K/2, use the unitary generator G=K/2. This factor must not be
absorbed silently into the sampled time or temperature. For empirical Gram
matrices involving several observables, apply the same random unitary in
each draw to all observable indices.

Direct verification commands:

  python modular/positive_bessel_filters.py --exact-only
  python modular/positive_bessel_filters.py --quick
  python modular/positive_bessel_filters.py --quick --monte-carlo-samples 2000

The first command checks 40 rational recurrence/orthogonality cases. The
second adds 216 dense-matrix cases on three- and five-spin chains, 45 metric
checks, and an adverse control. The last additionally samples random
clocks. Without --quick, the dense diagnostic includes larger finite chains.

Gauss and Radau give upper and lower scalar spectral multipliers and hence
bracket the stated quadratic metrics. Their difference is generally not a
completely positive map. The individual approximating channels are
completely positive. The retained adverse controls distinguish these claims.

modular/finite_arithmetic_certificate.py

  python modular/finite_arithmetic_certificate.py

This checks 32 rational root-isolation/rounding cases, chooses among local
observable error certificates for 15 temperature/tolerance combinations,
and produces 16 Arb metric brackets for a specified depolarized Slater
example. The exact pure-state tangent norm supplied to that example is
stated in its JSON output and in the paper; no 84-dimensional dense
Hamiltonian is diagonalized. A failed order budget is reported as "budget
not certified", not rounded into success. These are observable-norm error
budgets, not dimension-free diamond-norm estimates or a general efficiency
theorem at arbitrary temperature.

modular/local_commutator_certificate.py checks rational Pauli expansions
through derivative order 14 for chains of 8, 16, and 32 spins. It compares
the local coefficients for the two larger chains and independently checks
orders 1 through 6 by exact dense three-spin commutators.

modular/lee_yang_compiler.py --exact-only builds exact moment sequences for
nine finite Ising partition polynomials and validates 72 positive
quadrature rules. The positive underlying zero measure is supplied by the
Lee--Yang theorem; finitely many positive moments do not establish that
global property for an arbitrary input model. Omitting --exact-only adds
floating scalar-frequency checks.

modular/verify_ordered_heaps.py compares three formulas for ordered-log
coefficients on all 50 naturally labelled posets of sizes one through
four. It also checks 15 Bernoulli star values and the rational arithmetic
in the finite star obstruction. General order-polynomial reciprocity and
the heap-algebra identity are analytic/algebraic arguments in the paper.

modular/score_and_metric_audit.py and
modular_response/verify_power_response_and_obstructions.py are bounded
floating diagnostics of score normalization, monotone-metric formulas,
Fourier responses, and modular obstructions. The latter imports only the
included sibling verify_modular_obstructions.py.


5. CHANNEL AND NETWORK GAP CERTIFICATES
----------------------------------------

networks/channel_gap_compiler.py provides four subcommands:

  python networks/channel_gap_compiler.py aklt --degree 3 --decoration 4
  python networks/channel_gap_compiler.py plan --degree 31 --target 1/100
  python networks/channel_gap_compiler.py channel networks/compiler_examples/complex_choi.json
  python networks/channel_gap_compiler.py graph networks/compiler_examples/path4_aklt.json

Every subcommand accepts --output PATH after the subcommand. The examples
also include a graph with mixed channels and their expected JSON outputs.

Input entries are integers, rational strings such as "1/7", or exact
complex pairs {"re": "1/2", "im": "1/3"}. JSON floating-point numbers are
rejected for exact arithmetic. The compiler verifies complete-positivity
sandwiches by rational Hermitian congruence elimination, including
rank-deficient and zero-pivot cases. A numerical Perron vector may propose
graph weights; the final spectral-radius inequality is rationally checked.

The reported gap is initially the gap of the normalized coarse projector
Hamiltonian. Conversion to a microscopic physical Hamiltonian retains the
explicit finite-block gap factor g_seed and covering normalization. The
compiler does not infer g_seed from a coarse gap or perform many-body
diagonalization. The aklt and plan subcommands apply to the decorated
models and hypotheses specified by the theorem; they do not certify every
undecorated AKLT lattice.

  python networks/test_channel_gap_compiler.py

This verifier includes exact principal-minor comparisons on 12 complex
matrices, invalid-input controls, rank-deficient Choi examples, and exact
end-to-end graph certificates. The recorded coarse examples include 3/16
for degree 3 with four decorations and 7/432 for degree 31 with six.

  python networks/verify_two_port_schur_angle.py --trials 24 --seed 2026111507

This optional floating diagnostic checks the two-port angle mechanism on
seeded adversarial matrices and six independently contracted finite stars.
It is an implementation check alongside the analytic proof.


6. PROJECTIVE GEOMETRY, MOMENTS, AND COHERENT SPECTRA
----------------------------------------------------

probability/toric_assignment_certificate.py supplies an exact optimal-
assignment certificate for the finite torus-averaged Slater energy bounds.
The optimal matching is certified by rational multiplicative duals; Arb
then encloses the logarithmic energy bounds without trusting floating
assignment weights. The default input is a deterministic rational example.

  python probability/toric_assignment_certificate.py --verify

This checks 720 exposed Newton assignments, 319 multinomial modes, 720
assignment comparisons, and the rational dual inequalities of the default
example. Custom input uses --input FILE with JSON fields q, m, coordinates;
coordinates are positive rational strings, with one simplex point per
coherent monomial. The tool bounds the conditional angular mean energy,
not an attractive partition function or a large-deviation rate.

projective_jets/verify_jet_moment_map.py verifies exact zero-moment-map
identities for nine projective-plane degrees and an explicit degree-two
Cayley hyperdeterminant. --degrees accepts an alternate finite list.

projective_jets/verify_projective_jet_extension.py verifies four specified
higher-dimensional cases, including all root-support disjointness and
coordinate-weight identities. The all-dimension proof uses the separate
jet-construction and invariant-theory arguments in the paper.

geometry/verify_truncated_jet_chain.py checks six nonlinear chart examples,
their complementary-minor identities, and 100 exact finite threshold
identities. These finite checks are not a proof of the full constrained
second-moment entropy-energy threshold.

geometry/verify_singer_nef_obstruction.py checks the weighted ten-point
design's combinatorics, the support obstruction for nef nine-point
couplings, and the sharp 20/21 dilution arithmetic. The design itself is
attributed in the paper. The K3 cover and its lattice are established by
the geometric argument and cited classification inputs, not certified by
this finite combinatorial script.

probability/verify_microscopic_repair.py checks positive moment-repair
algebra and exact cancellation formulas.

probability/verify_coherent_gram_moments.py --exact-only enumerates all
26,442 set partitions through order nine, checks all rooted Eulerian
cofactors, and computes rational tree-weighted moments. It independently
checks the first four finite-level expectation formulas at seven degrees.
The first four limiting qutrit moments are 1, 2, 5, and 57/4. Monte Carlo
is opt-in:

  python probability/verify_coherent_gram_moments.py --monte-carlo --levels 2 4 --repetitions 4 --seed 20261115

Here --levels denotes anticanonical levels k; the coherent polynomial
degree is 3k and the square Gram dimension is binomial(3k+2,2). Numerical
log determinants are reported only when the computed spectrum is positive.
They are diagnostics and do not certify control of small eigenvalues.

probability/verify_probability_extensions.py independently enumerates
5,295 set partitions through order eight. It checks the crossing/tree
criterion, Narayana counts, 124 pairing bounds, aspect-ratio and dimension
identities, and the finite combinatorics behind the interpolation toward
the Marchenko--Pastur moments. Positive moments alone do not establish an
attractive pressure limit or an attractive large-deviation principle.


7. OPERATIONAL QUTRIT CONTACT GEOMETRY
--------------------------------------

The three files in qutrit/ check exact identities used in the operational
5/12 result:

  python qutrit/verify_qutrit_packet.py
  python qutrit/verify_three_ray_flag.py
  python qutrit/verify_four_ray_flag.py

They verify Haar-cell constants, the three-ray formula, and the four-ray
coefficient/SOS inequalities. The certified lower assignment coefficient
is 2767/2970, exceeding 9/10 by 47/1485. Geometric sign conditions and
the analytic integral estimates used with these identities are justified
in the proof, not inferred from sampled configurations.

The operational theorem applies to the stated reducible/projective-
simulable centers and their neighborhoods, including zero measurement
labels. The neighborhood theorem is qualitative at fixed outcome number;
the finite coefficient margin is not an explicit operational neighborhood
radius. The programs make no claim of universal joint measurability for
all irreducible qutrit POVMs at visibility 5/12.


8. REUSING AND EXTENDING THE MATERIAL
--------------------------------------

formalization_guide.tex and theorem_registry.json provide the proof
interfaces, normalizations, external theorem dependencies, and mappings
to the computational checks. The registry distinguishes supplied prose
proofs from independently verified proof-assistant results.

Each generated JSON document states its finite scope and preserves exact
rationals as strings. Keep these strings when importing a certificate into
another system. For a proof-assistant translation, the natural finite
interfaces are rational polynomial identities, exact positivity transcripts,
root-isolating intervals, integer graph cofactors, and fixed combinatorial
lists. The external analytic and geometric theorem dependencies should
remain explicit.

When adapting an example, distinguish the supplied model assumptions from
the certificate produced under those assumptions. In particular, retain
Hamiltonian normalization and finite-block gap inputs for network models;
matched-replica and sampling assumptions for ensemble certification; the
ad_K/2 normalization for information metrics; and the positivity of the
underlying measure for quadrature compilation.

The paper gives source attribution and proofs. The computational files are
organized to expose finite mathematical content rather than to replace
those arguments by numerical evidence.
