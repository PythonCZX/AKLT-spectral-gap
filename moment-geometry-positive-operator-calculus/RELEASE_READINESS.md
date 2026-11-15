# Publication readiness — source export

## Export method and intended scope

The export is an **allowlist copy** of supplied public material, built directly
after stopping the slow publication agent. Original supplied archives remain
untouched. The two duplicate `-2` attachment variants were **not** included.
Source materials (`main.tex`, `proofs/`, `sections/`, `data/`, original document
code) retain the layout `Moment_Geometry/` required by the existing build scripts
and theorem registry. Main Lean source names retain `lean/MomentGeometry/`.

This export excludes local project history and irrelevant research directories;
it does not claim a whole-repository push is appropriate. Nothing has been
pushed or published.

## Verified export contents checked

- `Moment_Geometry/`: the rendered report (99 pages) and formalization guide
  (12 pages), 13 PDF figures, TeX/article/proof sources, code and bibliography.
- `Moment_Geometry/supplements/`: all executable finite verification sources,
  exact/certificate inputs and supplied legitimate reports (with separate
  evidence classes clearly labelled).
- `lean/MomentGeometry/`: 28 direct Lean source modules, not `.olean` caches.
- `scripts/`: Lean module/axiom gate, main coverage updater and
  secondary declaration-resolving coverage auditor.
- `status/`: curated current roadmap, coverage JSONs and latest primary logs.

The article renders had no undefined references or overfull boxes. The supplied
finite validation passed 18 exact, 3 certified arithmetic and four bounded
numerical diagnostic suites. Latest main Lean checks compiled **28 modules and
201 directly printed standard-axiom reports**.

These results document what was actually reproduced, not a blanket proof of the
paper or of all 74 registered contracts.

## Exclusions (deliberate, not ignored regressions)

No inclusion of

- `.git`, `.ultramath`, agent transcripts, memory/context files, orchestration
  files, rejections or unrelated previous research outputs;
- `.scratch/`, `.venv/`, `__pycache__`, Python bytecode, Lean `.olean` caches,
  timed-out or failure/OOM logs as publication content;
- attachments and duplicate `-2` archives, or the original ZIPs whose contents
  are already included;
- `external/` local dependency trees/library caches;
- `results/gap_closure/` and `results/coherent_continuation/` older unrelated
  research directories, apart from directly relevant current status/review logs;
- unrelated root research workbenches and interactive state;
- absolute local home paths, credentials or other secret material.

The `.git` status of the source repository is **not** used as implicit permission
to export all untracked contents. An allowlist rather than broad directory copy
is the release policy.

## Publication gating (not yet authorization to publish)

Review

1. the public [README](README.md) and coverage in [status/ROADMAP.md](status/ROADMAP.md);
2. `MANIFEST.json` file/bytes/sha256 records and validation output;
3. `status/COVERAGE.json` and `status/coverage_74_audit.json`, including precise
   remaining analytic inputs and the actual single operator-level completed
   theorem (finite-patch `q:lem-seed`);
4. whether kernel/cosine conditions such as `hcross`/`hcos` and Fourier-density
   interface remain publicly marked as pending rather than hidden in
   finished-sounding theorem names.

**Do not publish by describing a complete spin-3/2 AKLT gap, a complete
fractional-power theorem or all 74 proof contracts as if done.** Current state:
one source contract complete, nine additional component-records and sixty-four
assigned, not full coverage. Lean 4.33.1 is fixed for this package; other
versions/ABIs are not an interchangeable substitute.

The supplied verification environment requires its pinned packages plus
`pypdf`; the environment itself is **never committed**. Environment versions
and the validation log location belong in an eventual publication changelog.
