#!/usr/bin/env python3
"""Build the integrated MomentGeometry finite-CP interfaces and audit their axioms.

This script does not validate the full theorem registry. The component coverage
ledger is kept separately in results/moment_geometry/.
"""
from __future__ import annotations
import os
from pathlib import Path
import re
import subprocess
import sys

ROOT = Path(__file__).resolve().parent.parent
LEAN = Path('/opt/lean/bin/lean')
MODULES = [
    'MomentGeometry/Operator/CP/Base',
    'MomentGeometry/Operator/CP/Closure',
    'MomentGeometry/Operator/CP/Kraus',
    'MomentGeometry/Operator/Clock',
    'MomentGeometry/Operator/KMS',
    'MomentGeometry/Coherent/Moments',
    'MomentGeometry/Coherent/CycleCofactor',
    'MomentGeometry/Coherent/Axioms',
    'MomentGeometry/Coherent/UnitDensity',
    'MomentGeometry/Repair/Frame',
    'MomentGeometry/Frozen/Statements',
    'MomentGeometry/Composed',
    'MomentGeometry/Operator/Powers',
    'MomentGeometry/Network/CPOrder',
    'MomentGeometry/Network/ProjBasics',
    'MomentGeometry/Network/GapAssembly',
    'MomentGeometry/Network/GapSpectral',
    'MomentGeometry/Network/RowCriterion',
    'MomentGeometry/Network/SchurConstant',
    'MomentGeometry/Network/WireGap',
    'MomentGeometry/Swarm/Seed',
    'MomentGeometry/Swarm/Oblique',
    'MomentGeometry/Swarm/Filtered',
    'MomentGeometry/AKLT/Wire',
    'MomentGeometry/AKLT/Radius',
    'MomentGeometry/AKLT/Finite',
    'MomentGeometry/AKLT/Decoration',
    'MomentGeometry/AKLT/Bridge',
]
STANDARD = {'propext', 'Classical.choice', 'Quot.sound'}


def code_only(text: str) -> str:
    """Exclude nested comments and line comments from a simple forbidden-token scan."""
    result = []
    depth = 0
    i = 0
    while i < len(text):
        if text.startswith('/-', i):
            depth += 1
            result.append('  ')
            i += 2
        elif text.startswith('-/', i):
            depth = max(depth - 1, 0)
            result.append('  ')
            i += 2
        elif depth == 0 and text.startswith('--', i):
            result.extend(' ' for _ in range(len(text) - i))
            break
        elif depth == 0:
            result.append(text[i])
            i += 1
        else:
            result.append('\n' if text[i] == '\n' else ' ')
            i += 1
    return '\n'.join(line for s in result for line in s.splitlines())


def main() -> int:
    if not LEAN.is_file():
        print(f'missing pinned Lean executable {LEAN}', file=sys.stderr)
        print(subprocess.run(['lean', '--version'], capture_output=True, text=True).stdout)
        return 1
    print(subprocess.check_output([str(LEAN), '--version'], text=True).strip())
    env = os.environ.copy()
    env['LEAN_PATH'] = f"{ROOT / 'lean'}:" + env['LEAN_PATH']
    logdir = ROOT / 'results' / 'moment_geometry' / 'review'
    logdir.mkdir(parents=True, exist_ok=True)
    combined = []
    for module in MODULES:
        rel_path = Path('lean') / (module + '.lean')
        source = ROOT / rel_path
        cleaned = code_only(source.read_text())
        forbidden = re.findall(r'(?<![A-Za-z_])(?:sorry|admit|axiom|native_decide|unsafe)(?![A-Za-z_])', cleaned)
        if forbidden:
            print(f'FORBIDDEN tokens in {rel_path}: {forbidden}', file=sys.stderr)
            return 1
        stem = module.rsplit('/', 1)[-1]
        olean = source.with_suffix('.olean')
        proc = subprocess.run([str(LEAN), '-o', str(olean), str(source)], cwd=ROOT,
                              env=env, capture_output=True, text=True)
        log = logdir / (stem + '.build.log')
        log.write_text(proc.stdout + proc.stderr)
        combined.append(f'== {module}\n{proc.stdout}{proc.stderr}')
        print(f'{module}: exit {proc.returncode}')
        if proc.returncode:
            print(log.read_text())
            return proc.returncode
    count = 0
    for module in MODULES:
        source = ROOT / 'lean' / (module + '.lean')
        audit_process = subprocess.run([str(LEAN), str(source)], cwd=ROOT, env=env,
                                       capture_output=True, text=True)
        stem = module.rsplit('/', 1)[-1]
        (logdir / (stem + '.audit.log')).write_text(audit_process.stdout + audit_process.stderr)
        combined.append(f'== {module} axiom audit\n{audit_process.stdout}{audit_process.stderr}')
        if audit_process.returncode:
            print(audit_process.stdout + audit_process.stderr)
            return 1
        for line in (audit_process.stdout + audit_process.stderr).splitlines():
            if 'depends on axioms: [' in line:
                axioms = set(line.split('depends on axioms: [', 1)[1].split(']', 1)[0].split(','))
                axioms = {a.strip() for a in axioms if a.strip()}
                if not axioms <= STANDARD:
                    print(f'NONSTANDARD AXIOMS: {line}', file=sys.stderr)
                    return 1
                if 'sorryAx' in line:
                    return 1
                count += 1
    (logdir / 'integrate_build.log').write_text('\n'.join(combined))
    print(f'PASS {len(MODULES)} modules; {count} audited theorem reports use only {sorted(STANDARD)}')
    print(f'Log: {logdir / "integrate_build.log"}')
    return 0


if __name__ == '__main__':
    raise SystemExit(main())
