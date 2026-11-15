"""Exact cycle-quotient tree counts and a diagnostic coherent-Gram experiment.

The finite combinatorics and finite-level expectation identities are exact.
The Monte Carlo section is a diagnostic, not a proof of the spectral theorem.
Run from any directory; writes a sibling JSON result.
"""
from collections import Counter
from fractions import Fraction
from pathlib import Path
import argparse
import json
import math
import numpy as np


def partitions(n):
    if n == 0:
        yield ()
        return
    a = [0] * n

    def rec(j, largest):
        if j == n:
            yield tuple(a)
            return
        for x in range(largest + 2):
            a[j] = x
            yield from rec(j + 1, max(largest, x))

    yield from rec(1, 0)


def determinant_bareiss(a):
    a = [list(row) for row in a]
    n = len(a)
    if n == 0:
        return 1
    sign, previous = 1, 1
    for j in range(n - 1):
        if a[j][j] == 0:
            r = next(r for r in range(j + 1, n) if a[r][j])
            a[j], a[r] = a[r], a[j]
            sign = -sign
        pivot = a[j][j]
        for r in range(j + 1, n):
            for c in range(j + 1, n):
                numerator = a[r][c] * pivot - a[r][j] * a[j][c]
                assert numerator % previous == 0
                a[r][c] = numerator // previous
        previous = pivot
        for r in range(j + 1, n):
            a[r][j] = 0
    return sign * a[-1][-1]


def tree_number(word):
    r = max(word) + 1
    lap = [[0] * r for _ in range(r)]
    for a, b in zip(word, word[1:] + word[:1]):
        if a != b:
            lap[a][a] += 1
            lap[a][b] -= 1
    # Eulerian connected cycle quotients have equal rooted cofactors.
    cofactors = []
    for root in range(r):
        cofactor = [[lap[i][j] for j in range(r) if j != root]
                    for i in range(r) if i != root]
        cofactors.append(determinant_bareiss(cofactor))
    assert len(set(cofactors)) == 1 and cofactors[0] >= 1
    return cofactors[0]


def finite_expectations(d):
    n = (d + 1) * (d + 2) // 2
    m = (2 * d + 1) * (2 * d + 2) // 2
    return [Fraction(1), Fraction(2 * n - 1, n),
            Fraction(5 * n * n - 6 * n + 2, n * n),
            (Fraction(n + 6 * (n - 1), n)
             + Fraction(n - 1, m)
             + Fraction(6 * (n - 1) * (n - 2), n * n)
             + Fraction((n - 1) * (n - 2) * (n - 3), n ** 3))]


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    mode = parser.add_mutually_exclusive_group()
    mode.add_argument("--exact-only", action="store_true",
                      help="Run finite exact enumeration only (the default).")
    mode.add_argument("--monte-carlo", action="store_true",
                      help="Explicitly enable the optional floating experiment.")
    parser.add_argument("--levels", type=int, nargs="+", default=[4, 8, 12])
    parser.add_argument("--repetitions", type=int, default=24)
    parser.add_argument("--seed", type=int, default=20261115)
    parser.add_argument("--output", type=Path,
                        default=Path(__file__).with_name("coherent_gram_moments_verified.json"))
    args = parser.parse_args()
    if args.repetitions < 2 or any(k < 1 for k in args.levels):
        parser.error("levels must be positive and repetitions at least two")
    tables = []
    for p in range(1, 10):
        counts = Counter()
        by_vertices = Counter()
        for word in partitions(p):
            t = tree_number(word)
            counts[t] += 1
            by_vertices[(max(word) + 1, t)] += 1
        moment = sum((Fraction(c, t * t) for t, c in counts.items()), Fraction(0))
        tables.append({"p": p, "partitions": sum(counts.values()),
                       "tree_histogram": dict(sorted(counts.items())),
                       "by_vertices_and_trees": [
                           {"vertices": r, "trees": t, "count": c}
                           for (r, t), c in sorted(by_vertices.items())],
                       "qutrit_moment_exact": str(moment),
                       "qutrit_moment_float": float(moment)})
    assert [x["qutrit_moment_exact"] for x in tables[:4]] == ["1", "2", "5", "57/4"]
    assert tables[3]["tree_histogram"] == {1: 14, 2: 1}
    assert [x["partitions"] for x in tables] == [1, 2, 5, 15, 52, 203, 877, 4140, 21147]

    # Independently sum the exact p<=4 partition contractions and compare
    # with the supplied finite-level closed forms. The exceptional abab
    # cycle has integral 1/dim Sym^(2d); all other terms at these orders
    # reduce by reproducing-kernel contraction.
    finite_checks = []
    for degree in (1, 2, 3, 6, 12, 24, 36):
        n = (degree+1)*(degree+2)//2
        n2 = (2*degree+1)*(2*degree+2)//2
        enumerated = []
        for p in range(1, 5):
            total = Fraction(0)
            for word in partitions(p):
                r = max(word)+1
                multiplicity = math.prod(n-j for j in range(r))
                integral = (Fraction(1, n2) if tree_number(word) == 2
                            else Fraction(1, n**(r-1)))
                total += Fraction(multiplicity, n)*integral
            enumerated.append(total)
        assert enumerated == finite_expectations(degree)
        finite_checks.append({"degree":degree, "N":n,
                              "moments_exact":[str(x) for x in enumerated],
                              "partition_contractions_match_closed_form":True})
    rng = np.random.default_rng(args.seed)
    diagnostics = []
    for k in (args.levels if args.monte_carlo else []):
        d = 3 * k
        n = (d + 1) * (d + 2) // 2
        moments = []
        energy = []
        repetitions = args.repetitions
        for _ in range(repetitions):
            z = rng.normal(size=(n, 3)) + 1j * rng.normal(size=(n, 3))
            z /= np.linalg.norm(z, axis=1)[:, None]
            gram = (z @ z.conj().T) ** d
            eigenvalues = np.linalg.eigvalsh(gram)
            moments.append([float(np.mean(eigenvalues ** p)) for p in range(1, 5)])
            if eigenvalues[0] > 0:
                energy.append(float(-np.log(eigenvalues).mean() / k - math.log(n) / k))
        moments = np.asarray(moments)
        diagnostics.append({"k": k, "N": n, "repetitions": repetitions,
                            "exact_finite_moment_expectations": [str(x) for x in finite_expectations(d)],
                            "exact_finite_moment_expectations_float": [float(x) for x in finite_expectations(d)],
                            "monte_carlo_mean": moments.mean(axis=0).tolist(),
                            "monte_carlo_standard_error": (moments.std(axis=0, ddof=1) / np.sqrt(repetitions)).tolist(),
                            "diagnostic_energy_mean": float(np.mean(energy)) if energy else None,
                            "energy_samples_with_positive_numerical_spectrum": len(energy)})
    result = {"status": "Exact graph enumeration and finite expectation identities; Monte Carlo is diagnostic only.",
              "moments": tables, "finite_level_identity_checks":finite_checks,
              "diagnostics": diagnostics,
              "monte_carlo_enabled":args.monte_carlo,"seed":args.seed,
              "warning": "Positive spectral moments do not establish logarithmic uniform integrability or attractive pressure/LDP."}
    out = args.output
    out.write_text(json.dumps(result, indent=2) + "\n")
    print(json.dumps({"output": str(out), "moments": [x["qutrit_moment_exact"] for x in tables],
                      "partitions_checked": sum(x["partitions"] for x in tables)}, indent=2))


if __name__ == "__main__":
    main()
