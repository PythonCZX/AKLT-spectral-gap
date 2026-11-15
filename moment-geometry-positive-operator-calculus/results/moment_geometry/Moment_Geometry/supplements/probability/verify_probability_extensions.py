"""Exact finite combinatorial checks for the coherent spectral-law extension.

No floating-point simulation is used.  The output corroborates finite
identities; the asymptotic and analytic proofs are in attractive_ldp.tex.
Run from any directory.  Only Python's standard library is required.
"""
from collections import Counter
from fractions import Fraction
from math import comb
from pathlib import Path
import json


def partitions(n):
    word = [0] * n
    def rec(j, largest):
        if j == n:
            yield tuple(word)
            return
        for x in range(largest + 2):
            word[j] = x
            yield from rec(j + 1, max(largest, x))
    yield from rec(1, 0)


def det_bareiss(matrix):
    a = [list(row) for row in matrix]
    n = len(a)
    if n == 0:
        return 1
    denominator = 1
    sign = 1
    for j in range(n - 1):
        if a[j][j] == 0:
            i = next(i for i in range(j + 1, n) if a[i][j])
            a[j], a[i] = a[i], a[j]
            sign *= -1
        pivot = a[j][j]
        for i in range(j + 1, n):
            for h in range(j + 1, n):
                numerator = a[i][h] * pivot - a[i][j] * a[j][h]
                assert numerator % denominator == 0
                a[i][h] = numerator // denominator
        denominator = pivot
        for i in range(j + 1, n):
            a[i][j] = 0
    return sign * a[-1][-1]


def tree_count(word):
    r = max(word) + 1
    lap = [[0] * r for _ in range(r)]
    for a, b in zip(word, word[1:] + word[:1]):
        if a != b:
            lap[a][a] += 1
            lap[a][b] -= 1
    cofactors = [det_bareiss([[lap[i][j] for j in range(r) if j != o]
                             for i in range(r) if i != o]) for o in range(r)]
    assert len(set(cofactors)) == 1 and cofactors[0] >= 1
    return cofactors[0]


def noncrossing(word):
    n = len(word)
    return not any(word[a] == word[c] and word[b] == word[d]
                   and word[a] != word[b]
                   for a in range(n) for b in range(a + 1, n)
                   for c in range(b + 1, n) for d in range(c + 1, n))


def main():
    tables = []
    checked = 0
    pair_checked = 0
    for p in range(1, 9):
        counts = Counter()
        nc_counts = Counter()
        for word in partitions(p):
            r = max(word) + 1
            tau = tree_count(word)
            nc = noncrossing(word)
            assert (tau == 1) == nc
            counts[r, tau] += 1
            if nc:
                nc_counts[r] += 1
            sizes = Counter(word)
            if all(x == 2 for x in sizes.values()):
                assert tau <= 2 ** (r - 1)
                pair_checked += 1
            checked += 1
        for r in range(1, p + 1):
            assert nc_counts[r] == comb(p, r) * comb(p, r - 1) // p
        moments = []
        for rho in (Fraction(1, 2), Fraction(1), Fraction(2)):
            for q in (1, 2, 4, 8):
                moment = sum((count * rho ** (r - 1) / tau ** q
                              for (r, tau), count in counts.items()), Fraction())
                mp = sum((count * rho ** (r - 1)
                          for r, count in nc_counts.items()), Fraction())
                weighted_bell = sum((count * rho ** (r - 1)
                                     for (r, tau), count in counts.items()), Fraction())
                assert mp <= moment <= weighted_bell
                assert moment - mp <= (weighted_bell - mp) / 2 ** q
                expected = [None, Fraction(1), 1 + rho,
                            1 + 3 * rho + rho ** 2,
                            1 + (6 + Fraction(1, 2 ** q)) * rho
                            + 6 * rho ** 2 + rho ** 3]
                if p <= 4:
                    assert moment == expected[p]
                moments.append({'q': q, 'rho': str(rho),
                                'moment': str(moment), 'mp_moment': str(mp)})
        tables.append({'p': p,
                       'counts': [{'blocks': r, 'trees': tau, 'count': count}
                                  for (r, tau), count in sorted(counts.items())],
                       'moments': moments})
    out = Path(__file__).with_name('probability_extensions_verified.json')
    result = {'status': 'exact finite combinatorial verification',
              'partitions_checked': checked,
              'pair_partitions_checked': pair_checked,
              'checks': ['all rooted tree cofactors equal and positive',
                         'tree count one iff independently tested noncrossing',
                         'pair partition tree bound',
                         'Narayana noncrossing counts',
                         'arbitrary-aspect first-four-moment formula',
                         'Touchard upper bound and dimension-decay inequality'],
              'scope': 'Analytic limits and all-order inequalities use the written proofs.',
              'tables': tables}
    out.write_text(json.dumps(result, indent=2) + '\n')
    print(json.dumps({'output': str(out), 'partitions_checked': checked,
                      'pair_partitions_checked': pair_checked}, indent=2))


if __name__ == '__main__':
    main()
