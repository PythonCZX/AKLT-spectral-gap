#!/usr/bin/env python3
"""Exact small-channel and graph certificates for the primitive-wire gap theorem.

Floating point is used only to suggest a positive graph vector. Every accepted
channel sandwich and every accepted spectral-radius inequality is checked in
exact rational arithmetic. No many-body Hamiltonian is diagonalized.
"""
from __future__ import annotations

import argparse
from fractions import Fraction as F
import json
from pathlib import Path
import sys

import numpy as np
import sympy as sp


class CertificateError(ValueError):
    pass


def rational(value):
    if isinstance(value, bool) or not isinstance(value, (int, str, F)):
        raise CertificateError("Exact numbers must be integers or rational strings, not JSON floats.")
    try:
        return F(value)
    except (ValueError, ZeroDivisionError) as exc:
        raise CertificateError(f"Invalid exact rational: {value!r}") from exc


def exact_scalar(value):
    if isinstance(value, dict):
        if not value or set(value) - {"re", "im"}:
            raise CertificateError("A complex scalar has only 're' and 'im' rational fields.")
        re, im = rational(value.get("re", 0)), rational(value.get("im", 0))
        return sp.Rational(re.numerator, re.denominator) + sp.I * sp.Rational(im.numerator, im.denominator)
    q = rational(value)
    return sp.Rational(q.numerator, q.denominator)


def exact_matrix(value, name):
    if not isinstance(value, list) or not value or not all(isinstance(row, list) for row in value):
        raise CertificateError(f"{name} must be a nonempty rectangular matrix.")
    width = len(value[0])
    if not width or any(len(row) != width for row in value):
        raise CertificateError(f"{name} must be rectangular.")
    return sp.Matrix([[exact_scalar(x) for x in row] for row in value])


def exact_psd(matrix, *, positive_definite=False):
    """Hermitian rational congruence elimination, safe at zero pivots.

    A zero diagonal with a nonzero entry in its row gives a negative 2x2
    principal minor. Otherwise a positive diagonal pivot reduces positivity
    to the Schur complement. All comparisons are exact, including complex
    off-diagonal entries. The returned transcript is independently replayable.
    """
    matrix = matrix.applyfunc(sp.expand)
    if matrix.rows != matrix.cols:
        return {"valid": False, "reason": "not_square"}
    if matrix != matrix.conjugate().T:
        return {"valid": False, "reason": "not_Hermitian"}
    work = matrix.copy()
    indices = list(range(matrix.rows))
    pivots = []
    zero_indices = []
    while work.rows:
        positive = []
        for i in range(work.rows):
            diagonal = sp.expand(work[i, i])
            if diagonal.is_Rational is not True:
                raise CertificateError("Internal error: a Hermitian exact Schur diagonal is not rational.")
            if diagonal < 0:
                return {"valid": False, "reason": "negative_Schur_diagonal",
                        "index": indices[i], "value": str(diagonal), "pivots": pivots}
            if diagonal == 0:
                for j in range(work.cols):
                    if work[i, j] != 0:
                        minor = sp.expand(-work[i, j] * sp.conjugate(work[i, j]))
                        return {"valid": False, "reason": "zero_diagonal_nonzero_row",
                                "indices": [indices[i], indices[j]],
                                "negative_principal_minor": str(minor), "pivots": pivots}
            else:
                positive.append(i)
        if not positive:
            zero_indices.extend(indices)
            break
        pivot_index = positive[0]
        rest = [j for j in range(work.rows) if j != pivot_index]
        pivot = work[pivot_index, pivot_index]
        pivots.append({"index": indices[pivot_index], "value": str(pivot)})
        work = sp.Matrix(len(rest), len(rest), lambda i, j: sp.expand(
            work[rest[i], rest[j]] - work[rest[i], pivot_index] * work[pivot_index, rest[j]] / pivot))
        indices = [indices[j] for j in rest]
    rank = len(pivots)
    valid = not positive_definite or rank == matrix.rows
    return {"valid": valid, "kind": "positive_definite" if positive_definite else "positive_semidefinite",
            "rank": rank, "dimension": matrix.rows, "pivots": pivots,
            "zero_indices": zero_indices,
            **({"reason": "singular_reference"} if not valid else {})}


def require_psd(matrix, label, *, positive_definite=False):
    proof = exact_psd(matrix, positive_definite=positive_definite)
    if not proof["valid"]:
        raise CertificateError(f"{label} failed exact positivity: {json.dumps(proof)}")
    return proof


def aklt_channel(length):
    if isinstance(length, bool) or not isinstance(length, int) or length < 2:
        raise CertificateError("An AKLT half-wire length must be an integer at least 2 for this strict CP certificate.")
    beta = F((-1) ** length, 3 ** length)
    lower, upper = sorted((1 + 3 * beta, 1 - beta))
    delta = (upper - lower) / (upper + lower)
    assert delta == F(2, 3 ** length + (-1) ** length)
    return {"kind": "aklt", "half_length": length, "input_dimension": 2,
            "output_dimension": 2, "beta": str(beta),
            "sandwich_lower": str(lower), "sandwich_upper": str(upper),
            "center_scale": str((lower + upper) / 2), "delta": str(delta),
            "proof": "Exact Choi eigenvalues 1+3*beta and 1-beta relative to depolarizing preparation."}


def choi_channel(data):
    for key in ("J", "R", "L", "lower", "upper"):
        if key not in data:
            raise CertificateError(f"Missing Choi sandwich field: {key}")
    J, R, L = (exact_matrix(data[key], key) for key in ("J", "R", "L"))
    pR = require_psd(R, "R", positive_definite=True)
    pL = require_psd(L, "L", positive_definite=True)
    reference = sp.kronecker_product(R, L.T)
    if J.shape != reference.shape:
        raise CertificateError("J must have dimension (dim R * dim L) squared, in output-first Choi order.")
    lower, upper = rational(data["lower"]), rational(data["upper"])
    if not 0 < lower <= upper:
        raise CertificateError("Choi sandwich constants must satisfy 0 < lower <= upper.")
    lo = sp.Rational(lower.numerator, lower.denominator)
    hi = sp.Rational(upper.numerator, upper.denominator)
    p_lower = require_psd(J - lo * reference, "J-lower*(R tensor L^T)")
    p_upper = require_psd(hi * reference - J, "upper*(R tensor L^T)-J")
    return {"kind": "choi", "input_dimension": L.rows, "output_dimension": R.rows,
            "sandwich_lower": str(lower), "sandwich_upper": str(upper),
            "center_scale": str((lower + upper) / 2),
            "delta": str((upper - lower) / (upper + lower)),
            "exact_positivity_proofs": {"R": pR, "L": pL,
                                       "lower_residual": p_lower, "upper_residual": p_upper}}


def load_channel(data, directory):
    if not isinstance(data, dict):
        raise CertificateError("Each channel must be a JSON object.")
    if data.get("kind") == "aklt":
        return aklt_channel(data.get("length"))
    if data.get("kind") == "choi":
        if "file" in data:
            return choi_channel(json.loads((directory / data["file"]).read_text()))
        return choi_channel(data)
    raise CertificateError("Channel kind must be 'aklt' or 'choi'.")


def pair_bound(delta_i, delta_j):
    if not 0 <= delta_i < 1 or not 0 <= delta_j < 1:
        raise CertificateError("The strict two-port certificate requires 0 <= delta < 1.")
    return 2 * delta_i * delta_j * (1 + delta_i * delta_j) / ((1 - delta_i) ** 2 * (1 - delta_j) ** 2)


def exact_vector_bound(C, vector):
    if len(vector) != len(C) or any(v <= 0 for v in vector):
        raise CertificateError("A spectral certificate requires one strictly positive rational weight per edge.")
    ratios = [sum((c * v for c, v in zip(row, vector)), F(0)) / vector[i]
              for i, row in enumerate(C)]
    return max(ratios, default=F(0)), ratios


def graph_components(C):
    unseen = set(range(len(C)))
    result = []
    while unseen:
        start = min(unseen)
        unseen.remove(start)
        stack, component = [start], [start]
        while stack:
            i = stack.pop()
            neighbors = [j for j in sorted(unseen) if C[i][j] > 0]
            for j in neighbors:
                unseen.remove(j)
                stack.append(j)
                component.append(j)
        result.append(component)
    return result


def spectral_certificate(C, supplied=None):
    n = len(C)
    candidates = [("all_ones", [F(1)] * n)]
    numerical_radius = None
    if supplied is not None:
        candidates = [("supplied_positive_vector", supplied)]
    else:
        # Floating point only proposes weights. It never decides acceptance.
        proposal = np.ones(n)
        numerical_radius = 0.0
        for component in graph_components(C):
            block = np.array([[float(C[i][j]) for j in component] for i in component])
            values, vectors = np.linalg.eigh(block)
            numerical_radius = max(numerical_radius, float(values[-1]))
            vector = np.abs(vectors[:, -1])
            vector /= max(float(vector.max()), 1e-300)
            for i, value in zip(component, vector):
                proposal[i] = max(float(value), 1e-12)
        for digits in (3, 6, 9, 12):
            denominator = 10 ** digits
            vector = [F(max(1, round(float(v) * denominator)), denominator) for v in proposal]
            candidates.append((f"rationalized_Perron_vector_{digits}_digits", vector))
    checked = []
    for method, vector in candidates:
        bound, ratios = exact_vector_bound(C, vector)
        checked.append((bound, method, vector, ratios))
    bound, method, vector, ratios = min(checked, key=lambda item: item[0])
    gap = max(F(0), 1 - bound)
    return {"certified": bound < 1, "method": method,
            "spectral_radius_upper_bound": str(bound),
            "positive_vector": list(map(str, vector)),
            "row_ratios": list(map(str, ratios)),
            "coarse_gap_lower_bound": str(gap),
            "coarse_gap_lower_bound_decimal": float(gap),
            "numerical_radius_diagnostic_only": numerical_radius,
            "acceptance_rule": "All weights positive and C*w <= lambda*w with exact rational lambda < 1."}


def graph_certificate(data, directory):
    raw_channels = data.get("channels", {})
    if not isinstance(raw_channels, dict) or not raw_channels:
        raise CertificateError("A graph requires a nonempty 'channels' object.")
    channels = {name: load_channel(spec, directory) for name, spec in raw_channels.items()}
    edges = data.get("edges")
    if not isinstance(edges, list) or not edges:
        raise CertificateError("A graph requires a nonempty edge list.")
    incidence = {}
    edge_ids, endpoints, port_channels = [], [], []
    seen_pairs = set()
    for edge in edges:
        if not isinstance(edge, dict) or set(edge) - {"id", "u", "v", "ports"}:
            raise CertificateError("Each edge has fields id, u, v, and ports.")
        identifier, u, v = edge.get("id"), edge.get("u"), edge.get("v")
        if not all(isinstance(x, str) and x for x in (identifier, u, v)):
            raise CertificateError("Edge and vertex identifiers must be nonempty strings.")
        if identifier in edge_ids or u == v or frozenset((u, v)) in seen_pairs:
            raise CertificateError("The graph must be simple, without loops or duplicate edge IDs.")
        seen_pairs.add(frozenset((u, v)))
        ports = edge.get("ports", {})
        if not isinstance(ports, dict) or set(ports) != {u, v} or any(name not in channels for name in ports.values()):
            raise CertificateError("Every edge needs one declared channel ID at each of its two endpoint ports.")
        if channels[ports[u]]["output_dimension"] != channels[ports[v]]["output_dimension"]:
            raise CertificateError(f"Edge {identifier} has unequal endpoint output dimensions.")
        i = len(edge_ids)
        edge_ids.append(identifier)
        endpoints.append((u, v))
        port_channels.append(ports)
        for vertex in (u, v):
            incidence.setdefault(vertex, []).append(i)
    if "vertices" in data and (not isinstance(data["vertices"], list) or set(data["vertices"]) != set(incidence)):
        raise CertificateError("Optional vertices must be exactly the incident vertices; isolated blocks need a separate local-image term.")
    n = len(edges)
    C = [[F(0) for j in range(n)] for i in range(n)]
    pair_records = []
    for vertex, incident in incidence.items():
        for offset, i in enumerate(incident):
            for j in incident[offset + 1:]:
                di = rational(channels[port_channels[i][vertex]]["delta"])
                dj = rational(channels[port_channels[j][vertex]]["delta"])
                raw = pair_bound(di, dj)
                C[i][j] = C[j][i] = min(F(1), raw)
                pair_records.append({"edges": [edge_ids[i], edge_ids[j]], "shared_vertex": vertex,
                                     "raw_two_port_bound": str(raw), "angle_bound": str(C[i][j])})
    supplied = data.get("certificate_weights")
    if supplied is not None:
        if not isinstance(supplied, dict) or set(supplied) != set(edge_ids):
            raise CertificateError("certificate_weights must provide exactly one rational weight for each edge ID.")
        supplied = [rational(supplied[name]) for name in edge_ids]
    certificate = spectral_certificate(C, supplied)
    degree = max(map(len, incidence.values()))
    gap = rational(certificate["coarse_gap_lower_bound"])
    return {"schema": "primitive-wire-gap-certificate-v1", "channels": channels,
            "edge_order": edge_ids, "vertex_degrees": {v: len(es) for v, es in incidence.items()},
            "maximum_degree": degree, "pair_bounds": pair_records,
            "influence_matrix": [[str(x) for x in row] for row in C],
            "spectral_certificate": certificate,
            "microscopic_gap_multiplier_for_g_seed": str(gap / degree),
            "scope": SCOPE,
            "failure_interpretation": "Failure to certify is not evidence that the model is gapless."}


SCOPE = {
    "coarse": "The bound is for the normalized two-block projector parent of an arbitrary nonzero positive core tensor at every vertex, with the certified primitive wire channels and full-Schmidt-rank bonds.",
    "microscopic": "For the actual microscopic parent, additionally prove equality of each two-block kernel with the tensor image and a finite seed gap g_seed. If each microscopic term occurs in at most Delta patches, gap >= g_seed * coarse_gap / Delta. Decorated AKLT has the required kernel identity by singlet-bracket divisibility.",
    "boundary": "Use full core-plus-half-wire blocks, including dangling half-wires at the boundary. No undecorated AKLT or pressure/LDP conclusion is asserted."
}


def uniform_aklt(degree, decoration):
    if isinstance(degree, bool) or not isinstance(degree, int) or degree < 1:
        raise CertificateError("degree must be a positive integer.")
    if isinstance(decoration, bool) or not isinstance(decoration, int) or decoration < 4 or decoration % 2:
        raise CertificateError("Uniform decoration must be an even integer >=4; unequal half-lengths are supported in graph mode.")
    channel = aklt_channel(decoration // 2)
    delta = rational(channel["delta"])
    pair = pair_bound(delta, delta)
    row = 2 * (degree - 1) * pair
    gap = max(F(0), 1 - row)
    return {"schema": "primitive-wire-gap-certificate-v1", "mode": "uniform_aklt",
            "maximum_degree": degree, "decoration_per_original_edge": decoration,
            "half_channel": channel, "pair_angle_bound": str(pair),
            "row_sum_upper_bound": str(row), "certified": row < 1,
            "coarse_gap_lower_bound": str(gap), "coarse_gap_lower_bound_decimal": float(gap),
            "microscopic_gap_multiplier_for_g_seed": str(gap / degree), "scope": SCOPE}


def plan_aklt(degree, target, maximum_half_length):
    if degree < 1 or maximum_half_length < 2:
        raise CertificateError("degree must be positive and max-half-length must be at least 2.")
    target = rational(target)
    if not 0 < target <= 1:
        raise CertificateError("The target coarse gap must lie in (0,1].")
    if target == 1 and degree > 1:
        return {"certified": False, "reason": "No finite uniform wire length attains the exact bound 1 when degree > 1.",
                "target_coarse_gap": str(target)}
    checked = []
    for length in range(2, maximum_half_length + 1):
        result = uniform_aklt(degree, 2 * length)
        checked.append({"decoration": 2 * length, "gap": result["coarse_gap_lower_bound"]})
        if rational(result["coarse_gap_lower_bound"]) >= target:
            result.update({"mode": "minimum_uniform_plan", "target_coarse_gap": str(target),
                           "minimality": "Every smaller allowed half-length >=2 was checked exactly.",
                           "checked_lengths": checked})
            return result
    return {"certified": False, "reason": "No plan met the target within max-half-length.",
            "target_coarse_gap": str(target), "checked_lengths": checked}


def main(argv=None):
    parser = argparse.ArgumentParser(description=__doc__)
    sub = parser.add_subparsers(dest="command", required=True)
    p = sub.add_parser("aklt", help="Exact bound for a degree and an even decoration count.")
    p.add_argument("--degree", type=int, required=True)
    p.add_argument("--decoration", type=int, required=True)
    p = sub.add_parser("plan", help="Find the smallest allowed uniform decoration meeting a coarse-gap target.")
    p.add_argument("--degree", type=int, required=True)
    p.add_argument("--target", default="1/10")
    p.add_argument("--max-half-length", type=int, default=128)
    for command in ("channel", "graph"):
        p = sub.add_parser(command, help="Validate an exact Choi sandwich." if command == "channel" else "Compile exact port channels and a graph into a gap certificate.")
        p.add_argument("input", type=Path)
    for p in sub.choices.values():
        p.add_argument("--output", type=Path)
    args = parser.parse_args(argv)
    try:
        if args.command == "aklt":
            result = uniform_aklt(args.degree, args.decoration)
        elif args.command == "plan":
            result = plan_aklt(args.degree, args.target, args.max_half_length)
        else:
            data = json.loads(args.input.read_text())
            result = choi_channel(data) if args.command == "channel" else graph_certificate(data, args.input.parent)
        rendered = json.dumps(result, indent=2) + "\n"
        if args.output:
            args.output.write_text(rendered)
        print(rendered, end="")
        return 0
    except (CertificateError, OSError, json.JSONDecodeError) as exc:
        print(json.dumps({"certified": False, "input_error": str(exc)}, indent=2), file=sys.stderr)
        return 2


if __name__ == "__main__":
    raise SystemExit(main())
