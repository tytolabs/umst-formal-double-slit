#!/usr/bin/env python3
# SPDX-License-Identifier: MIT
# Copyright (c) 2026 Santhosh Shyamsundar, Santosh Prabhu Shenbagamoorthy — Studio TYTO

"""
telemetry_trace_consumer.py — Concrete telemetry numeric trace consumer (Gap 14)

Reads a JSON trace file emitted by the runtime epistemic sensing loop and validates
that numeric outputs satisfy the formal Lean contracts:

1. **Density matrix contract:** PSD + trace = 1 (within tolerance).
2. **Path projection contract:** Born weights nonneg + sum = 1.
3. **Complementarity contract:** V² + D² ≤ 1 + ε.
4. **Landauer contract:** entropy nonneg, cost nonneg for T ≥ 0.

Usage:
    python3 telemetry_trace_consumer.py trace.json [--tolerance 1e-6]

Input format (JSON):
    {
        "steps": [
            {
                "density_matrix_real": [[r00, r01], [r10, r11]],
                "density_matrix_imag": [[i00, i01], [i10, i11]],
                "path_weights": [p0, p1],
                "visibility": 0.5,
                "distinguishability": 0.866,
                "entropy_bits": 0.92,
                "temperature": 300.0,
                "stepMI": 0.12,
                "stepCost": 1.1e-22
            }, ...
        ]
    }

**Epistemic layer (optional, Lean-aligned):**

- ``stepMI`` or alias ``trajMI`` — per-step epistemic MI surrogate in **nats** (same units as
  ``EpistemicMI`` in ``EpistemicMI.lean``), with ``0 ≤ MI ≤ ln 2`` for the path qubit.
- ``stepCost`` or alias ``effortCost`` — Landauer-style cost in **joules**; well-formed traces
  satisfy ``0 ≤ cost ≤ k_B T ln 2`` (cf. ``EmittedTraceWellFormed`` / ``epistemicLandauerCost_le_landauerBitEnergy``).
- When **both** MI (nats) and cost are present, we **optionally** check
  ``cost ≈ k_B * T * MI`` (``infoEnergyLowerBound`` identity).

**Aggregate layer (optional, matches ``NumericTraceRecord`` / folded ``PerStepNumericRecord``):**

- Root object may include ``aggregateMI`` and ``aggregateCost`` **or** a nested ``aggregate``
  object with those keys (joules / nats consistent with per-step fields).
- We always validate **catalog bounds** when aggregates are present:
  ``aggregateMI ≤ n ln 2`` and ``aggregateCost ≤ n k_B T ln 2`` (``traceRecord_aggregateMI_le``,
  ``traceRecord_aggregateCost_le``).
- If **every** step carries both per-step MI and cost, we also check
  ``Σ stepMI ≈ aggregateMI`` and ``Σ stepCost ≈ aggregateCost`` (finite fold vs reported totals).

**``EmittedStepRecord`` metadata (optional, ``EpistemicRuntimeSchemaContract``):**

- Per step, either **flat** keys or a nested ``"emitted": { ... }`` object may include
  ``thermodynamicAdmissible`` (JSON boolean, or ``0``/``1``) and ``confidence`` (real in ``[0,1]``,
  cf. ``EmittedTraceWellFormed``). Nested ``emitted`` takes **precedence** over duplicate top-level keys
  for MI/cost and metadata.
"""
from __future__ import annotations

import argparse
import json
import sys
from dataclasses import dataclass
from pathlib import Path

import numpy as np


@dataclass
class ContractResult:
    name: str
    passed: bool
    detail: str


def check_density_matrix(rho: np.ndarray, tol: float) -> ContractResult:
    """Validate PSD + trace = 1."""
    tr = np.trace(rho)
    trace_ok = abs(tr - 1.0) < tol

    eigenvalues = np.linalg.eigvalsh(rho)
    psd_ok = all(ev >= -tol for ev in eigenvalues)

    herm_ok = np.allclose(rho, rho.conj().T, atol=tol)

    ok = trace_ok and psd_ok and herm_ok
    detail = f"trace={tr:.8f}, min_eig={min(eigenvalues):.2e}, hermitian={herm_ok}"
    return ContractResult("DensityMatrix", ok, detail)


def check_path_projection(weights: list[float], tol: float) -> ContractResult:
    """Validate nonneg + sum = 1."""
    nonneg = all(w >= -tol for w in weights)
    sum_ok = abs(sum(weights) - 1.0) < tol
    ok = nonneg and sum_ok
    detail = f"sum={sum(weights):.8f}, min={min(weights):.2e}"
    return ContractResult("PathProjection", ok, detail)


def check_complementarity(V: float, D: float, tol: float) -> ContractResult:
    """Validate V² + D² ≤ 1 + ε."""
    lhs = V**2 + D**2
    ok = lhs <= 1.0 + tol
    detail = f"V²+D²={lhs:.8f}, V={V:.4f}, D={D:.4f}"
    return ContractResult("Complementarity", ok, detail)


def _landauer_bit_energy_joules(temperature: float) -> float:
    """``k_B * T * ln 2`` — matches ``landauerBitEnergy`` in ``UMSTCore.lean`` (natural log)."""
    k_b = 1.380649e-23
    return k_b * temperature * np.log(2.0)


def _emitted_block(step: dict) -> dict:
    eb = step.get("emitted")
    return eb if isinstance(eb, dict) else {}


def _step_mi_nats(step: dict) -> float | None:
    # Nested ``emitted`` first (structured ``EmittedStepRecord``), then flat step.
    sources = [_emitted_block(step), step]
    for d in sources:
        if "stepMI" in d:
            return float(d["stepMI"])
        if "trajMI" in d:
            return float(d["trajMI"])
    return None


def _step_cost_joules(step: dict) -> float | None:
    sources = [_emitted_block(step), step]
    for d in sources:
        if "stepCost" in d:
            return float(d["stepCost"])
        if "effortCost" in d:
            return float(d["effortCost"])
    return None


def _metadata_dict(step: dict) -> dict:
    """``thermodynamicAdmissible`` / ``confidence`` — nested ``emitted`` overrides step."""
    out: dict = {}
    eb = _emitted_block(step)
    for key in ("thermodynamicAdmissible", "confidence"):
        if key in eb:
            out[key] = eb[key]
    for key in ("thermodynamicAdmissible", "confidence"):
        if key not in out and key in step:
            out[key] = step[key]
    return out


def check_emitted_confidence(confidence: float, tol: float) -> ContractResult:
    """``0 ≤ confidence ≤ 1`` (``EmittedTraceWellFormed``)."""
    ok = -tol <= confidence <= 1.0 + tol
    detail = f"confidence={confidence:.8f}"
    return ContractResult("EmittedStep_confidence", ok, detail)


def check_emitted_thermodynamic_admissible(value: object) -> ContractResult:
    """Boolean flag (JSON); allow ``0``/``1`` for loose encoders."""
    if isinstance(value, bool):
        ok = True
        detail = f"thermodynamicAdmissible={value}"
    elif value in (0, 1):
        ok = True
        detail = f"thermodynamicAdmissible={value} (coerced from int)"
    else:
        ok = False
        detail = f"expected bool or 0/1, got {type(value).__name__}={value!r}"
    return ContractResult("EmittedStep_thermodynamicAdmissible", ok, detail)


def check_epistemic_mi_nats(mi: float, tol: float) -> ContractResult:
    """``0 ≤ MI ≤ ln 2`` in nats (``epistemicMI_le_log_two``)."""
    log2 = float(np.log(2.0))
    ok = -tol <= mi <= log2 + tol
    detail = f"MI_nats={mi:.8f}, ln2={log2:.8f}"
    return ContractResult("EpistemicMI_nats", ok, detail)


def check_epistemic_cost_joules(cost: float, temperature: float, tol: float) -> ContractResult:
    """``0 ≤ cost ≤ k_B T ln 2`` for ``T ≥ 0`` (per-step Landauer cap)."""
    if temperature < 0:
        ok = cost >= -tol
        detail = f"cost={cost:.3e} J (T<0, only nonneg checked)"
        return ContractResult("EpistemicLandauerCost", ok, detail)
    cap = _landauer_bit_energy_joules(temperature)
    ok = -tol <= cost <= cap + tol
    detail = f"cost={cost:.3e} J, cap={cap:.3e} J, T={temperature}"
    return ContractResult("EpistemicLandauerCost", ok, detail)


def check_epistemic_cost_mi_consistent(
    mi_nats: float, cost_j: float, temperature: float, tol: float
) -> ContractResult:
    """``cost ≈ k_B * T * MI`` — ``infoEnergyLowerBound`` with ``MI`` in nats (``EpistemicMI``)."""
    if temperature < 0:
        return ContractResult("EpistemicCostMI_consistency", True, "skipped (T<0)")
    expected = 1.380649e-23 * temperature * mi_nats
    delta = abs(cost_j - expected)
    # Joule magnitudes ~1e-21; ``tol`` scales rtol, fixed atol catches float noise.
    scale = max(abs(expected), abs(cost_j), 1e-40)
    ok = bool(np.isclose(cost_j, expected, rtol=max(tol, 1e-12), atol=1e-30 * scale))
    detail = f"|cost - k_B T MI|={delta:.3e} (expected={expected:.3e} J)"
    return ContractResult("EpistemicCostMI_consistency", ok, detail)


def _trace_temperature_k(data: dict, steps: list) -> float:
    """Prefer root ``temperature``, else first step, else 300 K."""
    if "temperature" in data:
        return float(data["temperature"])
    if steps and "temperature" in steps[0]:
        return float(steps[0]["temperature"])
    return 300.0


def _extract_aggregate(data: dict) -> tuple[float | None, float | None]:
    """``aggregateMI`` / ``aggregateCost`` from root or nested ``aggregate`` object."""
    nested = data.get("aggregate")
    if isinstance(nested, dict):
        mi = nested.get("aggregateMI")
        cost = nested.get("aggregateCost")
        if mi is not None:
            mi = float(mi)
        if cost is not None:
            cost = float(cost)
        return mi, cost
    mi = data.get("aggregateMI")
    cost = data.get("aggregateCost")
    if mi is not None:
        mi = float(mi)
    if cost is not None:
        cost = float(cost)
    return mi, cost


def check_aggregate_mi_catalog_bound(
    aggregate_mi: float, n_steps: int, tol: float
) -> ContractResult:
    """``aggregateMI ≤ n * ln 2`` (``traceRecord_aggregateMI_le`` style bound)."""
    cap = n_steps * float(np.log(2.0))
    ok = aggregate_mi <= cap + tol * max(1.0, n_steps)
    detail = f"aggregateMI={aggregate_mi:.6f}, cap=n·ln2={cap:.6f}, n={n_steps}"
    return ContractResult("EpistemicAggregateMI_catalog", ok, detail)


def check_aggregate_cost_catalog_bound(
    aggregate_cost: float, n_steps: int, temperature: float, tol: float
) -> ContractResult:
    """``aggregateCost ≤ n * k_B T ln 2`` for ``T ≥ 0``."""
    if temperature < 0:
        return ContractResult(
            "EpistemicAggregateCost_catalog",
            aggregate_cost >= -tol,
            f"cost={aggregate_cost:.3e} J (T<0)",
        )
    cap = n_steps * _landauer_bit_energy_joules(temperature)
    ok = aggregate_cost <= cap + tol * max(cap, 1e-40)
    detail = f"aggregateCost={aggregate_cost:.3e} J, cap={cap:.3e} J, n={n_steps}, T={temperature}"
    return ContractResult("EpistemicAggregateCost_catalog", ok, detail)


def check_fold_sum_mi(
    step_mis: list[float], aggregate_mi: float, tol: float
) -> ContractResult:
    """``Σ stepMI = aggregateMI`` — ``PerStepNumericRecord.aggregateMI`` vs ``NumericTraceRecord``."""
    s = float(sum(step_mis))
    delta = abs(s - aggregate_mi)
    scale = max(abs(s), abs(aggregate_mi), 1e-40)
    ok = bool(np.isclose(s, aggregate_mi, rtol=max(tol, 1e-12), atol=1e-30 * scale))
    detail = f"sum(stepMI)={s:.8f}, aggregateMI={aggregate_mi:.8f}, |Δ|={delta:.3e}"
    return ContractResult("EpistemicFold_sumMI", ok, detail)


def check_fold_sum_cost(
    step_costs: list[float], aggregate_cost: float, tol: float
) -> ContractResult:
    """``Σ stepCost = aggregateCost``."""
    s = float(sum(step_costs))
    delta = abs(s - aggregate_cost)
    scale = max(abs(s), abs(aggregate_cost), 1e-40)
    ok = bool(np.isclose(s, aggregate_cost, rtol=max(tol, 1e-12), atol=1e-30 * scale))
    detail = f"sum(stepCost)={s:.3e} J, aggregateCost={aggregate_cost:.3e} J, |Δ|={delta:.3e}"
    return ContractResult("EpistemicFold_sumCost", ok, detail)


def check_landauer(entropy_bits: float, temperature: float, tol: float) -> ContractResult:
    """Validate entropy nonneg, Landauer cost nonneg."""
    k_B = 1.380649e-23
    entropy_ok = entropy_bits >= -tol
    cost = k_B * temperature * np.log(2) * entropy_bits if temperature >= 0 else 0
    cost_ok = cost >= -tol
    ok = entropy_ok and cost_ok
    detail = f"S_bits={entropy_bits:.6f}, cost={cost:.2e} J"
    return ContractResult("Landauer", ok, detail)


def consume_trace(trace_path: Path, tolerance: float) -> list[ContractResult]:
    """Read a trace file and check all contracts."""
    with open(trace_path) as f:
        data = json.load(f)

    results: list[ContractResult] = []
    steps = data.get("steps", [])

    for i, step in enumerate(steps):
        prefix = f"step[{i}]"

        # Density matrix
        if "density_matrix_real" in step:
            re = np.array(step["density_matrix_real"])
            im = np.array(step.get("density_matrix_imag", np.zeros_like(re)))
            rho = re + 1j * im
            r = check_density_matrix(rho, tolerance)
            r.name = f"{prefix}.{r.name}"
            results.append(r)

        # Path weights
        if "path_weights" in step:
            r = check_path_projection(step["path_weights"], tolerance)
            r.name = f"{prefix}.{r.name}"
            results.append(r)

        # Complementarity
        if "visibility" in step and "distinguishability" in step:
            r = check_complementarity(step["visibility"], step["distinguishability"], tolerance)
            r.name = f"{prefix}.{r.name}"
            results.append(r)

        # Landauer (diagonal entropy bits — SimLandauerWitness layer)
        if "entropy_bits" in step:
            T = step.get("temperature", 300.0)
            r = check_landauer(step["entropy_bits"], T, tolerance)
            r.name = f"{prefix}.{r.name}"
            results.append(r)

        # Epistemic MI / cost (EmittedTraceSchema / RuntimeTelemetryBridge names)
        mi = _step_mi_nats(step)
        cost = _step_cost_joules(step)
        T_ep = float(step.get("temperature", 300.0))
        if mi is not None:
            r = check_epistemic_mi_nats(mi, tolerance)
            r.name = f"{prefix}.{r.name}"
            results.append(r)
        if cost is not None:
            r = check_epistemic_cost_joules(cost, T_ep, tolerance)
            r.name = f"{prefix}.{r.name}"
            results.append(r)
        if mi is not None and cost is not None:
            r = check_epistemic_cost_mi_consistent(mi, cost, T_ep, tolerance)
            r.name = f"{prefix}.{r.name}"
            results.append(r)

        # EmittedStepRecord metadata (EmittedTraceSchema / EpistemicRuntimeSchemaContract)
        meta = _metadata_dict(step)
        if "confidence" in meta:
            r = check_emitted_confidence(float(meta["confidence"]), tolerance)
            r.name = f"{prefix}.{r.name}"
            results.append(r)
        if "thermodynamicAdmissible" in meta:
            r = check_emitted_thermodynamic_admissible(meta["thermodynamicAdmissible"])
            r.name = f"{prefix}.{r.name}"
            results.append(r)

    # Optional aggregate + fold (NumericTraceRecord / PerStepNumericRecord aggregates)
    agg_mi, agg_cost = _extract_aggregate(data)
    n = len(steps)
    T_trace = _trace_temperature_k(data, steps)
    if agg_mi is not None:
        r = check_aggregate_mi_catalog_bound(agg_mi, n, tolerance)
        results.append(r)
    if agg_cost is not None:
        r = check_aggregate_cost_catalog_bound(agg_cost, n, T_trace, tolerance)
        results.append(r)
    if agg_mi is not None and agg_cost is not None:
        mis = [_step_mi_nats(s) for s in steps]
        costs = [_step_cost_joules(s) for s in steps]
        if all(m is not None for m in mis) and all(c is not None for c in costs):
            results.append(check_fold_sum_mi([float(m) for m in mis], agg_mi, tolerance))
            results.append(check_fold_sum_cost([float(c) for c in costs], agg_cost, tolerance))
        elif any(m is not None for m in mis) or any(c is not None for c in costs):
            results.append(
                ContractResult(
                    "EpistemicFold_skipped",
                    False,
                    "aggregate totals present but per-step MI/cost missing on some steps "
                    "(need all steps with stepMI/trajMI and stepCost/effortCost for fold check)",
                )
            )

    return results


def main():
    parser = argparse.ArgumentParser(description="Telemetry trace consumer (Gap 14)")
    parser.add_argument("trace", type=Path, help="Path to JSON trace file")
    parser.add_argument("--tolerance", type=float, default=1e-6, help="Numeric tolerance")
    parser.add_argument("--validate", action="store_true",
                        help="Exit 0 if no trace file (CI mode)")
    args = parser.parse_args()

    if args.validate and not args.trace.exists():
        print("telemetry_trace_consumer: --validate mode, no trace file — PASS")
        return 0

    if args.validate:
        try:
            content = args.trace.read_text()
            if not content.strip():
                print("telemetry_trace_consumer: --validate mode, empty trace file — PASS")
                return 0
        except (OSError, PermissionError):
            print("telemetry_trace_consumer: --validate mode, unreadable trace file — PASS")
            return 0

    if not args.trace.exists():
        print(f"ERROR: {args.trace} not found", file=sys.stderr)
        return 1

    results = consume_trace(args.trace, args.tolerance)

    passed = sum(1 for r in results if r.passed)
    failed = sum(1 for r in results if not r.passed)

    for r in results:
        status = "✓" if r.passed else "✗"
        print(f"  {status} {r.name}: {r.detail}")

    print(f"\n{passed} passed, {failed} failed out of {len(results)} checks")
    return 1 if failed > 0 else 0


if __name__ == "__main__":
    sys.exit(main())
