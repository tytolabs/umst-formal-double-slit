#!/usr/bin/env python3
# SPDX-License-Identifier: MIT
# Copyright (c) 2026 Santhosh Shyamsundar, Santosh Prabhu Shenbagamoorthy — Studio TYTO

"""
export_sample_telemetry_trace.py — Reference **producer** for Gap 14 (Lean-aligned JSON)

Writes a multi-step trace consumable by ``telemetry_trace_consumer.py``, using the same
**diagonal path entropy** story as Lean ``vonNeumannDiagonal`` / ``whichPathMI``:

- ``pathWeight i = Re(ρ[i,i])`` (qubit).
- Epistemic MI in **nats** = binary Shannon ``-p0 ln p0 - p1 ln p1`` (``shannonBinary`` / ``vonNeumannDiagonal``).
- ``pathEntropyBits`` analogue = MI / ln 2.
- ``effortCost`` = ``k_B * T * MI_nats`` (``infoEnergyLowerBound`` with MI in nats).

This is **not** a full RL pipeline; it is a **golden** emitter so sim/RL integrations can mirror field names.

Usage::

    python3 sim/export_sample_telemetry_trace.py --out sim/out/sample_lean_aligned_telemetry.json
    python3 sim/export_sample_telemetry_trace.py --out trace.json --validate
"""

from __future__ import annotations

import argparse
import json
import math
import subprocess
import sys
from pathlib import Path

import numpy as np

K_B = 1.380649e-23


def shannon_binary_nats(p0: float) -> float:
    """Binary Shannon entropy in nats; ``p1 = 1 - p0``. Matches diagonal path entropy on the qubit."""
    eps = 1e-15
    p0 = float(np.clip(p0, eps, 1.0 - eps))
    p1 = 1.0 - p0
    return float(-(p0 * math.log(p0) + p1 * math.log(p1)))


def rho_to_step(
    rho: np.ndarray,
    temperature: float,
    *,
    thermodynamic_admissible: bool = True,
    confidence: float = 1.0,
) -> dict:
    """One step dict: SimLeanBridge + nested ``emitted`` (``EmittedStepRecord`` shape)."""
    assert rho.shape == (2, 2)
    p0 = float(np.real(rho[0, 0]))
    p1 = float(np.real(rho[1, 1]))
    p0 = max(0.0, min(1.0, p0))
    p1 = max(0.0, min(1.0, p1))
    # Renormalize diagonal drift from numerics
    s = p0 + p1
    if s > 1e-12:
        p0, p1 = p0 / s, p1 / s

    mi_nats = shannon_binary_nats(p0)
    entropy_bits = mi_nats / math.log(2.0)
    cost_j = K_B * temperature * mi_nats

    v = float(2.0 * abs(rho[0, 1]))
    d = abs(p0 - p1)

    re = np.real(rho).tolist()
    im = np.imag(rho).tolist()

    return {
        "density_matrix_real": re,
        "density_matrix_imag": im,
        "path_weights": [p0, p1],
        "visibility": v,
        "distinguishability": d,
        "entropy_bits": entropy_bits,
        "temperature": temperature,
        "emitted": {
            "stepMI": mi_nats,
            "stepCost": cost_j,
            "thermodynamicAdmissible": thermodynamic_admissible,
            "confidence": confidence,
        },
    }


def build_demo_trace(temperature: float = 300.0) -> dict:
    """
    Three steps: |+⟩⟨+|, still coherent; optional middle; Lüders diagonal (mixed).
    Uses same physics as ``qubit_kraus_sweep`` (diagonal channel).
    """
    # |+> = (|0>+|1>)/√2
    psi = np.array([1.0, 1.0], dtype=np.complex128) / math.sqrt(2.0)
    rho_coherent = np.outer(psi, np.conj(psi))

    # Lüders which-path: keep diagonal only
    p0 = float(np.real(rho_coherent[0, 0]))
    p1 = float(np.real(rho_coherent[1, 1]))
    rho_measured = np.array([[p0, 0.0], [0.0, p1]], dtype=np.complex128)

    steps = [
        rho_to_step(rho_coherent, temperature, confidence=1.0),
        rho_to_step(rho_coherent, temperature, confidence=0.99),
        rho_to_step(rho_measured, temperature, confidence=1.0),
    ]

    sum_mi = sum(s["emitted"]["stepMI"] for s in steps)
    sum_cost = sum(s["emitted"]["stepCost"] for s in steps)

    return {
        "temperature": temperature,
        "description": "Lean-aligned sample: EpistemicMI = diagonal Shannon nats; costs = k_B T MI.",
        "steps": steps,
        "aggregate": {
            "aggregateMI": sum_mi,
            "aggregateCost": sum_cost,
        },
    }


def main() -> int:
    root = Path(__file__).resolve().parents[1]
    default_out = root / "sim" / "out" / "sample_lean_aligned_telemetry.json"

    p = argparse.ArgumentParser(description="Export sample Lean-aligned telemetry JSON")
    p.add_argument("--out", type=Path, default=default_out, help="Output JSON path")
    p.add_argument("--temperature", type=float, default=300.0, help="Bath temperature (K)")
    p.add_argument("--validate", action="store_true", help="Run telemetry_trace_consumer.py on output")
    args = p.parse_args()

    trace = build_demo_trace(temperature=args.temperature)
    args.out.parent.mkdir(parents=True, exist_ok=True)
    with open(args.out, "w", encoding="utf-8") as f:
        json.dump(trace, f, indent=2)
    print(f"Wrote {args.out}", flush=True)

    if args.validate:
        consumer = root / "sim" / "telemetry_trace_consumer.py"
        r = subprocess.run(
            [sys.executable, str(consumer), str(args.out), "--tolerance", "1e-8"],
            cwd=str(root),
        )
        return int(r.returncode)
    return 0


if __name__ == "__main__":
    sys.exit(main())
