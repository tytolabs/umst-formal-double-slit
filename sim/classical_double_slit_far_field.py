#!/usr/bin/env python3
# SPDX-License-Identifier: MIT
# Copyright (c) 2026 Santhosh Shyamsundar, Santosh Prabhu Shenbagamoorthy — Studio TYTO

"""
Classical far-field (Fraunhofer) double-slit intensity on a screen.

Two identical slits of width `a`, center-to-center separation `d`, monochromatic
light wavelength `lam`.  For observation angle θ (from the normal),

  I(θ) ∝  [ sin(β)/β ]²  ·  cos²(α)

with β = π a sinθ / λ and α = π d sinθ / λ (standard textbook form).

We report a **normalized** intensity with I(0) = 1 (after taking sinβ/β → 1 at β=0).

This is complementary to the toy `fringe_intensity` in `toy_double_slit_mi_gate.py`
(which encodes a phenomenological V–I curve) and to the quantum / Kraus simulators.
"""

from __future__ import annotations

import argparse
import math
from pathlib import Path


def sinc_ratio(beta: float) -> float:
    """sin(β)/β with correct limit 1 at β = 0."""
    if abs(beta) < 1e-15:
        return 1.0
    return math.sin(beta) / beta


def intensity_unnormalized(sin_theta: float, lam: float, a: float, d: float) -> float:
    """Proportional intensity; not normalized."""
    if lam <= 0.0 or a <= 0.0 or d <= 0.0:
        raise ValueError("lam, a, d must be positive")
    if abs(sin_theta) > 1.0:
        raise ValueError("sin_theta must lie in [-1, 1]")
    beta = math.pi * a * sin_theta / lam
    alpha = math.pi * d * sin_theta / lam
    env = sinc_ratio(beta)
    return (env * env) * (math.cos(alpha) ** 2)


def intensity_normalized(sin_theta: float, lam: float, a: float, d: float) -> float:
    """Intensity with I(0) = 1."""
    peak = intensity_unnormalized(0.0, lam, a, d)
    if peak <= 0.0:
        raise ValueError("unexpected zero peak at θ=0")
    return intensity_unnormalized(sin_theta, lam, a, d) / peak


def _parse_args() -> argparse.Namespace:
    p = argparse.ArgumentParser(description="Classical Fraunhofer double-slit intensity.")
    p.add_argument("--lam", type=float, default=500e-9, help="Wavelength (m), default 500 nm.")
    p.add_argument("--a", type=float, default=10e-6, help="Slit width (m), default 10 µm.")
    p.add_argument("--d", type=float, default=100e-6, help="Slit separation (m), default 100 µm.")
    p.add_argument("--sin-max", type=float, default=0.02, help="Sample |sin θ| up to this (default 0.02).")
    p.add_argument("--points", type=int, default=4001, help="Number of samples for CSV output.")
    p.add_argument(
        "--out",
        type=str,
        default=None,
        help="CSV path sin_theta,intensity (default: sim/out/classical_double_slit_far_field.csv).",
    )
    p.add_argument(
        "--validate",
        action="store_true",
        help="Check I(0)=1, non-negativity, even symmetry on a coarse grid.",
    )
    return p.parse_args()


def main() -> None:
    args = _parse_args()
    if args.validate:
        for u in (0.0, 0.001, -0.001, 0.005):
            iu = intensity_normalized(u, args.lam, args.a, args.d)
            if iu < -1e-12:
                raise SystemExit(f"validate: negative intensity at sin_theta={u}")
        i0 = intensity_normalized(0.0, args.lam, args.a, args.d)
        if abs(i0 - 1.0) > 1e-9:
            raise SystemExit(f"validate: I(0) should be 1, got {i0}")
        for u in (0.002, 0.004, -0.003):
            i_p = intensity_normalized(u, args.lam, args.a, args.d)
            i_m = intensity_normalized(-u, args.lam, args.a, args.d)
            if abs(i_p - i_m) > 1e-9:
                raise SystemExit(f"validate: symmetry broken at ±{u}")
        print("validate: I(0)=1, nonnegative samples, even symmetry OK")

    out_path = (
        Path(args.out)
        if args.out
        else Path("sim/out/classical_double_slit_far_field.csv")
    )
    out_path.parent.mkdir(parents=True, exist_ok=True)
    n = max(101, min(args.points, 20001))
    sin_max = args.sin_max
    with out_path.open("w", encoding="utf-8", newline="") as f:
        f.write("sin_theta,intensity_norm\n")
        for i in range(n):
            u = -sin_max + (2.0 * sin_max * i) / (n - 1)
            val = intensity_normalized(u, args.lam, args.a, args.d)
            f.write(f"{u:.10g},{val:.14g}\n")
    print(f"wrote {out_path} ({n} rows)")


if __name__ == "__main__":
    main()
