#!/usr/bin/env python3
"""
Closed-form probability density for a freely spreading 1D Gaussian wavepacket.

Pedagogical / smoke use only (not a full double-slit propagator).

Convention (dimensionless): ħ = 1, m = 1. Initial state is a minimum-uncertainty
Gaussian centered at x0 with spatial width parameter σ0 and average momentum k0
(so group velocity ≈ k0/m = k0).

|ψ(x,t)|² is Gaussian with center μ(t) = x0 + k0 t and variance σ(t)² where
  σ(t)² = σ0² + t² / (4 σ0²).

This matches the standard textbook free-Gaussian spreading when σ0 is the
position standard deviation at t=0 (see e.g. Griffiths QM, Gaussian packet).
"""

from __future__ import annotations

import argparse
import math
from pathlib import Path
from typing import Tuple


def density(
    x: float,
    t: float,
    *,
    x0: float = 0.0,
    k0: float = 0.0,
    sigma0: float = 1.0,
) -> float:
    """|ψ(x,t)|² for the free Gaussian described in the module docstring."""
    if sigma0 <= 0.0:
        raise ValueError("sigma0 must be positive")
    var = sigma0 * sigma0 + (t * t) / (4.0 * sigma0 * sigma0)
    if var <= 0.0:
        raise ValueError("non-positive variance")
    sigma_t = math.sqrt(var)
    mu = x0 + k0 * t
    inv_norm = 1.0 / (sigma_t * math.sqrt(2.0 * math.pi))
    z = (x - mu) / sigma_t
    return inv_norm * math.exp(-0.5 * z * z)


def trapezoid_integral(xs: list[float], ys: list[float]) -> float:
    if len(xs) != len(ys) or len(xs) < 2:
        raise ValueError("need at least two aligned samples")
    total = 0.0
    for i in range(len(xs) - 1):
        dx = xs[i + 1] - xs[i]
        total += 0.5 * (ys[i] + ys[i + 1]) * dx
    return total


def validate_normalization(
    *,
    t: float,
    x0: float,
    k0: float,
    sigma0: float,
    half_width: float,
    n_points: int,
) -> Tuple[float, float]:
    """
    Return (integral_estimate, max_density) on [-half_width, half_width].
    Integral should be ~1 if the grid covers the bulk of the mass.
    """
    if n_points < 3:
        raise ValueError("n_points must be at least 3")
    xs = []
    ys = []
    for i in range(n_points):
        frac = i / (n_points - 1)
        x = -half_width + 2.0 * half_width * frac
        xs.append(x)
        ys.append(density(x, t, x0=x0, k0=k0, sigma0=sigma0))
    return trapezoid_integral(xs, ys), max(ys)


def _parse_args() -> argparse.Namespace:
    p = argparse.ArgumentParser(
        description="Free 1D Gaussian |ψ|² (closed form). Optional spatial track starter."
    )
    p.add_argument("--t", type=float, default=0.0, help="Time (default: 0).")
    p.add_argument("--x0", type=float, default=0.0, help="Initial center (default: 0).")
    p.add_argument("--k0", type=float, default=0.0, help="Initial momentum / ħ (default: 0).")
    p.add_argument("--sigma0", type=float, default=1.0, help="Initial σ_x (default: 1).")
    p.add_argument(
        "--half-width",
        type=float,
        default=12.0,
        help="Integration / sample window half-width (default: 12).",
    )
    p.add_argument("--points", type=int, default=20001, help="Sample count for --validate.")
    p.add_argument(
        "--out",
        type=str,
        default=None,
        help="Optional CSV path: x, density (default: sim/out/spatial_free_gaussian.csv).",
    )
    p.add_argument(
        "--validate",
        action="store_true",
        help="Check normalization (trapezoid) and non-negativity on the grid.",
    )
    return p.parse_args()


def main() -> None:
    args = _parse_args()
    if args.validate:
        integral, peak = validate_normalization(
            t=args.t,
            x0=args.x0,
            k0=args.k0,
            sigma0=args.sigma0,
            half_width=args.half_width,
            n_points=args.points,
        )
        if peak <= 0.0:
            raise SystemExit("validate: expected positive peak density")
        if abs(integral - 1.0) > 5e-3:
            raise SystemExit(
                f"validate: normalization off (integral≈{integral}, expected ~1); "
                "widen --half-width or increase --points"
            )
        print(f"validate: integral≈{integral:.6f}, peak_density≈{peak:.6f}")

    out_path = Path(args.out) if args.out else Path("sim/out/spatial_free_gaussian.csv")
    out_path.parent.mkdir(parents=True, exist_ok=True)
    n_write = min(2001, max(101, args.points))
    with out_path.open("w", encoding="utf-8", newline="") as f:
        f.write("x,rho\n")
        for i in range(n_write):
            frac = i / (n_write - 1)
            x = -args.half_width + 2.0 * args.half_width * frac
            r = density(x, args.t, x0=args.x0, k0=args.k0, sigma0=args.sigma0)
            f.write(f"{x:.8g},{r:.12g}\n")
    print(f"wrote {out_path} ({n_write} rows)")


if __name__ == "__main__":
    main()
