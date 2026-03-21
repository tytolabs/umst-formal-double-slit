#!/usr/bin/env python3
# SPDX-License-Identifier: MIT
# Copyright (c) 2026 Santhosh Shyamsundar, Santosh Prabhu Shenbagamoorthy — Studio TYTO

"""
1D caricature of a **double slit**: a high potential plateau with two Gaussian
“openings”, active only for **x >= x_screen** (pedagogical screen + two soft holes).

Uses Strang splitting from `schrodinger_1d_split_step.py`.  **Requires NumPy.**

This is **not** a physical 2D slit geometry; it is a minimal grid model to show
interference-like structure after a localized barrier with two low-V windows.
"""

from __future__ import annotations

import argparse
import importlib.util
from pathlib import Path

import numpy as np


def _load_split():
    here = Path(__file__).resolve().parent
    script = here / "schrodinger_1d_split_step.py"
    spec = importlib.util.spec_from_file_location("schrodinger_1d_split_step", script)
    mod = importlib.util.module_from_spec(spec)
    assert spec and spec.loader
    spec.loader.exec_module(mod)
    return mod


def _load_fft():
    here = Path(__file__).resolve().parent
    script = here / "schrodinger_1d_free_fft.py"
    spec = importlib.util.spec_from_file_location("schrodinger_1d_free_fft", script)
    mod = importlib.util.module_from_spec(spec)
    assert spec and spec.loader
    spec.loader.exec_module(mod)
    return mod


def soft_double_slit_potential(
    xs: np.ndarray,
    *,
    v0: float,
    x_screen: float,
    slit_separation: float,
    slit_sigma: float,
    slit_center_offset: float = 0.0,
) -> np.ndarray:
    """
    For ``x < x_screen``: V = 0.

    For ``x >= x_screen``: V = V0 * (1 - min(1, g1 + g2)) with Gaussians centered
    at ``x_screen + slit_center_offset ± slit_separation/2`` (clipped to the
    half-line so openings sit just past the screen edge when offset is small).
    """
    if v0 < 0.0:
        raise ValueError("v0 must be non-negative")
    if slit_separation <= 0.0 or slit_sigma <= 0.0:
        raise ValueError("slit_separation and slit_sigma must be positive")
    base = x_screen + slit_center_offset
    mu1 = base - slit_separation / 2.0
    mu2 = base + slit_separation / 2.0
    g1 = np.exp(-((xs - mu1) / slit_sigma) ** 2)
    g2 = np.exp(-((xs - mu2) / slit_sigma) ** 2)
    openings = np.minimum(1.0, g1 + g2)
    v = np.zeros_like(xs, dtype=float)
    mask = xs >= x_screen
    v[mask] = v0 * (1.0 - openings[mask])
    return v


def count_local_maxima(y: np.ndarray) -> int:
    """Interior strict local maxima (1D array)."""
    if y.size < 3:
        return 0
    c = 0
    for i in range(1, y.size - 1):
        if y[i] > y[i - 1] and y[i] > y[i + 1]:
            c += 1
    return c


def count_coarse_local_maxima(y: np.ndarray, *, stride: int = 20) -> int:
    """Count local maxima on a downsampled envelope (kills grid-scale oscillations)."""
    if stride < 2:
        raise ValueError("stride must be >= 2")
    yc = y[::stride]
    return count_local_maxima(yc)


def _parse_args() -> argparse.Namespace:
    p = argparse.ArgumentParser(description="Soft double-slit screen (1D split-step).")
    p.add_argument("--length", type=float, default=56.0)
    p.add_argument("-n", "--points", type=int, default=4096, dest="n")
    p.add_argument("--t", type=float, default=2.5)
    p.add_argument("--steps", type=int, default=500)
    p.add_argument("--v0", type=float, default=28.0)
    p.add_argument("--x-screen", type=float, default=-2.0)
    p.add_argument("--slit-sep", type=float, default=1.4)
    p.add_argument("--slit-sigma", type=float, default=0.22)
    p.add_argument("--slit-offset", type=float, default=0.35)
    p.add_argument("--x0", type=float, default=-18.0)
    p.add_argument("--k0", type=float, default=1.35)
    p.add_argument("--sigma0", type=float, default=1.1)
    p.add_argument(
        "--validate",
        action="store_true",
        help="Check unitarity and interference-style structure in rho.",
    )
    return p.parse_args()


def main() -> None:
    args = _parse_args()
    sp = _load_split()
    ff = _load_fft()
    xs, dx = ff.make_grid(args.length, args.n)
    v_x = soft_double_slit_potential(
        xs,
        v0=args.v0,
        x_screen=args.x_screen,
        slit_separation=args.slit_sep,
        slit_sigma=args.slit_sigma,
        slit_center_offset=args.slit_offset,
    )
    psi0 = ff.initial_gaussian(xs, x0=args.x0, k0=args.k0, sigma0=args.sigma0)
    psi0 = psi0 / np.sqrt(ff.norm_dx(psi0, dx))
    dt = args.t / args.steps
    psi_t = sp.split_step_evolve(psi0, dx, dt=dt, n_steps=args.steps, v_x=v_x)
    rho = ff.density(psi_t)

    if args.validate:
        nrm = ff.norm_dx(psi_t, dx)
        if abs(nrm - 1.0) > 2e-3:
            raise SystemExit(f"validate: norm ~ {nrm}, expected ~1")
        # Look right of screen for multiple peaks (diffraction-style).
        right = xs >= (args.x_screen + 0.5)
        rho_r = rho[right]
        peaks = count_coarse_local_maxima(rho_r, stride=20)
        if peaks < 8 or peaks > 45:
            raise SystemExit(
                f"validate: expected ~8–45 coarse local maxima right of screen, got {peaks} "
                "(tune --t/--k0/--v0/--slit-* if needed)"
            )
        print(f"validate: norm~{nrm:.5f}, coarse_local_maxima(right of screen)={peaks}")

    out = Path("sim/out/schrodinger_soft_double_slit_rho.csv")
    out.parent.mkdir(parents=True, exist_ok=True)
    with out.open("w", encoding="utf-8", newline="") as f:
        f.write("x,V,rho\n")
        for x, vv, r in zip(xs, v_x, rho):
            f.write(f"{float(x):.10g},{float(vv):.10g},{float(r):.14g}\n")
    print(f"wrote {out}")


if __name__ == "__main__":
    main()
