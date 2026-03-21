#!/usr/bin/env python3
# SPDX-License-Identifier: MIT
# Copyright (c) 2026 Santhosh Shyamsundar, Santosh Prabhu Shenbagamoorthy — Studio TYTO

"""
2D split-step Schrödinger with **Perfectly Matched Layer** (PML) boundaries.

Implements coordinate-stretching-based PML for the time-dependent Schrödinger
equation.  In the PML region, a polynomial-graded conductivity profile
``σ(x) = σ_max * ((x - x_pml) / d_pml)^p`` damps outgoing waves via an
exponential factor ``exp(-σ*dt)`` applied after each kinetic half-step.

The simple-PML approach (multiplicative damping) is highly effective for
Schrödinger and produces significantly less spurious reflection than a
constant-amplitude sponge layer of equal thickness.

Reuses propagator pieces from ``schrodinger_2d_soft_double_slit.py``.
**Requires NumPy.**

**Validate:** ``--validate`` compares PML vs simple sponge reflection.
"""

from __future__ import annotations

import argparse
import importlib.util
from pathlib import Path

import numpy as np


def _load_2d():
    here = Path(__file__).resolve().parent
    script = here / "schrodinger_2d_soft_double_slit.py"
    spec = importlib.util.spec_from_file_location("schrodinger_2d_soft_double_slit", script)
    mod = importlib.util.module_from_spec(spec)
    assert spec and spec.loader
    spec.loader.exec_module(mod)
    return mod


def _load_1d_absorb():
    here = Path(__file__).resolve().parent
    script = here / "schrodinger_1d_absorbing_edges.py"
    spec = importlib.util.spec_from_file_location("schrodinger_1d_absorbing_edges", script)
    mod = importlib.util.module_from_spec(spec)
    assert spec and spec.loader
    spec.loader.exec_module(mod)
    return mod


# ---------------------------------------------------------------------------
# PML conductivity and damping
# ---------------------------------------------------------------------------


def pml_conductivity_profile(
    x: np.ndarray,
    x_pml: float,
    d_pml: float,
    sigma_max: float,
    order: int = 3,
) -> np.ndarray:
    """Polynomial-graded conductivity ``σ(x) = σ_max * ((x - x_pml)/d_pml)^order``.

    Returns zero where ``x < x_pml``; ramps from 0 to σ_max over the PML
    thickness ``d_pml``.
    """
    if d_pml <= 0.0:
        raise ValueError("d_pml must be positive")
    if sigma_max < 0.0:
        raise ValueError("sigma_max must be non-negative")
    if order < 1:
        raise ValueError("order must be >= 1")
    depth = np.clip((x - x_pml) / d_pml, 0.0, 1.0)
    return sigma_max * depth ** order


def pml_damping_mask_1d(
    n: int,
    n_pml: int,
    sigma_max: float,
    dt: float,
    order: int = 3,
) -> np.ndarray:
    """Symmetric PML damping mask for one dimension.

    Returns ``exp(-σ(x)*dt)`` where σ ramps polynomially from both edges
    over ``n_pml`` grid points.
    """
    if n < 2:
        raise ValueError("n must be >= 2")
    if n_pml < 0:
        raise ValueError("n_pml must be non-negative")
    if n_pml == 0 or sigma_max == 0.0:
        return np.ones(n, dtype=float)
    sigma = np.zeros(n, dtype=float)
    d_pml = float(max(n_pml - 1, 1))
    for j in range(n_pml):
        depth = (n_pml - 1 - j) / d_pml
        val = sigma_max * depth ** order
        sigma[j] = max(sigma[j], val)
    for j in range(n_pml):
        depth = (n_pml - 1 - j) / d_pml
        val = sigma_max * depth ** order
        sigma[n - 1 - j] = max(sigma[n - 1 - j], val)
    return np.exp(-sigma * dt)


def pml_damping_mask_2d(
    nx: int,
    ny: int,
    n_pml_x: int,
    n_pml_y: int,
    sigma_max: float,
    dt: float,
    order: int = 3,
) -> np.ndarray:
    """Separable 2D PML damping mask: ``mask[i,j] = mx[i] * my[j]``."""
    mx = pml_damping_mask_1d(nx, n_pml_x, sigma_max, dt, order)
    my = pml_damping_mask_1d(ny, n_pml_y, sigma_max, dt, order)
    return mx[:, np.newaxis] * my[np.newaxis, :]


def split_step_evolve_2d_pml(
    psi: np.ndarray,
    dx: float,
    dy: float,
    dt: float,
    n_steps: int,
    v_xy: np.ndarray,
    n_pml_x: int,
    n_pml_y: int,
    sigma_max: float,
    mass: float = 1.0,
    order: int = 3,
) -> np.ndarray:
    """Strang split-step with PML damping applied after each full step."""
    if n_steps < 1:
        raise ValueError("n_steps must be >= 1")
    m2 = _load_2d()
    mask = pml_damping_mask_2d(psi.shape[0], psi.shape[1], n_pml_x, n_pml_y,
                               sigma_max, dt, order)
    if mask.shape != psi.shape:
        raise ValueError("mask shape must match psi")
    out = psi.copy()
    for _ in range(n_steps):
        out = m2.kinetic_half_step_2d(out, dx, dy, dt=dt, mass=mass)
        out = m2.potential_full_step(out, v_xy, dt)
        out = m2.kinetic_half_step_2d(out, dx, dy, dt=dt, mass=mass)
        out *= mask
    return out


# ---------------------------------------------------------------------------
# CLI
# ---------------------------------------------------------------------------


def _parse_args() -> argparse.Namespace:
    p = argparse.ArgumentParser(description="2D split-step + PML boundaries (numpy).")
    p.add_argument("--lx", type=float, default=48.0)
    p.add_argument("--ly", type=float, default=48.0)
    p.add_argument("--nx", type=int, default=192)
    p.add_argument("--ny", type=int, default=192)
    p.add_argument("--t", type=float, default=2.0)
    p.add_argument("--steps", type=int, default=400)
    p.add_argument("--v0", type=float, default=24.0)
    p.add_argument("--x-screen", type=float, default=-4.0)
    p.add_argument("--slit-sep", type=float, default=1.6)
    p.add_argument("--slit-sigma", type=float, default=0.35)
    p.add_argument("--slit-y-offset", type=float, default=0.0)
    p.add_argument("--x0", type=float, default=-14.0)
    p.add_argument("--y0", type=float, default=0.0)
    p.add_argument("--kx0", type=float, default=1.4)
    p.add_argument("--ky0", type=float, default=0.0)
    p.add_argument("--sigma0", type=float, default=1.1)
    p.add_argument("--mass", type=float, default=1.0)
    p.add_argument("--n-pml-x", type=int, default=36)
    p.add_argument("--n-pml-y", type=int, default=36)
    p.add_argument("--sigma-max", type=float, default=5.0)
    p.add_argument("--pml-order", type=int, default=3)
    p.add_argument(
        "--validate",
        action="store_true",
        help="Compare PML vs simple sponge reflection",
    )
    return p.parse_args()


def main() -> None:
    args = _parse_args()
    m2 = _load_2d()
    X, Y, dx, dy = m2.make_grid_2d(args.lx, args.ly, args.nx, args.ny)

    # ---- validation: PML vs simple sponge ----
    if args.validate:
        # Use a packet aimed at the right edge to measure reflection
        xs_1d = X[:, 0]
        x_max = float(np.max(xs_1d))
        # Packet starting near right boundary, moving rightward
        psi_test = m2.initial_gaussian_2d(
            X, Y,
            x0=x_max - 6.0,
            y0=0.0,
            kx0=2.0,
            ky0=0.0,
            sigma0=1.0,
        )
        psi_test = psi_test / np.sqrt(m2.norm_dxy(psi_test, dx, dy))
        v_zero = np.zeros_like(X, dtype=float)
        dt = args.t / args.steps

        # PML evolution
        psi_pml = split_step_evolve_2d_pml(
            psi_test, dx, dy, dt, args.steps, v_zero,
            args.n_pml_x, args.n_pml_y, args.sigma_max,
            mass=args.mass, order=args.pml_order,
        )
        norm_pml = m2.norm_dxy(psi_pml, dx, dy)

        # Simple sponge evolution (same number of absorbing cells)
        ab = _load_1d_absorb()
        mx_sponge = ab.absorption_mask(args.nx, args.n_pml_x, 0.88)
        my_sponge = ab.absorption_mask(args.ny, args.n_pml_y, 0.88)
        mask_sponge = mx_sponge[:, np.newaxis] * my_sponge[np.newaxis, :]
        out_sponge = psi_test.copy()
        for _ in range(args.steps):
            out_sponge = m2.kinetic_half_step_2d(out_sponge, dx, dy, dt=dt, mass=args.mass)
            out_sponge = m2.potential_full_step(out_sponge, v_zero, dt)
            out_sponge = m2.kinetic_half_step_2d(out_sponge, dx, dy, dt=dt, mass=args.mass)
            out_sponge *= mask_sponge
        norm_sponge = m2.norm_dxy(out_sponge, dx, dy)

        # Measure reflected amplitude: density remaining in the interior
        # (lower norm = more absorbed = less reflection)
        interior_x = slice(args.n_pml_x, args.nx - args.n_pml_x)
        interior_y = slice(args.n_pml_y, args.ny - args.n_pml_y)
        rho_pml_int = float(np.sum(m2.density(psi_pml)[interior_x, interior_y]) * dx * dy)
        rho_sponge_int = float(np.sum(m2.density(out_sponge)[interior_x, interior_y]) * dx * dy)

        print(f"validate PML:    total norm = {norm_pml:.8f}, interior density = {rho_pml_int:.8f}")
        print(f"validate sponge: total norm = {norm_sponge:.8f}, interior density = {rho_sponge_int:.8f}")
        print(f"  PML norm loss  = {1.0 - norm_pml:.6f}")
        print(f"  sponge norm loss = {1.0 - norm_sponge:.6f}")
        if rho_pml_int < rho_sponge_int:
            print("  PML has LESS interior residual (less reflection) — OK")
        else:
            print("  WARNING: PML did not outperform sponge with these parameters")
        return

    # ---- normal evolution with slit potential ----
    psi0 = m2.initial_gaussian_2d(
        X, Y,
        x0=args.x0, y0=args.y0,
        kx0=args.kx0, ky0=args.ky0,
        sigma0=args.sigma0,
    )
    psi0 = psi0 / np.sqrt(m2.norm_dxy(psi0, dx, dy))
    dt = args.t / args.steps
    v_xy = m2.soft_double_slit_potential_2d(
        X, Y,
        v0=args.v0,
        x_screen=args.x_screen,
        slit_separation=args.slit_sep,
        slit_sigma=args.slit_sigma,
        slit_center_offset=args.slit_y_offset,
    )
    psi = split_step_evolve_2d_pml(
        psi0, dx, dy, dt, args.steps, v_xy,
        args.n_pml_x, args.n_pml_y, args.sigma_max,
        mass=args.mass, order=args.pml_order,
    )
    norm_final = m2.norm_dxy(psi, dx, dy)
    print(f"final norm = {norm_final:.8f} (norm loss = {1.0 - norm_final:.6f})")

    out = Path("sim/out/schrodinger_2d_pml_rho.csv")
    out.parent.mkdir(parents=True, exist_ok=True)
    rho = m2.density(psi)
    with out.open("w", encoding="utf-8", newline="") as f:
        f.write("x,y,rho\n")
        for i in range(args.nx):
            for j in range(args.ny):
                f.write(
                    f"{float(X[i, j]):.10g},{float(Y[i, j]):.10g},{float(rho[i, j]):.14g}\n"
                )
    print(f"wrote {out}")


if __name__ == "__main__":
    main()
