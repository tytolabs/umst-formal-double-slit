#!/usr/bin/env python3
# SPDX-License-Identifier: MIT
# Copyright (c) 2026 Santhosh Shyamsundar, Santosh Prabhu Shenbagamoorthy — Studio TYTO

"""
2D Strang split-step Schrödinger on a periodic grid (ħ = 1).

**Geometry:** a vertical **soft screen** at ``x >= x_screen`` with two Gaussian
openings in **y** (minimal 2D double-slit caricature). Initial state: separable
minimum-uncertainty Gaussian with momenta ``kx0``, ``ky0``.

**Requires NumPy.** Not part of default ``make sim``; covered by unittest when NumPy
is installed.

**Validate:** ``--validate`` with ``--v0 0`` checks split-step vs one-shot 2D FFT
free propagator; with ``--v0 > 0`` checks norm ≈ 1 (unitarity smoke).
"""

from __future__ import annotations

import argparse
from pathlib import Path

import numpy as np


def make_grid_2d(
    length_x: float,
    length_y: float,
    nx: int,
    ny: int,
) -> tuple[np.ndarray, np.ndarray, float, float]:
    if nx < 8 or ny < 8 or nx % 2 != 0 or ny % 2 != 0:
        raise ValueError("nx, ny must be even integers >= 8")
    if length_x <= 0 or length_y <= 0:
        raise ValueError("lengths must be positive")
    dx = length_x / nx
    dy = length_y / ny
    xs = np.linspace(-length_x / 2.0 + dx / 2.0, length_x / 2.0 - dx / 2.0, nx)
    ys = np.linspace(-length_y / 2.0 + dy / 2.0, length_y / 2.0 - dy / 2.0, ny)
    X, Y = np.meshgrid(xs, ys, indexing="ij")
    return X, Y, dx, dy


def initial_gaussian_2d(
    X: np.ndarray,
    Y: np.ndarray,
    *,
    x0: float,
    y0: float,
    kx0: float,
    ky0: float,
    sigma0: float,
) -> np.ndarray:
    """Separable minimum-uncertainty Gaussian (same 1D convention as free_fft)."""
    if sigma0 <= 0.0:
        raise ValueError("sigma0 must be positive")
    norm = (2.0 * np.pi * sigma0**2) ** (-0.5)
    gx = np.exp(-((X - x0) ** 2) / (4.0 * sigma0**2) + 1j * kx0 * X)
    gy = np.exp(-((Y - y0) ** 2) / (4.0 * sigma0**2) + 1j * ky0 * Y)
    return norm * gx * gy


def density(psi: np.ndarray) -> np.ndarray:
    return np.real(np.conjugate(psi) * psi)


def norm_dxy(psi: np.ndarray, dx: float, dy: float) -> float:
    return float(np.sum(density(psi)) * dx * dy)


def max_abs_rel_err(
    rho_num: np.ndarray,
    rho_ref: np.ndarray,
    *,
    eps: float = 1e-15,
) -> float:
    den = np.maximum(np.abs(rho_ref), eps)
    return float(np.max(np.abs(rho_num - rho_ref) / den))


def kinetic_half_step_2d(
    psi: np.ndarray,
    dx: float,
    dy: float,
    *,
    dt: float,
    mass: float = 1.0,
) -> np.ndarray:
    if mass <= 0.0:
        raise ValueError("mass must be positive")
    nx, ny = psi.shape
    kx = (2.0 * np.pi * np.fft.fftfreq(nx, d=dx))[:, np.newaxis]
    ky = (2.0 * np.pi * np.fft.fftfreq(ny, d=dy))[np.newaxis, :]
    p2 = kx**2 + ky**2
    psi_k = np.fft.fft2(psi)
    phase = np.exp(-1j * p2 / (2.0 * mass) * (dt / 2.0))
    return np.fft.ifft2(phase * psi_k)


def potential_full_step(psi: np.ndarray, v: np.ndarray, dt: float) -> np.ndarray:
    if v.shape != psi.shape:
        raise ValueError("V must match psi shape")
    return psi * np.exp(-1j * v * dt)


def split_step_evolve_2d(
    psi: np.ndarray,
    dx: float,
    dy: float,
    *,
    dt: float,
    n_steps: int,
    v_xy: np.ndarray,
    mass: float = 1.0,
) -> np.ndarray:
    if n_steps < 1:
        raise ValueError("n_steps must be >= 1")
    out = psi.copy()
    for _ in range(n_steps):
        out = kinetic_half_step_2d(out, dx, dy, dt=dt, mass=mass)
        out = potential_full_step(out, v_xy, dt)
        out = kinetic_half_step_2d(out, dx, dy, dt=dt, mass=mass)
    return out


def propagate_free_fft2(
    psi: np.ndarray,
    dx: float,
    dy: float,
    *,
    total_time: float,
    mass: float = 1.0,
) -> np.ndarray:
    """One-shot free evolution (periodic boundaries)."""
    if mass <= 0.0:
        raise ValueError("mass must be positive")
    nx, ny = psi.shape
    kx = (2.0 * np.pi * np.fft.fftfreq(nx, d=dx))[:, np.newaxis]
    ky = (2.0 * np.pi * np.fft.fftfreq(ny, d=dy))[np.newaxis, :]
    p2 = kx**2 + ky**2
    psi_k = np.fft.fft2(psi)
    phase = np.exp(-1j * p2 / (2.0 * mass) * total_time)
    return np.fft.ifft2(phase * psi_k)


def soft_double_slit_potential_2d(
    X: np.ndarray,
    Y: np.ndarray,
    *,
    v0: float,
    x_screen: float,
    slit_separation: float,
    slit_sigma: float,
    slit_center_offset: float = 0.0,
) -> np.ndarray:
    """For ``x < x_screen``: V = 0. For ``x >= x_screen``: soft two-slit mask in y."""
    if v0 < 0.0:
        raise ValueError("v0 must be non-negative")
    if slit_separation <= 0.0 or slit_sigma <= 0.0:
        raise ValueError("slit_separation and slit_sigma must be positive")
    base_y = slit_center_offset
    mu1 = base_y - slit_separation / 2.0
    mu2 = base_y + slit_separation / 2.0
    g1 = np.exp(-((Y - mu1) / slit_sigma) ** 2)
    g2 = np.exp(-((Y - mu2) / slit_sigma) ** 2)
    openings = np.minimum(1.0, g1 + g2)
    mask = X >= x_screen
    v = np.zeros_like(X, dtype=float)
    v[mask] = v0 * (1.0 - openings[mask])
    return v


def _parse_args() -> argparse.Namespace:
    p = argparse.ArgumentParser(description="2D soft double slit (split-step, numpy).")
    p.add_argument("--lx", type=float, default=48.0, help="Periodic box length in x")
    p.add_argument("--ly", type=float, default=48.0, help="Periodic box length in y")
    p.add_argument("--nx", type=int, default=192, help="Grid points in x (even, >= 8)")
    p.add_argument("--ny", type=int, default=192, help="Grid points in y (even, >= 8)")
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
    p.add_argument(
        "--validate",
        action="store_true",
        help="V=0: vs FFT2; V>0: norm smoke",
    )
    return p.parse_args()


def main() -> None:
    args = _parse_args()
    X, Y, dx, dy = make_grid_2d(args.lx, args.ly, args.nx, args.ny)
    psi0 = initial_gaussian_2d(
        X,
        Y,
        x0=args.x0,
        y0=args.y0,
        kx0=args.kx0,
        ky0=args.ky0,
        sigma0=args.sigma0,
    )
    psi0 = psi0 / np.sqrt(norm_dxy(psi0, dx, dy))
    dt = args.t / args.steps
    v_xy = soft_double_slit_potential_2d(
        X,
        Y,
        v0=args.v0,
        x_screen=args.x_screen,
        slit_separation=args.slit_sep,
        slit_sigma=args.slit_sigma,
        slit_center_offset=args.slit_y_offset,
    )
    psi = split_step_evolve_2d(
        psi0,
        dx,
        dy,
        dt=dt,
        n_steps=args.steps,
        v_xy=v_xy,
        mass=args.mass,
    )

    if args.validate:
        nrm = norm_dxy(psi, dx, dy)
        if args.v0 == 0.0:
            psi_ref = propagate_free_fft2(psi0, dx, dy, total_time=args.t, mass=args.mass)
            err = max_abs_rel_err(density(psi), density(psi_ref))
            if abs(nrm - 1.0) > 1e-4:
                raise SystemExit(f"validate V=0: norm ~ {nrm}, expected ~1")
            if err > 1e-5:
                raise SystemExit(f"validate V=0: split-step vs FFT2 max rel err {err}")
            print(f"validate V=0: norm~{nrm:.8f}, max_rel_err_vs_fft2~{err:.3e}")
        else:
            if abs(nrm - 1.0) > 2e-3:
                raise SystemExit(f"validate: norm ~ {nrm} with barrier")
            print(f"validate barrier: norm~{nrm:.6f} (unitarity smoke)")

    out = Path("sim/out/schrodinger_2d_soft_double_slit_rho.csv")
    out.parent.mkdir(parents=True, exist_ok=True)
    rho = density(psi)
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
