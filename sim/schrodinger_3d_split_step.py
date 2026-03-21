#!/usr/bin/env python3
# SPDX-License-Identifier: MIT
# Copyright (c) 2026 Santhosh Shyamsundar, Santosh Prabhu Shenbagamoorthy — Studio TYTO

"""
3D Strang split-step Schrödinger on a periodic grid (hbar = 1).

Extends the 2D split-step from ``schrodinger_2d_soft_double_slit.py`` to three
spatial dimensions.  The double-slit geometry has a Gaussian barrier screen at
``x = x_screen`` with two **circular** openings in the ``(y, z)`` plane,
separated along ``y``.

Includes separable absorption masks (sponge) and optional PML damping masks
for boundary treatment.

**Requires NumPy.** Default grid is 32x32x32 for fast validation; use
``--nx/--ny/--nz`` for larger runs.

**Validate:** ``--validate`` checks free-propagation norm conservation and
prints summary statistics.
"""

from __future__ import annotations

import argparse
import time
from pathlib import Path

import numpy as np


# ---------------------------------------------------------------------------
# Grid
# ---------------------------------------------------------------------------


def make_grid_3d(
    lx: float,
    ly: float,
    lz: float,
    nx: int,
    ny: int,
    nz: int,
) -> tuple[np.ndarray, np.ndarray, np.ndarray, float, float, float]:
    """Create a 3D Cartesian grid centred at the origin.

    Returns ``(X, Y, Z, dx, dy, dz)`` with ``X.shape == (nx, ny, nz)``.
    """
    for n, name in ((nx, "nx"), (ny, "ny"), (nz, "nz")):
        if n < 8 or n % 2 != 0:
            raise ValueError(f"{name} must be an even integer >= 8")
    for l, name in ((lx, "lx"), (ly, "ly"), (lz, "lz")):
        if l <= 0:
            raise ValueError(f"{name} must be positive")
    dx = lx / nx
    dy = ly / ny
    dz = lz / nz
    xs = np.linspace(-lx / 2.0 + dx / 2.0, lx / 2.0 - dx / 2.0, nx)
    ys = np.linspace(-ly / 2.0 + dy / 2.0, ly / 2.0 - dy / 2.0, ny)
    zs = np.linspace(-lz / 2.0 + dz / 2.0, lz / 2.0 - dz / 2.0, nz)
    X, Y, Z = np.meshgrid(xs, ys, zs, indexing="ij")
    return X, Y, Z, dx, dy, dz


# ---------------------------------------------------------------------------
# Initial state
# ---------------------------------------------------------------------------


def initial_gaussian_3d(
    X: np.ndarray,
    Y: np.ndarray,
    Z: np.ndarray,
    x0: float,
    y0: float,
    z0: float,
    kx0: float,
    ky0: float,
    kz0: float,
    sigma0: float,
) -> np.ndarray:
    """Separable minimum-uncertainty 3D Gaussian with momentum."""
    if sigma0 <= 0.0:
        raise ValueError("sigma0 must be positive")
    norm = (2.0 * np.pi * sigma0**2) ** (-0.75)
    gx = np.exp(-((X - x0) ** 2) / (4.0 * sigma0**2) + 1j * kx0 * X)
    gy = np.exp(-((Y - y0) ** 2) / (4.0 * sigma0**2) + 1j * ky0 * Y)
    gz = np.exp(-((Z - z0) ** 2) / (4.0 * sigma0**2) + 1j * kz0 * Z)
    return norm * gx * gy * gz


# ---------------------------------------------------------------------------
# Helpers
# ---------------------------------------------------------------------------


def density_3d(psi: np.ndarray) -> np.ndarray:
    return np.real(np.conjugate(psi) * psi)


def norm_3d(psi: np.ndarray, dx: float, dy: float, dz: float) -> float:
    return float(np.sum(density_3d(psi)) * dx * dy * dz)


# ---------------------------------------------------------------------------
# Split-step pieces
# ---------------------------------------------------------------------------


def kinetic_half_step_3d(
    psi: np.ndarray,
    dx: float,
    dy: float,
    dz: float,
    dt: float,
    mass: float = 1.0,
) -> np.ndarray:
    """Half-step kinetic propagator via 3D FFT."""
    if mass <= 0.0:
        raise ValueError("mass must be positive")
    nx, ny, nz = psi.shape
    kx = (2.0 * np.pi * np.fft.fftfreq(nx, d=dx))[:, np.newaxis, np.newaxis]
    ky = (2.0 * np.pi * np.fft.fftfreq(ny, d=dy))[np.newaxis, :, np.newaxis]
    kz = (2.0 * np.pi * np.fft.fftfreq(nz, d=dz))[np.newaxis, np.newaxis, :]
    p2 = kx**2 + ky**2 + kz**2
    psi_k = np.fft.fftn(psi)
    phase = np.exp(-1j * p2 / (2.0 * mass) * (dt / 2.0))
    return np.fft.ifftn(phase * psi_k)


def potential_full_step_3d(
    psi: np.ndarray,
    v: np.ndarray,
    dt: float,
) -> np.ndarray:
    if v.shape != psi.shape:
        raise ValueError("V must match psi shape")
    return psi * np.exp(-1j * v * dt)


def split_step_evolve_3d(
    psi: np.ndarray,
    dx: float,
    dy: float,
    dz: float,
    dt: float,
    n_steps: int,
    v_xyz: np.ndarray,
    mass: float = 1.0,
) -> np.ndarray:
    """Strang split-step evolution for n_steps."""
    if n_steps < 1:
        raise ValueError("n_steps must be >= 1")
    out = psi.copy()
    for _ in range(n_steps):
        out = kinetic_half_step_3d(out, dx, dy, dz, dt, mass)
        out = potential_full_step_3d(out, v_xyz, dt)
        out = kinetic_half_step_3d(out, dx, dy, dz, dt, mass)
    return out


# ---------------------------------------------------------------------------
# Double-slit potential
# ---------------------------------------------------------------------------


def soft_double_slit_potential_3d(
    X: np.ndarray,
    Y: np.ndarray,
    Z: np.ndarray,
    v0: float,
    x_screen: float,
    slit_separation: float,
    slit_sigma: float,
    screen_sigma: float,
) -> np.ndarray:
    """Soft double-slit barrier in 3D.

    The screen is a Gaussian barrier in ``x`` centred at ``x_screen`` with
    width ``screen_sigma``.  Two circular openings are placed in the ``(y,z)``
    plane, separated along ``y`` by ``slit_separation``.
    """
    if v0 < 0.0:
        raise ValueError("v0 must be non-negative")
    if slit_separation <= 0.0 or slit_sigma <= 0.0 or screen_sigma <= 0.0:
        raise ValueError("slit_separation, slit_sigma, screen_sigma must be positive")
    # Screen profile in x
    screen = np.exp(-((X - x_screen) / screen_sigma) ** 2)
    # Two circular openings in (y, z) plane
    y1 = -slit_separation / 2.0
    y2 = slit_separation / 2.0
    r1_sq = (Y - y1) ** 2 + Z**2
    r2_sq = (Y - y2) ** 2 + Z**2
    g1 = np.exp(-r1_sq / slit_sigma**2)
    g2 = np.exp(-r2_sq / slit_sigma**2)
    openings = np.minimum(1.0, g1 + g2)
    return v0 * screen * (1.0 - openings)


# ---------------------------------------------------------------------------
# Absorption / PML masks
# ---------------------------------------------------------------------------


def _absorption_mask_1d(n: int, n_absorb: int, eta: float) -> np.ndarray:
    """Cosine-taper sponge mask for one dimension (same convention as 1D code)."""
    mask = np.ones(n, dtype=float)
    if n_absorb <= 0 or abs(eta) < 1e-15:
        return mask
    for j in range(n_absorb):
        val = eta * (1.0 - np.cos(np.pi * j / (2.0 * n_absorb))) ** 2
        mask[j] = 1.0 - val
        mask[n - 1 - j] = 1.0 - val
    return mask


def absorption_mask_3d(
    nx: int,
    ny: int,
    nz: int,
    n_absorb: int,
    eta: float,
) -> np.ndarray:
    """Separable 3D sponge mask: ``mask[i,j,k] = mx[i]*my[j]*mz[k]``."""
    mx = _absorption_mask_1d(nx, n_absorb, eta)
    my = _absorption_mask_1d(ny, n_absorb, eta)
    mz = _absorption_mask_1d(nz, n_absorb, eta)
    return (mx[:, np.newaxis, np.newaxis]
            * my[np.newaxis, :, np.newaxis]
            * mz[np.newaxis, np.newaxis, :])


def _pml_damping_1d(n: int, n_pml: int, sigma_max: float, dt: float, order: int = 3) -> np.ndarray:
    """PML damping mask for one dimension (replicates pattern from schrodinger_2d_pml)."""
    if n_pml <= 0 or sigma_max == 0.0:
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


def pml_damping_mask_3d(
    nx: int,
    ny: int,
    nz: int,
    n_pml: int,
    sigma_max: float,
    dt: float,
    order: int = 3,
) -> np.ndarray:
    """Separable 3D PML damping mask."""
    mx = _pml_damping_1d(nx, n_pml, sigma_max, dt, order)
    my = _pml_damping_1d(ny, n_pml, sigma_max, dt, order)
    mz = _pml_damping_1d(nz, n_pml, sigma_max, dt, order)
    return (mx[:, np.newaxis, np.newaxis]
            * my[np.newaxis, :, np.newaxis]
            * mz[np.newaxis, np.newaxis, :])


# ---------------------------------------------------------------------------
# CLI
# ---------------------------------------------------------------------------


def _parse_args() -> argparse.Namespace:
    p = argparse.ArgumentParser(description="3D split-step Schrödinger double slit (numpy).")
    p.add_argument("--lx", type=float, default=24.0)
    p.add_argument("--ly", type=float, default=24.0)
    p.add_argument("--lz", type=float, default=24.0)
    p.add_argument("--nx", type=int, default=32)
    p.add_argument("--ny", type=int, default=32)
    p.add_argument("--nz", type=int, default=32)
    p.add_argument("--t", type=float, default=1.0)
    p.add_argument("--steps", type=int, default=100)
    p.add_argument("--v0", type=float, default=20.0)
    p.add_argument("--x-screen", type=float, default=-2.0)
    p.add_argument("--slit-sep", type=float, default=2.0)
    p.add_argument("--slit-sigma", type=float, default=0.6)
    p.add_argument("--screen-sigma", type=float, default=0.5)
    p.add_argument("--x0", type=float, default=-8.0)
    p.add_argument("--y0", type=float, default=0.0)
    p.add_argument("--z0", type=float, default=0.0)
    p.add_argument("--kx0", type=float, default=2.0)
    p.add_argument("--ky0", type=float, default=0.0)
    p.add_argument("--kz0", type=float, default=0.0)
    p.add_argument("--sigma0", type=float, default=1.0)
    p.add_argument("--mass", type=float, default=1.0)
    p.add_argument("--n-absorb", type=int, default=6)
    p.add_argument("--eta", type=float, default=0.85)
    p.add_argument("--x-detect", type=float, default=4.0, help="x position of detection plane")
    p.add_argument(
        "--validate",
        action="store_true",
        help="Free propagation norm conservation check",
    )
    return p.parse_args()


def main() -> None:
    args = _parse_args()
    t0 = time.perf_counter()
    X, Y, Z, dx, dy, dz = make_grid_3d(args.lx, args.ly, args.lz,
                                        args.nx, args.ny, args.nz)
    psi0 = initial_gaussian_3d(X, Y, Z, args.x0, args.y0, args.z0,
                               args.kx0, args.ky0, args.kz0, args.sigma0)
    psi0 = psi0 / np.sqrt(norm_3d(psi0, dx, dy, dz))
    dt = args.t / args.steps
    n0 = norm_3d(psi0, dx, dy, dz)

    print(f"grid: {args.nx}x{args.ny}x{args.nz} = {args.nx * args.ny * args.nz} points")
    print(f"dx={dx:.4f}, dy={dy:.4f}, dz={dz:.4f}, dt={dt:.6f}")
    print(f"initial norm = {n0:.10f}")

    if args.validate:
        # Free propagation: V=0, no absorption
        v_zero = np.zeros_like(X, dtype=float)
        psi_free = split_step_evolve_3d(
            psi0, dx, dy, dz, dt, args.steps, v_zero, mass=args.mass,
        )
        n1 = norm_3d(psi_free, dx, dy, dz)
        elapsed = time.perf_counter() - t0
        print(f"free propagation: final norm = {n1:.10f}")
        print(f"  norm change = {abs(n1 - n0):.2e}")
        print(f"  elapsed = {elapsed:.2f}s")
        if abs(n1 - n0) > 1e-6:
            raise SystemExit(f"validate: norm not conserved ({n0:.10f} -> {n1:.10f})")
        print("validate: free propagation norm conservation OK")
        return

    # Double-slit evolution with absorption
    v_xyz = soft_double_slit_potential_3d(
        X, Y, Z,
        v0=args.v0,
        x_screen=args.x_screen,
        slit_separation=args.slit_sep,
        slit_sigma=args.slit_sigma,
        screen_sigma=args.screen_sigma,
    )
    mask = absorption_mask_3d(args.nx, args.ny, args.nz, args.n_absorb, args.eta)

    out = psi0.copy()
    for step in range(args.steps):
        out = kinetic_half_step_3d(out, dx, dy, dz, dt, args.mass)
        out = potential_full_step_3d(out, v_xyz, dt)
        out = kinetic_half_step_3d(out, dx, dy, dz, dt, args.mass)
        out *= mask

    n1 = norm_3d(out, dx, dy, dz)
    elapsed = time.perf_counter() - t0
    print(f"final norm = {n1:.10f} (norm loss = {1.0 - n1:.6f})")
    print(f"elapsed = {elapsed:.2f}s")

    # Save |psi|^2 on the (y,z) detection plane at x closest to x_detect
    xs_1d = X[:, 0, 0]
    i_detect = int(np.argmin(np.abs(xs_1d - args.x_detect)))
    x_actual = float(xs_1d[i_detect])
    rho_yz = density_3d(out)[i_detect, :, :]
    print(f"detection plane at x = {x_actual:.4f} (requested {args.x_detect:.4f})")

    csv_out = Path("sim/out/schrodinger_3d_double_slit_yz.csv")
    csv_out.parent.mkdir(parents=True, exist_ok=True)
    ys_1d = Y[0, :, 0]
    zs_1d = Z[0, 0, :]
    with csv_out.open("w", encoding="utf-8", newline="") as f:
        f.write("y,z,rho\n")
        for j in range(args.ny):
            for k in range(args.nz):
                f.write(f"{float(ys_1d[j]):.10g},{float(zs_1d[k]):.10g},{float(rho_yz[j, k]):.14g}\n")
    print(f"wrote {csv_out}")


if __name__ == "__main__":
    main()
