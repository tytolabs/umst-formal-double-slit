#!/usr/bin/env python3
# SPDX-License-Identifier: MIT
# Copyright (c) 2026 Santhosh Shyamsundar, Santosh Prabhu Shenbagamoorthy — Studio TYTO

"""
Optional **QuTiP** vs **SciPy** parity for **2D soft slit** on a **small FD grid**.

Hamiltonian (periodic finite-difference Laplacian + diagonal potential):

  ``H = T_FD + diag(V_flat)``

where ``V(x,y)`` is **`soft_double_slit_potential_2d`** from
``schrodinger_2d_soft_double_slit.py`` — the **same** discrete values NumPy uses on
the tensor grid. **Kinetic** matches ``qutip_schrodinger_2d_free_parity`` (FD), not
the split-step **FFT** kinetic; use this script to validate QuTiP wiring for
**nonzero V**, not to match ``split_step_evolve_2d`` exactly.

**Requires** ``qutip`` and ``scipy``. See ``sim/tests/test_qutip_2d_slit_parity.py``.
"""

from __future__ import annotations

import importlib.util
from pathlib import Path
from typing import Tuple

import numpy as np


def have_qutip() -> bool:
    try:
        import qutip  # noqa: F401

        return True
    except ImportError:
        return False


def _load_free_parity():
    here = Path(__file__).resolve().parent
    spec = importlib.util.spec_from_file_location(
        "qutip_schrodinger_2d_free_parity",
        here / "qutip_schrodinger_2d_free_parity.py",
    )
    mod = importlib.util.module_from_spec(spec)
    assert spec and spec.loader
    spec.loader.exec_module(mod)
    return mod


def _load_schrodinger_2d():
    here = Path(__file__).resolve().parent
    spec = importlib.util.spec_from_file_location(
        "schrodinger_2d_soft_double_slit",
        here / "schrodinger_2d_soft_double_slit.py",
    )
    mod = importlib.util.module_from_spec(spec)
    assert spec and spec.loader
    spec.loader.exec_module(mod)
    return mod


def hamiltonian_soft_slit_fd(
    nx: int,
    ny: int,
    lx: float,
    ly: float,
    *,
    mass: float = 1.0,
    v0: float = 12.0,
    x_screen: float = -2.0,
    slit_separation: float = 1.4,
    slit_sigma: float = 0.32,
    slit_center_offset: float = 0.0,
) -> Tuple[np.ndarray, np.ndarray, float, float]:
    """
    Return (H, psi0_flat, dx, dy) with psi0 normalized on the grid.

    ``nx``, ``ny`` must be even and >= 8 (shared grid convention).
    """
    if nx % 2 != 0 or ny % 2 != 0 or nx < 8 or ny < 8:
        raise ValueError("nx and ny must be even integers >= 8")
    if mass <= 0.0 or lx <= 0.0 or ly <= 0.0:
        raise ValueError("invalid box or mass")
    dx = lx / nx
    dy = ly / ny
    fp = _load_free_parity()
    m2 = _load_schrodinger_2d()
    X, Y, _, _ = m2.make_grid_2d(lx, ly, nx, ny)
    V = m2.soft_double_slit_potential_2d(
        X,
        Y,
        v0=v0,
        x_screen=x_screen,
        slit_separation=slit_separation,
        slit_sigma=slit_sigma,
        slit_center_offset=slit_center_offset,
    )
    T = fp.hamiltonian_free_2d_periodic(nx, ny, dx, dy, mass=mass)
    vf = V.ravel(order="C")
    H = T + np.diag(vf.astype(np.complex128))
    psi2 = m2.initial_gaussian_2d(
        X,
        Y,
        x0=-lx * 0.22,
        y0=0.15,
        kx0=0.75,
        ky0=-0.08,
        sigma0=0.82,
    )
    psi2 = psi2 / np.sqrt(m2.norm_dxy(psi2, dx, dy))
    psi0 = psi2.ravel(order="C")
    return H, psi0, dx, dy


def run_slit_parity(
    *,
    nx: int = 12,
    ny: int = 10,
    t: float = 0.22,
    mass: float = 1.0,
    v0: float = 14.0,
) -> Tuple[float, float]:
    """Return (max_abs_diff_psi, sum|psi_qt|^2)."""
    fp = _load_free_parity()
    lx, ly = float(nx), float(ny)
    H, psi0, _, _ = hamiltonian_soft_slit_fd(
        nx,
        ny,
        lx,
        ly,
        mass=mass,
        v0=v0,
    )
    ps = fp.evolve_scipy_expm(H, psi0, t)
    pq = fp.evolve_qutip_sesolve(H, psi0, t)
    diff = float(np.max(np.abs(ps - pq)))
    nrm = float(np.sum(np.abs(pq) ** 2))
    return diff, nrm


def split_step_vs_fd_density_gap(
    *,
    nx: int = 16,
    ny: int = 16,
    t: float = 0.18,
    mass: float = 1.0,
    v0: float = 10.0,
    n_steps: int = 36,
) -> float:
    """
    Diagnostic: max relative |ρ_splitstep - ρ_FD| (different kinetic discretizations).
    """
    fp = _load_free_parity()
    m2 = _load_schrodinger_2d()
    lx, ly = float(nx), float(ny)
    dx = lx / nx
    dy = ly / ny
    X, Y, _, _ = m2.make_grid_2d(lx, ly, nx, ny)
    V = m2.soft_double_slit_potential_2d(
        X,
        Y,
        v0=v0,
        x_screen=-2.0,
        slit_separation=1.4,
        slit_sigma=0.32,
    )
    psi0 = m2.initial_gaussian_2d(
        X,
        Y,
        x0=-lx * 0.22,
        y0=0.15,
        kx0=0.75,
        ky0=-0.08,
        sigma0=0.82,
    )
    psi0 = psi0 / np.sqrt(m2.norm_dxy(psi0, dx, dy))
    dt = t / n_steps
    psi_ss = m2.split_step_evolve_2d(
        psi0, dx, dy, dt=dt, n_steps=n_steps, v_xy=V, mass=mass
    )
    rho_ss = m2.density(psi_ss).ravel(order="C")
    H, p0, _, _ = hamiltonian_soft_slit_fd(
        nx, ny, lx, ly, mass=mass, v0=v0,
        x_screen=-2.0,
        slit_separation=1.4,
        slit_sigma=0.32,
    )
    psif = fp.evolve_scipy_expm(H, p0, t)
    rho_fd = np.abs(psif) ** 2
    den = np.maximum(rho_ss, 1e-15)
    return float(np.max(np.abs(rho_ss - rho_fd) / den))


def main() -> None:
    import argparse

    p = argparse.ArgumentParser(description="QuTiP vs scipy 2D soft-slit FD parity.")
    p.add_argument("--nx", type=int, default=12)
    p.add_argument("--ny", type=int, default=10)
    p.add_argument("--t", type=float, default=0.22)
    p.add_argument("--v0", type=float, default=14.0)
    p.add_argument(
        "--diagnostic-ss-fd",
        action="store_true",
        help="print split-step vs FD density gap (expected nonzero)",
    )
    args = p.parse_args()
    if not have_qutip():
        raise SystemExit("qutip not installed (pip install -r sim/requirements-optional.txt)")
    d, nrm = run_slit_parity(nx=args.nx, ny=args.ny, t=args.t, v0=args.v0)
    print(f"slit parity max|psi_qt - psi_scipy| = {d:.3e},  sum|psi|^2 ~ {nrm:.6f}")
    if d > 1e-5:
        raise SystemExit("slit parity check failed")
    if args.diagnostic_ss_fd:
        g = split_step_vs_fd_density_gap()
        print(f"diagnostic max rel |rho_splitstep - rho_fd| ~ {g:.3e}")


if __name__ == "__main__":
    main()
