#!/usr/bin/env python3
"""
Benchmark: **2D split-step (FFT kinetic)** vs **one-shot FD + expm** for the soft slit.

- **Split-step:** ``schrodinger_2d_soft_double_slit.split_step_evolve_2d`` (same as production sim).
- **FD reference:** periodic Laplacian + diagonal ``V`` from ``soft_double_slit_potential_2d``,
  then ``scipy.linalg.expm(-1j H t)`` on the flattened state (small grids only).

Prints wall times and **max relative** ``|ρ_ss - ρ_fd| / max(ρ_ss, ε)``. Large gaps are
expected on coarse grids (different kinetic discretizations).

**Requires** NumPy + SciPy. Not part of ``make sim``. See unittest when SciPy is installed.
"""

from __future__ import annotations

import importlib.util
import json
import time
from pathlib import Path
from typing import Any, Dict, Tuple

import numpy as np


def _load_2d():
    here = Path(__file__).resolve().parent
    spec = importlib.util.spec_from_file_location(
        "schrodinger_2d_soft_double_slit",
        here / "schrodinger_2d_soft_double_slit.py",
    )
    mod = importlib.util.module_from_spec(spec)
    assert spec and spec.loader
    spec.loader.exec_module(mod)
    return mod


def _load_fd_h():
    here = Path(__file__).resolve().parent
    spec = importlib.util.spec_from_file_location(
        "qutip_schrodinger_2d_free_parity",
        here / "qutip_schrodinger_2d_free_parity.py",
    )
    mod = importlib.util.module_from_spec(spec)
    assert spec and spec.loader
    spec.loader.exec_module(mod)
    return mod


def compare_split_step_vs_fd(
    *,
    nx: int,
    ny: int,
    lx: float,
    ly: float,
    t: float,
    n_steps: int,
    mass: float = 1.0,
    v0: float = 12.0,
    x_screen: float = -2.0,
    slit_separation: float = 1.4,
    slit_sigma: float = 0.32,
) -> Tuple[float, float, float, float]:
    """
    Return (max_rel_rho_gap, seconds_split_step, seconds_fd_expm, norm_split_step).

    ``nx``, ``ny`` must be even and >= 8.
    """
    if nx % 2 != 0 or ny % 2 != 0 or nx < 8 or ny < 8:
        raise ValueError("nx and ny must be even integers >= 8")
    from scipy.linalg import expm

    m2 = _load_2d()
    fd = _load_fd_h()
    dx = lx / nx
    dy = ly / ny
    X, Y, _, _ = m2.make_grid_2d(lx, ly, nx, ny)
    V = m2.soft_double_slit_potential_2d(
        X,
        Y,
        v0=v0,
        x_screen=x_screen,
        slit_separation=slit_separation,
        slit_sigma=slit_sigma,
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

    t0 = time.perf_counter()
    psi_ss = m2.split_step_evolve_2d(
        psi0, dx, dy, dt=dt, n_steps=n_steps, v_xy=V, mass=mass
    )
    t_split = time.perf_counter() - t0

    T = fd.hamiltonian_free_2d_periodic(nx, ny, dx, dy, mass=mass)
    vf = V.ravel(order="C")
    H = T + np.diag(vf.astype(np.complex128))
    p0 = psi0.ravel(order="C")
    t1 = time.perf_counter()
    psif = expm(-1j * H * t) @ p0
    t_fd = time.perf_counter() - t1

    rho_ss = m2.density(psi_ss).ravel(order="C")
    rho_fd = np.abs(psif) ** 2
    den = np.maximum(rho_ss, 1e-15)
    gap = float(np.max(np.abs(rho_ss - rho_fd) / den))
    nrm = m2.norm_dxy(psi_ss, dx, dy)
    return gap, t_split, t_fd, float(nrm)


def main() -> None:
    import argparse

    p = argparse.ArgumentParser(
        description="Benchmark 2D split-step vs FD+expm (soft slit, small grid)."
    )
    p.add_argument("--nx", type=int, default=24)
    p.add_argument("--ny", type=int, default=24)
    p.add_argument("--lx", type=float, default=None, help="default: nx")
    p.add_argument("--ly", type=float, default=None, help="default: ny")
    p.add_argument("--t", type=float, default=0.35)
    p.add_argument("--steps", type=int, default=70)
    p.add_argument("--v0", type=float, default=12.0)
    p.add_argument("--json", action="store_true", help="print one JSON object")
    args = p.parse_args()
    lx = float(args.nx) if args.lx is None else args.lx
    ly = float(args.ny) if args.ly is None else args.ly
    gap, ts, tf, nrm = compare_split_step_vs_fd(
        nx=args.nx,
        ny=args.ny,
        lx=lx,
        ly=ly,
        t=args.t,
        n_steps=args.steps,
        v0=args.v0,
    )
    if args.json:
        out: Dict[str, Any] = {
            "nx": args.nx,
            "ny": args.ny,
            "t": args.t,
            "steps": args.steps,
            "v0": args.v0,
            "max_rel_rho_gap": gap,
            "seconds_split_step": ts,
            "seconds_fd_expm": tf,
            "norm_split_step": nrm,
        }
        print(json.dumps(out, indent=2))
    else:
        print(
            f"grid {args.nx}x{args.ny}  t={args.t}  steps={args.steps}  v0={args.v0}\n"
            f"  max_rel_rho_gap  {gap:.6e}\n"
            f"  time split-step  {ts:.6f} s\n"
            f"  time FD expm      {tf:.6f} s\n"
            f"  norm (split-step) {nrm:.8f}"
        )


if __name__ == "__main__":
    main()
