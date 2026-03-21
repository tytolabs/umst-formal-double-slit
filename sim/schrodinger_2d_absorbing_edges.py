#!/usr/bin/env python3
"""
2D split-step Schrödinger with **separable absorbing mask** (pedagogical sponge).

After each full Strang step, ψ is multiplied by ``m_x[i] * m_y[j]`` where ``m_x``,
``m_y`` are the same edge tapers as in ``schrodinger_1d_absorbing_edges.py``.

Reuses the soft double-slit potential and propagator pieces from
``schrodinger_2d_soft_double_slit.py``. **Requires NumPy.**

**Validate:** ``n_absorb_x = n_absorb_y = 0`` matches plain 2D split-step; a **corner-
localized** packet loses norm when sponge layers are enabled.

Default CSV matches the 2D heatmap plotter: ``x,y,rho`` → use
``plot_schrodinger_2d_soft_double_slit_svg.py --in …``.
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


def absorption_mask_2d(
    nx: int,
    ny: int,
    n_absorb_x: int,
    n_absorb_y: int,
    eta: float,
) -> np.ndarray:
    """Separable sponge: ``mask[i,j] = m_x[i] * m_y[j]``."""
    ab = _load_1d_absorb()
    mx = ab.absorption_mask(nx, n_absorb_x, eta)
    my = ab.absorption_mask(ny, n_absorb_y, eta)
    return mx[:, np.newaxis] * my[np.newaxis, :]


def split_step_evolve_2d_with_absorption(
    psi: np.ndarray,
    dx: float,
    dy: float,
    *,
    dt: float,
    n_steps: int,
    v_xy: np.ndarray,
    mask: np.ndarray,
    mass: float = 1.0,
) -> np.ndarray:
    m2 = _load_2d()
    if mask.shape != psi.shape:
        raise ValueError("mask shape must match psi")
    out = psi.copy()
    for _ in range(n_steps):
        out = m2.kinetic_half_step_2d(out, dx, dy, dt=dt, mass=mass)
        out = m2.potential_full_step(out, v_xy, dt)
        out = m2.kinetic_half_step_2d(out, dx, dy, dt=dt, mass=mass)
        out *= mask
    return out


def _parse_args() -> argparse.Namespace:
    p = argparse.ArgumentParser(description="2D soft slit + absorbing sponge (numpy).")
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
    p.add_argument("--n-absorb-x", type=int, default=36)
    p.add_argument("--n-absorb-y", type=int, default=36)
    p.add_argument("--eta", type=float, default=0.88)
    p.add_argument(
        "--validate",
        action="store_true",
        help="n_absorb=0 vs plain 2D split-step; corner packet norm drop",
    )
    return p.parse_args()


def main() -> None:
    args = _parse_args()
    m2 = _load_2d()
    X, Y, dx, dy = m2.make_grid_2d(args.lx, args.ly, args.nx, args.ny)
    psi0 = m2.initial_gaussian_2d(
        X,
        Y,
        x0=args.x0,
        y0=args.y0,
        kx0=args.kx0,
        ky0=args.ky0,
        sigma0=args.sigma0,
    )
    psi0 = psi0 / np.sqrt(m2.norm_dxy(psi0, dx, dy))
    dt = args.t / args.steps
    v_xy = m2.soft_double_slit_potential_2d(
        X,
        Y,
        v0=args.v0,
        x_screen=args.x_screen,
        slit_separation=args.slit_sep,
        slit_sigma=args.slit_sigma,
        slit_center_offset=args.slit_y_offset,
    )
    mask = absorption_mask_2d(args.nx, args.ny, args.n_absorb_x, args.n_absorb_y, args.eta)

    if args.validate:
        mask0 = absorption_mask_2d(args.nx, args.ny, 0, 0, args.eta)
        psi_a = split_step_evolve_2d_with_absorption(
            psi0,
            dx,
            dy,
            dt=dt,
            n_steps=args.steps,
            v_xy=v_xy,
            mask=mask0,
            mass=args.mass,
        )
        psi_b = m2.split_step_evolve_2d(
            psi0, dx, dy, dt=dt, n_steps=args.steps, v_xy=v_xy, mass=args.mass
        )
        err = float(np.max(np.abs(psi_a - psi_b)))
        if err > 1e-9:
            raise SystemExit(f"validate: zero-absorb mismatch max|Δψ|={err}")

        xs_1d = X[:, 0]
        ys_1d = Y[0, :]
        x_max = float(np.max(xs_1d))
        y_max = float(np.max(ys_1d))
        psi_c = m2.initial_gaussian_2d(
            X,
            Y,
            x0=x_max - 1.5,
            y0=y_max - 1.5,
            kx0=0.55,
            ky0=0.45,
            sigma0=0.38,
        )
        psi_c = psi_c / np.sqrt(m2.norm_dxy(psi_c, dx, dy))
        n_ax = min(28, max(12, args.nx // 14))
        n_ay = min(28, max(12, args.ny // 14))
        mask_c = absorption_mask_2d(args.nx, args.ny, n_ax, n_ay, 0.72)
        psi_d = split_step_evolve_2d_with_absorption(
            psi_c,
            dx,
            dy,
            dt=dt,
            n_steps=args.steps,
            v_xy=v_xy,
            mask=mask_c,
            mass=args.mass,
        )
        n0 = m2.norm_dxy(psi_c, dx, dy)
        n1 = m2.norm_dxy(psi_d, dx, dy)
        if n1 >= n0 - 1e-4:
            raise SystemExit(
                f"validate: expected norm drop with 2D sponge, got {n0} -> {n1} (try more --steps)"
            )
        print(f"validate: zero-absorb match OK; corner sponge norm {n0:.6f} -> {n1:.6f}")

    psi = split_step_evolve_2d_with_absorption(
        psi0,
        dx,
        dy,
        dt=dt,
        n_steps=args.steps,
        v_xy=v_xy,
        mask=mask,
        mass=args.mass,
    )
    out = Path("sim/out/schrodinger_2d_absorbing_edges_rho.csv")
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
