#!/usr/bin/env python3
"""
Strang split-step 1D Schrödinger on a periodic grid: K(dt/2) V(dt) K(dt/2).

Units: ħ = 1.  Real potential V(x) applied in position space; kinetic factor
exp(-i p²/(2m) · dt/2) in momentum space (FFT).

**Requires NumPy.** For **V = 0**, n_steps with step dt = T/n_steps reproduces the
single-step propagator in `schrodinger_1d_free_fft.py` (up to floating-point noise).

Example soft barrier: Gaussian bump V(x) = V₀ exp(-((x-x_b)/w)²).
"""

from __future__ import annotations

import argparse
import importlib.util
from pathlib import Path

import numpy as np


def _load_free_fft():
    here = Path(__file__).resolve().parent
    script = here / "schrodinger_1d_free_fft.py"
    spec = importlib.util.spec_from_file_location("schrodinger_1d_free_fft", script)
    mod = importlib.util.module_from_spec(spec)
    assert spec and spec.loader
    spec.loader.exec_module(mod)
    return mod


def kinetic_half_step(
    psi: np.ndarray,
    dx: float,
    *,
    dt: float,
    mass: float = 1.0,
) -> np.ndarray:
    if mass <= 0.0:
        raise ValueError("mass must be positive")
    n = psi.shape[0]
    k = 2.0 * np.pi * np.fft.fftfreq(n, d=dx)
    psi_k = np.fft.fft(psi)
    phase = np.exp(-1j * (k**2) / (2.0 * mass) * (dt / 2.0))
    return np.fft.ifft(phase * psi_k)


def potential_full_step(psi: np.ndarray, v_x: np.ndarray, dt: float) -> np.ndarray:
    if v_x.shape != psi.shape:
        raise ValueError("v_x must match psi shape")
    return psi * np.exp(-1j * v_x * dt)


def split_step_evolve(
    psi: np.ndarray,
    dx: float,
    *,
    dt: float,
    n_steps: int,
    v_x: np.ndarray,
    mass: float = 1.0,
) -> np.ndarray:
    """Strang splitting for `n_steps` steps (each of duration `dt`)."""
    if n_steps < 1:
        raise ValueError("n_steps must be >= 1")
    out = psi.copy()
    for _ in range(n_steps):
        out = kinetic_half_step(out, dx, dt=dt, mass=mass)
        out = potential_full_step(out, v_x, dt)
        out = kinetic_half_step(out, dx, dt=dt, mass=mass)
    return out


def gaussian_barrier(xs: np.ndarray, *, v0: float, xb: float, width: float) -> np.ndarray:
    if width <= 0.0:
        raise ValueError("width must be positive")
    return v0 * np.exp(-((xs - xb) / width) ** 2)


def _parse_args() -> argparse.Namespace:
    p = argparse.ArgumentParser(description="Split-step 1D Schrödinger (numpy).")
    p.add_argument("--length", type=float, default=40.0)
    p.add_argument("-n", "--points", type=int, default=2048, dest="n")
    p.add_argument("--t", type=float, default=1.0, help="Total time")
    p.add_argument("--steps", type=int, default=200, help="Number of Strang steps")
    p.add_argument("--v0", type=float, default=0.0, help="Gaussian barrier height (0 => free)")
    p.add_argument("--xb", type=float, default=4.0, help="Barrier center")
    p.add_argument("--barrier-width", type=float, default=0.6, dest="bw")
    p.add_argument("--x0", type=float, default=-6.0, help="Initial packet center")
    p.add_argument("--k0", type=float, default=1.2, help="Initial momentum")
    p.add_argument("--sigma0", type=float, default=1.0)
    p.add_argument(
        "--validate",
        action="store_true",
        help="V=0: match free FFT; V>0: check norm ~ 1",
    )
    return p.parse_args()


def main() -> None:
    args = _parse_args()
    ff = _load_free_fft()
    xs, dx = ff.make_grid(args.length, args.n)
    psi0 = ff.initial_gaussian(xs, x0=args.x0, k0=args.k0, sigma0=args.sigma0)
    psi0 = psi0 / np.sqrt(ff.norm_dx(psi0, dx))
    dt = args.t / args.steps
    v_x = gaussian_barrier(xs, v0=args.v0, xb=args.xb, width=args.bw)
    psi_ss = split_step_evolve(psi0, dx, dt=dt, n_steps=args.steps, v_x=v_x)

    if args.validate:
        if args.v0 == 0.0:
            psi_ref = ff.propagate_free_fft(psi0, dx, total_time=args.t)
            err = ff.max_abs_rel_err(ff.density(psi_ss), ff.density(psi_ref))
            nrm = ff.norm_dx(psi_ss, dx)
            if abs(nrm - 1.0) > 1e-4:
                raise SystemExit(f"validate: norm ~ {nrm}, expected ~1")
            if err > 1e-6:
                raise SystemExit(f"validate: split-step != free FFT, max rel err {err}")
            print(f"validate V=0: norm~{nrm:.8f}, max_rel_err_vs_fft~{err:.3e}")
        else:
            nrm = ff.norm_dx(psi_ss, dx)
            if abs(nrm - 1.0) > 1e-3:
                raise SystemExit(f"validate: norm ~ {nrm} with barrier")
            print(f"validate barrier: norm~{nrm:.6f} (unitarity smoke)")

    out = Path("sim/out/schrodinger_split_step_rho.csv")
    out.parent.mkdir(parents=True, exist_ok=True)
    rho = ff.density(psi_ss)
    with out.open("w", encoding="utf-8", newline="") as f:
        f.write("x,rho\n")
        for x, r in zip(xs, rho):
            f.write(f"{float(x):.10g},{float(r):.14g}\n")
    print(f"wrote {out}")


if __name__ == "__main__":
    main()
