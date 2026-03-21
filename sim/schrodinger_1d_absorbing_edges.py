#!/usr/bin/env python3
"""
1D split-step propagation with a simple **absorbing edge mask** (pedagogical).

After each full Strang step, ψ is multiplied by a real taper that is **1** in the
bulk and drops to **η ∈ (0,1]** in the outermost `n_absorb` cells on **each**
side. This is **not** a physical perfectly absorbing boundary; it removes
probability mass to mimic outgoing radiation on a finite periodic grid.

**Requires NumPy.** Reuses `schrodinger_1d_split_step.split_step_evolve` for one
Strang step at a time.
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


def absorption_mask(n: int, n_absorb: int, eta: float) -> np.ndarray:
    """
    Length-`n` real multipliers in `[eta, 1]`, symmetric, unity in the interior.

    Left edge: cells `0 .. n_absorb-1` linearly ramp from `eta` to `1`.
    Right edge: mirror. If `n_absorb == 0`, all ones.
    """
    if n < 4:
        raise ValueError("n must be at least 4")
    if not (0.0 < eta <= 1.0):
        raise ValueError("eta must lie in (0, 1]")
    if n_absorb < 0:
        raise ValueError("n_absorb must be non-negative")
    m = np.ones(n, dtype=float)
    if n_absorb == 0:
        return m
    if 2 * n_absorb > n:
        raise ValueError("n_absorb too large for grid")
    for j in range(n_absorb):
        t = float(j) / float(max(n_absorb - 1, 1))
        fac = eta + (1.0 - eta) * t
        m[j] = min(m[j], fac)
        m[n - 1 - j] = min(m[n - 1 - j], fac)
    return m


def split_step_evolve_with_absorption(
    psi: np.ndarray,
    dx: float,
    *,
    dt: float,
    n_steps: int,
    v_x: np.ndarray,
    mask: np.ndarray,
    mass: float = 1.0,
) -> np.ndarray:
    """One Strang step per iteration, then multiply by `mask`."""
    sp = _load_split()
    if mask.shape != psi.shape:
        raise ValueError("mask shape must match psi")
    out = psi.copy()
    for _ in range(n_steps):
        out = sp.split_step_evolve(out, dx, dt=dt, n_steps=1, v_x=v_x, mass=mass)
        out *= mask
    return out


def _parse_args() -> argparse.Namespace:
    p = argparse.ArgumentParser(description="Split-step with absorbing edge mask.")
    p.add_argument("--length", type=float, default=40.0)
    p.add_argument("-n", "--points", type=int, default=2048, dest="n")
    p.add_argument("--t", type=float, default=1.2)
    p.add_argument("--steps", type=int, default=240)
    p.add_argument("--n-absorb", type=int, default=48)
    p.add_argument("--eta", type=float, default=0.88)
    p.add_argument("--v0", type=float, default=0.0)
    p.add_argument("--xb", type=float, default=3.0)
    p.add_argument("--barrier-width", type=float, default=0.55, dest="bw")
    p.add_argument("--x0", type=float, default=-7.0)
    p.add_argument("--k0", type=float, default=1.1)
    p.add_argument("--sigma0", type=float, default=1.0)
    p.add_argument(
        "--validate",
        action="store_true",
        help="n_absorb=0 matches plain split-step; with absorption norm decreases.",
    )
    return p.parse_args()


def main() -> None:
    args = _parse_args()
    sp = _load_split()
    ff = _load_fft()
    xs, dx = ff.make_grid(args.length, args.n)
    v_x = sp.gaussian_barrier(xs, v0=args.v0, xb=args.xb, width=args.bw) if args.v0 != 0.0 else np.zeros_like(xs)
    psi0 = ff.initial_gaussian(xs, x0=args.x0, k0=args.k0, sigma0=args.sigma0)
    psi0 = psi0 / np.sqrt(ff.norm_dx(psi0, dx))
    dt = args.t / args.steps
    mask = absorption_mask(args.n, args.n_absorb, args.eta)

    if args.validate:
        # n_absorb = 0 => mask all ones => must match split_step_evolve
        mask0 = absorption_mask(args.n, 0, args.eta)
        psi_a = split_step_evolve_with_absorption(
            psi0, dx, dt=dt, n_steps=args.steps, v_x=v_x, mask=mask0
        )
        psi_b = sp.split_step_evolve(psi0, dx, dt=dt, n_steps=args.steps, v_x=v_x)
        err = float(np.max(np.abs(psi_a - psi_b)))
        if err > 1e-10:
            raise SystemExit(f"validate: zero-absorb mismatch max|Δψ|={err}")
        # Localize near a boundary so the edge mask removes mass (bulk packet may never visit edges).
        x_right = float(xs[-1])
        psi_edge = ff.initial_gaussian(
            xs, x0=x_right - 1.8, k0=0.6, sigma0=0.42
        )
        psi_edge = psi_edge / np.sqrt(ff.norm_dx(psi_edge, dx))
        n_sp = min(120, max(40, args.n // 12))
        mask_s = absorption_mask(args.n, n_sp, 0.72)
        psi_c = split_step_evolve_with_absorption(
            psi_edge, dx, dt=dt, n_steps=args.steps, v_x=v_x, mask=mask_s
        )
        n0e = ff.norm_dx(psi_edge, dx)
        n1e = ff.norm_dx(psi_c, dx)
        if n1e >= n0e - 1e-4:
            raise SystemExit(
                f"validate: expected norm drop with absorption, got {n0e} -> {n1e} (try more --steps)"
            )
        print(f"validate: zero-absorb match OK; edge-packet sponge norm {n0e:.6f} -> {n1e:.6f}")

    psi_t = split_step_evolve_with_absorption(
        psi0, dx, dt=dt, n_steps=args.steps, v_x=v_x, mask=mask
    )
    out = Path("sim/out/schrodinger_absorbing_edges_rho.csv")
    out.parent.mkdir(parents=True, exist_ok=True)
    rho = ff.density(psi_t)
    with out.open("w", encoding="utf-8", newline="") as f:
        f.write("x,rho\n")
        for x, r in zip(xs, rho):
            f.write(f"{float(x):.10g},{float(r):.14g}\n")
    print(f"wrote {out}")


if __name__ == "__main__":
    main()
