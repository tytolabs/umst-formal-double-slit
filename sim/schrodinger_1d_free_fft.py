#!/usr/bin/env python3
# SPDX-License-Identifier: MIT
# Copyright (c) 2026 Santhosh Shyamsundar, Santosh Prabhu Shenbagamoorthy — Studio TYTO

"""
Free 1D Schrödinger propagation on a periodic grid via FFT (V = 0).

Units: ħ = 1, m = 1.  Evolves ψ with exp(-i T p²/(2m)) in momentum space.

**Requires NumPy** (install via `pip install -r sim/requirements-optional.txt`;
matplotlib pulls NumPy in CI).

Cross-check: compare |ψ(x,T)|² to the closed form in `spatial_free_gaussian_1d.py`
for a minimum-uncertainty Gaussian initial state.
"""

from __future__ import annotations

import argparse
import importlib.util
from pathlib import Path

import numpy as np


def _load_closed_form():
    here = Path(__file__).resolve().parent
    script = here / "spatial_free_gaussian_1d.py"
    spec = importlib.util.spec_from_file_location("spatial_free_gaussian_1d", script)
    mod = importlib.util.module_from_spec(spec)
    assert spec and spec.loader
    spec.loader.exec_module(mod)
    return mod


def make_grid(length: float, n: int) -> tuple[np.ndarray, float]:
    if n < 8 or n % 2 != 0:
        raise ValueError("n must be an even integer >= 8")
    if length <= 0.0:
        raise ValueError("length must be positive")
    dx = length / n
    xs = np.linspace(-length / 2.0 + dx / 2.0, length / 2.0 - dx / 2.0, n)
    return xs, dx


def initial_gaussian(
    xs: np.ndarray,
    *,
    x0: float = 0.0,
    k0: float = 0.0,
    sigma0: float = 1.0,
) -> np.ndarray:
    """Minimum-uncertainty Gaussian (same convention as Griffiths, ħ=m=1)."""
    if sigma0 <= 0.0:
        raise ValueError("sigma0 must be positive")
    norm = (2.0 * np.pi * sigma0**2) ** (-0.25)
    return norm * np.exp(-((xs - x0) ** 2) / (4.0 * sigma0**2) + 1j * k0 * xs)


def propagate_free_fft(
    psi: np.ndarray,
    dx: float,
    *,
    mass: float = 1.0,
    total_time: float,
) -> np.ndarray:
    """One-shot free evolution for time `total_time` (periodic boundary)."""
    if mass <= 0.0:
        raise ValueError("mass must be positive")
    n = psi.shape[0]
    k = 2.0 * np.pi * np.fft.fftfreq(n, d=dx)
    psi_k = np.fft.fft(psi)
    phase = np.exp(-1j * (k**2) / (2.0 * mass) * total_time)
    out = np.fft.ifft(phase * psi_k)
    return out


def density(psi: np.ndarray) -> np.ndarray:
    return np.real(np.conjugate(psi) * psi)


def norm_dx(psi: np.ndarray, dx: float) -> float:
    return float(np.sum(density(psi)) * dx)


def max_abs_rel_err(
    rho_num: np.ndarray,
    rho_ref: np.ndarray,
    *,
    eps: float = 1e-15,
) -> float:
    den = np.maximum(np.abs(rho_ref), eps)
    return float(np.max(np.abs(rho_num - rho_ref) / den))


def run_case(
    *,
    length: float,
    n: int,
    t: float,
    x0: float,
    k0: float,
    sigma0: float,
) -> tuple[float, float]:
    """
    Return (norm_after, max_relative_error_vs_closed_form) for |psi|^2.
    """
    cf = _load_closed_form()
    xs, dx = make_grid(length, n)
    psi0 = initial_gaussian(xs, x0=x0, k0=k0, sigma0=sigma0)
    psi0 = psi0 / np.sqrt(norm_dx(psi0, dx))
    psi_t = propagate_free_fft(psi0, dx, total_time=t)
    rho_n = density(psi_t)
    rho_a = np.array([cf.density(float(x), t, x0=x0, k0=k0, sigma0=sigma0) for x in xs])
    nrm = norm_dx(psi_t, dx)
    err = max_abs_rel_err(rho_n, rho_a)
    return nrm, err


def _parse_args() -> argparse.Namespace:
    p = argparse.ArgumentParser(description="Free 1D Schrödinger FFT propagation (numpy).")
    p.add_argument("--length", type=float, default=40.0, help="Periodic box length L (default 40).")
    p.add_argument("-n", "--points", type=int, default=2048, dest="n", help="Grid points (even, default 2048).")
    p.add_argument("--t", type=float, default=1.0, help="Evolution time (default 1).")
    p.add_argument("--x0", type=float, default=0.0)
    p.add_argument("--k0", type=float, default=0.0)
    p.add_argument("--sigma0", type=float, default=1.0)
    p.add_argument(
        "--validate",
        action="store_true",
        help="Check normalization and agreement with spatial_free_gaussian_1d.",
    )
    p.add_argument(
        "--out",
        type=str,
        default=None,
        help="Optional CSV path x, rho_num, rho_analytic",
    )
    return p.parse_args()


def main() -> None:
    args = _parse_args()
    cf = _load_closed_form()
    xs, dx = make_grid(args.length, args.n)
    psi0 = initial_gaussian(xs, x0=args.x0, k0=args.k0, sigma0=args.sigma0)
    psi0 = psi0 / np.sqrt(norm_dx(psi0, dx))
    psi_t = propagate_free_fft(psi0, dx, total_time=args.t)
    rho_n = density(psi_t)
    rho_a = np.array(
        [
            cf.density(float(x), args.t, x0=args.x0, k0=args.k0, sigma0=args.sigma0)
            for x in xs
        ]
    )

    if args.validate:
        nrm = norm_dx(psi_t, dx)
        if abs(nrm - 1.0) > 1e-4:
            raise SystemExit(f"validate: norm integral ~ {nrm}, expected ~1")
        err = max_abs_rel_err(rho_n, rho_a)
        if err > 0.02:
            raise SystemExit(
                f"validate: max rel err vs closed form {err} (increase --length/-n or reduce --t)"
            )
        print(f"validate: norm~{nrm:.6f}, max_rel_err~{err:.6f}")

    if args.out:
        out_path = Path(args.out)
        out_path.parent.mkdir(parents=True, exist_ok=True)
        with out_path.open("w", encoding="utf-8", newline="") as f:
            f.write("x,rho_fft,rho_closed_form\n")
            for x, a, b in zip(xs, rho_n, rho_a):
                f.write(f"{float(x):.10g},{float(a):.14g},{float(b):.14g}\n")
        print(f"wrote {out_path}")


if __name__ == "__main__":
    main()
