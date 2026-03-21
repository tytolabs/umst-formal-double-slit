#!/usr/bin/env python3
"""
Optional **QuTiP** vs **SciPy matrix exponential** parity for **2D free** evolution
(periodic finite-difference Laplacian, ħ = 1).

Validates that ``qutip.sesolve`` agrees with ``scipy.linalg.expm(-1j * H * t)`` on the
same dense Hamiltonian — a lightweight **spatial dynamics** hook before heavier QuTiP
experiments.

**Requires** ``qutip`` and ``scipy`` (pulled in by QuTiP). Not used in default ``make sim``.

See ``sim/tests/test_qutip_2d_free_parity.py``.
"""

from __future__ import annotations

import importlib.util
from pathlib import Path
from typing import Any, Tuple

import numpy as np


def have_qutip() -> bool:
    try:
        import qutip  # noqa: F401

        return True
    except ImportError:
        return False


def periodic_laplacian_1d(n: int, dx: float) -> np.ndarray:
    """1D periodic second-difference operator / dx² (real symmetric)."""
    if n < 3 or dx <= 0.0:
        raise ValueError("invalid grid")
    inv_dx2 = 1.0 / (dx * dx)
    L = np.zeros((n, n), dtype=float)
    for i in range(n):
        L[i, i] = -2.0 * inv_dx2
        L[i, (i + 1) % n] += inv_dx2
        L[i, (i - 1) % n] += inv_dx2
    return L


def hamiltonian_free_2d_periodic(
    nx: int,
    ny: int,
    dx: float,
    dy: float,
    *,
    mass: float = 1.0,
) -> np.ndarray:
    """
    H = -(1/(2m)) ( Δ_x ⊗ I_y + I_x ⊗ Δ_y ) on a tensor grid, C-order vec index i*ny+j.
    """
    if mass <= 0.0:
        raise ValueError("mass must be positive")
    lx = periodic_laplacian_1d(nx, dx)
    ly = periodic_laplacian_1d(ny, dy)
    ix = np.eye(nx)
    iy = np.eye(ny)
    lap2d = np.kron(lx, iy) + np.kron(ix, ly)
    return (-1.0 / (2.0 * mass)) * lap2d


def initial_gaussian_flat(
    nx: int,
    ny: int,
    dx: float,
    dy: float,
    *,
    x0: float,
    y0: float,
    kx0: float,
    ky0: float,
    sigma0: float,
) -> np.ndarray:
    """Separable minimum-uncertainty Gaussian, flattened C-order (i slow, j fast)."""
    here = Path(__file__).resolve().parent
    spec = importlib.util.spec_from_file_location("schrodinger_2d_soft_double_slit", here / "schrodinger_2d_soft_double_slit.py")
    mod = importlib.util.module_from_spec(spec)
    assert spec and spec.loader
    spec.loader.exec_module(mod)
    X, Y, _, _ = mod.make_grid_2d(nx * dx, ny * dy, nx, ny)
    psi2 = mod.initial_gaussian_2d(X, Y, x0=x0, y0=y0, kx0=kx0, ky0=ky0, sigma0=sigma0)
    nrm = np.sqrt(mod.norm_dxy(psi2, dx, dy))
    psi2 = psi2 / nrm
    return psi2.ravel(order="C")


def evolve_scipy_expm(
    H: np.ndarray,
    psi0: np.ndarray,
    t: float,
) -> np.ndarray:
    from scipy.linalg import expm

    return expm(-1j * H * t) @ psi0


def evolve_qutip_sesolve(
    H: np.ndarray,
    psi0: np.ndarray,
    t: float,
) -> np.ndarray:
    import qutip

    n = H.shape[0]
    Hq = qutip.Qobj(H, dims=[[n], [n]])
    psi0q = qutip.Qobj(psi0, dims=[[n], [1]])
    result = qutip.sesolve(Hq, psi0q, [0.0, t], [])
    out = result.states[-1].full().ravel()
    return np.asarray(out, dtype=np.complex128)


def max_abs_diff(a: np.ndarray, b: np.ndarray) -> float:
    return float(np.max(np.abs(a - b)))


def run_parity(
    *,
    nx: int = 12,
    ny: int = 10,
    t: float = 0.35,
    mass: float = 1.0,
) -> Tuple[float, float]:
    """
    Return (max_abs_diff_psi, norm_check) between QuTiP sesolve and scipy expm.

    ``nx`` and ``ny`` must be **even** (``>= 8``) so the shared Gaussian grid helper
    from ``schrodinger_2d_soft_double_slit`` matches CI sim conventions.
    """
    if nx % 2 != 0 or ny % 2 != 0 or nx < 8 or ny < 8:
        raise ValueError("nx and ny must be even integers >= 8")
    lx = float(nx)
    ly = float(ny)
    dx = lx / nx
    dy = ly / ny
    H = hamiltonian_free_2d_periodic(nx, ny, dx, dy, mass=mass)
    psi0 = initial_gaussian_flat(
        nx,
        ny,
        dx,
        dy,
        x0=-2.0,
        y0=0.5,
        kx0=0.6,
        ky0=-0.2,
        sigma0=0.85,
    )
    ps = evolve_scipy_expm(H, psi0, t)
    pq = evolve_qutip_sesolve(H, psi0, t)
    diff = max_abs_diff(ps, pq)
    nrm = float(np.sum(np.abs(pq) ** 2))
    return diff, nrm


def _load_fft2_mod():
    here = Path(__file__).resolve().parent
    spec = importlib.util.spec_from_file_location("schrodinger_2d_soft_double_slit", here / "schrodinger_2d_soft_double_slit.py")
    mod = importlib.util.module_from_spec(spec)
    assert spec and spec.loader
    spec.loader.exec_module(mod)
    return mod


def spectral_vs_fd_gap(
    *,
    nx: int = 16,
    ny: int = 16,
    t: float = 0.25,
    mass: float = 1.0,
) -> float:
    """
    Illustrative gap: max |ρ_spectral - ρ_fd| for the same initial Gaussian (both periodic).
    Not a failure mode — different discretizations.
    """
    m2 = _load_fft2_mod()
    lx = float(nx)
    ly = float(ny)
    dx = lx / nx
    dy = ly / ny
    X, Y, _, _ = m2.make_grid_2d(lx, ly, nx, ny)
    psi0 = m2.initial_gaussian_2d(X, Y, x0=-3.0, y0=0.0, kx0=0.8, ky0=0.1, sigma0=0.9)
    psi0 = psi0 / np.sqrt(m2.norm_dxy(psi0, dx, dy))
    psi_sp = m2.propagate_free_fft2(psi0, dx, dy, total_time=t, mass=mass)
    rho_sp = m2.density(psi_sp).ravel(order="C")
    H = hamiltonian_free_2d_periodic(nx, ny, dx, dy, mass=mass)
    psif = evolve_scipy_expm(H, psi0.ravel(order="C"), t)
    rho_fd = np.abs(psif) ** 2
    den = np.maximum(rho_sp, 1e-15)
    return float(np.max(np.abs(rho_sp - rho_fd) / den))


def main() -> None:
    import argparse

    p = argparse.ArgumentParser(description="QuTiP vs scipy 2D free parity (optional).")
    p.add_argument("--nx", type=int, default=12)
    p.add_argument("--ny", type=int, default=10)
    p.add_argument("--t", type=float, default=0.35)
    p.add_argument("--spectral-gap", action="store_true", help="print FD vs FFT rho gap (diagnostic)")
    args = p.parse_args()
    if not have_qutip():
        raise SystemExit("qutip not installed (pip install -r sim/requirements-optional.txt)")
    d, nrm = run_parity(nx=args.nx, ny=args.ny, t=args.t)
    print(f"parity max|psi_qt - psi_scipy| = {d:.3e},  sum|rho_qt| (unnormalized check) ~ {nrm:.6f}")
    if d > 1e-5:
        raise SystemExit("parity check failed")
    if args.spectral_gap:
        g = spectral_vs_fd_gap(nx=16, ny=16, t=0.25)
        print(f"diagnostic max rel |rho_fft - rho_fd| ~ {g:.3e} (expected O(1) on coarse grid)")


if __name__ == "__main__":
    main()
