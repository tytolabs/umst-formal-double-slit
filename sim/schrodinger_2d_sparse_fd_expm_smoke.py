#!/usr/bin/env python3
"""
Smoke test: **sparse** periodic FD Laplacian + diagonal slit **V**, one-shot
``expm(-i H t) |ψ⟩`` via ``scipy.sparse.linalg.expm_multiply`` vs **dense**
``scipy.linalg.expm``.

Same discrete **H** as ``qutip_schrodinger_2d_slit_parity.hamiltonian_soft_slit_fd`` (up to
ordering). Intended as a hook toward **large-grid** evolution without forming dense ``N²``
matrices in memory.

**Requires** NumPy + SciPy. Not in ``make sim``. See unittest.
"""

from __future__ import annotations

import importlib.util
from pathlib import Path
from typing import Tuple

import numpy as np


def _load_slit_parity():
    here = Path(__file__).resolve().parent
    spec = importlib.util.spec_from_file_location(
        "qutip_schrodinger_2d_slit_parity",
        here / "qutip_schrodinger_2d_slit_parity.py",
    )
    mod = importlib.util.module_from_spec(spec)
    assert spec and spec.loader
    spec.loader.exec_module(mod)
    return mod


def periodic_laplacian_1d_csr(n: int, dx: float):
    """1D periodic Laplacian / dx² as CSR (real symmetric)."""
    import scipy.sparse as sp

    if n < 3 or dx <= 0.0:
        raise ValueError("invalid grid")
    inv = 1.0 / (dx * dx)
    rows: list[int] = []
    cols: list[int] = []
    data: list[float] = []
    for i in range(n):
        im, ip = (i - 1) % n, (i + 1) % n
        rows.extend([i, i, i])
        cols.extend([i, im, ip])
        data.extend([-2.0 * inv, inv, inv])
    return sp.csr_matrix((data, (rows, cols)), shape=(n, n), dtype=np.float64)


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


def hamiltonian_soft_slit_sparse(
    nx: int,
    ny: int,
    lx: float,
    ly: float,
    *,
    mass: float = 1.0,
    v0: float = 8.0,
    x_screen: float = -2.0,
    slit_separation: float = 1.4,
    slit_sigma: float = 0.32,
    slit_center_offset: float = 0.0,
):
    """Sparse H = T_FD + diag(V), matching dense ``hamiltonian_soft_slit_fd``."""
    import scipy.sparse as sp

    if mass <= 0.0:
        raise ValueError("mass must be positive")
    dx = lx / nx
    dy = ly / ny
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
    vf = V.ravel(order="C").astype(np.float64)
    Lx = periodic_laplacian_1d_csr(nx, dx)
    Ly = periodic_laplacian_1d_csr(ny, dy)
    Ix = sp.eye(nx, format="csr", dtype=np.float64)
    Iy = sp.eye(ny, format="csr", dtype=np.float64)
    lap2d = sp.kron(Lx, Iy) + sp.kron(Ix, Ly)
    H_sp = (-1.0 / (2.0 * mass)) * lap2d + sp.diags(vf, offsets=0, format="csr", dtype=np.float64)
    return H_sp


def sparse_vs_dense_expm_psi(
    *,
    nx: int = 10,
    ny: int = 10,
    t: float = 0.12,
    mass: float = 1.0,
    v0: float = 7.0,
) -> Tuple[float, int]:
    """
    Return (max_abs_diff_psi, hilbert_dim).

    ``nx``, ``ny`` even and >= 8.
    """
    from scipy.linalg import expm
    from scipy.sparse.linalg import expm_multiply

    qp = _load_slit_parity()
    lx, ly = float(nx), float(ny)
    H_dense, psi0, _, _ = qp.hamiltonian_soft_slit_fd(
        nx, ny, lx, ly, mass=mass, v0=v0
    )
    H_sp = hamiltonian_soft_slit_sparse(nx, ny, lx, ly, mass=mass, v0=v0)
    psi_col = psi0.reshape(-1, 1)
    ref = expm(-1j * H_dense * t) @ psi0
    # expm_multiply(A, B) ≈ exp(A) @ B for vector B
    out = expm_multiply(-1j * H_sp * t, psi_col).ravel()
    diff = float(np.max(np.abs(ref - out)))
    return diff, nx * ny


def main() -> None:
    import argparse

    p = argparse.ArgumentParser(description="Sparse vs dense FD expm smoke (2D slit).")
    p.add_argument("--nx", type=int, default=12)
    p.add_argument("--ny", type=int, default=10)
    p.add_argument("--t", type=float, default=0.1)
    p.add_argument("--v0", type=float, default=9.0)
    args = p.parse_args()
    d, n = sparse_vs_dense_expm_psi(
        nx=args.nx, ny=args.ny, t=args.t, v0=args.v0
    )
    print(f"N={n}  max|psi_dense - psi_sparse_expm_multiply| = {d:.3e}")
    if d > 1e-8:
        raise SystemExit("sparse dense mismatch")


if __name__ == "__main__":
    main()
