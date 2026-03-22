#!/usr/bin/env python3
# SPDX-License-Identifier: MIT
# Copyright (c) 2026 Santhosh Shyamsundar, Santosh Prabhu Shenbagamoorthy — Studio TYTO

"""Generate lightweight physics-style simulation GIFs (1D double-slit + 2D with edge damping).

Usage:
    python3 scripts/generate_sim_gifs.py
    python3 scripts/generate_sim_gifs.py --validate   # smoke: deps + tiny run

Outputs (default):
    Docs/Media/sim_1d_double_slit.gif
    Docs/Media/sim_2d_pml_style.gif
"""

from __future__ import annotations

import argparse
import os
import sys


def check_deps() -> bool:
    try:
        import matplotlib  # noqa: F401
        import numpy  # noqa: F401
        import imageio  # noqa: F401
        return True
    except ImportError as e:
        print(f"Missing dependency: {e}. Install via: pip install matplotlib numpy imageio")
        return False


def split_step_1d(psi: "np.ndarray", k: "np.ndarray", v: "np.ndarray", dt: float) -> "np.ndarray":
    """One split-step FFT unit (ħ=m=1): half V, full K, half V."""
    import numpy as np

    psi = np.exp(-1j * v * (dt / 2)) * psi
    psi_k = np.fft.fft(psi)
    psi_k *= np.exp(-1j * (k**2) * (dt / 2))
    psi = np.fft.ifft(psi_k)
    psi = np.exp(-1j * v * (dt / 2)) * psi
    return psi


def soft_double_slit_mask(x: "np.ndarray", slit_sep: float, slit_w: float, wall: float) -> "np.ndarray":
    """Smooth transmission [0,1]: two openings around ±slit_sep/2, absorbing elsewhere."""
    import numpy as np

    # Soft block between slits and outside; openings as products of sigmoid steps
    s = slit_w * 0.35
    left_open = 0.5 * (1 + np.tanh((x + slit_sep / 2 + wall) / s)) * 0.5 * (
        1 - np.tanh((x + slit_sep / 2 - wall) / s)
    )
    right_open = 0.5 * (1 + np.tanh((x - slit_sep / 2 + wall) / s)) * 0.5 * (
        1 - np.tanh((x - slit_sep / 2 - wall) / s)
    )
    return np.clip(left_open + right_open, 0.0, 1.0)


def generate_1d_gif(out_path: str, n_frames: int = 80, nx: int = 512, validate: bool = False):
    import numpy as np
    import matplotlib

    matplotlib.use("Agg")
    import matplotlib.pyplot as plt
    import imageio.v2 as imageio

    if validate:
        n_frames = 4
        nx = 128

    L = 24.0
    dx = L / nx
    x = (np.arange(nx) - nx // 2) * dx
    k = 2 * np.pi * np.fft.fftfreq(nx, d=dx)

    # Initial Gaussian packet, moving right
    x0 = -7.0
    sigma = 0.85
    k0 = 2.2
    psi = np.exp(-((x - x0) ** 2) / (2 * sigma**2) + 1j * k0 * x)
    psi /= np.sqrt(np.sum(np.abs(psi) ** 2) * dx)

    # Soft slits at x≈0
    slit_sep = 2.2
    slit_w = 0.55
    mask = soft_double_slit_mask(x, slit_sep, slit_w, wall=0.35)
    v = 18.0 * (1.0 - mask)

    dt = 0.018 if not validate else 0.05
    frames = []
    tmp = os.path.join(os.path.dirname(out_path) or ".", "tmp_sim_frames")
    os.makedirs(tmp, exist_ok=True)

    bg = "#0a0a1a"
    accent = "#e94560"

    for t in range(n_frames):
        for _ in range(3 if not validate else 1):
            psi = split_step_1d(psi, k, v, dt)
        rho = np.abs(psi) ** 2
        rho /= np.max(rho) + 1e-12

        fig, ax = plt.subplots(figsize=(9, 3.2), facecolor=bg)
        ax.set_facecolor(bg)
        ax.plot(x, rho, color=accent, lw=1.6)
        ax.fill_between(x, rho, color=accent, alpha=0.25)
        ax.set_xlim(x.min(), x.max())
        ax.set_ylim(0, 1.05)
        ax.set_xlabel("x", color="white")
        ax.set_ylabel("|ψ|²", color="white")
        ax.set_title("1D soft double slit — |ψ(x,t)|²", color="white", fontsize=11)
        ax.tick_params(colors="#aaa")
        for spine in ax.spines.values():
            spine.set_color("#444")
        fig.tight_layout()
        fp = os.path.join(tmp, f"1d_{t:04d}.png")
        fig.savefig(fp, dpi=100, facecolor=bg)
        plt.close(fig)
        frames.append(imageio.imread(fp))

    os.makedirs(os.path.dirname(out_path) or ".", exist_ok=True)
    imageio.mimsave(out_path, frames, duration=0.06, loop=0)
    print(f"Wrote {out_path} ({len(frames)} frames)")


def generate_2d_gif(out_path: str, n_frames: int = 80, n: int = 128, validate: bool = False):
    import numpy as np
    import matplotlib

    matplotlib.use("Agg")
    import matplotlib.pyplot as plt
    import imageio.v2 as imageio

    if validate:
        n_frames = 4
        n = 48

    L = 14.0
    dx = L / n
    x = (np.arange(n) - n // 2) * dx
    y = (np.arange(n) - n // 2) * dx
    xv, yv = np.meshgrid(x, y, indexing="ij")

    kx = 2 * np.pi * np.fft.fftfreq(n, d=dx)
    ky = 2 * np.pi * np.fft.fftfreq(n, d=dx)
    kx2, ky2 = np.meshgrid(kx, ky, indexing="ij")
    k2 = kx2**2 + ky2**2

    # 2D split-step with mild edge damping (visual PML-style boundary)
    sigma = 1.1
    psi = np.exp(-((xv + 4.5) ** 2 + yv**2) / (2 * sigma**2)) * np.exp(1j * 1.8 * xv)
    psi /= np.sqrt(np.sum(np.abs(psi) ** 2) * dx * dx)

    # Circular soft obstacle (double-slit proxy: bar with two holes along y)
    mask = soft_double_slit_mask(yv[0, :], slit_sep=1.8, slit_w=0.5, wall=0.28)
    barrier = np.broadcast_to((1.0 - mask)[None, :], (n, n))
    v = 22.0 * barrier * np.exp(-(xv**2) / 2.0)

    absorb = np.ones((n, n))
    w = max(4, n // 16)
    ramp = np.linspace(0.0, 1.0, w)
    absorb[:w, :] *= ramp[:, None]
    absorb[-w:, :] *= ramp[::-1, None]
    absorb[:, :w] *= ramp[None, :]
    absorb[:, -w:] *= ramp[None, ::-1]

    dt = 0.012 if not validate else 0.04
    frames = []
    tmp = os.path.join(os.path.dirname(out_path) or ".", "tmp_sim_frames")
    os.makedirs(tmp, exist_ok=True)

    bg = "#0a0a1a"

    for t in range(n_frames):
        for _ in range(2 if not validate else 1):
            psi = np.exp(-1j * v * (dt / 2)) * psi
            psi_k = np.fft.fft2(psi)
            psi_k *= np.exp(-1j * k2 * (dt / 2))
            psi = np.fft.ifft2(psi_k)
            psi = np.exp(-1j * v * (dt / 2)) * psi
            psi *= absorb

        rho = np.abs(psi) ** 2
        rho /= np.max(rho) + 1e-12

        fig, ax = plt.subplots(figsize=(5.5, 5), facecolor=bg)
        ax.set_facecolor(bg)
        im = ax.imshow(
            rho.T,
            origin="lower",
            cmap="plasma",
            extent=(x.min(), x.max(), y.min(), y.max()),
            vmin=0,
            vmax=1,
            aspect="equal",
        )
        ax.set_title("2D |ψ(x,y,t)|² (edge-damped)", color="white", fontsize=11)
        ax.set_xlabel("x", color="white")
        ax.set_ylabel("y", color="white")
        ax.tick_params(colors="#aaa")
        cbar = plt.colorbar(im, ax=ax, fraction=0.046, pad=0.04)
        cbar.ax.tick_params(colors="#aaa")
        fig.tight_layout()
        fp = os.path.join(tmp, f"2d_{t:04d}.png")
        fig.savefig(fp, dpi=90, facecolor=bg)
        plt.close(fig)
        frames.append(imageio.imread(fp))

    os.makedirs(os.path.dirname(out_path) or ".", exist_ok=True)
    imageio.mimsave(out_path, frames, duration=0.06, loop=0)
    print(f"Wrote {out_path} ({len(frames)} frames)")


def main() -> int:
    p = argparse.ArgumentParser(description="Generate simulation GIFs for docs/media.")
    p.add_argument("--validate", action="store_true", help="Smoke test: tiny grids, few frames")
    p.add_argument(
        "--out-dir",
        default=os.path.join(os.path.dirname(__file__), "..", "Docs", "Media"),
        help="Output directory for GIFs",
    )
    args = p.parse_args()

    if not check_deps():
        return 1

    out_dir = os.path.abspath(args.out_dir)
    os.makedirs(out_dir, exist_ok=True)
    g1 = os.path.join(out_dir, "sim_1d_double_slit.gif")
    g2 = os.path.join(out_dir, "sim_2d_pml_style.gif")

    try:
        generate_1d_gif(g1, validate=args.validate)
        generate_2d_gif(g2, validate=args.validate)
    except Exception as e:
        print(f"Error: {e}", file=sys.stderr)
        return 1
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
