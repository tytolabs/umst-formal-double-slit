#!/usr/bin/env python3
# SPDX-License-Identifier: MIT
# Copyright (c) 2026 Santhosh Shyamsundar, Santosh Prabhu Shenbagamoorthy — Studio TYTO

"""Generate lightweight wave-mechanics GIFs (1D line + 2D heatmap) for docs / smoke tests.

Usage:
    python3 scripts/generate_sim_gifs.py
    python3 scripts/generate_sim_gifs.py --validate   # no imageio write; sanity check only

Outputs (non-validate):
    Docs/Media/sim-1d-wave.gif
    Docs/Media/sim-2d-wave.gif
"""

from __future__ import annotations

import argparse
import math
import os
import sys


def check_deps():
    try:
        import matplotlib  # noqa: F401
        import numpy  # noqa: F401
        import imageio  # noqa: F401
        return True
    except ImportError as e:
        print(f"Missing dependency: {e}. Install via: pip install matplotlib numpy imageio")
        return False


def _soft_double_slit_1d(x, slit_sep, slit_w):
    import numpy as np
    g1 = np.exp(-0.5 * ((x - slit_sep / 2) / slit_w) ** 2)
    g2 = np.exp(-0.5 * ((x + slit_sep / 2) / slit_w) ** 2)
    return np.clip(g1 + g2, 0.0, 1.0)


def _evolve_split_step_1d(psi, dx, dt, k, v_x):
    """One split-step: half V, full T, half V (atomic units ℏ = m = 1)."""
    import numpy as np
    psi = psi * np.exp(-0.5j * v_x * dt)
    psi_k = np.fft.fft(psi)
    psi_k *= np.exp(-0.5j * (k ** 2) * dt)
    psi = np.fft.ifft(psi_k)
    psi = psi * np.exp(-0.5j * v_x * dt)
    return psi


def generate_1d_gif(out_path: str, n_frames: int = 80):
    import numpy as np
    import matplotlib
    matplotlib.use("Agg")
    import matplotlib.pyplot as plt
    import imageio.v2 as imageio

    nx = 900
    x = np.linspace(-12.0, 12.0, nx, dtype=np.float64)
    dx = float(x[1] - x[0])
    k = 2.0 * np.pi * np.fft.fftfreq(nx, d=dx)

    x0 = -7.0
    sigma = 0.55
    k0 = 3.2
    psi = np.exp(-((x - x0) ** 2) / (4.0 * sigma**2) + 1j * k0 * x)
    psi /= np.sqrt(np.sum(np.abs(psi) ** 2) * dx)

    barrier_x = 0.0
    slit_sep = 1.1
    slit_w = 0.22
    barrier_w = 0.08
    v_max = 120.0
    v_x = np.zeros_like(x)
    mask_barrier = np.abs(x - barrier_x) < barrier_w
    trans = _soft_double_slit_1d(x, slit_sep, slit_w)
    aperture = np.where(mask_barrier, trans, 1.0)
    v_x[mask_barrier] = v_max * (1.0 - np.clip(trans[mask_barrier], 0.0, 1.0))

    dt = 0.012
    frames = []
    bg = "#0a0a1a"
    accent = "#e94560"

    for frame in range(n_frames):
        for _ in range(3):
            psi = _evolve_split_step_1d(psi, dx, dt, k, v_x)
            psi *= aperture
            psi /= np.sqrt(np.sum(np.abs(psi) ** 2) * dx)

        prob = np.abs(psi) ** 2
        fig, ax = plt.subplots(figsize=(10, 4), facecolor=bg)
        ax.set_facecolor(bg)
        ax.fill_between(x, 0, prob, color=accent, alpha=0.35)
        ax.plot(x, prob, color=accent, lw=1.2)
        ax.axvline(barrier_x, color="#444", ls="--", lw=0.8)
        ax.set_xlim(x[0], x[-1])
        ax.set_ylim(0, max(0.02, float(prob.max()) * 1.15))
        ax.set_xlabel("x (arb.)", color="white")
        ax.set_ylabel(r"$|\psi|^2$", color="white")
        ax.set_title(
            f"1D soft double slit — frame {frame + 1}/{n_frames}",
            color="#aaa",
            fontsize=10,
        )
        ax.tick_params(colors="white")
        for spine in ax.spines.values():
            spine.set_color("#333")

        fig.canvas.draw()
        rgba = np.asarray(fig.canvas.buffer_rgba())
        frames.append(rgba[:, :, :3])
        plt.close(fig)

    os.makedirs(os.path.dirname(out_path), exist_ok=True)
    imageio.mimsave(out_path, frames, duration=0.06, loop=0)
    print(f"Wrote {out_path}")


def _pml_mask_2d(ny: int, nx: int, width: int):
    """Smooth absorption mask near borders (PML-style envelope)."""
    import numpy as np
    yy, xx = np.mgrid[0:ny, 0:nx]
    d = np.minimum.reduce([xx, nx - 1 - xx, yy, ny - 1 - yy]).astype(np.float64)
    ramp = np.clip(d / float(width), 0.0, 1.0)
    return ramp ** 2


def generate_2d_gif(out_path: str, n_frames: int = 80, grid: int = 128):
    import numpy as np
    import matplotlib
    matplotlib.use("Agg")
    import matplotlib.pyplot as plt
    import imageio.v2 as imageio

    ny = nx = grid
    x = np.linspace(-6.0, 6.0, nx)
    y = np.linspace(-6.0, 6.0, ny)
    dx = float(x[1] - x[0])
    X, Y = np.meshgrid(x, y, indexing="xy")

    kx = 2.0 * np.pi * np.fft.fftfreq(nx, d=dx)
    ky = 2.0 * np.pi * np.fft.fftfreq(ny, d=dx)
    kx2, ky2 = np.meshgrid(kx, ky, indexing="xy")
    k2 = kx2 ** 2 + ky2 ** 2

    psi = np.zeros((ny, nx), dtype=np.complex128)
    x0, y0 = -3.2, 0.0
    sig = 0.45
    k0x, k0y = 2.4, 0.15
    psi += np.exp(
        -((X - x0) ** 2 + (Y - y0) ** 2) / (4.0 * sig**2) + 1j * (k0x * X + k0y * Y)
    )
    psi /= np.sqrt(np.sum(np.abs(psi) ** 2) * dx * dx)

    slit_sep = 1.0
    slit_w = 0.18
    barrier = np.abs(X) < 0.12
    trans = _soft_double_slit_1d(Y[0, :], slit_sep, slit_w)
    trans2d = np.tile(trans, (ny, 1))
    aperture = np.where(barrier, trans2d, 1.0)

    v_max = 90.0
    v_xy = np.where(barrier, v_max * (1.0 - np.clip(trans2d, 0.0, 1.0)), 0.0)

    absorb = _pml_mask_2d(ny, nx, width=14)
    dt = 0.008
    frames = []
    bg = "#0a0a1a"

    for frame in range(n_frames):
        for _ in range(2):
            psi *= np.exp(-0.5j * v_xy * dt)
            psi_k = np.fft.fft2(psi)
            psi_k *= np.exp(-0.5j * k2 * dt)
            psi = np.fft.ifft2(psi_k)
            psi *= np.exp(-0.5j * v_xy * dt)
            psi *= aperture
            psi *= absorb
            nrm = np.sqrt(np.sum(np.abs(psi) ** 2) * dx * dx)
            if nrm > 1e-12:
                psi /= nrm

        prob = np.abs(psi) ** 2
        fig, ax = plt.subplots(figsize=(5.5, 5.0), facecolor=bg)
        ax.set_facecolor(bg)
        im = ax.imshow(
            prob,
            origin="lower",
            cmap="plasma",
            extent=(x[0], x[-1], y[0], y[-1]),
            aspect="equal",
            vmin=0.0,
            vmax=float(prob.max()) + 1e-9,
        )
        ax.set_xlabel("x", color="white")
        ax.set_ylabel("y", color="white")
        ax.set_title(
            f"2D with absorbing boundary — frame {frame + 1}/{n_frames}",
            color="#aaa",
            fontsize=9,
        )
        ax.tick_params(colors="white")
        plt.colorbar(im, ax=ax, fraction=0.046, pad=0.04)

        fig.canvas.draw()
        rgba = np.asarray(fig.canvas.buffer_rgba())
        frames.append(rgba[:, :, :3])
        plt.close(fig)

    os.makedirs(os.path.dirname(out_path), exist_ok=True)
    imageio.mimsave(out_path, frames, duration=0.07, loop=0)
    print(f"Wrote {out_path}")


def main():
    parser = argparse.ArgumentParser(description="Generate simulation GIFs.")
    parser.add_argument(
        "--validate",
        action="store_true",
        help="Run numerics and one matplotlib draw without writing GIFs.",
    )
    args = parser.parse_args()

    if not check_deps():
        sys.exit(1)

    import numpy as np
    import matplotlib
    matplotlib.use("Agg")
    import matplotlib.pyplot as plt

    repo_root = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
    out_dir = os.path.join(repo_root, "Docs", "Media")

    if args.validate:
        x = np.linspace(-4, 4, 200)
        p = _soft_double_slit_1d(x, 1.0, 0.2)
        assert p.shape == x.shape and float(p.max()) <= 1.0 + 1e-9
        fig, ax = plt.subplots()
        ax.plot(x, p)
        fig.canvas.draw()
        plt.close(fig)
        print("sim-gifs validate OK")
        return

    generate_1d_gif(os.path.join(out_dir, "sim-1d-wave.gif"))
    generate_2d_gif(os.path.join(out_dir, "sim-2d-wave.gif"))
    print("Done.")


if __name__ == "__main__":
    main()
