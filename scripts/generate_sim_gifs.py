#!/usr/bin/env python3
# SPDX-License-Identifier: MIT
# Copyright (c) 2026 Santhosh Shyamsundar, Santosh Prabhu Shenbagamoorthy — Studio TYTO

"""Export lightweight wave-simulation GIFs (1D soft double-slit + 2D with absorbing edges).

Usage:
    python3 scripts/generate_sim_gifs.py
    python3 scripts/generate_sim_gifs.py --validate   # 2 frames each, no disk write

Requires: numpy, matplotlib, imageio (see sim/requirements-optional.txt).
"""

from __future__ import annotations

import argparse
import math
import os
import sys


def _check_deps() -> bool:
    try:
        import matplotlib  # noqa: F401
        import numpy  # noqa: F401
        import imageio  # noqa: F401
    except ImportError as e:
        print(f"Missing dependency: {e}. pip install matplotlib numpy imageio", file=sys.stderr)
        return False
    return True


def _soft_double_slit_potential(x: "np.ndarray", slit_sep: float, width: float) -> "np.ndarray":
    import numpy as np
    left = np.exp(-0.5 * ((x + slit_sep / 2) / width) ** 2)
    right = np.exp(-0.5 * ((x - slit_sep / 2) / width) ** 2)
    return -(left + right)


def simulate_1d(
    n_frames: int,
    nx: int = 512,
    x_max: float = 12.0,
    dt: float = 0.015,
    validate: bool = False,
) -> list:
    import numpy as np
    import matplotlib

    matplotlib.use("Agg")
    import matplotlib.pyplot as plt

    x = np.linspace(-x_max, x_max, nx, dtype=np.float64)
    dx = float(x[1] - x[0])
    k0 = 18.0
    psi = np.exp(1j * k0 * x) * np.exp(-((x + x_max * 0.55) / 1.2) ** 2)
    psi = psi / np.sqrt(np.sum(np.abs(psi) ** 2) * dx)
    v = _soft_double_slit_potential(x, slit_sep=2.2, width=0.35)

    frames = []
    bg = "#0a0a1a"
    accent = "#e94560"

    absorb = np.ones(nx, dtype=np.float64)
    absorb[:10] *= np.linspace(0, 1, 10) ** 2
    absorb[-10:] *= np.linspace(1, 0, 10) ** 2

    for frame in range(n_frames):
        for _ in range(3):
            psi2 = np.fft.ifft(np.fft.fft(psi) * np.exp(-1j * (np.fft.fftfreq(nx, dx) * 2 * math.pi) ** 2 * dt))
            psi = np.exp(-1j * v * dt) * psi2
        if validate:
            psi[-8:] = 0
            psi[:8] = 0
        else:
            psi *= absorb

        prob = np.abs(psi) ** 2
        prob = prob / (prob.max() + 1e-12)

        fig, ax = plt.subplots(figsize=(10, 4), facecolor=bg)
        ax.set_facecolor(bg)
        ax.plot(x, prob, color=accent, lw=1.4)
        ax.fill_between(x, 0, prob, color=accent, alpha=0.25)
        ax.set_xlim(x[0], x[-1])
        ax.set_ylim(0, 1.05)
        ax.set_title("|ψ(x,t)|² — soft double slit", color="white", fontsize=11)
        ax.set_xlabel("x", color="#ccc")
        ax.set_ylabel("probability density", color="#ccc")
        ax.tick_params(colors="#888")
        for s in ax.spines.values():
            s.set_color("#333")
        fig.text(0.02, 0.02, f"frame {frame + 1}/{n_frames}", color="#666", fontsize=8)
        fig.canvas.draw()
        rgba = np.asarray(fig.canvas.buffer_rgba())
        frames.append(rgba[:, :, :3].copy())
        plt.close(fig)

    return frames


def _laplacian_2d(psi: "np.ndarray", dx: float) -> "np.ndarray":
    import numpy as np
    out = np.zeros_like(psi, dtype=np.complex128)
    out[1:-1, 1:-1] = (
        psi[2:, 1:-1] + psi[:-2, 1:-1] + psi[1:-1, 2:] + psi[1:-1, :-2] - 4 * psi[1:-1, 1:-1]
    ) / (dx * dx)
    return out


def simulate_2d_pml(
    n_frames: int,
    n: int = 128,
    box: float = 10.0,
    dt: float = 0.012,
    validate: bool = False,
) -> list:
    import numpy as np
    import matplotlib

    matplotlib.use("Agg")
    import matplotlib.pyplot as plt

    x = np.linspace(-box, box, n)
    y = np.linspace(-box, box, n)
    xv, yv = np.meshgrid(x, y, indexing="ij")
    dx = float(x[1] - x[0])

    kx, ky = 14.0, 0.0
    psi = np.exp(1j * (kx * xv + ky * yv)) * np.exp(-((xv + box * 0.45) ** 2 + yv**2) / 1.8)
    psi = psi / np.sqrt(np.sum(np.abs(psi) ** 2) * dx * dx)

    v = _soft_double_slit_potential(yv, slit_sep=1.8, width=0.28) * np.exp(-((xv + 1.5) / 0.9) ** 2)

    pml_w = 12
    sigma = np.zeros((n, n), dtype=np.float64)
    ramp = np.linspace(0, 1, pml_w) ** 2
    sigma[:pml_w, :] += ramp[:, None]
    sigma[-pml_w:, :] += ramp[::-1, None]
    sigma[:, :pml_w] += ramp[None, :]
    sigma[:, -pml_w:] += ramp[None, ::-1]
    sigma = sigma * 0.08

    frames = []
    bg = "#0a0a1a"

    for frame in range(n_frames):
        for _ in range(2):
            lap = _laplacian_2d(psi, dx)
            psi = psi + 1j * dt * (-lap + v * psi)
            psi *= np.exp(-sigma * dt)
        prob = np.abs(psi) ** 2
        prob = prob / (prob.max() + 1e-18)

        fig, ax = plt.subplots(figsize=(5.5, 5), facecolor=bg)
        ax.set_facecolor(bg)
        im = ax.imshow(
            prob.T,
            origin="lower",
            extent=(x[0], x[-1], y[0], y[-1]),
            cmap="plasma",
            vmin=0,
            vmax=1,
            aspect="equal",
        )
        ax.set_title("|ψ(x,y,t)|² (PML-style absorption at edges)", color="white", fontsize=10)
        ax.set_xlabel("x", color="#ccc")
        ax.set_ylabel("y", color="#ccc")
        plt.colorbar(im, ax=ax, fraction=0.046, pad=0.04)
        fig.text(0.02, 0.02, f"frame {frame + 1}/{n_frames}", color="#666", fontsize=8)
        fig.canvas.draw()
        rgba = np.asarray(fig.canvas.buffer_rgba())
        frames.append(rgba[:, :, :3].copy())
        plt.close(fig)

    return frames


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--validate", action="store_true", help="fast smoke run (2 frames, no GIF write)")
    args = parser.parse_args()

    if not _check_deps():
        return 1

    out_dir = os.path.join(os.path.dirname(__file__), "..", "Docs", "Media")
    n_1d = 2 if args.validate else 80
    n_2d = 2 if args.validate else 80

    frames_1d = simulate_1d(n_1d, validate=args.validate)
    frames_2d = simulate_2d_pml(n_2d, validate=args.validate)

    if args.validate:
        assert len(frames_1d) == n_1d and len(frames_2d) == n_2d
        print("sim-gifs validate: ok")
        return 0

    os.makedirs(out_dir, exist_ok=True)
    import imageio.v2 as imageio

    path_1d = os.path.join(out_dir, "sim-double-slit-1d.gif")
    path_2d = os.path.join(out_dir, "sim-pml-2d.gif")
    imageio.mimsave(path_1d, frames_1d, duration=0.06, loop=0)
    imageio.mimsave(path_2d, frames_2d, duration=0.06, loop=0)
    print(f"Wrote {path_1d} ({len(frames_1d)} frames)")
    print(f"Wrote {path_2d} ({len(frames_2d)} frames)")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
