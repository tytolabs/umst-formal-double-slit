#!/usr/bin/env python3
# SPDX-License-Identifier: MIT
# Copyright (c) 2026 Santhosh Shyamsundar, Santosh Prabhu Shenbagamoorthy — Studio TYTO

"""Export short Schrödinger simulation GIFs (1D soft double slit, 2D + PML).

Usage:
    python3 scripts/generate_sim_gifs.py
    python3 scripts/generate_sim_gifs.py --validate   # tiny grid, 3 frames, write to /tmp

Requires: numpy, matplotlib, imageio.

Outputs (default): Docs/Media/sim_1d_soft_slit.gif, Docs/Media/sim_2d_pml.gif
"""

from __future__ import annotations

import argparse
import importlib.util
import os
import sys
from pathlib import Path


def _repo_root() -> Path:
    return Path(__file__).resolve().parents[1]


def _load_sim_module(name: str, filename: str):
    sim_dir = _repo_root() / "sim"
    script = sim_dir / filename
    spec = importlib.util.spec_from_file_location(name, script)
    mod = importlib.util.module_from_spec(spec)
    assert spec and spec.loader
    spec.loader.exec_module(mod)
    return mod


def _deps_ok() -> bool:
    try:
        import matplotlib  # noqa: F401
        import numpy  # noqa: F401
        import imageio  # noqa: F401
        return True
    except ImportError as e:
        print(f"Missing dependency: {e}. pip install numpy matplotlib imageio", file=sys.stderr)
        return False


def run_1d_frames(*, n_frames: int, validate: bool) -> list:
    """Return list of RGB uint8 arrays (H,W,3) for |psi|^2 line plot."""
    import matplotlib

    matplotlib.use("Agg")
    import matplotlib.pyplot as plt
    import numpy as np

    ff = _load_sim_module("schrodinger_1d_free_fft", "schrodinger_1d_free_fft.py")
    sp = _load_sim_module("schrodinger_1d_split_step", "schrodinger_1d_split_step.py")
    sd = _load_sim_module("schrodinger_1d_soft_double_slit", "schrodinger_1d_soft_double_slit.py")

    length = 40.0 if validate else 56.0
    n = 256 if validate else 2048
    total_t = 0.6 if validate else 2.5
    steps_total = 60 if validate else 500

    xs, dx = ff.make_grid(length, n)
    v_x = sd.soft_double_slit_potential(
        xs,
        v0=28.0,
        x_screen=-2.0,
        slit_separation=1.4,
        slit_sigma=0.22,
        slit_center_offset=0.35,
    )
    psi0 = ff.initial_gaussian(xs, x0=-18.0, k0=1.35, sigma0=1.1)
    psi0 = psi0 / np.sqrt(ff.norm_dx(psi0, dx))

    frames: list = []
    bg = "#0a0a1a"
    accent = "#e94560"

    for k in range(n_frames):
        n_steps = max(1, (k + 1) * steps_total // n_frames)
        dt = total_t / n_steps
        psi = sp.split_step_evolve(psi0, dx, dt=dt, n_steps=n_steps, v_x=v_x)
        rho = np.real(np.conjugate(psi) * psi)

        fig, ax = plt.subplots(figsize=(8, 3.5), facecolor=bg)
        ax.set_facecolor(bg)
        ax.plot(xs, rho, color=accent, lw=1.2)
        ax.set_xlim(float(xs[0]), float(xs[-1]))
        y1 = float(np.max(rho) * 1.05) if rho.size else 1.0
        ax.set_ylim(0.0, max(y1, 1e-12))
        ax.tick_params(colors="white", labelsize=8)
        ax.xaxis.label.set_color("white")
        ax.yaxis.label.set_color("white")
        ax.set_title("|ψ(x,t)|² — 1D soft double slit", color="white", fontsize=10)
        ax.set_xlabel("x")
        ax.set_ylabel("ρ")
        fig.canvas.draw()
        buf = np.asarray(fig.canvas.buffer_rgba())[..., :3]
        frames.append(buf.copy())
        plt.close(fig)

    return frames


def run_2d_frames(*, n_frames: int, validate: bool) -> list:
    """Return list of RGB uint8 arrays for |psi|^2 heatmap (2D PML)."""
    import matplotlib

    matplotlib.use("Agg")
    import matplotlib.pyplot as plt
    import numpy as np

    pml = _load_sim_module("schrodinger_2d_pml", "schrodinger_2d_pml.py")
    m2 = _load_sim_module("schrodinger_2d_soft_double_slit", "schrodinger_2d_soft_double_slit.py")

    nx = 64 if validate else 128
    ny = 64 if validate else 128
    lx, ly = (24.0, 24.0) if validate else (48.0, 48.0)
    total_t = 0.5 if validate else 2.0
    steps_total = 30 if validate else 400
    n_pml = 8 if validate else 32

    X, Y, dx, dy = m2.make_grid_2d(lx, ly, nx, ny)
    psi0 = m2.initial_gaussian_2d(X, Y, x0=-14.0, y0=0.0, kx0=1.4, ky0=0.0, sigma0=1.1)
    psi0 = psi0 / np.sqrt(m2.norm_dxy(psi0, dx, dy))
    v_xy = m2.soft_double_slit_potential_2d(
        X, Y,
        v0=24.0,
        x_screen=-4.0,
        slit_separation=1.6,
        slit_sigma=0.35,
        slit_center_offset=0.0,
    )

    frames: list = []
    bg = "#0a0a1a"

    for k in range(n_frames):
        n_steps = max(1, (k + 1) * steps_total // n_frames)
        dt = total_t / n_steps
        psi = pml.split_step_evolve_2d_pml(
            psi0, dx, dy, dt, n_steps, v_xy,
            n_pml, n_pml, 5.0,
            mass=1.0, order=3,
        )
        rho = m2.density(psi)
        rmax = float(np.max(rho)) if rho.size else 1.0

        fig, ax = plt.subplots(figsize=(5.5, 5), facecolor=bg)
        ax.set_facecolor(bg)
        im = ax.imshow(
            rho.T,
            origin="lower",
            extent=(float(X.min()), float(X.max()), float(Y.min()), float(Y.max())),
            aspect="auto",
            cmap="plasma",
            vmin=0.0,
            vmax=max(rmax, 1e-15),
        )
        ax.set_title("|ψ(x,y,t)|² — 2D soft slit + PML", color="white", fontsize=10)
        ax.set_xlabel("x", color="white")
        ax.set_ylabel("y", color="white")
        ax.tick_params(colors="white", labelsize=7)
        cbar = fig.colorbar(im, ax=ax, fraction=0.046, pad=0.04)
        cbar.ax.yaxis.set_tick_params(colors="white")
        fig.canvas.draw()
        buf = np.asarray(fig.canvas.buffer_rgba())[..., :3]
        frames.append(buf.copy())
        plt.close(fig)

    return frames


def write_gif(path: Path, frames: list, *, fps: float) -> None:
    import imageio.v2 as imageio

    path.parent.mkdir(parents=True, exist_ok=True)
    imageio.mimsave(path, frames, fps=fps, loop=0)


def main() -> int:
    p = argparse.ArgumentParser(description="Generate 1D/2D Schrödinger GIFs for Docs/Media.")
    p.add_argument("--validate", action="store_true", help="Fast smoke: 3 frames, /tmp outputs")
    p.add_argument("--frames", type=int, default=80, help="Frames per GIF (default 80)")
    p.add_argument("--fps", type=float, default=12.0)
    args = p.parse_args()

    if not _deps_ok():
        return 1

    n_frames = 3 if args.validate else max(3, args.frames)
    out_dir = Path(os.environ.get("TMPDIR", "/tmp")) if args.validate else _repo_root() / "Docs" / "Media"

    print(f"Generating 1D GIF ({n_frames} frames)...")
    f1 = run_1d_frames(n_frames=n_frames, validate=args.validate)
    out1 = out_dir / "sim_1d_soft_slit.gif"
    write_gif(out1, f1, fps=args.fps)
    print(f"  wrote {out1}")

    print(f"Generating 2D PML GIF ({n_frames} frames)...")
    f2 = run_2d_frames(n_frames=n_frames, validate=args.validate)
    out2 = out_dir / "sim_2d_pml.gif"
    write_gif(out2, f2, fps=args.fps)
    print(f"  wrote {out2}")

    return 0


if __name__ == "__main__":
    raise SystemExit(main())
