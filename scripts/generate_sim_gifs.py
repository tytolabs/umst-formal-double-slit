#!/usr/bin/env python3
# SPDX-License-Identifier: MIT
# Copyright (c) 2026 Santhosh Shyamsundar, Santosh Prabhu Shenbagamoorthy — Studio TYTO

"""Generate illustrative simulation GIFs (1D soft double-slit + 2D with absorbing edges).

Usage:
    python3 scripts/generate_sim_gifs.py
    python3 scripts/generate_sim_gifs.py --validate   # smoke: few frames, small outputs

Outputs (under Docs/Media/ by default):
    sim-1d-double-slit.gif
    sim-2d-pml.gif
"""

from __future__ import annotations

import argparse
import math
import os
import sys


def check_deps() -> bool:
    try:
        import matplotlib  # noqa: F401
        import numpy  # noqa: F401
        import imageio  # noqa: F401
        return True
    except ImportError as e:
        print(f"Missing dependency: {e}. pip install matplotlib numpy imageio")
        return False


def _theme() -> dict:
    return {
        "bg": "#0a0a1a",
        "fg": "#e8e8f0",
        "grid": "#333355",
        "accent": "#e94560",
        "line": "#7dd3fc",
    }


def generate_1d_gif(out_path: str, n_frames: int) -> None:
    import numpy as np
    import matplotlib
    matplotlib.use("Agg")
    import matplotlib.pyplot as plt
    import imageio.v2 as imageio

    v = _theme()
    x = np.linspace(-12.0, 12.0, 500)
    slit_sep = 2.2
    slit_w = 0.35
    # Soft transmission: two Gaussians (slits) on a barrier plateau
    y1 = np.exp(-0.5 * ((x + slit_sep / 2) / slit_w) ** 2)
    y2 = np.exp(-0.5 * ((x - slit_sep / 2) / slit_w) ** 2)
    soft_slits = np.clip(y1 + y2, 0.0, 1.0)

    frames = []
    tmp = out_path + ".frames"
    os.makedirs(tmp, exist_ok=True)

    for t in range(n_frames):
        u = t / max(n_frames - 1, 1)
        # Wave packet center sweeps in; visibility ramps up after passing slits
        x0 = -10.0 + 18.0 * u
        sigma = 1.1
        envelope = np.exp(-0.5 * ((x - x0) / sigma) ** 2)
        vis = max(0.0, min(1.0, (u - 0.35) / 0.45))
        k = 2.8
        phase = k * x * (0.3 + 0.7 * u)
        interference = 0.5 * (1.0 + vis * np.cos(phase))
        prob = envelope * (0.15 + 0.85 * soft_slits) * interference
        prob = prob / (np.max(prob) + 1e-12)

        fig, ax = plt.subplots(figsize=(10, 4), facecolor=v["bg"])
        ax.set_facecolor(v["bg"])
        ax.fill_between(x, prob, color=v["line"], alpha=0.85, linewidth=0)
        ax.plot(x, prob, color=v["accent"], linewidth=1.2)
        ax.set_xlim(x.min(), x.max())
        ax.set_ylim(0, 1.05)
        ax.set_xlabel("x (arb.)", color=v["fg"])
        ax.set_ylabel(r"$|\psi|^2$", color=v["fg"])
        ax.set_title("1D soft double slit — approach → interaction → fringes", color=v["fg"], fontsize=11)
        ax.tick_params(colors=v["fg"])
        ax.grid(True, color=v["grid"], alpha=0.35)
        for sp in ax.spines.values():
            sp.set_color(v["grid"])
        fp = os.path.join(tmp, f"f{t:03d}.png")
        fig.savefig(fp, dpi=100, facecolor=v["bg"], edgecolor="none", bbox_inches="tight")
        plt.close(fig)
        frames.append(imageio.imread(fp))

    imageio.mimsave(out_path, frames, duration=0.07, loop=0)
    for t in range(n_frames):
        try:
            os.remove(os.path.join(tmp, f"f{t:03d}.png"))
        except OSError:
            pass
    try:
        os.rmdir(tmp)
    except OSError:
        pass
    print(f"Wrote {out_path}")


def generate_2d_gif(out_path: str, n_frames: int, grid_n: int = 128) -> None:
    import numpy as np
    import matplotlib
    matplotlib.use("Agg")
    import matplotlib.pyplot as plt
    import imageio.v2 as imageio

    v = _theme()
    lim = 8.0
    xs = np.linspace(-lim, lim, grid_n)
    ys = np.linspace(-lim, lim, grid_n)
    X, Y = np.meshgrid(xs, ys, indexing="xy")

    pml_w = 18  # pixels from each edge: ramp absorption (visual PML-style mask)
    ii = np.arange(grid_n, dtype=np.float64)[:, None]
    jj = np.arange(grid_n, dtype=np.float64)[None, :]
    dist_edge = np.minimum(np.minimum(ii, grid_n - 1 - ii), np.minimum(jj, grid_n - 1 - jj))
    pml_mask = np.clip(dist_edge / float(pml_w), 0.0, 1.0) ** 2

    slit_y = 2.4
    slit_w = 0.55
    barrier_x = -0.5
    # Two soft slits on a vertical barrier line (Gaussian in y, narrow in x)
    s1 = np.exp(-0.5 * ((X - barrier_x) / 0.35) ** 2) * np.exp(-0.5 * ((Y + slit_y) / slit_w) ** 2)
    s2 = np.exp(-0.5 * ((X - barrier_x) / 0.35) ** 2) * np.exp(-0.5 * ((Y - slit_y) / slit_w) ** 2)
    aperture = np.clip(s1 + s2, 0.0, 1.0)

    frames = []
    tmp = out_path + ".frames"
    os.makedirs(tmp, exist_ok=True)

    for t in range(n_frames):
        u = t / max(n_frames - 1, 1)
        x0 = -5.5 + 10.5 * u
        y0 = 0.2 * math.sin(4.0 * math.pi * u)
        sigma = 1.4
        packet = np.exp(-0.5 * (((X - x0) / sigma) ** 2 + ((Y - y0) / sigma) ** 2))
        vis = 0.25 + 0.75 * u
        k = 1.6
        prob = packet * (0.2 + 0.8 * aperture) * (0.5 * (1.0 + vis * np.cos(k * X + 0.7 * k * Y * u)))
        prob = prob * pml_mask
        prob = prob / (np.max(prob) + 1e-12)

        fig, ax = plt.subplots(figsize=(6.5, 5.5), facecolor=v["bg"])
        ax.set_facecolor(v["bg"])
        im = ax.imshow(
            prob,
            origin="lower",
            extent=(xs.min(), xs.max(), ys.min(), ys.max()),
            cmap="plasma",
            vmin=0.0,
            vmax=1.0,
            aspect="auto",
        )
        cb = plt.colorbar(im, ax=ax, fraction=0.046, pad=0.04)
        cb.ax.yaxis.set_tick_params(color=v["fg"])
        plt.setp(plt.getp(cb.ax.axes, "yticklabels"), color=v["fg"])
        ax.set_xlabel("x", color=v["fg"])
        ax.set_ylabel("y", color=v["fg"])
        ax.set_title(r"2D $|\psi|^2$ with absorbing-edge mask (PML-style)", color=v["fg"], fontsize=10)
        ax.tick_params(colors=v["fg"])
        for sp in ax.spines.values():
            sp.set_color(v["grid"])
        fp = os.path.join(tmp, f"f{t:03d}.png")
        fig.savefig(fp, dpi=110, facecolor=v["bg"], edgecolor="none", bbox_inches="tight")
        plt.close(fig)
        frames.append(imageio.imread(fp))

    imageio.mimsave(out_path, frames, duration=0.07, loop=0)
    for t in range(n_frames):
        try:
            os.remove(os.path.join(tmp, f"f{t:03d}.png"))
        except OSError:
            pass
    try:
        os.rmdir(tmp)
    except OSError:
        pass
    print(f"Wrote {out_path}")


def main() -> None:
    parser = argparse.ArgumentParser(description="Generate simulation GIFs.")
    parser.add_argument(
        "--validate",
        action="store_true",
        help="Quick smoke run (3 frames, skip full 80-frame renders).",
    )
    parser.add_argument(
        "--out-dir",
        default=None,
        help="Output directory (default: <repo>/Docs/Media).",
    )
    args = parser.parse_args()

    if not check_deps():
        sys.exit(1)

    repo_root = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
    out_dir = args.out_dir or os.path.join(repo_root, "Docs", "Media")
    os.makedirs(out_dir, exist_ok=True)

    n_frames = 3 if args.validate else 80
    path_1d = os.path.join(out_dir, "sim-1d-double-slit.gif")
    path_2d = os.path.join(out_dir, "sim-2d-pml.gif")

    generate_1d_gif(path_1d, n_frames)
    generate_2d_gif(path_2d, n_frames, grid_n=128)

    for p in (path_1d, path_2d):
        if not os.path.isfile(p) or os.path.getsize(p) < 256:
            raise SystemExit(f"validation failed: missing or tiny file {p}")


if __name__ == "__main__":
    main()
