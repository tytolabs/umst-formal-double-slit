#!/usr/bin/env python3
# SPDX-License-Identifier: MIT
# Copyright (c) 2026 Santhosh Shyamsundar, Santosh Prabhu Shenbagamoorthy — Studio TYTO

"""Generate a spectacular double-slit interference collapse GIF + teaser image.

Usage:
    python3 scripts/generate_spectacular_gif.py

Outputs:
    Docs/Media/double-slit-collapse.gif   — animated GIF
    Docs/Media/teaser.png (and teaser-light.png)                 — static teaser image for social/README
"""

import math
import os
import sys

def check_deps():
    try:
        import matplotlib
        import numpy
        import imageio
        return True
    except ImportError as e:
        print(f"Missing dependency: {e}. Install via: pip install matplotlib numpy imageio")
        return False

def fringe_pattern(x_arr, visibility, n_slits=2, slit_sep=5.0, wavelength=1.0):
    """Compute double-slit interference pattern intensity."""
    import numpy as np
    k = 2 * np.pi / wavelength
    phase = k * slit_sep * np.sin(np.arctan(x_arr / 50.0))
    # Interference envelope
    interference = (1 + visibility * np.cos(phase)) / 2.0
    # Single-slit diffraction envelope
    slit_width = slit_sep / 5.0
    alpha = k * slit_width * np.sin(np.arctan(x_arr / 50.0)) / 2.0
    diffraction = np.where(np.abs(alpha) < 1e-10, 1.0, (np.sin(alpha) / alpha) ** 2)
    return interference * diffraction


def generate_gif(out_dir):
    import numpy as np
    import matplotlib
    matplotlib.use('Agg')
    matplotlib.rcParams['font.family'] = 'serif'
    matplotlib.rcParams['font.serif'] = ['Times New Roman', 'Palatino', 'DejaVu Serif']
    import matplotlib.pyplot as plt
    from matplotlib.gridspec import GridSpec
    import imageio.v2 as imageio

    x = np.linspace(-20, 20, 500)
    n_frames = 60
    info_vals = np.linspace(0, 1, n_frames)

    bg_color = '#0a0a1a'
    text_color = 'white'
    sub_text_color = '#888'
    grid_color = '#333'
    accent_color = '#e94560'
    trail_color = '#8b5cf6'

    gif_frames = []
    tmp_dir = os.path.join(out_dir, "tmp_frames")
    os.makedirs(tmp_dir, exist_ok=True)

    print(f"Generating {n_frames} frames...")

    for idx, info in enumerate(info_vals):
        vis = math.sqrt(max(0, 1 - info**2))  # Englert: V = sqrt(1 - I^2)
        residual = 1 - info  # Principle of Maximal Information Collapse

        fig = plt.figure(figsize=(13, 6.5), facecolor=bg_color)
        gs = GridSpec(1, 3, width_ratios=[3, 1.2, 1.2], wspace=0.35)

        # Main title — positioned with generous clearance from subplots
        fig.text(0.5, 0.96,
                 "The Thermodynamic Cost of Knowing",
                 ha='center', va='top', color=text_color, fontsize=15, fontweight='bold')
        fig.text(0.5, 0.915,
                 "Observation as irreversible payment — each fraction of a bit costs proportional Landauer energy",
                 ha='center', va='top', color=sub_text_color, fontsize=9, fontstyle='italic')

        # --- Panel 1: Interference pattern ---
        ax1 = fig.add_subplot(gs[0])
        ax1.set_facecolor('#0a0a1a')

        intensity = fringe_pattern(x, vis)

        # Filled intensity with gradient coloring
        colors = plt.cm.plasma(intensity)
        for i in range(len(x) - 1):
            ax1.fill_between(x[i:i+2], 0, intensity[i:i+2],
                           color=plt.cm.plasma(intensity[i] * 0.8 + 0.1), alpha=0.9)
        ax1.plot(x, intensity, color=accent_color, lw=1.5, alpha=0.8)

        ax1.set_xlim(-20, 20)
        ax1.set_ylim(0, 1.15)
        ax1.set_xlabel("Screen Position (detector array behind slits)", color=text_color, fontsize=10)
        ax1.set_ylabel("Intensity  (photon arrival probability)", color=text_color, fontsize=10)
        ax1.set_title("Photon Detection Screen", color=sub_text_color, fontsize=9, pad=4)
        ax1.tick_params(colors='white')
        for spine in ax1.spines.values():
            spine.set_color('#333')

        # Info/Vis annotation — placed inside plot area, clear of title
        ax1.text(0.98, 0.95, f"I = {info:.2f}  (which-path info)",
                color='#00d2ff', fontsize=9, transform=ax1.transAxes,
                verticalalignment='top', horizontalalignment='right', fontfamily='monospace')
        ax1.text(0.98, 0.87, f"V = {vis:.2f}  (fringe visibility)",
                color=accent_color, fontsize=9, transform=ax1.transAxes,
                verticalalignment='top', horizontalalignment='right', fontfamily='monospace')
        ax1.text(0.98, 0.79, f"V\u00b2 + I\u00b2 = {vis**2 + info**2:.2f} \u2264 1  (Englert)",
                color=sub_text_color, fontsize=8, transform=ax1.transAxes,
                verticalalignment='top', horizontalalignment='right', fontfamily='monospace')

        # --- Panel 2: Complementarity disk ---
        ax2 = fig.add_subplot(gs[1])
        ax2.set_facecolor('#0a0a1a')
        ax2.set_aspect('equal')

        # Quarter disk boundary
        theta = np.linspace(0, np.pi/2, 100)
        ax2.fill_between(np.cos(theta), 0, np.sin(theta), color='#1a1a3e', alpha=0.5)
        ax2.plot(np.cos(theta), np.sin(theta), color=grid_color, lw=1.5, ls='--')

        # Current state point
        ax2.plot(info, vis, 'o', color=accent_color, markersize=10, zorder=5)
        # Trail
        trail_i = info_vals[:idx+1]
        trail_v = np.sqrt(np.maximum(0, 1 - trail_i**2))
        ax2.plot(trail_i, trail_v, color=accent_color, lw=1, alpha=0.5)

        ax2.set_xlim(-0.05, 1.1)
        ax2.set_ylim(-0.05, 1.1)
        ax2.set_xlabel("I (info)", color=text_color, fontsize=9)
        ax2.set_ylabel("V (visibility)", color=text_color, fontsize=9)
        ax2.set_title("V\u00b2 + I\u00b2 \u2264 1", color=text_color, fontsize=10, fontweight='bold')
        ax2.tick_params(colors='white', labelsize=7)
        for spine in ax2.spines.values():
            spine.set_color('#333')

        # --- Panel 3: Residual coherence bar ---
        ax3 = fig.add_subplot(gs[2])
        ax3.set_facecolor('#0a0a1a')

        bar_colors = ['#e94560', '#533483']
        ax3.barh([0], [1 - residual], color=bar_colors[0], height=0.5, label='Extracted')
        ax3.barh([0], [residual], left=[1 - residual], color=bar_colors[1], height=0.5, label='Residual')

        ax3.set_xlim(0, 1)
        ax3.set_yticks([])
        ax3.set_xlabel("Fraction", color=text_color, fontsize=9)
        ax3.set_title("Coherence Capacity", color=text_color, fontsize=10, fontweight='bold')
        ax3.tick_params(colors='white', labelsize=7)
        for spine in ax3.spines.values():
            spine.set_color('#333')

        # Labels inside bars
        if (1 - residual) > 0.15:
            ax3.text((1 - residual)/2, 0, f"{(1-residual)*100:.0f}%",
                    ha='center', va='center', color=text_color, fontsize=10, fontweight='bold')
        if residual > 0.15:
            ax3.text(1 - residual + residual/2, 0, f"{residual*100:.0f}%",
                    ha='center', va='center', color=text_color, fontsize=10, fontweight='bold')

        ax3.legend(loc='upper right', fontsize=7, facecolor=bg_color,
                  edgecolor=grid_color, labelcolor=text_color)

        # Bottom annotation
        fig.text(0.5, 0.01,
                "Principle of Maximal Information Collapse: Residual = 1 \u2212 MI\u2091\u2093\u209c / (k\u0042 T ln 2)",
                ha='center', color=sub_text_color, fontsize=8, fontfamily='monospace')

        plt.subplots_adjust(top=0.85, bottom=0.14, left=0.06, right=0.97)
        frame_path = os.path.join(tmp_dir, f"frame_{idx:03d}.png")
        plt.savefig(frame_path, dpi=120, pad_inches=0.15,
                   facecolor=fig.get_facecolor(), edgecolor='none')
        gif_frames.append(imageio.imread(frame_path))
        plt.close()

        if (idx + 1) % 10 == 0:
            print(f"  Frame {idx + 1}/{n_frames}")

    # Save GIF with pause at start and end
    final_frames = gif_frames[:1] * 8 + gif_frames + gif_frames[-1:] * 12
    gif_path = os.path.join(out_dir, "double-slit-collapse.gif")
    imageio.mimsave(gif_path, final_frames, fps=12, loop=0)
    print(f"Wrote GIF to {gif_path}")

    # Cleanup
    for f in os.listdir(tmp_dir):
        os.remove(os.path.join(tmp_dir, f))
    os.rmdir(tmp_dir)

    return gif_path


def generate_teaser(out_dir):
    """Generate dark teaser (README) and light teaser (paper) images."""
    import numpy as np
    import matplotlib
    matplotlib.use('Agg')
    matplotlib.rcParams['font.family'] = 'serif'
    matplotlib.rcParams['font.serif'] = ['Times New Roman', 'Palatino', 'DejaVu Serif']
    import matplotlib.pyplot as plt
    from matplotlib.gridspec import GridSpec

    variants = [
        {   # Dark mode for README
            'suffix': '',  # teaser.png
            'bg': '#0a0a1a', 'text': 'white', 'sub': '#888', 'grid': '#333',
            'accent': '#e94560', 'trail': '#8b5cf6', 'fill_a': '#533483',
            'cyan': '#00d2ff', 'badge_bg': '#1a1a3e', 'badge_edge': '#333',
            'tick': 'white',
        },
        {   # Light mode for LaTeX paper
            'suffix': '-paper',  # teaser-paper.png
            'bg': '#ffffff', 'text': '#111111', 'sub': '#555555', 'grid': '#cccccc',
            'accent': '#c0392b', 'trail': '#6c3483', 'fill_a': '#d2b4de',
            'cyan': '#2471a3', 'badge_bg': '#eaf2f8', 'badge_edge': '#aab7b8',
            'tick': '#333333',
        },
    ]

    for v in variants:
        fig = plt.figure(figsize=(14, 7), facecolor=v['bg'])
        gs = GridSpec(1, 2, width_ratios=[1.3, 1], wspace=0.3)

        fig.text(0.5, 0.97,
                 "The Thermodynamic Cost of Knowing",
                 ha='center', va='top', color=v['text'], fontsize=16, fontweight='bold')
        fig.text(0.5, 0.93,
                 "Observation as Irreversible Payment",
                 ha='center', va='top', color=v['sub'], fontsize=11, fontstyle='italic')

        x = np.linspace(-20, 20, 500)

        # --- Left panel: Before/After comparison ---
        ax1 = fig.add_subplot(gs[0])
        ax1.set_facecolor(v['bg'])

        int_full = fringe_pattern(x, 1.0)
        ax1.fill_between(x, 0, int_full, color=v['fill_a'], alpha=0.4)
        ax1.plot(x, int_full, color=v['trail'], lw=2, label='No detector (V=1, full interference)')

        int_none = fringe_pattern(x, 0.0)
        ax1.fill_between(x, 0, int_none, color=v['accent'], alpha=0.3)
        ax1.plot(x, int_none, color=v['accent'], lw=2, ls='--', label='Which-path detector (V=0, collapsed)')

        ax1.set_xlim(-20, 20)
        ax1.set_ylim(0, 1.15)
        ax1.set_xlabel("Screen Position (detector array behind slits)", color=v['text'], fontsize=11)
        ax1.set_ylabel("Intensity (photon arrival probability)", color=v['text'], fontsize=11)
        ax1.set_title("Photon Detection Screen", color=v['sub'], fontsize=9, pad=4)
        ax1.legend(fontsize=9, facecolor=v['bg'], edgecolor=v['grid'], labelcolor=v['text'], loc='upper right')
        ax1.tick_params(colors=v['tick'])
        for spine in ax1.spines.values():
            spine.set_color(v['grid'])
        plt.subplots_adjust(top=0.85, bottom=0.12)

        # --- Right panel: Key equations ---
        ax2 = fig.add_subplot(gs[1])
        ax2.set_facecolor(v['bg'])
        ax2.axis('off')

        ax2.text(0.5, 0.95, "Formally Verified in Lean 4",
                ha='center', va='top', color=v['accent'], fontsize=14, fontweight='bold',
                transform=ax2.transAxes)

        equations = [
            (0.82, "Englert Complementarity", r"$V^2 + I^2 \leq 1$", v['cyan']),
            (0.68, "Landauer Bound", r"$Q \geq k_B T \cdot H$", v['trail']),
            (0.54, "Maximal Information Collapse",
             r"Residual $= 1 - \frac{\mathrm{MI}_{\mathrm{extracted}}}{k_B T \ln 2}$", v['accent']),
            (0.38, "", r"$\mathrm{MI} = 0 \Rightarrow$ full interference", v['sub']),
            (0.30, "", r"$\mathrm{MI} = k_B T \ln 2 \Rightarrow$ complete collapse", v['sub']),
        ]

        for y, label, eq, color in equations:
            if label:
                ax2.text(0.05, y + 0.04, label, ha='left', va='top', color=v['sub'],
                        fontsize=9, transform=ax2.transAxes, fontstyle='italic')
            ax2.text(0.08, y - 0.02, eq, ha='left', va='top', color=color,
                    fontsize=12, transform=ax2.transAxes)

        stats = "467 theorems  |  0 sorry  |  5 axioms  |  48 modules"
        ax2.text(0.5, 0.12, stats, ha='center', va='top', color=v['sub'],
                fontsize=10, transform=ax2.transAxes, fontfamily='monospace')

        ax2.text(0.5, 0.03, "The Thermodynamic Cost of Knowing",
                ha='center', va='top', color=v['text'], fontsize=13, fontweight='bold',
                transform=ax2.transAxes,
                bbox=dict(boxstyle='round,pad=0.4', facecolor=v['badge_bg'],
                          edgecolor=v['badge_edge'], alpha=0.8))

        teaser_path = os.path.join(out_dir, f"teaser{v['suffix']}.png")
        plt.savefig(teaser_path, dpi=150, pad_inches=0.15,
                   facecolor=fig.get_facecolor(), edgecolor='none')
        plt.close()
        print(f"Wrote teaser to {teaser_path}")

    return os.path.join(out_dir, "teaser.png")


def main():
    if not check_deps():
        sys.exit(1)

    repo_root = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
    out_dir = os.path.join(repo_root, "Docs", "Media")
    os.makedirs(out_dir, exist_ok=True)

    generate_gif(out_dir)
    generate_teaser(out_dir)

    print("\nDone! Files in Docs/:")
    print("  - double-slit-collapse.gif")
    print("  - teaser.png")


if __name__ == "__main__":
    main()
