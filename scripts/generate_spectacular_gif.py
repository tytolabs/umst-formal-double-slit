#!/usr/bin/env python3
"""Generate a spectacular double-slit interference collapse GIF + teaser image.

Usage:
    python3 scripts/generate_spectacular_gif.py

Outputs:
    Docs/double-slit-collapse.gif   — animated GIF
    Docs/teaser.png                 — static teaser image for social/README
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
    import matplotlib.pyplot as plt
    from matplotlib.gridspec import GridSpec
    import imageio.v2 as imageio

    x = np.linspace(-20, 20, 500)
    n_frames = 60
    info_vals = np.linspace(0, 1, n_frames)

    gif_frames = []
    tmp_dir = os.path.join(out_dir, "tmp_frames")
    os.makedirs(tmp_dir, exist_ok=True)

    print(f"Generating {n_frames} frames...")

    for idx, info in enumerate(info_vals):
        vis = math.sqrt(max(0, 1 - info**2))  # Englert: V = sqrt(1 - I^2)
        residual = 1 - info  # Principle of Maximal Information Collapse

        fig = plt.figure(figsize=(12, 6), facecolor='#0a0a1a')
        gs = GridSpec(1, 3, width_ratios=[3, 1.2, 1.2], wspace=0.35)

        # Main title above all panels (no overlap)
        fig.suptitle("Double-Slit Interference Collapse",
                     color='white', fontsize=14, fontweight='bold', y=0.97)
        fig.text(0.5, 0.935,
                 "Observing which slit the particle passes through destroys the interference pattern",
                 ha='center', color='#888', fontsize=9, fontstyle='italic')

        # --- Panel 1: Interference pattern ---
        ax1 = fig.add_subplot(gs[0])
        ax1.set_facecolor('#0a0a1a')

        intensity = fringe_pattern(x, vis)

        # Filled intensity with gradient coloring
        colors = plt.cm.plasma(intensity)
        for i in range(len(x) - 1):
            ax1.fill_between(x[i:i+2], 0, intensity[i:i+2],
                           color=plt.cm.plasma(intensity[i] * 0.8 + 0.1), alpha=0.9)
        ax1.plot(x, intensity, color='#e94560', lw=1.5, alpha=0.8)

        ax1.set_xlim(-20, 20)
        ax1.set_ylim(0, 1.15)
        ax1.set_xlabel("Screen Position (detector array behind slits)", color='white', fontsize=10)
        ax1.set_ylabel("Intensity  (photon arrival probability)", color='white', fontsize=10)
        ax1.set_title("Photon Detection Screen", color='#aaa', fontsize=10, pad=8)
        ax1.tick_params(colors='white')
        for spine in ax1.spines.values():
            spine.set_color('#333')

        # Info/Vis annotation — placed inside plot area, clear of title
        ax1.text(0.98, 0.95, f"I = {info:.2f}  (which-path info)",
                color='#00d2ff', fontsize=9, transform=ax1.transAxes,
                verticalalignment='top', horizontalalignment='right', fontfamily='monospace')
        ax1.text(0.98, 0.87, f"V = {vis:.2f}  (fringe visibility)",
                color='#e94560', fontsize=9, transform=ax1.transAxes,
                verticalalignment='top', horizontalalignment='right', fontfamily='monospace')
        ax1.text(0.98, 0.79, f"V\u00b2 + I\u00b2 = {vis**2 + info**2:.2f} \u2264 1  (Englert)",
                color='#aaa', fontsize=8, transform=ax1.transAxes,
                verticalalignment='top', horizontalalignment='right', fontfamily='monospace')

        # --- Panel 2: Complementarity disk ---
        ax2 = fig.add_subplot(gs[1])
        ax2.set_facecolor('#0a0a1a')
        ax2.set_aspect('equal')

        # Quarter disk boundary
        theta = np.linspace(0, np.pi/2, 100)
        ax2.fill_between(np.cos(theta), 0, np.sin(theta), color='#1a1a3e', alpha=0.5)
        ax2.plot(np.cos(theta), np.sin(theta), color='#333', lw=1.5, ls='--')

        # Current state point
        ax2.plot(info, vis, 'o', color='#e94560', markersize=10, zorder=5)
        # Trail
        trail_i = info_vals[:idx+1]
        trail_v = np.sqrt(np.maximum(0, 1 - trail_i**2))
        ax2.plot(trail_i, trail_v, color='#e94560', lw=1, alpha=0.5)

        ax2.set_xlim(-0.05, 1.1)
        ax2.set_ylim(-0.05, 1.1)
        ax2.set_xlabel("I (info)", color='white', fontsize=9)
        ax2.set_ylabel("V (visibility)", color='white', fontsize=9)
        ax2.set_title("V\u00b2 + I\u00b2 \u2264 1", color='white', fontsize=10, fontweight='bold')
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
        ax3.set_xlabel("Fraction", color='white', fontsize=9)
        ax3.set_title("Coherence Capacity", color='white', fontsize=10, fontweight='bold')
        ax3.tick_params(colors='white', labelsize=7)
        for spine in ax3.spines.values():
            spine.set_color('#333')

        # Labels inside bars
        if (1 - residual) > 0.15:
            ax3.text((1 - residual)/2, 0, f"{(1-residual)*100:.0f}%",
                    ha='center', va='center', color='white', fontsize=10, fontweight='bold')
        if residual > 0.15:
            ax3.text(1 - residual + residual/2, 0, f"{residual*100:.0f}%",
                    ha='center', va='center', color='white', fontsize=10, fontweight='bold')

        ax3.legend(loc='upper right', fontsize=7, facecolor='#0a0a1a',
                  edgecolor='#333', labelcolor='white')

        # Bottom annotation
        fig.text(0.5, 0.01,
                "Principle of Maximal Information Collapse: Residual = 1 \u2212 MI\u2091\u2093\u209c / (k\u0042 T ln 2)",
                ha='center', color='#888', fontsize=8, fontfamily='monospace')

        plt.subplots_adjust(top=0.88, bottom=0.14)
        frame_path = os.path.join(tmp_dir, f"frame_{idx:03d}.png")
        plt.savefig(frame_path, dpi=120, bbox_inches='tight',
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
    """Generate a static teaser image showing the key result."""
    import numpy as np
    import matplotlib
    matplotlib.use('Agg')
    import matplotlib.pyplot as plt
    from matplotlib.gridspec import GridSpec

    fig = plt.figure(figsize=(14, 7), facecolor='#0a0a1a')
    gs = GridSpec(1, 2, width_ratios=[1.3, 1], wspace=0.3)

    fig.suptitle("Measurement Destroys Interference",
                 color='white', fontsize=16, fontweight='bold', y=0.97)
    fig.text(0.5, 0.93,
             "Knowing which slit the particle traversed eliminates the wave pattern on the detection screen",
             ha='center', color='#888', fontsize=10, fontstyle='italic')

    x = np.linspace(-20, 20, 500)

    # --- Left panel: Before/After comparison ---
    ax1 = fig.add_subplot(gs[0])
    ax1.set_facecolor('#0a0a1a')

    # No measurement (V=1)
    int_full = fringe_pattern(x, 1.0)
    ax1.fill_between(x, 0, int_full, color='#533483', alpha=0.4)
    ax1.plot(x, int_full, color='#8b5cf6', lw=2, label='No detector (V=1, full interference)')

    # Full measurement (V=0)
    int_none = fringe_pattern(x, 0.0)
    ax1.fill_between(x, 0, int_none, color='#e94560', alpha=0.3)
    ax1.plot(x, int_none, color='#e94560', lw=2, ls='--', label='Which-path detector (V=0, collapsed)')

    ax1.set_xlim(-20, 20)
    ax1.set_ylim(0, 1.15)
    ax1.set_xlabel("Screen Position (detector array behind slits)", color='white', fontsize=11)
    ax1.set_ylabel("Intensity (photon arrival probability)", color='white', fontsize=11)
    ax1.set_title("Photon Detection Screen", color='#aaa', fontsize=10, pad=8)
    ax1.legend(fontsize=9, facecolor='#0a0a1a', edgecolor='#333', labelcolor='white', loc='upper right')
    ax1.tick_params(colors='white')
    for spine in ax1.spines.values():
        spine.set_color('#333')
    plt.subplots_adjust(top=0.86, bottom=0.12)

    # --- Right panel: Key equations ---
    ax2 = fig.add_subplot(gs[1])
    ax2.set_facecolor('#0a0a1a')
    ax2.axis('off')

    title_y = 0.95
    ax2.text(0.5, title_y, "Formally Verified in Lean 4",
            ha='center', va='top', color='#e94560', fontsize=14, fontweight='bold',
            transform=ax2.transAxes)

    equations = [
        (0.82, "Englert Complementarity", r"$V^2 + I^2 \leq 1$", '#00d2ff'),
        (0.68, "Landauer Bound", r"$Q \geq k_B T \cdot H$", '#8b5cf6'),
        (0.54, "Maximal Information Collapse",
         r"Residual $= 1 - \frac{\mathrm{MI}_{\mathrm{extracted}}}{k_B T \ln 2}$", '#e94560'),
        (0.38, "", r"$\mathrm{MI} = 0 \Rightarrow$ full interference", '#888'),
        (0.30, "", r"$\mathrm{MI} = k_B T \ln 2 \Rightarrow$ complete collapse", '#888'),
    ]

    for y, label, eq, color in equations:
        if label:
            ax2.text(0.05, y + 0.04, label, ha='left', va='top', color='#aaa',
                    fontsize=9, transform=ax2.transAxes, fontstyle='italic')
        ax2.text(0.08, y - 0.02, eq, ha='left', va='top', color=color,
                fontsize=12, transform=ax2.transAxes)

    # Stats bar
    stats_y = 0.12
    stats = "360 theorems  |  0 sorry  |  1 axiom  |  38 modules"
    ax2.text(0.5, stats_y, stats, ha='center', va='top', color='#666',
            fontsize=10, transform=ax2.transAxes, fontfamily='monospace')

    ax2.text(0.5, 0.03, "Measurement IS Thermodynamics",
            ha='center', va='top', color='white', fontsize=13, fontweight='bold',
            transform=ax2.transAxes,
            bbox=dict(boxstyle='round,pad=0.4', facecolor='#e94560', alpha=0.8))

    teaser_path = os.path.join(out_dir, "teaser.png")
    plt.savefig(teaser_path, dpi=150, bbox_inches='tight',
               facecolor=fig.get_facecolor(), edgecolor='none')
    plt.close()
    print(f"Wrote teaser to {teaser_path}")
    return teaser_path


def main():
    if not check_deps():
        sys.exit(1)

    repo_root = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
    out_dir = os.path.join(repo_root, "Docs")
    os.makedirs(out_dir, exist_ok=True)

    generate_gif(out_dir)
    generate_teaser(out_dir)

    print("\nDone! Files in Docs/:")
    print("  - double-slit-collapse.gif")
    print("  - teaser.png")


if __name__ == "__main__":
    main()
