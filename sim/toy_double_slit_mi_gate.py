#!/usr/bin/env python3
# SPDX-License-Identifier: MIT
# Copyright (c) 2026 Santhosh Shyamsundar, Santosh Prabhu Shenbagamoorthy — Studio TYTO

"""
Toy MI+gate double-slit simulator.

Purpose:
- Demonstrate a controlled "info up -> visibility down" curve.
- Attach an explicit info-energy lower bound (Landauer-style).

This is an illustrative model, not a full quantum derivation.
"""

from __future__ import annotations

import argparse
import csv
import math
from pathlib import Path


K_B = 1.380649e-23  # J/K
LN2 = math.log(2.0)


def visibility_from_info(i_val: float) -> float:
    """Use V = sqrt(max(0, 1 - I^2)) as a complementarity toy law."""
    return math.sqrt(max(0.0, 1.0 - i_val * i_val))


def landauer_energy(bits: float, temp_k: float) -> float:
    """Lower bound energy to erase `bits` at `temp_k`."""
    return K_B * temp_k * LN2 * bits


def fringe_intensity(x: float, visibility: float) -> float:
    """
    Simple normalized fringe profile:
    I(x) = 0.5 * (1 + V * cos(2*pi*x))
    """
    return 0.5 * (1.0 + visibility * math.cos(2.0 * math.pi * x))


def _parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(description="Toy MI+gate double-slit simulator.")
    parser.add_argument(
        "--temp-k",
        type=float,
        default=300.0,
        help="Temperature in Kelvin for Landauer energy (default: 300).",
    )
    parser.add_argument(
        "--x-steps",
        type=int,
        default=40,
        help="Number of x-intervals on [0,1] (default: 40).",
    )
    parser.add_argument(
        "--info-steps",
        type=int,
        default=20,
        help="Number of I-intervals on [0,1] (default: 20).",
    )
    parser.add_argument(
        "--out",
        type=str,
        default=None,
        help="Output CSV path (default: sim/out/results_double_slit_toy.csv).",
    )
    parser.add_argument(
        "--summary-csv",
        type=str,
        default=None,
        help="Optional summary CSV path (one row per info_I).",
    )
    parser.add_argument(
        "--validate",
        action="store_true",
        help="Validate complementarity and intensity bounds while generating rows.",
    )
    parser.add_argument(
        "--plot",
        action="store_true",
        help="Generate a static matplotlib plot for the complementarity curves.",
    )
    parser.add_argument(
        "--generate-gif",
        action="store_true",
        help="Generate an animated GIF of the interference pattern collapse.",
    )
    return parser.parse_args()


def _default_out_csv() -> Path:
    return Path(__file__).resolve().parent / "out" / "results_double_slit_toy.csv"


def _validate_row(info: float, vis: float, intensity: float, tol: float = 1e-9) -> None:
    # Toy complementarity law should satisfy V^2 + I^2 <= 1.
    comp = vis * vis + info * info
    if comp > 1.0 + tol:
        raise ValueError(f"Complementarity violation: I={info}, V={vis}, V^2+I^2={comp}")
    if intensity < -tol or intensity > 1.0 + tol:
        raise ValueError(f"Intensity out of bounds [0,1]: {intensity}")


def main() -> None:
    args = _parse_args()
    out_csv = Path(args.out) if args.out else _default_out_csv()
    out_csv.parent.mkdir(parents=True, exist_ok=True)

    if args.x_steps <= 0 or args.info_steps <= 0:
        raise ValueError("--x-steps and --info-steps must be positive")

    temp_k = args.temp_k
    x_samples = [i / float(args.x_steps) for i in range(args.x_steps + 1)]
    info_grid = [i / float(args.info_steps) for i in range(args.info_steps + 1)]  # 0..1

    rows = []
    summary_rows = []
    for info in info_grid:
        vis = visibility_from_info(info)
        e_min = landauer_energy(info, temp_k)
        comp = vis * vis + info * info
        summary_rows.append(
            {
                "info_I": f"{info:.6f}",
                "visibility_V": f"{vis:.6f}",
                "V_sq_plus_I_sq": f"{comp:.10f}",
                "landauer_energy_j": f"{e_min:.12e}",
                "temp_k": f"{temp_k:.4f}",
            }
        )
        for x in x_samples:
            intensity = fringe_intensity(x, vis)
            if args.validate:
                _validate_row(info, vis, intensity)
            rows.append(
                {
                    "info_I": f"{info:.6f}",
                    "visibility_V": f"{vis:.6f}",
                    "V_sq_plus_I_sq": f"{comp:.10f}",
                    "x": f"{x:.6f}",
                    "intensity": f"{intensity:.8f}",
                    "landauer_energy_j": f"{e_min:.12e}",
                    "temp_k": f"{temp_k:.4f}",
                }
            )

    with out_csv.open("w", newline="", encoding="utf-8") as f:
        writer = csv.DictWriter(
            f,
            fieldnames=[
                "info_I",
                "visibility_V",
                "V_sq_plus_I_sq",
                "x",
                "intensity",
                "landauer_energy_j",
                "temp_k",
            ],
        )
        writer.writeheader()
        writer.writerows(rows)

    if args.summary_csv:
        summary_path = Path(args.summary_csv)
        summary_path.parent.mkdir(parents=True, exist_ok=True)
        with summary_path.open("w", newline="", encoding="utf-8") as f:
            writer = csv.DictWriter(
                f,
                fieldnames=[
                    "info_I",
                    "visibility_V",
                    "V_sq_plus_I_sq",
                    "landauer_energy_j",
                    "temp_k",
                ],
            )
            writer.writeheader()
            writer.writerows(summary_rows)
        print(f"Wrote {len(summary_rows)} summary rows to {summary_path}")

    print(f"Wrote {len(rows)} rows to {out_csv}")

    if args.plot or args.generate_gif:
        try:
            import matplotlib.pyplot as plt
        except ImportError:
            print("matplotlib is required for --plot or --generate-gif. Install it via pip.")
            return

        if args.plot:
            plt.figure(figsize=(8, 6))
            I_vals = [float(r["info_I"]) for r in summary_rows]
            V_vals = [float(r["visibility_V"]) for r in summary_rows]
            plt.plot(I_vals, V_vals, 'b-', label='Visibility (V)')
            plt.plot(I_vals, [1]*len(I_vals), 'k:', alpha=0.5)
            plt.fill_between(I_vals, 0, V_vals, alpha=0.1, color='blue')
            plt.xlabel("Distinguishability Info (I)")
            plt.ylabel("Visibility (V)")
            plt.title("Complementarity Curve: V vs I")
            plt.legend()
            plot_path = out_csv.parent / "complementarity_toy_plot.png"
            plt.savefig(plot_path)
            print(f"Wrote plot to {plot_path}")

        if args.generate_gif:
            try:
                import imageio.v2 as imageio
            except ImportError:
                print("imageio is required for --generate-gif. Install it via pip.")
                return

            gif_frames = []
            tmp_dir = out_csv.parent / "tmp_frames"
            tmp_dir.mkdir(exist_ok=True)

            print("Generating GIF frames...")
            for idx, info in enumerate(info_grid):
                plt.figure(figsize=(8, 6))
                vis = visibility_from_info(info)
                y_vals = [fringe_intensity(x, vis) for x in x_samples]
                plt.plot(x_samples, y_vals, 'k-', lw=2)
                plt.ylim(0, 1.05)
                plt.xlabel("Screen Position (x)")
                plt.ylabel("Intensity")
                plt.title(f"Interference Collapse (Info I={info:.2f}, Vis V={vis:.2f})")

                frame_path = tmp_dir / f"frame_{idx:03d}.png"
                plt.savefig(frame_path)
                gif_frames.append(imageio.imread(frame_path))
                plt.close()

            gif_path = out_csv.parent / "interference_collapse.gif"
            imageio.mimsave(gif_path, gif_frames, fps=10)
            print(f"Wrote GIF to {gif_path}")

            for f in tmp_dir.glob("*.png"):
                f.unlink()
            tmp_dir.rmdir()


if __name__ == "__main__":
    main()

