#!/usr/bin/env python3
# SPDX-License-Identifier: MIT
# Copyright (c) 2026 Santhosh Shyamsundar, Santosh Prabhu Shenbagamoorthy — Studio TYTO

"""
Toy complementarity diagram (stdlib SVG): reads `results_double_slit_toy.csv` from
`sim/toy_double_slit_mi_gate.py` and plots the (I, V) curve with the V²+I²≤1 quarter-disk.

One sample per distinct `info_I` (first row wins). Validates V²+I²≤1 when `--validate`.
"""

from __future__ import annotations

import argparse
import csv
from pathlib import Path
from typing import Dict, List, Tuple


def _parse_args() -> argparse.Namespace:
    p = argparse.ArgumentParser(description="Toy complementarity SVG from toy double-slit CSV.")
    p.add_argument(
        "--in",
        dest="in_path",
        type=str,
        default=None,
        help="Input CSV (default: sim/out/results_double_slit_toy.csv)",
    )
    p.add_argument(
        "--out",
        type=str,
        default=None,
        help="Output SVG (default: sim/out/complementarity_toy_sweep.svg)",
    )
    p.add_argument(
        "--validate",
        action="store_true",
        help="Require each (I,V) to satisfy V²+I² ≤ 1 + 1e-6 (CSV rounds V).",
    )
    return p.parse_args()


def _defaults() -> Tuple[Path, Path]:
    d = Path(__file__).resolve().parent / "out"
    return d / "results_double_slit_toy.csv", d / "complementarity_toy_sweep.svg"


def _read_curve(csv_path: Path, validate: bool) -> List[Tuple[float, float]]:
    """Unique (I,V) by info_I, ascending I."""
    # CSV rounds V to 6 decimals; V²+I² can exceed 1 slightly — use loose tol.
    tol = 1e-6
    by_i: Dict[float, Tuple[float, float]] = {}
    with csv_path.open("r", encoding="utf-8", newline="") as f:
        reader = csv.DictReader(f)
        for row in reader:
            i_val = float(row["info_I"])
            v_val = float(row["visibility_V"])
            if validate and v_val * v_val + i_val * i_val > 1.0 + tol:
                raise ValueError(f"toy complementarity fail: I={i_val}, V={v_val}")
            if i_val not in by_i:
                by_i[i_val] = (i_val, v_val)
    curve = sorted(by_i.values(), key=lambda t: t[0])
    if len(curve) < 2:
        raise ValueError("need at least two distinct info_I values in CSV")
    return curve


def build_toy_svg(curve: List[Tuple[float, float]], width: int = 520, height: int = 480) -> str:
    margin_l, margin_r, margin_t, margin_b = 72, 40, 40, 72
    ox = margin_l
    oy = margin_t
    r = min(width - margin_l - margin_r, height - margin_t - margin_b)
    cx, cy = ox, oy + r
    x1, y1 = cx + r, cy
    x2, y2 = ox, cy - r

    def data_to_px(iv: float, vv: float) -> Tuple[float, float]:
        return ox + iv * r, oy + (1.0 - vv) * r

    parts: List[str] = [
        '<?xml version="1.0" encoding="UTF-8"?>',
        f'<svg xmlns="http://www.w3.org/2000/svg" width="{width}" height="{height}" '
        f'viewBox="0 0 {width} {height}">',
        "  <defs>",
        '    <style type="text/css"><![CDATA[',
        "      .axis { stroke: #333; stroke-width: 1.2; fill: none; }",
        "      .arc { stroke: #0a5; stroke-width: 2; fill: none; }",
        "      .fill { fill: rgba(10, 160, 80, 0.08); stroke: none; }",
        "      .curve { stroke: #06c; stroke-width: 2.5; fill: none; }",
        "      .title { font-family: system-ui, sans-serif; font-size: 15px; font-weight: 600; fill: #111; }",
        "      .lbl { font-family: system-ui, sans-serif; font-size: 11px; fill: #222; }",
        "    ]]></style>",
        "  </defs>",
        f'  <text x="{width // 2}" y="26" text-anchor="middle" class="title">'
        "Toy complementarity: V = sqrt(max(0, 1 - I^2)) vs feasible region</text>",
        f'  <path class="fill" d="M {ox} {cy} L {x1} {y1} A {r} {r} 0 0 1 {x2} {y2} L {ox} {cy} Z"/>',
        f'  <line class="axis" x1="{ox}" y1="{cy}" x2="{ox + r}" y2="{cy}"/>',
        f'  <line class="axis" x1="{ox}" y1="{cy}" x2="{ox}" y2="{cy - r}"/>',
        f'  <path class="arc" d="M {x1} {y1} A {r} {r} 0 0 1 {x2} {y2}"/>',
    ]

    d_parts = []
    for i, (iv, vv) in enumerate(curve):
        px, py = data_to_px(iv, vv)
        d_parts.append(f"{px:.2f},{py:.2f}")
    d_attr = "M " + " L ".join(d_parts)
    parts.append(f'  <path class="curve" d="{d_attr}"/>')

    parts.extend(
        [
            f'  <text x="{ox + r // 2}" y="{height - 28}" text-anchor="middle" class="lbl">'
            f"info gain I (toy)</text>",
            f'  <text transform="translate(22 {oy + r // 2}) rotate(-90)" text-anchor="middle" class="lbl">'
            f"visibility V</text>",
            "</svg>",
        ]
    )
    return "\n".join(parts) + "\n"


def main() -> None:
    args = _parse_args()
    din, dout = _defaults()
    in_path = Path(args.in_path) if args.in_path else din
    out_path = Path(args.out) if args.out else dout
    if not in_path.is_file():
        raise SystemExit(f"missing {in_path} — run toy_double_slit_mi_gate.py first")
    curve = _read_curve(in_path, validate=args.validate)
    svg = build_toy_svg(curve)
    out_path.parent.mkdir(parents=True, exist_ok=True)
    out_path.write_text(svg, encoding="utf-8")
    print(f"Wrote {out_path}")


if __name__ == "__main__":
    main()
