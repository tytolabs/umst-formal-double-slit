#!/usr/bin/env python3
# SPDX-License-Identifier: MIT
# Copyright (c) 2026 Santhosh Shyamsundar, Santosh Prabhu Shenbagamoorthy — Studio TYTO

"""
Publication-style complementarity diagram (stdlib only): Englert quarter-disk V²+I²≤1 in the (I, V) plane.

Reads `qubit_kraus_sweep.csv` (columns `whichPathDistinguishability_I`, `fringeVisibility_V`, `state`, `channel`)
and writes a minimal SVG suitable for papers/slides.
"""

from __future__ import annotations

import argparse
import csv
import re
import xml.sax.saxutils
from pathlib import Path
from typing import List, Tuple


def _parse_args() -> argparse.Namespace:
    p = argparse.ArgumentParser(description="Plot complementarity diagram from qubit sweep CSV (SVG).")
    p.add_argument(
        "--in",
        dest="in_path",
        type=str,
        default=None,
        help="Input CSV (default: sim/out/qubit_kraus_sweep.csv next to this script)",
    )
    p.add_argument(
        "--out",
        type=str,
        default=None,
        help="Output SVG (default: sim/out/complementarity_qubit_sweep.svg)",
    )
    p.add_argument(
        "--validate",
        action="store_true",
        help="Require every point to satisfy V²+I² ≤ 1 + 1e-9.",
    )
    return p.parse_args()


def _default_paths() -> Tuple[Path, Path]:
    root = Path(__file__).resolve().parent
    out_dir = root / "out"
    return out_dir / "qubit_kraus_sweep.csv", out_dir / "complementarity_qubit_sweep.svg"


def _read_points(csv_path: Path, validate: bool) -> List[Tuple[float, float, str]]:
    rows: List[Tuple[float, float, str]] = []
    tol = 1e-9
    with csv_path.open("r", encoding="utf-8", newline="") as f:
        reader = csv.DictReader(f)
        for row in reader:
            i_val = float(row["whichPathDistinguishability_I"])
            v_val = float(row["fringeVisibility_V"])
            label = f"{row['state']}/{row['channel']}"
            if validate and v_val * v_val + i_val * i_val > 1.0 + tol:
                raise ValueError(f"complementarity violated for {label}: V²+I²={v_val**2+i_val**2}")
            rows.append((i_val, v_val, label))
    return rows


def _svg_escape(s: str) -> str:
    return xml.sax.saxutils.escape(s)


def _sanitize_id(s: str) -> str:
    return re.sub(r"[^a-zA-Z0-9_-]+", "_", s)


def build_svg(points: List[Tuple[float, float, str]], width: int = 520, height: int = 480) -> str:
    """
    I horizontal [0,1], V vertical up (SVG y down): y = top + (1-V)*plot_h.
    Feasible set: quarter circle I²+V²≤1 in first quadrant.
    """
    margin_l, margin_r, margin_t, margin_b = 72, 40, 40, 72
    pw = width - margin_l - margin_r
    ph = height - margin_t - margin_b
    ox = margin_l
    oy = margin_t

    # Quarter-circle arc: center (ox, oy+ph), radius pw (== ph assumed square plot)
    r = min(pw, ph)
    cx, cy = ox, oy + r
    # Arc from (I,V)=(1,0) -> (ox+r, cy) to (0,1) -> (ox, cy-r)
    x1, y1 = cx + r, cy
    x2, y2 = ox, cy - r

    def data_to_px(iv: float, vv: float) -> Tuple[float, float]:
        x = ox + iv * r
        y = oy + (1.0 - vv) * r
        return x, y

    lines = [
        '<?xml version="1.0" encoding="UTF-8"?>',
        f'<svg xmlns="http://www.w3.org/2000/svg" width="{width}" height="{height}" '
        f'viewBox="0 0 {width} {height}">',
        '  <defs>',
        '    <style type="text/css"><![CDATA[',
        "      .axis { stroke: #333; stroke-width: 1.2; fill: none; }",
        "      .arc { stroke: #0a5; stroke-width: 2; fill: none; }",
        "      .fill { fill: rgba(10, 160, 80, 0.08); stroke: none; }",
        "      .point { fill: #c03; stroke: #fff; stroke-width: 1.5; }",
        "      .lbl { font-family: system-ui, sans-serif; font-size: 11px; fill: #222; }",
        "      .title { font-family: system-ui, sans-serif; font-size: 15px; font-weight: 600; fill: #111; }",
        "    ]]></style>",
        "  </defs>",
        f'  <text x="{width // 2}" y="26" text-anchor="middle" class="title">'
        f"{_svg_escape('Complementarity (qubit path bit): V² + I² ≤ 1')}</text>",
        # Feasible region: wedge under arc
        f'  <path class="fill" d="M {ox} {cy} L {x1} {y1} A {r} {r} 0 0 1 {x2} {y2} L {ox} {cy} Z"/>',
        # Axes
        f'  <line class="axis" x1="{ox}" y1="{cy}" x2="{ox + r}" y2="{cy}"/>',
        f'  <line class="axis" x1="{ox}" y1="{cy}" x2="{ox}" y2="{cy - r}"/>',
        f'  <path class="arc" d="M {x1} {y1} A {r} {r} 0 0 1 {x2} {y2}"/>',
    ]

    # Axis labels
    lines.append(
        f'  <text x="{ox + r // 2}" y="{height - 28}" text-anchor="middle" class="lbl">'
        f"{_svg_escape('which-path distinguishability I')}</text>"
    )
    lines.append(
        f'  <text transform="translate(22 {oy + r // 2}) rotate(-90)" text-anchor="middle" class="lbl">'
        f"{_svg_escape('fringe visibility V')}</text>"
    )
    lines.append(f'  <text x="{ox + r - 4}" y="{cy + 14}" text-anchor="end" class="lbl">1</text>')
    lines.append(f'  <text x="{ox - 6}" y="{cy - r + 4}" text-anchor="end" class="lbl">1</text>')
    lines.append(f'  <text x="{ox - 4}" y="{cy + 4}" text-anchor="end" class="lbl">0</text>')

    for i_val, v_val, label in points:
        px, py = data_to_px(i_val, v_val)
        pid = _sanitize_id(label)
        lines.append(f'  <circle class="point" cx="{px:.2f}" cy="{py:.2f}" r="5" id="pt_{pid}"/>')
        lx = px + 8
        ly = py - 6
        if lx + 120 > width - 8:
            lx = px - 128
        if ly < margin_t + 4:
            ly = py + 14
        lines.append(
            f'  <text x="{lx:.2f}" y="{ly:.2f}" class="lbl">{_svg_escape(label)}</text>'
        )

    lines.append("</svg>")
    return "\n".join(lines) + "\n"


def main() -> None:
    args = _parse_args()
    default_in, default_out = _default_paths()
    in_path = Path(args.in_path) if args.in_path else default_in
    out_path = Path(args.out) if args.out else default_out
    if not in_path.is_file():
        raise SystemExit(f"missing input CSV: {in_path} (run qubit_kraus_sweep.py first)")
    points = _read_points(in_path, validate=args.validate)
    svg = build_svg(points)
    out_path.parent.mkdir(parents=True, exist_ok=True)
    out_path.write_text(svg, encoding="utf-8")
    print(f"Wrote {out_path}")


if __name__ == "__main__":
    main()
