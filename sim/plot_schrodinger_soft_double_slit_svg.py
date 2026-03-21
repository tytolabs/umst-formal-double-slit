#!/usr/bin/env python3
# SPDX-License-Identifier: MIT
# Copyright (c) 2026 Santhosh Shyamsundar, Santosh Prabhu Shenbagamoorthy — Studio TYTO

"""
Stdlib SVG: |psi|^2 (rho) and potential V vs x from
`schrodinger_1d_soft_double_slit.py` output CSV (`x`, `V`, `rho`).

V is drawn scaled into the upper portion of the plot band so both curves are
visible without a second axis.
"""

from __future__ import annotations

import argparse
import csv
from pathlib import Path
from typing import List, Tuple


def _default_out() -> Path:
    return Path(__file__).resolve().parent / "out" / "schrodinger_soft_double_slit.svg"


def _parse_args() -> argparse.Namespace:
    p = argparse.ArgumentParser(description="SVG for soft double-slit rho + V vs x.")
    p.add_argument(
        "--in",
        dest="in_path",
        type=str,
        default=None,
        help="CSV with x,V,rho (default: sim/out/schrodinger_soft_double_slit_rho.csv)",
    )
    p.add_argument(
        "--out",
        type=str,
        default=None,
        help="Output SVG (default: sim/out/schrodinger_soft_double_slit.svg)",
    )
    p.add_argument(
        "--validate",
        action="store_true",
        help="Check x roughly monotone, rho >= 0, at least 8 rows.",
    )
    return p.parse_args()


def read_csv(path: Path, validate: bool) -> Tuple[List[float], List[float], List[float]]:
    xs, vs, rs = [], [], []
    with path.open("r", encoding="utf-8", newline="") as f:
        reader = csv.DictReader(f)
        for row in reader:
            xs.append(float(row["x"]))
            vs.append(float(row["V"]))
            rs.append(float(row["rho"]))
    if len(xs) < 8:
        raise ValueError("need at least 8 CSV rows")
    if validate:
        for r in rs:
            if r < -1e-12:
                raise ValueError("negative rho in CSV")
        for i in range(1, len(xs)):
            if xs[i] < xs[i - 1] - 1e-9:
                raise ValueError("x not monotone increasing in CSV")
    return xs, vs, rs


def build_svg(
    xs: List[float],
    vs: List[float],
    rs: List[float],
    width: int = 700,
    height: int = 420,
) -> str:
    margin_l, margin_r, margin_t, margin_b = 72, 28, 44, 62
    ox = margin_l
    oy = margin_t
    plot_w = width - margin_l - margin_r
    plot_h = height - margin_t - margin_b

    x_min, x_max = min(xs), max(xs)
    span = x_max - x_min
    if span <= 0.0:
        raise ValueError("degenerate x span")

    r_max = max(rs) if rs else 1.0
    r_top = max(r_max * 1.06, 1e-12)
    v_max = max(vs) if vs else 1.0
    v_scale = 0.32 * r_top / max(v_max, 1e-12)

    def x_to_px(x: float) -> float:
        return ox + (x - x_min) / span * plot_w

    def val_to_py(val: float) -> float:
        return oy + plot_h - min(val / r_top, 1.0) * plot_h

    parts: List[str] = [
        '<?xml version="1.0" encoding="UTF-8"?>',
        f'<svg xmlns="http://www.w3.org/2000/svg" width="{width}" height="{height}" '
        f'viewBox="0 0 {width} {height}">',
        "  <defs>",
        '    <style type="text/css"><![CDATA[',
        "      .axis { stroke: #333; stroke-width: 1.2; fill: none; }",
        "      .rho { stroke: #06c; stroke-width: 2.2; fill: none; }",
        "      .pot { stroke: #a40; stroke-width: 1.6; fill: none; opacity: 0.85; }",
        "      .title { font-family: system-ui, sans-serif; font-size: 15px; font-weight: 600; fill: #111; }",
        "      .lbl { font-family: system-ui, sans-serif; font-size: 11px; fill: #222; }",
        "      .note { font-family: system-ui, sans-serif; font-size: 10px; fill: #555; }",
        "    ]]></style>",
        "  </defs>",
        (
            f'  <text x="{width // 2}" y="28" text-anchor="middle" class="title">'
            f"Soft double-slit (1D): |psi|^2 and scaled V(x)</text>"
        ),
        f'  <line class="axis" x1="{ox}" y1="{oy + plot_h}" x2="{ox + plot_w}" y2="{oy + plot_h}"/>',
        f'  <line class="axis" x1="{ox}" y1="{oy}" x2="{ox}" y2="{oy + plot_h}"/>',
        f'  <text x="{ox + plot_w - 4}" y="{oy + 14}" text-anchor="end" class="note">V scaled ×{v_scale:.3g}</text>',
    ]

    d_rho = [f"{x_to_px(xs[0]):.2f},{val_to_py(rs[0]):.2f}"]
    d_v = [f"{x_to_px(xs[0]):.2f},{val_to_py(vs[0] * v_scale):.2f}"]
    for i in range(1, len(xs)):
        d_rho.append(f"{x_to_px(xs[i]):.2f},{val_to_py(rs[i]):.2f}")
        d_v.append(f"{x_to_px(xs[i]):.2f},{val_to_py(vs[i] * v_scale):.2f}")
    parts.append(f'  <path class="pot" d="M {" L ".join(d_v)}"/>')
    parts.append(f'  <path class="rho" d="M {" L ".join(d_rho)}"/>')

    parts.extend(
        [
            f'  <text x="{ox + plot_w // 2}" y="{height - 22}" text-anchor="middle" class="lbl">x</text>',
            (
                f'  <text transform="translate(24 {oy + plot_h // 2}) rotate(-90)" text-anchor="middle" class="lbl">'
                f"rho / scaled V</text>"
            ),
            "</svg>",
        ]
    )
    return "\n".join(parts) + "\n"


def main() -> None:
    args = _parse_args()
    default_csv = Path(__file__).resolve().parent / "out" / "schrodinger_soft_double_slit_rho.csv"
    in_path = Path(args.in_path) if args.in_path else default_csv
    out_path = Path(args.out) if args.out else _default_out()
    if not in_path.is_file():
        raise SystemExit(f"missing {in_path} — run schrodinger_1d_soft_double_slit.py first")
    xs, vs, rs = read_csv(in_path, validate=args.validate)
    svg = build_svg(xs, vs, rs)
    out_path.parent.mkdir(parents=True, exist_ok=True)
    out_path.write_text(svg, encoding="utf-8")
    print(f"Wrote {out_path}")


if __name__ == "__main__":
    main()
