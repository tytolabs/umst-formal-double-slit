#!/usr/bin/env python3
"""
Stdlib SVG: |psi|^2 vs x from `schrodinger_1d_split_step.py` output
(`schrodinger_split_step_rho.csv`, columns `x`, `rho`).
"""

from __future__ import annotations

import argparse
import csv
from pathlib import Path
from typing import List, Tuple


def _default_out() -> Path:
    return Path(__file__).resolve().parent / "out" / "schrodinger_split_step.svg"


def _parse_args() -> argparse.Namespace:
    p = argparse.ArgumentParser(description="SVG for split-step rho vs x.")
    p.add_argument(
        "--in",
        dest="in_path",
        type=str,
        default=None,
        help="CSV x,rho (default: sim/out/schrodinger_split_step_rho.csv)",
    )
    p.add_argument(
        "--out",
        type=str,
        default=None,
        help="Output SVG (default: sim/out/schrodinger_split_step.svg)",
    )
    p.add_argument(
        "--validate",
        action="store_true",
        help="Check x monotone, rho >= 0, len >= 8.",
    )
    return p.parse_args()


def read_csv(path: Path, validate: bool) -> Tuple[List[float], List[float]]:
    xs, rs = [], []
    with path.open("r", encoding="utf-8", newline="") as f:
        reader = csv.DictReader(f)
        for row in reader:
            xs.append(float(row["x"]))
            rs.append(float(row["rho"]))
    if len(xs) < 8:
        raise ValueError("need at least 8 rows")
    if validate:
        for r in rs:
            if r < -1e-12:
                raise ValueError("negative rho")
        for i in range(1, len(xs)):
            if xs[i] < xs[i - 1] - 1e-9:
                raise ValueError("x not monotone")
    return xs, rs


def build_svg(xs: List[float], rs: List[float], width: int = 680, height: int = 400) -> str:
    margin_l, margin_r, margin_t, margin_b = 72, 28, 44, 58
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

    def x_to_px(x: float) -> float:
        return ox + (x - x_min) / span * plot_w

    def r_to_py(r: float) -> float:
        return oy + plot_h - min(r / r_top, 1.0) * plot_h

    parts: List[str] = [
        '<?xml version="1.0" encoding="UTF-8"?>',
        f'<svg xmlns="http://www.w3.org/2000/svg" width="{width}" height="{height}" '
        f'viewBox="0 0 {width} {height}">',
        "  <defs>",
        '    <style type="text/css"><![CDATA[',
        "      .axis { stroke: #333; stroke-width: 1.2; fill: none; }",
        "      .rho { stroke: #2a7; stroke-width: 2.2; fill: none; }",
        "      .title { font-family: system-ui, sans-serif; font-size: 15px; font-weight: 600; fill: #111; }",
        "      .lbl { font-family: system-ui, sans-serif; font-size: 11px; fill: #222; }",
        "    ]]></style>",
        "  </defs>",
        (
            f'  <text x="{width // 2}" y="28" text-anchor="middle" class="title">'
            f"Strang split-step: |psi|^2 vs x</text>"
        ),
        f'  <line class="axis" x1="{ox}" y1="{oy + plot_h}" x2="{ox + plot_w}" y2="{oy + plot_h}"/>',
        f'  <line class="axis" x1="{ox}" y1="{oy}" x2="{ox}" y2="{oy + plot_h}"/>',
    ]
    d = [f"{x_to_px(xs[0]):.2f},{r_to_py(rs[0]):.2f}"]
    for i in range(1, len(xs)):
        d.append(f"{x_to_px(xs[i]):.2f},{r_to_py(rs[i]):.2f}")
    parts.append(f'  <path class="rho" d="M {" L ".join(d)}"/>')
    parts.extend(
        [
            f'  <text x="{ox + plot_w // 2}" y="{height - 20}" text-anchor="middle" class="lbl">x</text>',
            (
                f'  <text transform="translate(22 {oy + plot_h // 2}) rotate(-90)" text-anchor="middle" class="lbl">'
                f"|psi|^2</text>"
            ),
            "</svg>",
        ]
    )
    return "\n".join(parts) + "\n"


def main() -> None:
    args = _parse_args()
    default_csv = Path(__file__).resolve().parent / "out" / "schrodinger_split_step_rho.csv"
    in_path = Path(args.in_path) if args.in_path else default_csv
    out_path = Path(args.out) if args.out else _default_out()
    if not in_path.is_file():
        raise SystemExit(f"missing {in_path} — run schrodinger_1d_split_step.py first")
    xs, rs = read_csv(in_path, validate=args.validate)
    out_path.parent.mkdir(parents=True, exist_ok=True)
    out_path.write_text(build_svg(xs, rs), encoding="utf-8")
    print(f"Wrote {out_path}")


if __name__ == "__main__":
    main()
