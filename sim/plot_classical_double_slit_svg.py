#!/usr/bin/env python3
# SPDX-License-Identifier: MIT
# Copyright (c) 2026 Santhosh Shyamsundar, Santosh Prabhu Shenbagamoorthy — Studio TYTO

"""
Stdlib SVG: classical Fraunhofer double-slit intensity vs sin(theta).

Either samples `classical_double_slit_far_field.intensity_normalized` directly
(default) or reads a CSV produced by `classical_double_slit_far_field.py`
(columns `sin_theta`, `intensity_norm`).
"""

from __future__ import annotations

import argparse
import csv
import importlib.util
from pathlib import Path
from typing import List, Tuple


def _load_classical():
    here = Path(__file__).resolve().parent
    script = here / "classical_double_slit_far_field.py"
    spec = importlib.util.spec_from_file_location("classical_double_slit_far_field", script)
    mod = importlib.util.module_from_spec(spec)
    assert spec and spec.loader
    spec.loader.exec_module(mod)
    return mod


def _parse_args() -> argparse.Namespace:
    p = argparse.ArgumentParser(description="Classical double-slit far-field intensity SVG.")
    p.add_argument(
        "--in",
        dest="in_path",
        type=str,
        default=None,
        help="Optional CSV (sin_theta,intensity_norm). If omitted, curve is computed.",
    )
    p.add_argument(
        "--out",
        type=str,
        default=None,
        help="Output SVG (default: sim/out/classical_double_slit_far_field.svg)",
    )
    p.add_argument("--lam", type=float, default=500e-9)
    p.add_argument("--a", type=float, default=10e-6)
    p.add_argument("--d", type=float, default=100e-6)
    p.add_argument("--sin-max", type=float, default=0.02)
    p.add_argument("--points", type=int, default=801)
    p.add_argument(
        "--validate",
        action="store_true",
        help="Check intensities in [0,1] (loose) and even symmetry when sampling.",
    )
    return p.parse_args()


def _default_out() -> Path:
    return Path(__file__).resolve().parent / "out" / "classical_double_slit_far_field.svg"


def sample_curve(
    mod,
    *,
    lam: float,
    a: float,
    d: float,
    sin_max: float,
    n: int,
    validate: bool,
) -> List[Tuple[float, float]]:
    if n < 3:
        raise ValueError("need at least 3 points")
    st_min, st_max = -sin_max, sin_max
    pts: List[Tuple[float, float]] = []
    for i in range(n):
        u = st_min + (st_max - st_min) * i / (n - 1)
        v = mod.intensity_normalized(u, lam, a, d)
        pts.append((u, v))
    if validate:
        tol = 1e-5
        for u, y in pts:
            if y < -tol or y > 1.0 + 1e-3:
                raise ValueError(f"intensity out of range: sinθ={u}, I={y}")
        mid = n // 2
        for k in (1, 2, 3, 10, min(20, mid - 1)):
            if mid + k >= n:
                break
            y_p = pts[mid + k][1]
            y_m = pts[mid - k][1]
            if abs(y_p - y_m) > 1e-5:
                raise ValueError(f"symmetry fail at offset {k}: {y_p} vs {y_m}")
    return pts


def read_curve_csv(path: Path, validate: bool) -> List[Tuple[float, float]]:
    tol = 1e-5
    out: List[Tuple[float, float]] = []
    with path.open("r", encoding="utf-8", newline="") as f:
        reader = csv.DictReader(f)
        for row in reader:
            u = float(row["sin_theta"])
            y = float(row["intensity_norm"])
            if validate and (y < -tol or y > 1.0 + 1e-3):
                raise ValueError(f"CSV intensity out of range: sinθ={u}, I={y}")
            out.append((u, y))
    if len(out) < 3:
        raise ValueError("need at least 3 CSV rows")
    return out


def build_svg(samples: List[Tuple[float, float]], width: int = 640, height: int = 420) -> str:
    margin_l, margin_r, margin_t, margin_b = 80, 36, 44, 64
    ox = margin_l
    oy = margin_t
    plot_w = width - margin_l - margin_r
    plot_h = height - margin_t - margin_b

    st_vals = [t[0] for t in samples]
    st_min, st_max = min(st_vals), max(st_vals)
    span = st_max - st_min
    if span <= 0.0:
        raise ValueError("degenerate sin_theta span")

    i_max = max(t[1] for t in samples)
    y_top = max(1.05 * i_max, 0.05)

    def st_to_x(u: float) -> float:
        return ox + (u - st_min) / span * plot_w

    def i_to_y(ii: float) -> float:
        return oy + plot_h - min(ii / y_top, 1.0) * plot_h

    parts: List[str] = [
        '<?xml version="1.0" encoding="UTF-8"?>',
        f'<svg xmlns="http://www.w3.org/2000/svg" width="{width}" height="{height}" '
        f'viewBox="0 0 {width} {height}">',
        "  <defs>",
        '    <style type="text/css"><![CDATA[',
        "      .axis { stroke: #333; stroke-width: 1.2; fill: none; }",
        "      .curve { stroke: #06c; stroke-width: 2.2; fill: none; }",
        "      .title { font-family: system-ui, sans-serif; font-size: 15px; font-weight: 600; fill: #111; }",
        "      .lbl { font-family: system-ui, sans-serif; font-size: 11px; fill: #222; }",
        "    ]]></style>",
        "  </defs>",
        f'  <text x="{width // 2}" y="28" text-anchor="middle" class="title">'
        "Classical Fraunhofer double-slit: normalized intensity vs sin(theta)</text>",
        f'  <line class="axis" x1="{ox}" y1="{oy + plot_h}" x2="{ox + plot_w}" y2="{oy + plot_h}"/>',
        f'  <line class="axis" x1="{ox}" y1="{oy}" x2="{ox}" y2="{oy + plot_h}"/>',
    ]

    d_parts = [f"{st_to_x(samples[0][0]):.2f},{i_to_y(samples[0][1]):.2f}"]
    for u, ii in samples[1:]:
        d_parts.append(f"{st_to_x(u):.2f},{i_to_y(ii):.2f}")
    d_attr = "M " + " L ".join(d_parts)
    parts.append(f'  <path class="curve" d="{d_attr}"/>')

    parts.extend(
        [
            f'  <text x="{ox + plot_w // 2}" y="{height - 22}" text-anchor="middle" class="lbl">'
            f"sin(theta)</text>",
            f'  <text transform="translate(26 {oy + plot_h // 2}) rotate(-90)" text-anchor="middle" class="lbl">'
            f"normalized I</text>",
            "</svg>",
        ]
    )
    return "\n".join(parts) + "\n"


def main() -> None:
    args = _parse_args()
    out_path = Path(args.out) if args.out else _default_out()
    mod = _load_classical()

    if args.in_path:
        samples = read_curve_csv(Path(args.in_path), validate=args.validate)
    else:
        samples = sample_curve(
            mod,
            lam=args.lam,
            a=args.a,
            d=args.d,
            sin_max=args.sin_max,
            n=args.points,
            validate=args.validate,
        )

    svg = build_svg(samples)
    out_path.parent.mkdir(parents=True, exist_ok=True)
    out_path.write_text(svg, encoding="utf-8")
    print(f"Wrote {out_path}")


if __name__ == "__main__":
    main()
