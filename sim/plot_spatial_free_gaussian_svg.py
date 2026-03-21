#!/usr/bin/env python3
# SPDX-License-Identifier: MIT
# Copyright (c) 2026 Santhosh Shyamsundar, Santosh Prabhu Shenbagamoorthy — Studio TYTO

"""
Stdlib SVG: free 1D Gaussian |psi(x,t)|^2 vs x.

Samples `spatial_free_gaussian_1d.density` by default, or reads CSV from
`spatial_free_gaussian_1d.py` output (columns `x`, `rho`).
"""

from __future__ import annotations

import argparse
import csv
import importlib.util
from pathlib import Path
from typing import List, Tuple


def _load_spatial():
    here = Path(__file__).resolve().parent
    script = here / "spatial_free_gaussian_1d.py"
    spec = importlib.util.spec_from_file_location("spatial_free_gaussian_1d", script)
    mod = importlib.util.module_from_spec(spec)
    assert spec and spec.loader
    spec.loader.exec_module(mod)
    return mod


def _default_out() -> Path:
    return Path(__file__).resolve().parent / "out" / "spatial_free_gaussian.svg"


def _parse_args() -> argparse.Namespace:
    p = argparse.ArgumentParser(description="Free Gaussian |psi|^2 vs x (SVG).")
    p.add_argument(
        "--in",
        dest="in_path",
        type=str,
        default=None,
        help="Optional CSV (x,rho). If omitted, curve is computed.",
    )
    p.add_argument(
        "--out",
        type=str,
        default=None,
        help="Output SVG (default: sim/out/spatial_free_gaussian.svg)",
    )
    p.add_argument("--t", type=float, default=0.5)
    p.add_argument("--x0", type=float, default=0.0)
    p.add_argument("--k0", type=float, default=0.0)
    p.add_argument("--sigma0", type=float, default=1.0)
    p.add_argument(
        "--half-width",
        type=float,
        default=14.0,
        help="Sample x in [-w,w] (default: 14; widen if --validate integral fails).",
    )
    p.add_argument("--points", type=int, default=801)
    p.add_argument(
        "--validate",
        action="store_true",
        help="Check rho >= 0 and trapezoid integral ~ 1 on the sample grid.",
    )
    return p.parse_args()


def sample_curve(
    mod,
    *,
    t: float,
    x0: float,
    k0: float,
    sigma0: float,
    half_width: float,
    n: int,
    validate: bool,
) -> List[Tuple[float, float]]:
    if n < 3:
        raise ValueError("need at least 3 points")
    xs: list[float] = []
    ys: list[float] = []
    for i in range(n):
        frac = i / (n - 1)
        x = -half_width + 2.0 * half_width * frac
        xs.append(x)
        ys.append(mod.density(x, t, x0=x0, k0=k0, sigma0=sigma0))
    if validate:
        for x, y in zip(xs, ys):
            if y < -1e-12:
                raise ValueError(f"negative density at x={x}: rho={y}")
        integral = mod.trapezoid_integral(xs, ys)
        if abs(integral - 1.0) > 8e-3:
            raise ValueError(
                f"normalization off on grid (integral~{integral}); widen --half-width or increase --points"
            )
    return list(zip(xs, ys))


def read_curve_csv(path: Path, validate: bool) -> List[Tuple[float, float]]:
    out: List[Tuple[float, float]] = []
    xs: list[float] = []
    ys: list[float] = []
    with path.open("r", encoding="utf-8", newline="") as f:
        reader = csv.DictReader(f)
        for row in reader:
            x = float(row["x"])
            y = float(row["rho"])
            if validate and y < -1e-12:
                raise ValueError(f"CSV negative rho at x={x}")
            xs.append(x)
            ys.append(y)
            out.append((x, y))
    if len(out) < 3:
        raise ValueError("need at least 3 CSV rows")
    if validate:
        integral = _load_spatial().trapezoid_integral(xs, ys)
        if abs(integral - 1.0) > 8e-3:
            raise ValueError(f"CSV grid normalization off (integral~{integral})")
    return out


def build_svg(samples: List[Tuple[float, float]], width: int = 640, height: int = 420) -> str:
    margin_l, margin_r, margin_t, margin_b = 80, 36, 44, 64
    ox = margin_l
    oy = margin_t
    plot_w = width - margin_l - margin_r
    plot_h = height - margin_t - margin_b

    x_vals = [t[0] for t in samples]
    x_min, x_max = min(x_vals), max(x_vals)
    span = x_max - x_min
    if span <= 0.0:
        raise ValueError("degenerate x span")

    rho_max = max(t[1] for t in samples)
    y_top = max(rho_max * 1.08, 1e-9)

    def x_to_px(u: float) -> float:
        return ox + (u - x_min) / span * plot_w

    def rho_to_py(r: float) -> float:
        return oy + plot_h - min(r / y_top, 1.0) * plot_h

    parts: List[str] = [
        '<?xml version="1.0" encoding="UTF-8"?>',
        f'<svg xmlns="http://www.w3.org/2000/svg" width="{width}" height="{height}" '
        f'viewBox="0 0 {width} {height}">',
        "  <defs>",
        '    <style type="text/css"><![CDATA[',
        "      .axis { stroke: #333; stroke-width: 1.2; fill: none; }",
        "      .curve { stroke: #2a7; stroke-width: 2.2; fill: none; }",
        "      .title { font-family: system-ui, sans-serif; font-size: 15px; font-weight: 600; fill: #111; }",
        "      .lbl { font-family: system-ui, sans-serif; font-size: 11px; fill: #222; }",
        "    ]]></style>",
        "  </defs>",
        f'  <text x="{width // 2}" y="28" text-anchor="middle" class="title">'
        "Free 1D Gaussian: |psi(x,t)|^2 (closed form)</text>",
        f'  <line class="axis" x1="{ox}" y1="{oy + plot_h}" x2="{ox + plot_w}" y2="{oy + plot_h}"/>',
        f'  <line class="axis" x1="{ox}" y1="{oy}" x2="{ox}" y2="{oy + plot_h}"/>',
    ]

    d_parts = [f"{x_to_px(samples[0][0]):.2f},{rho_to_py(samples[0][1]):.2f}"]
    for u, r in samples[1:]:
        d_parts.append(f"{x_to_px(u):.2f},{rho_to_py(r):.2f}")
    d_attr = "M " + " L ".join(d_parts)
    parts.append(f'  <path class="curve" d="{d_attr}"/>')

    parts.extend(
        [
            f'  <text x="{ox + plot_w // 2}" y="{height - 22}" text-anchor="middle" class="lbl">x</text>',
            f'  <text transform="translate(26 {oy + plot_h // 2}) rotate(-90)" text-anchor="middle" class="lbl">'
            f"|psi|^2</text>",
            "</svg>",
        ]
    )
    return "\n".join(parts) + "\n"


def main() -> None:
    args = _parse_args()
    out_path = Path(args.out) if args.out else _default_out()
    mod = _load_spatial()

    if args.in_path:
        samples = read_curve_csv(Path(args.in_path), validate=args.validate)
    else:
        samples = sample_curve(
            mod,
            t=args.t,
            x0=args.x0,
            k0=args.k0,
            sigma0=args.sigma0,
            half_width=args.half_width,
            n=args.points,
            validate=args.validate,
        )

    svg = build_svg(samples)
    out_path.parent.mkdir(parents=True, exist_ok=True)
    out_path.write_text(svg, encoding="utf-8")
    print(f"Wrote {out_path}")


if __name__ == "__main__":
    main()
