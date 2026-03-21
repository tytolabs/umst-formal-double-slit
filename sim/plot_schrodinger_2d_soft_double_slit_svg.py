#!/usr/bin/env python3
"""
Stdlib SVG heatmap: |psi|^2 from ``schrodinger_2d_soft_double_slit.py`` CSV
(columns ``x``, ``y``, ``rho``).

Downsamples with ``--stride`` if the grid is large (fewer SVG rects).
"""

from __future__ import annotations

import argparse
import csv
from pathlib import Path
from typing import List, Sequence, Tuple


def _default_out() -> Path:
    return Path(__file__).resolve().parent / "out" / "schrodinger_2d_soft_double_slit.svg"


def _parse_args() -> argparse.Namespace:
    p = argparse.ArgumentParser(description="SVG heatmap for 2D soft double-slit rho CSV.")
    p.add_argument(
        "--in",
        dest="in_path",
        type=str,
        default=None,
        help="CSV x,y,rho (default: sim/out/schrodinger_2d_soft_double_slit_rho.csv)",
    )
    p.add_argument(
        "--out",
        type=str,
        default=None,
        help="Output SVG (default: sim/out/schrodinger_2d_soft_double_slit.svg)",
    )
    p.add_argument(
        "--stride",
        type=int,
        default=1,
        help="Sample every Nth index in x and y (>=1, default 1)",
    )
    p.add_argument(
        "--validate",
        action="store_true",
        help="Check rho >= 0, rectangular grid, at least 16 cells",
    )
    return p.parse_args()


def read_csv_rows(path: Path) -> Tuple[List[float], List[float], List[float]]:
    xs, ys, rs = [], [], []
    with path.open("r", encoding="utf-8", newline="") as f:
        reader = csv.DictReader(f)
        for row in reader:
            xs.append(float(row["x"]))
            ys.append(float(row["y"]))
            rs.append(float(row["rho"]))
    return xs, ys, rs


def infer_grid(
    xs: Sequence[float],
    ys: Sequence[float],
    rs: Sequence[float],
    *,
    validate: bool,
) -> Tuple[List[float], List[float], List[List[float]]]:
    tol = 1e-5
    ux = sorted({float(x) for x in xs})
    uy = sorted({float(y) for y in ys})
    nx, ny = len(ux), len(uy)
    if nx * ny != len(xs):
        raise ValueError("CSV is not a full rectangular x,y grid")
    triples = sorted(zip(xs, ys, rs), key=lambda t: (t[0], t[1]))
    grid = [[0.0] * ny for _ in range(nx)]
    for k, (x, y, r) in enumerate(triples):
        i = k // ny
        j = k % ny
        if abs(x - ux[i]) > tol * max(1.0, abs(ux[i])):
            raise ValueError("x order does not match lexicographic sort")
        if abs(y - uy[j]) > tol * max(1.0, abs(uy[j])):
            raise ValueError("y order does not match lexicographic sort")
        grid[i][j] = r
    if validate:
        for row in grid:
            for r in row:
                if r < -1e-12:
                    raise ValueError("negative rho")
    return ux, uy, grid


def heat_color(t: float) -> Tuple[int, int, int]:
    """t in [0,1] -> RGB (dark blue -> yellow-white)."""
    t = max(0.0, min(1.0, t))
    r = int(255 * (0.15 + 0.85 * t))
    g = int(255 * (0.2 + 0.75 * t * t))
    b = int(255 * (0.5 + 0.5 * (1.0 - t)))
    return r, g, b


def build_svg(
    ux: List[float],
    uy: List[float],
    grid: List[List[float]],
    *,
    stride: int,
    width: int = 520,
    height: int = 520,
) -> str:
    if stride < 1:
        raise ValueError("stride must be >= 1")
    nx, ny = len(ux), len(uy)
    ix = list(range(0, nx, stride))
    jy = list(range(0, ny, stride))
    if len(ix) < 2 or len(jy) < 2:
        raise ValueError("stride too large for grid")
    r_max = max(max(row) for row in grid)
    if r_max <= 0.0:
        r_max = 1.0

    margin = 56
    plot_w = width - 2 * margin
    plot_h = height - 2 * margin
    x_min, x_max = ux[0], ux[-1]
    y_min, y_max = uy[0], uy[-1]
    span_x = x_max - x_min
    span_y = y_max - y_min
    if span_x <= 0 or span_y <= 0:
        raise ValueError("degenerate axis span")

    cell_w = plot_w / len(ix)
    cell_h = plot_h / len(jy)

    parts: List[str] = [
        f'<svg xmlns="http://www.w3.org/2000/svg" width="{width}" height="{height}" '
        f'viewBox="0 0 {width} {height}">',
        f'<rect width="100%" height="100%" fill="#0a0e14"/>',
        f'<text x="{width // 2}" y="28" text-anchor="middle" fill="#e6e6e6" '
        f'font-family="sans-serif" font-size="15">'
        f"2D soft double-slit: |ψ|² (heatmap)</text>",
    ]

    def px_x(i: int) -> float:
        return margin + (ux[i] - x_min) / span_x * plot_w

    def px_y(j: int) -> float:
        # screen y down
        return margin + (y_max - uy[j]) / span_y * plot_h

    for ii, i in enumerate(ix):
        for jj, j in enumerate(jy):
            r = grid[i][j]
            t = r / r_max
            rr, gg, bb = heat_color(t)
            x0 = px_x(i)
            if ii + 1 < len(ix):
                x1 = px_x(ix[ii + 1])
            else:
                x1 = margin + plot_w
            y0 = px_y(j)
            if jj + 1 < len(jy):
                y1 = px_y(jy[jj + 1])
            else:
                y1 = margin + plot_h
            w = max(1.0, x1 - x0)
            h = max(1.0, y1 - y0)
            parts.append(
                f'<rect x="{x0:.2f}" y="{y0:.2f}" width="{w:.2f}" height="{h:.2f}" '
                f'fill="rgb({rr},{gg},{bb})" stroke="none"/>'
            )

    parts.append(
        f'<text x="{margin}" y="{height - 18}" fill="#aaa" font-family="sans-serif" '
        f'font-size="11">x (horizontal)  stride={stride}</text>'
    )
    parts.append("</svg>")
    return "\n".join(parts)


def main() -> None:
    args = _parse_args()
    in_path = (
        Path(args.in_path)
        if args.in_path
        else Path(__file__).resolve().parent / "out" / "schrodinger_2d_soft_double_slit_rho.csv"
    )
    out_path = Path(args.out) if args.out else _default_out()
    if not in_path.is_file():
        raise SystemExit(f"missing {in_path} — run schrodinger_2d_soft_double_slit.py first")

    xs, ys, rs = read_csv_rows(in_path)
    if len(xs) < 16:
        raise SystemExit("CSV too small")
    ux, uy, grid = infer_grid(xs, ys, rs, validate=args.validate)
    if args.validate and len(ux) * len(uy) < 16:
        raise SystemExit("validate: need at least 16 grid cells")

    svg = build_svg(ux, uy, grid, stride=args.stride)
    out_path.parent.mkdir(parents=True, exist_ok=True)
    out_path.write_text(svg, encoding="utf-8")
    print(f"Wrote {out_path}")


if __name__ == "__main__":
    main()
