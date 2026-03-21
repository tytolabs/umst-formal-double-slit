#!/usr/bin/env python3
"""
Qubit path-bit Kraus sweep (stdlib only): matches Lean `QuantumClassicalBridge` metrics.

- pathWeight i  = Re(ρ[i,i])
- I (whichPathDistinguishability) = |p0 - p1|
- V (fringeVisibility) = 2 |ρ[0,1]|
- Lüders which-path channel: ρ ↦ diag(ρ[0,0], ρ[1,1])  (same as Lean `whichPath_map_eq_diagonal`)

This is not QuTiP; it is a minimal faithful 2×2 simulator for parity with formal definitions.
"""

from __future__ import annotations

import argparse
import csv
import math
from dataclasses import dataclass
from pathlib import Path
from typing import List, Tuple


@dataclass(frozen=True)
class C:
    re: float
    im: float

    def __add__(self, o: C) -> C:
        return C(self.re + o.re, self.im + o.im)

    def __neg__(self) -> C:
        return C(-self.re, -self.im)

    def __sub__(self, o: C) -> C:
        return self + (-o)

    def __mul__(self, o: C) -> C:
        return C(self.re * o.re - self.im * o.im, self.re * o.im + self.im * o.re)

    def conj(self) -> C:
        return C(self.re, -self.im)

    def abs(self) -> float:
        return math.hypot(self.re, self.im)


Mat2 = Tuple[Tuple[C, C], Tuple[C, C]]


def mat_zero() -> Mat2:
    z = C(0.0, 0.0)
    return ((z, z), (z, z))


def mat_add(a: Mat2, b: Mat2) -> Mat2:
    return tuple(
        tuple(a[i][j] + b[i][j] for j in range(2)) for i in range(2)
    )


def mat_mul(a: Mat2, b: Mat2) -> Mat2:
    res = [[C(0.0, 0.0), C(0.0, 0.0)], [C(0.0, 0.0), C(0.0, 0.0)]]
    for i in range(2):
        for j in range(2):
            s = C(0.0, 0.0)
            for k in range(2):
                s = s + a[i][k] * b[k][j]
            res[i][j] = s
    return ((res[0][0], res[0][1]), (res[1][0], res[1][1]))


def mat_conj_transpose(m: Mat2) -> Mat2:
    return tuple(
        tuple(m[j][i].conj() for j in range(2)) for i in range(2)
    )


def pure_density(psi: Tuple[C, C]) -> Mat2:
    """ρ_ij = ψ_i ψ_j* (column vector ψ)."""
    return tuple(
        tuple(psi[i] * psi[j].conj() for j in range(2)) for i in range(2)
    )


def kraus_apply(kraus: List[Mat2], rho: Mat2) -> Mat2:
    acc = mat_zero()
    for k in kraus:
        acc = mat_add(acc, mat_mul(mat_mul(k, rho), mat_conj_transpose(k)))
    return acc


def identity_kraus() -> List[Mat2]:
    one = C(1.0, 0.0)
    z = C(0.0, 0.0)
    idm = ((one, z), (z, one))
    return [idm]


def which_path_kraus() -> List[Mat2]:
    one = C(1.0, 0.0)
    z = C(0.0, 0.0)
    p0 = ((one, z), (z, z))
    p1 = ((z, z), (z, one))
    return [p0, p1]


def path_weight(rho: Mat2, i: int) -> float:
    return rho[i][i].re


def which_path_distinguishability(rho: Mat2) -> float:
    p0 = path_weight(rho, 0)
    p1 = path_weight(rho, 1)
    return abs(p0 - p1)


def fringe_visibility(rho: Mat2) -> float:
    return 2.0 * rho[0][1].abs()


def complementarity_sq(rho: Mat2) -> float:
    v = fringe_visibility(rho)
    i = which_path_distinguishability(rho)
    return v * v + i * i


def ket_plus() -> Tuple[C, C]:
    s = 1.0 / math.sqrt(2.0)
    return (C(s, 0.0), C(s, 0.0))


def ket0() -> Tuple[C, C]:
    return (C(1.0, 0.0), C(0.0, 0.0))


def ket1() -> Tuple[C, C]:
    return (C(0.0, 0.0), C(1.0, 0.0))


def label_state(name: str) -> Mat2:
    if name == "plus":
        return pure_density(ket_plus())
    if name == "zero":
        return pure_density(ket0())
    if name == "one":
        return pure_density(ket1())
    raise ValueError(f"unknown state {name!r} (use plus, zero, one)")


def _parse_args() -> argparse.Namespace:
    p = argparse.ArgumentParser(description="Qubit Kraus sweep vs Lean metrics.")
    p.add_argument(
        "--out",
        type=str,
        default=None,
        help="Output CSV (default: sim/out/qubit_kraus_sweep.csv)",
    )
    p.add_argument(
        "--validate",
        action="store_true",
        help="Assert V^2+I^2 <= 1 + tol for all rows.",
    )
    return p.parse_args()


def main() -> None:
    args = _parse_args()
    out = Path(args.out) if args.out else Path(__file__).resolve().parent / "out" / "qubit_kraus_sweep.csv"
    out.parent.mkdir(parents=True, exist_ok=True)

    states = ["plus", "zero", "one"]
    channels = [("identity", identity_kraus()), ("which_path", which_path_kraus())]

    rows: List[dict] = []
    tol = 1e-9
    for st in states:
        rho0 = label_state(st)
        for ch_name, ks in channels:
            rho = kraus_apply(ks, rho0)
            v = fringe_visibility(rho)
            i = which_path_distinguishability(rho)
            comp = v * v + i * i
            if args.validate and comp > 1.0 + tol:
                raise ValueError(f"complementarity fail {st} {ch_name}: V^2+I^2={comp}")
            rows.append(
                {
                    "state": st,
                    "channel": ch_name,
                    "pathWeight0": f"{path_weight(rho, 0):.10f}",
                    "pathWeight1": f"{path_weight(rho, 1):.10f}",
                    "fringeVisibility_V": f"{v:.10f}",
                    "whichPathDistinguishability_I": f"{i:.10f}",
                    "V_sq_plus_I_sq": f"{comp:.12f}",
                }
            )

    fieldnames = [
        "state",
        "channel",
        "pathWeight0",
        "pathWeight1",
        "fringeVisibility_V",
        "whichPathDistinguishability_I",
        "V_sq_plus_I_sq",
    ]
    with out.open("w", newline="", encoding="utf-8") as f:
        w = csv.DictWriter(f, fieldnames=fieldnames)
        w.writeheader()
        w.writerows(rows)
    print(f"Wrote {len(rows)} rows to {out}")


if __name__ == "__main__":
    main()
