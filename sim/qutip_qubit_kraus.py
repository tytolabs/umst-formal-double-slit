#!/usr/bin/env python3
# SPDX-License-Identifier: MIT
# Copyright (c) 2026 Santhosh Shyamsundar, Santosh Prabhu Shenbagamoorthy — Studio TYTO

"""
Optional QuTiP replication of the qubit path-bit metrics used in Lean `QuantumClassicalBridge`.

Requires `qutip` (see `sim/requirements-optional.txt`). When QuTiP is missing, importing this
module still works; call `have_qutip()` before using `metrics_from_qobj` / channel helpers.

Not run in default `make sim` / CI — use `unittest` in `test_qutip_parity.py` when QuTiP is installed.
"""

from __future__ import annotations

from typing import Any, Tuple


def have_qutip() -> bool:
    try:
        import qutip  # noqa: F401

        return True
    except ImportError:
        return False


def _q() -> Any:
    import qutip

    return qutip


def ket_plus() -> Any:
    q = _q()
    return (q.basis(2, 0) + q.basis(2, 1)).unit()


def ket0() -> Any:
    return _q().basis(2, 0)


def ket1() -> Any:
    return _q().basis(2, 1)


def pure_density(ket: Any) -> Any:
    return ket * ket.dag()


def apply_identity(rho: Any) -> Any:
    return rho


def apply_which_path(rho: Any) -> Any:
    q = _q()
    p0 = q.ket2dm(q.basis(2, 0))
    p1 = q.ket2dm(q.basis(2, 1))
    return p0 * rho * p0 + p1 * rho * p1


def metrics_from_qobj(rho: Any) -> Tuple[float, float, float, float]:
    """Returns (pathWeight0, pathWeight1, V, I)."""
    m = rho.full()
    p0 = float(m[0, 0].real)
    p1 = float(m[1, 1].real)
    coh = complex(m[0, 1])
    v = 2.0 * abs(coh)
    i = abs(p0 - p1)
    return p0, p1, v, i


def label_state(name: str) -> Any:
    if name == "plus":
        return pure_density(ket_plus())
    if name == "zero":
        return pure_density(ket0())
    if name == "one":
        return pure_density(ket1())
    raise ValueError(f"unknown state {name!r}")
