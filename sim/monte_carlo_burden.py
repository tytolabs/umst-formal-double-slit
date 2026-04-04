#!/usr/bin/env python3
"""
Monte Carlo check for burden / exploration dynamics (Wave 6 Track C).

Mirrors Lean `UMST.Economics.burden_expectation_symmetric_two_point` and geometric decay:
  - iid symmetric noise ±σ with P=1/2 ⇒ E[B₁] = B₀(1+μ)
  - multiplicative drift (1+μ)^n with |1+μ|<1 ⇒ decay toward 0

Stdlib-only (no NumPy required). Optional QuTiP import is attempted for environment parity.
"""
from __future__ import annotations

import math
import random

try:
    import qutip  # noqa: F401

    _QUTIP = True
except ImportError:
    _QUTIP = False


def run_monte_carlo(
    n_runs: int = 10_000,
    seed: int = 42,
    b0: float = 1.0,
    mu: float = -0.05,
    sigma: float = 0.2,
) -> dict[str, float]:
    rng = random.Random(seed)
    b1_samples: list[float] = []
    for _ in range(n_runs):
        xi = sigma if rng.random() < 0.5 else -sigma
        b1_samples.append(b0 * (1.0 + mu + xi))
    mean_b1 = sum(b1_samples) / n_runs
    predicted = b0 * (1.0 + mu)
    n_steps = 40
    r = 1.0 + mu
    traj_final = b0 * (r**n_steps)
    return {
        "n_runs": float(n_runs),
        "mean_b1": mean_b1,
        "predicted_e_b1": predicted,
        "abs_err_expectation": abs(mean_b1 - predicted),
        "theory_final_geom": traj_final,
        "qutip_available": float(_QUTIP),
    }


def main() -> None:
    out = run_monte_carlo()
    mc_se = 0.2 * 1.0 / math.sqrt(out["n_runs"])
    assert out["abs_err_expectation"] < 5 * mc_se, out
    print("monte_carlo_burden ok:", out)


if __name__ == "__main__":
    main()
