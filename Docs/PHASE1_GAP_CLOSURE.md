<!--
SPDX-License-Identifier: MIT
Copyright (c) 2026 Santhosh Shyamsundar, Santosh Prabhu Shenbagamoorthy — Studio TYTO
-->

# Phase 1 — gap closure (Lean)

Status for the six-phase plan, **Phase 1 only** (foundations).

**Full roadmap + later phases:** [`GAP_CLOSURE_PLAN.md`](GAP_CLOSURE_PLAN.md).

| Gap | Item | Status |
|-----|------|--------|
| **1** | `DensityMatrix.mixedDensity` | **Done** in `Lean/DensityState.lean` (convex `t·ρ₁ + (1-t)·ρ₂`). |
| **13** | `PMICVisibility` — `V² + residualCoherenceCapacity ≤ 1` | **Done** — entropy–quadratic bound proved in `Lean/PMICEntropyInterior.lean`; `PMICVisibility` imports it. |
| **17** | `QRBridge` — `Admissible` lifts ℚ → ℝ | **Done** in `Lean/QRBridge.lean` (`admissible_thermodynamicStateToReal`). |

## Gap 13 — proof architecture (closed)

1. **Elementary bound:** `2 * log (1 + v) > v` for `v ∈ (0,1)` (`two_mul_log_one_add_gt` via strict monotonicity of `log(1+t) - t/2`).
2. **Auxiliary `k(u)`:** `entropyBoundK u = (u²-1)log(1+u) - u² log u` has `k(1)=0` and `k'(u) > 0` for `u > 1` (rewrite to `(2/v)log(1+v)-1` with `v=1/u`).
3. **MVT:** `k(u) > 0` for `u > 1` (`entropyBoundK_pos`).
4. **Change of variables** `u = (1-x)/x` ⟺ `(1-x)² log(1-x) < x² log x` on `(0,1/2)` (`quad_log_lt_of_lt_half`).
5. **Ratio monotonicity:** `binEntropy t / (t(1-t))` strictly antitone on `[x,1/2]` ⟹ `binEntropy x / (x(1-x)) > 4 log 2` (`four_mul_x_one_sub_x_mul_log_two_interior`).

`four_mul_x_one_sub_x_mul_log_two_le_binEntropy` and `quadratic_le_entropy_bits` in `PMICVisibility.lean` are **sorry-free**.

## Build

`cd Lean && lake build` — roots include `PMICEntropyInterior`, `QRBridge`, `PMICVisibility`.
