SPDX-FileCopyrightText: 2026 Santosh Prabhu Shenbagamoorthy and Santhosh Shyamsundar
SPDX-License-Identifier: MIT
# Informational Formal Anchor Expansion Plan (M4-A8-R5)

| Field | Value |
|-------|-------|
| **Cell** | `M4-A8-R5` |
| **Mode** | Research only |
| **Repo** | `umst-formal-double-slit` (Knowing fiber) |
| **Consumer** | `umst-web` A8 axiom `𝒟_web_int` |

---

## 1. Goal

Expand the Knowing fiber so `umst-web::InformationalResponse` axiom legs cite **proved** Lean lemmas — not heuristic domain claims.

**Axiom (operational):**

```text
𝒟_web_int = ΔIntentFidelity − λ·ΔComplexityCost − μ·LandauerRenderingCost ≥ −ε_int
```

---

## 2. Lemma map (A8 leg → Lean anchor)

| A8 leg | Lean module | Primary symbol | Status |
|--------|-------------|----------------|--------|
| `LandauerRenderingCost` | `LandauerBound.lean` | `landauerCostDiagonal_whichPathInvariant` | **proved** |
| `LandauerRenderingCost` | `LandauerLaw.lean` | `landauerBitEnergy` | **proved** (integrated upstream) |
| `ΔComplexityCost` | `MeasurementCost.lean` | probe cost vs Landauer cap | **proved** |
| `ΔIntentFidelity` | `EpistemicGalois.lean` | required energy ↔ acquirable info | **proved** |
| `ΔIntentFidelity` | `QuantumMutualInfo.lean` | `mutualInformation_nonneg` | **proved** |

---

## 3. Expansion phases (no push until operator ceremony)

| Phase | Work | Repo |
|-------|------|------|
| **P0** (this R5) | Anchor table + `FORMAL_ANCHOR.md` wire in `umst-web` | `umst-web` |
| **P1** | `GateCompat.lean` import path for informational response shape | `umst-formal-double-slit` |
| **P2** | Cross-repo catalog dual-emit (`--also-lean-root`) | workspace `artifacts/catalog.json` |
| **P3** | Operator `[witnessed]` tier on compose stack | ceremony packet |

---

## 4. Honest boundary

| Claim | Verdict |
|-------|---------|
| Knowing fiber proves page is good | **NOT** |
| Landauer lemmas bound rendering cost floor | **YES** — diagonal path entropy |
| Full `𝒟_web_int` is a single Lean theorem today | **NOT** — operational Rust axiom + lemma cites |

---

## 5. Dependencies

| Token | Status |
|-------|--------|
| M3-G | ✅ |
| A8-I2 (`WebStateTensor`) | ✅ Wave 1 |
| A8-I10 wire | sibling cell 051 |

---

*Receipt slice: `umst-formal-double-slit/Docs/INFORMATIONAL_FORMAL_ANCHOR_PLAN.md` · **R complete** · **no push*
