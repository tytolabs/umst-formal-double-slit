# M4-A8-R5 — Formal Anchor Expansion Plan (Informational Path)

| Field | Value |
|-------|-------|
| **Cell** | **050** · `M4-A8-R5` |
| **Mode** | Research |
| **When** | 2026-07-19 08:15 IST |
| **Authority** | [`README.md`](../README.md) · [`M4_100_CELL_LATTICE_0752.md`](../../archived/residuals/misc-outputs-tmp/M4_100_CELL_LATTICE_0752.md) §A8 depth |
| **Sibling** | `M4-A8-I10` (W2) wires module cite into `umst-web` — **not claimed here** |

---

## 1. Anchor objective

Expand the **Knowing fiber** formal anchor from Landauer / measurement-cost lemmas onto the **informational web path** (`𝒟_web_int`) without duplicating proof logic in `umst-web`. Rust informational gate implements C6 constitutive response; Lean supplies thermodynamic floor citations only.

---

## 2. Primary formal modules (Knowing fiber)

| Item | Path | Role for A8 |
|------|------|-------------|
| Landauer bound | `Lean/LandauerBound.lean` | Rendering cost floor for `landauer_rendering` leg |
| Landauer law | `Lean/LandauerLaw.lean` | Bit energy at T — `landauer_bit_energy_joules` parity |
| Measurement cost | `Lean/MeasurementCost.lean` | Observation / measurement cost morphism |
| Epistemic Galois | `Lean/EpistemicGalois.lean` | Required energy ↔ acquirable info |
| Quantum MI | `Lean/QuantumMutualInfo.lean` | Intent-fidelity channel (advisory — not cert input) |
| Epistemic sensing | `Lean/EpistemicSensing.lean` | Sensing cost for web render transitions |
| Complementarity | `Lean/Complementarity.lean` | Englert bound — informational trade-off vocabulary |

**Explicit non-import into `umst-web` Rust:** no Lean runtime — doc-only cite + `umst.toml` `formal_anchors` pin.

---

## 3. Symbol map (Rust → Lean)

| A8 Rust surface | Lean anchor | Honest tier |
|-----------------|-------------|-------------|
| `InformationalResponse::landauer_rendering` | `LandauerBound` · `LandauerLaw` | thermodynamic floor |
| `InformationalResponse::intent_fidelity` | `EpistemicGalois` · `QuantumMutualInfo` | **advisory** — not Proved cert |
| `WebStateTensor::web_int_dissipation` | `MeasurementCost` · `Complementarity` | open-system witness vocabulary |
| `MonotoneHooks::accessibility_coverage` | — | **orthogonal** — no Lean claim (A8-R2) |

**Semantics tier:** `𝒟_web_int` certifies open-system dissipation admissibility — not WCAG, not epistemic MI Proved promotion.

---

## 4. Theorem inventory (representative)

| Cluster | Representative theorems | Rust parity |
|---------|-------------------------|-------------|
| Landauer floor | `landauerBound` · `dissipation_nonneg` | `InformationalResponse::informational_net` unit tests |
| Measurement cost | `measurementCost_nonneg` | gate fixture balanced / under-budget |
| Complementarity | `englertBound` | **doc-only** — no Rust reimplementation |
| Epistemic runtime | `EpistemicRuntimeContract` schema | UCRS `TemporalWitness` stamp (A8-I4) |

Full Lean stats: `scripts/lean_decl_stats.py` → catalog export in `artifacts/catalog.json`.

---

## 5. Operational boundaries (honest)

| Claim | Status |
|-------|--------|
| Knowing fiber Lean proofs run in browser wasm | **NOT** |
| `𝒟_web_int` = formal Proved tier | **NOT** — operator witnessed / Rust gate only |
| Epistemic MI from `umst_mi_estimate` is cert input | **NOT** — advisory channel |
| Monotone a11y hooks have Lean anchor | **NOT** — domain knowledge orthogonal layer |

---

## 6. `umst-web/FORMAL_ANCHOR.md` cite contract (I10 handoff)

I10 must ship:

1. Knowing fiber table → Lean module paths (§2)
2. `𝒟_web_int` axiom mapping → Rust `WebStateTensor` + Lean floor cites (§3)
3. Honest boundary paragraph (§5)
4. `umst.toml` `formal_anchors` expanded per §2 module names

**R5 done-when:** expansion plan doc (this file) + I10 wires cite — **R satisfied**.

---

## 7. W2 handoff (`M4-A8-I10`)

| I10 deliverable | Prerequisite from R5 |
|-----------------|---------------------|
| `formal_double_slit.rs` module wire | §2 module paths frozen |
| `FORMAL_ANCHOR.md` in `umst-web` | §6 cite contract |
| `umst.toml` anchor pin | §2 `formal_anchors` list |

---

*Receipt cell: **050** · `M4-A8-R5` · **no push** · **no M4 tick*
