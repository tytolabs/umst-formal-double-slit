<!--
SPDX-License-Identifier: MIT
Copyright (c) 2026 Santhosh Shyamsundar, Santosh Prabhu Shenbagamoorthy — Studio TYTO
-->

# Complete gap closure plan — 6 phases (status tracker)

Master list aligned with the original **9 new Lean files** roadmap, updated for **what is actually in-tree** as of the PMIC entropy closure.

**Legend:** `DONE` · `PARTIAL` · `TODO`  
**Lean:** `cd Lean && lake build` — **0 `sorry`** across all Lean files; **3 axioms** (`klein_inequality`, `vonNeumannEntropy_nondecreasing_unital`, `physicalSecondLaw`). **`VonNeumannEntropy`** general unitary invariance **proved**. DPI general unital: **axiom** (Klein — requires Mathlib matrix log). **Coordination:** see [`PARALLEL_WORK.md`](PARALLEL_WORK.md).

---

## Phase 1 — Foundations *(highest impact; others depend on this)*

| Step | Gap | Plan | Delivered | Key theorem / artifact | Status |
|:----:|:---:|:----:|:---------:|------------------------|:------:|
| 1 | **Gap 1** | Extend `DensityState.lean` | **`Lean/DensityState.lean`** | `mixedDensity` convex combination is `DensityMatrix` | **DONE** |
| 2 | **Gap 13** | NEW `PMICVisibility.lean` | **`Lean/PMICVisibility.lean`** + **`Lean/PMICEntropyInterior.lean`** *(supporting analytic layer)* | `visibility_sq_le_coherence_capacity` — **V² + residualCoherenceCapacity ≤ 1** | **DONE** |
| 3 | **Gap 17** | NEW `QRBridge.lean` | **`Lean/QRBridge.lean`** | `admissible_thermodynamicStateToReal` — ℚ `Admissible` → ℝ `UMST.Core.Admissible` | **DONE** |

**Crown jewel (Gap 13) — proved chain**

```
V² ≤ 4p₀p₁                     ← `normSq_coherence_le_product` / `PMICVisibility`
4p₀(1−p₀)·log 2 ≤ binEntropy p₀ ← `four_mul_x_one_sub_x_mul_log_two_le_binEntropy` + `PMICEntropyInterior`
⇒ V² ≤ pathEntropyBits ρ       ← `quadratic_le_entropy_bits`
V² + (1 − pathEntropyBits) ≤ 1 ← `visibility_sq_le_coherence_capacity`
```

See also: [`PHASE1_GAP_CLOSURE.md`](PHASE1_GAP_CLOSURE.md) (Phase 1 detail).

---

## Phase 2 — Generalization

| Step | Gap | Plan | Delivered | Key theorem | Status |
|:----:|:---:|:----:|:---------:|-------------|:------:|
| 4 | **Gap 2** | NEW `GeneralDimension.lean` | **`Lean/GeneralDimension.lean`**, **`LandauerBound.lean`** (`pathEntropyBits_n`, `landauerCostDiagonal_n_*`) | **`vonNeumannDiagonal_n_le_log_n`**; **`landauerCostDiagonal_n_le_logb_landauerBitEnergy`**. **Still TODO:** general-`n` residual-coherence narrative (qubit-only today) | **PARTIAL** |

**Next:** general-`n` thermodynamic / residual-coherence packaging if needed for paper narrative (qubit story unchanged).

---

## Phase 3 — Composite systems

| Step | Gap | Plan | Delivered | Key theorem | Status |
|:----:|:---:|:----:|:---------:|-------------|:------:|
| 5 | **Gap 3** | NEW `TensorPartialTrace.lean` | **`Lean/TensorPartialTrace.lean`** | **`tensorDensity`**, **`partialTraceRightFin_tensorDensity_carrier`**, Kronecker PSD, **`partialTraceRightProd_toDensityMatrix`** / **`partialTraceLeftProd_toDensityMatrix`** (general entangled states) | **DONE** |
| 6 | **Gap 10** | Extend `GateCompat.lean` | **`Lean/GateCompat.lean`** | Schematic `thermoFromQubitPath` ✓; **calibrated** `thermoCalibratedScaffold` (`freeEnergy = -landauerCostDiagonal ρ T`) ✓; `admissible_*` under `whichPath` ✓; `|freeEnergy| ≤ landauerBitEnergy` ✓. **Still TODO:** nontrivial `hydration` / `strength` from QM; beyond-qubit scaffold | **PARTIAL** |

---

## Phase 4 — Dynamics

| Step | Gap | Plan | Delivered | Key theorem | Status |
|:----:|:---:|:----:|:---------:|-------------|:------:|
| 7 | **Gap 5** | NEW `SchrodingerDynamics.lean` | **`Lean/SchrodingerDynamics.lean`** | `unitaryChannel`, PSD + trace preservation, `unitaryChannel_apply` / `DensityMatrix`, involution `U` then `Uᴴ` | **DONE** *(finite `Fin n`; Kraus API)* |
| 8 | **Gap 12** | NEW `LindbladDynamics.lean` | **`Lean/LindbladDynamics.lean`** | `dissipator`, `lindbladGenerator`, qubit dephasing vs path projectors; **`whichPath_eq_rho_plus_dissipator`** | **PARTIAL** *(qubit story; optional `γ → ∞` limit packaging)* |

---

## Phase 5 — Information theory

| Step | Gap | Plan | Delivered | Key theorem | Status |
|:----:|:---:|:----:|:---------:|-------------|:------:|
| 9 | **Gap 4** | NEW `VonNeumannEntropy.lean` | **`Lean/VonNeumannEntropy.lean`** | `vonNeumannEntropy` via eigenvalues; `trace_eq_sum_eigenvalues_hermitian`; nonneg; `≤ log n`; **`charpoly_unitary_conj`**; **`Fin 1`/`Fin 2`/`Fin n` unitary invariance** ✓ (**0** `sorry` in this file) | **DONE** *(Klein/DPI lives under Gap 11)* |
| 10 | **Gap 11** | NEW `DataProcessingInequality.lean` | **`Lean/DataProcessingInequality.lean`** | **Tier 1:** diagonal DPI ✓; **Tier 1b:** qubit diagonal ≥ spectral ✓ (`vonNeumannDiagonal_ge_vonNeumannEntropy`); **Tier 2:** identity channel ✓ (`vonNeumannEntropy_identity_apply`); **general** unital DPI via **`axiom`** (`vonNeumannEntropy_nondecreasing_unital`, `klein_inequality` — Mathlib matrix log) | **PARTIAL** |

`InfoEntropy.lean` already flags: general `n`, MI, DPI — **not yet**. Phase 5 files now cover DPI Tier 1 and state Tier 2.

---

## Phase 6 — Engineering

| Step | Gap | Plan | Delivered | Status |
|:----:|:---:|:----:|:---------:|:------:|
| 11 | **Gap 14** | Python/Haskell telemetry consumers | Extensive **`Epistemic*.lean`** + Haskell/Python tests; **no** single “consumer spec” tying every Lean name | **PARTIAL** |
| 12 | **Gap 16** | CI installs all optional deps | **`.github/workflows/lean.yml`** runs `pip install -r sim/requirements-optional.txt` before sim tests | **DONE** *(verify local skips if packages missing)* |
| 13 | **Gap 18** | `SimLeanBridge.lean` | **`Lean/SimLeanBridge.lean`** | Contract types: `SimDensityContract`, `SimPathProjectionContract`, `SimComplementarityWitness`, `SimLandauerWitness` (+ lift / inequalities) | **PARTIAL** *(trust-boundary props; Python witness pipeline not mechanized)* |
| 14 | **Gap 19** | Provenance in CHANGELOG | **`CHANGELOG.md`** + module docs | **PARTIAL** *(extend with release/DOI hooks as needed)* |

---

## Lean file count vs original “9 new files”

| Original intent | In repo |
|-----------------|---------|
| PMICVisibility | `PMICVisibility.lean` |
| QRBridge | `QRBridge.lean` |
| + 7 others (Phases 2–5) | **In progress** (2 of 7: `GeneralDimension.lean`, `TensorPartialTrace.lean`) |
| *Extra (recommended split)* | `PMICEntropyInterior.lean` — analytic core for Gap 13 |

**Registered roots:** see `Lean/lakefile.lean` (includes `PMICEntropyInterior`, `QRBridge`, `PMICVisibility`, …).

---

## Parallel workstreams (“swarm”)

**Coordination:** edit [`PARALLEL_WORK.md`](PARALLEL_WORK.md) with **active claims** before overlapping files.

Independent enough to run in parallel once Phase 1 is done (**Phase 1 is DONE**):

| Stream | Scope | Primary Lean touchpoints | Risk |
|--------|--------|---------------------------|------|
| **A — General n** | Phase 2 (+ bit of Phase 5 Tier 1) | `InfoEntropy.lean` or new `GeneralDimension.lean` | Medium — convexity / `log n` |
| **B — Composite** | Phase 3 | New `TensorPartialTrace.lean`, later `GateCompat` | High — linear algebra + defs |
| **C — Dynamics** | Phase 4 | New `SchrodingerDynamics.lean`, `LindbladDynamics.lean` | High — analysis + generators |
| **D — Entropy & DPI** | Phase 5 | New `VonNeumannEntropy.lean`, `DataProcessingInequality.lean` | Very high — spectrum + CPTP |
| **E — Engineering** | Phase 6 | `SimLeanBridge.lean`, CI, telemetry docs | Low–medium |

Recommended order after Phase 1: **A → B → E** (capability for sim/formal bridge before heavy CPTP), then **C** / **D** as paper needs.

---

## Quick gap checklist

- [x] Gap 1 — mixed states (convex `mixedDensity`)
- [x] Gap 13 — PMIC visibility / entropy–quadratic / **V² + RCC ≤ 1**
- [x] Gap 17 — ℚ → ℝ `Admissible`
- [ ] Gap 2 — **PARTIAL:** entropy + Landauer bit-cap for `Fin n` (`GeneralDimension` + `LandauerBound`); **still TODO:** multi-outcome residual-coherence packaging (if desired)
- [x] Gap 3 — **DONE:** `tensorDensity`, `partialTraceRightFin_*`, `partialTraceRightProd_*`, `partialTraceRightProd_toDensityMatrix` / `partialTraceLeftProd_toDensityMatrix` (general entangled states)
- [ ] Gap 10 — **PARTIAL:** calibrated `thermoCalibratedScaffold` + Landauer bounds; **TODO:** nontrivial hydration/strength, higher dimension
- [x] Gap 5 — **DONE:** `SchrodingerDynamics` — unitary as Kraus, PSD/trace, `DensityMatrix` closure
- [ ] Gap 12 — **PARTIAL:** `LindbladDynamics` — dissipator + qubit dephasing / `whichPath_eq_rho_plus_dissipator`; optional full trace-preservation / limit story
- [x] Gap 4 — **DONE:** `vonNeumannEntropy` via eigenvalues; trace=∑λ; nonneg; ≤ log n; **`vonNeumannEntropy_unitarily_invariant`** (general `Fin n`) ✓
- [x] Gap 11 — **PARTIAL:** Tier 1 ✓; Tier 1b ✓ (qubit: `vonNeumannDiagonal_ge_vonNeumannEntropy`); Tier 2 identity channel ✓; general unital DPI as **`axiom`** (Klein / matrix log — replace with proof when Mathlib ready)
- [ ] Gap 14 — telemetry consumers (tighten Lean↔runtime mapping)
- [x] Gap 16 — CI optional pip *(workflow present)*
- [ ] Gap 18 — **PARTIAL:** `SimLeanBridge` contract structures; **TODO:** sim postprocessor witnesses / CI hooks to Lean names
- [ ] Gap 19 — provenance *(extend as releases ship)*
