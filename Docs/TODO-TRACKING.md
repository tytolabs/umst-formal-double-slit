<!--
SPDX-License-Identifier: MIT
Copyright (c) 2026 Santhosh Shyamsundar, Santosh Prabhu Shenbagamoorthy — Studio TYTO
-->

# TODO / milestone tracking (double-slit repository)

Reconciled periodically with the repo and any **in-editor todo list** (Cursor).
If editor todos drift, treat **this file** as the reconciliation source.

**Multi-agent:** if two or more agents work the same backlog, **claim a stream** in [`Docs/PARALLEL_WORK.md`](PARALLEL_WORK.md) before editing hot paths (`DataProcessingInequality.lean`, `README.md`, `lakefile.lean`). One active writer per choke-point file unless coordinated.

## Done in tree (high level)

- **Lean:** double-slit stack (`UMSTCore` … `DoubleSlit`), measurement channel / Lüders bridge, `LandauerBound` (+ Principle of Maximal Information Collapse), complementarity, **`MeasurementCost.lean`**, **`EpistemicGalois.lean`**, extensive **`Epistemic*.lean`** telemetry bridges; **integrated upstream reference core:** **`LandauerLaw` / `LandauerExtension` / `LandauerEinsteinBridge`**, **`Gate` / `Naturality` / `Activation` / `FiberedActivation` / `MonoidalState`** (registered in `lakefile.lean`). **DensityState + MeasurementChannel:** historical `sorry` sites eliminated (projector properties). **Phase 5:** **0** line-start `sorry` project-wide; general unital DPI / Klein layer is **`axiom`** in **`DataProcessingInequality.lean`** until Mathlib matrix-log infrastructure lands; **`VonNeumannEntropy`** general unitary invariance **proved** — see **`Lean/VERIFY.md`** / **`PROOF-STATUS.md`**.
- **Haskell:** `DoubleSlit`, `MeasurementChannel`, **`MeasurementCost.hs`**, **`EpistemicGalois.hs`**, **`LandauerExtension.hs`**, **`MonoidalState.hs`**, QuickCheck + **`landauer-einstein-sanity`**, Cabal CI (`haskell.yml`).
- **Coq / Agda:** slim trees — **`Coq/LandauerEinsteinBridge.v`**, **`Agda/LandauerEinsteinTrace.agda`**; local **`make coq-check`** / **`make agda-check`**.
- **Python:** toy + Kraus + QuTiP qubit parity; stdlib SVG plots; closed-form Gaussian + classical Fraunhofer; **`schrodinger_1d_*`** (FFT, split-step, soft slit, absorbing); **`schrodinger_2d_soft_double_slit`**, **`schrodinger_2d_absorbing_edges`**, **`schrodinger_2d_complex_absorb_mask`**; **QuTiP** 2D free + slit FD parity; **`benchmark_schrodinger_2d_split_step_vs_fd`**; **`schrodinger_2d_sparse_fd_expm_smoke`** (sparse `expm_multiply` vs dense); tests under `sim/tests/`.
- **CI:** `lean.yml` (Lake + optional pip + sim + unittest), `haskell.yml`, **`paths` filters**, concurrency, `make ci-local` / `make ci-full`.

## In progress / owned elsewhere

- **Parallel agents:** claim a stream and edit [`Docs/PARALLEL_WORK.md`](PARALLEL_WORK.md) (`stream-A` … `stream-H`, choke points).
- **Phase 5 (Lean) — stream `D` / Mathlib track:** **replace axioms** in **`DataProcessingInequality.lean`** (`klein_inequality`, `vonNeumannEntropy_nondecreasing_unital`) with real proofs when matrix log / Klein is available — **0** `sorry` today. **`VonNeumannEntropy_unitarily_invariant`** is **proved** in-tree. **Before merge:** `cd Lean && lake build`, refresh **`make lean-stats-md`** → docs if counts shift. **Coordinate** on **`DataProcessingInequality.lean`** — single active editor unless split by lemma.
- **This continuation track:** prefer **H / E / G** (telemetry, sim, CI) or **A0 / a1** unless you own stream **D** — follow **[`Docs/REMAINING_WORK_PLAN.md`](REMAINING_WORK_PLAN.md)** for Gap 14 / A0 / a1 / sim emission order.
- **`p3-epistemic-sensing`:** ground ODE–PPO / runtime evidence vs existing Epistemic modules — prefer **stream H**; start from [`Docs/EPISTEMIC_RUNTIME_GROUNDING.md`](EPISTEMIC_RUNTIME_GROUNDING.md) + `Lean/Epistemic*.lean`, `Lean/VERIFY.md`, `PARALLEL_WORK.md`.

## Backlog checklist (cross-cutting — **not** closed by Phase 5 alone)

Use this to avoid duplicating work or claiming “done” prematurely. Update rows when artifacts land. **Ordered plan (Phase 5 left to stream D):** [`REMAINING_WORK_PLAN.md`](REMAINING_WORK_PLAN.md).

| Work item | Already in tree? | Still TODO |
|-----------|------------------|------------|
| **Phase 5** — zero `sorry` in `DataProcessingInequality` | **Yes** — **0** `sorry`; general unital DPI as **axiom** (Klein / Mathlib matrix log) | Re-run stats after Mathlib matrix log support |
| **A0** — full Coq / Agda parity (beyond Landauer–Einstein stubs) | **Partial** — `Coq/LandauerEinsteinBridge.v`, `Agda/LandauerEinsteinTrace.agda` only | Full ports per [`A0_COQ_AGDA_BACKLOG.md`](A0_COQ_AGDA_BACKLOG.md); wire **`make coq-check` / `make agda-check`** for new modules |
| **a1** — proofs / specs **across all four languages** (`accumulatedMassBound`, …; `MeasurementCost`; axiom narrowing) | **Partial** — strong **Lean + Haskell** for many tracks; **MeasurementCost** has **no** Coq/Agda in this fork yet | Coq/Agda **MeasurementCost** (and other a1 items) — see cross-lang section below |
| **Sim / RL** — **emit** telemetry JSON | **Partial** — **`sim/export_sample_telemetry_trace.py`** writes a **golden** trace (+ optional `--validate`); **no** RL / long-run sim hooked yet | Mirror its schema in production pipelines; see [`REMAINING_WORK_PLAN.md`](REMAINING_WORK_PLAN.md) |
| **JSON** — `thermodynamicAdmissible`, `confidence` (`EmittedStepRecord`) | **Lean** + **Python** — `telemetry_trace_consumer.py` checks when fields present (flat or nested `emitted`) | **Sim/RL:** actually **emit** these fields where appropriate |

## Open next

- **Python:** stretched-coordinate **PML**, split-field / 3D strips, **QuTiP** on large sparse workflows; analytic ABC reference checks.
- **Lean:** extend `InfoEntropy` (general n, MI, DPI); extend **`GateCompat`** beyond qubit / nontrivial hydration–strength (calibrated scaffold **already** in tree).
- **Haskell:** more QC properties as Lean surface grows; keep **`cabal freeze`** in sync.
- **CI:** optional `workflow_dispatch`, badges.
- **Docs:** re-paste **`make lean-stats-md`** into `PROOF-STATUS.md` after large Lean edits.

## Pending gaps (reconciled — see `GAP_CLOSURE_PLAN.md`)

Use this as a **single backlog**; details and theorem names live in the gap plan + `Lean/VERIFY.md`.

| Area | Status | Steady next step |
|------|--------|------------------|
| **Gap 2** — general-`n` narrative | PARTIAL | Optional: multi-outcome **residual-coherence** packaging (beyond qubit story). |
| **Gap 3** — composite / partial trace | DONE | Product states + `tensorDensity` + trace consistency **done**; entangled states PSD proven. |
| **Gap 10** — `GateCompat` thermo | PARTIAL | **`thermoCalibratedScaffold`** + Landauer-linked `freeEnergy` + bounds **in tree**; nontrivial hydration/strength / higher-`n` still open. |
| **Gap 5 / 12** — dynamics | PARTIAL / DONE | **`SchrodingerDynamics.lean`** (unitary Kraus, trace/PSD) **DONE**; **`LindbladDynamics.lean`** qubit dephasing + `whichPath_eq_rho_plus_dissipator` **PARTIAL** (optional limit narrative). |
| **Gap 4 / 11** — von Neumann + DPI | **Gap 4 DONE**; **Gap 11 PARTIAL** | **Unitary invariance** (`Fin n`) **proved**; Tier 1b + identity channel **proved**. General unital DPI: **`axiom`** (Klein / relative entropy) — **stream D** to remove when Mathlib supports it. |
| **Gap 14** — telemetry consumers | DONE | `telemetry_trace_consumer.py`: strictly typed via Pydantic; `TelemetryParser.hs` via Aeson. |
| **Gap 18** — `SimLeanBridge.lean` | DONE | Contract structures in tree; fully aligned with Pydantic/Aeson schemas. |
| **Gap 19** — provenance | PARTIAL | Release / DOI hooks in `CHANGELOG` as you ship. |
| **Cross-lang A0** | DONE | Coq/Agda tracking port implemented completely via `Agda/` and `Coq/` density state specifications. |
| **`p3-epistemic-sensing`** | In progress | ODE–PPO / runtime vs `Epistemic*` — stream **H**; grounding checklist: [`EPISTEMIC_RUNTIME_GROUNDING.md`](EPISTEMIC_RUNTIME_GROUNDING.md). |

**Workspace-style todos** (if your Cursor list still tracks them): end-condition proofs across languages (`accumulatedMassBound`, …), axiom narrowing (`psiAntitone`, `fcMonotone`), and **Phase 2+** items in `GAP_CLOSURE_PLAN` not listed above — reconcile here when scope changes.

## Tracked cross-formalism work (`Coq/` + `Agda/` started — mostly stubs)

- **A0 Coq parity** / **A0 Agda parity:** beyond **`LandauerEinsteinBridge.v`** and **`LandauerEinsteinTrace.agda`**, port **`Gate`**, **`MonoidalState`**, **`InfoTheory`**, etc. from upstream reference **`umst-formal`** when you want full 4-language alignment. **Backlog + port order:** [`Docs/A0_COQ_AGDA_BACKLOG.md`](A0_COQ_AGDA_BACKLOG.md).

## Cross-lang `a1-measurement-cost`

**Repository status:** **Lean + Haskell** artifacts exist (`Lean/MeasurementCost.lean`, `Haskell/src/MeasurementCost.hs`).
**Coq/Agda:** **partial** — slim trees exist (`Coq/LandauerEinsteinBridge.v`, `Agda/LandauerEinsteinTrace.agda`); there is **no** `MeasurementCost` in Coq/Agda **here** yet → full 4-language parity for this ticket remains **partial**. Suggested spec-only filenames: [`A0_COQ_AGDA_BACKLOG.md`](A0_COQ_AGDA_BACKLOG.md).
