<!--
SPDX-License-Identifier: MIT
Copyright (c) 2026 Santhosh Shyamsundar, Santosh Prabhu Shenbagamoorthy — Studio TYTO
-->

# Remaining work plan (double-slit fork)

Single place for **what to do next** when **telemetry / A0 / sim tracks** are the priority (Phase 5 has **0** `sorry`; remaining formal work is **axiom removal**).

## Phase 5 / stream D (optional — Mathlib-dependent)

- **Klein / general unital DPI** — no `sorry`; exposed as **`axiom`** in **`DataProcessingInequality.lean`** until matrix log / Klein is in Mathlib. **`VonNeumannEntropy`** unitary invariance is **proved**.  
  **Owner:** stream **`D`** — see [`PARALLEL_WORK.md`](PARALLEL_WORK.md).  
  Coordinate before parallel edits to **`DataProcessingInequality.lean`**.

## Planned order (remaining backlog)

1. **Gap 14 / p3 (streams H + E + G)** — telemetry path  
   - **`EmittedStepRecord` metadata** — `telemetry_trace_consumer.py` validates optional `thermodynamicAdmissible` / `confidence` (flat or nested `emitted` object).  
   - **Reference producer (golden JSON):** `sim/export_sample_telemetry_trace.py` — Lean-aligned diagonal entropy / costs + aggregates; run with `--validate` against the consumer.  
   - **Still TODO:** wire the same field shapes into **long-running** sim / RL loggers.  
   - Keep Lean ↔ Python field names aligned with [`EPISTEMIC_RUNTIME_GROUNDING.md`](EPISTEMIC_RUNTIME_GROUNDING.md).

2. **A0** — full **Coq / Agda** parity beyond Landauer–Einstein stubs  
   - Follow [`A0_COQ_AGDA_BACKLOG.md`](A0_COQ_AGDA_BACKLOG.md); wire each new file into **`Makefile`** targets.

3. **a1** — cross-language **MeasurementCost** (and other a1 tickets)  
   - Spec-only `.v` / `.agda` first, then proofs; keep parity with **Lean + Haskell** already in tree.

4. **Gaps 2 / 3 / 10 / 12 / 18 / 19** — as needed for paper / product narrative  
   - See [`GAP_CLOSURE_PLAN.md`](GAP_CLOSURE_PLAN.md) and [`TODO-TRACKING.md`](TODO-TRACKING.md).

5. **After Klein/DPI axioms become theorems** — refresh **`make lean-stats-md`** → **`PROOF-STATUS.md`**, **`README`**, **`OnePager`**, GIF overlay when **`axiom` count drops**.

## Related

- Milestones table: [`TODO-TRACKING.md`](TODO-TRACKING.md)  
- Multi-agent claims: [`PARALLEL_WORK.md`](PARALLEL_WORK.md)
