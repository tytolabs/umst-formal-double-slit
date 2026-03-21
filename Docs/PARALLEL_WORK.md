<!--
SPDX-License-Identifier: MIT
Copyright (c) 2026 Santhosh Shyamsundar, Santosh Prabhu Shenbagamoorthy — Studio TYTO
-->

# Parallel work — multi-agent coordination

Use this file when **more than one person or agent** is working on the repo at the same time.  
Goal: **minimise merge conflicts** and make ownership visible.

**Related:** [`GAP_CLOSURE_PLAN.md`](GAP_CLOSURE_PLAN.md) (what to build), [`TODO-TRACKING.md`](TODO-TRACKING.md) (milestones), [`REMAINING_WORK_PLAN.md`](REMAINING_WORK_PLAN.md) (**Phase 5 deferred** — what to do next), [`CONTRIBUTING.md`](../CONTRIBUTING.md) (Haskell / build hygiene).

---

## Rules (short)

1. **Claim before you code** — add or update a row in [Active claims](#active-claims) (branch + scope + date).
2. **Prefer disjoint files** — each stream should own a **narrow set of paths**; avoid editing the same `.lean` file as another active claim without agreeing.
3. **Serial “choke points”** — only **one** active change at a time for:
   - `Lean/lakefile.lean` (new roots / deps)
   - `README.md` (top-level counts / badges)
   - `Lean/VERIFY.md` (module map — can append rows in parallel if sections differ)
   - `CHANGELOG.md` — append under `[Unreleased]`; avoid rewriting history another agent just added.
4. **Land after `lake build`** — Lean claimants run `cd Lean && lake build` before merge.
5. **Clear your claim** when done or handed off (or mark `STALE` with date).
6. **Duplicate agents on the same backlog** — do **not** assume you are the only worker. If another agent already has `ACTIVE` on a path you need, either pick a **disjoint** stream or comment on their row (same PR / chat) before editing. Prefer **append-only** edits to `CHANGELOG.md` and shared docs.

---

## Streams (from gap plan)

These are **parallelisable** in principle; pick **one** stream per agent unless scopes are tiny.

| Stream | ID | Typical new / touched paths | Notes |
|--------|----|------------------------------|--------|
| **A — General `n` entropy** | `stream-A` | `Lean/InfoEntropy.lean` and/or **`Lean/GeneralDimension.lean`** | Avoid simultaneous heavy edits to `InfoEntropy` with stream D. |
| **B — Tensor / partial trace** | `stream-B` | **`Lean/TensorPartialTrace.lean`**, `Lean/DensityState.lean` (if extending) | High overlap risk with `DensityState` — coordinate. |
| **C — Dynamics** | `stream-C` | **`Lean/SchrodingerDynamics.lean`**, **`Lean/LindbladDynamics.lean`**, `Lean/MeasurementChannel.lean` (if needed) | Keep Kraus API stable; discuss API changes in claim. |
| **D — Von Neumann / DPI** | `stream-D` | **`Lean/VonNeumannEntropy.lean`**, **`Lean/DataProcessingInequality.lean`**, possibly `InfoEntropy` | Serialise with stream A if both touch `InfoEntropy`. |
| **E — Sim / bridge / CI** | `stream-E` | **`Lean/SimLeanBridge.lean`**, `sim/**`, `.github/workflows/*`, `Docs/*` | CI + `lakefile` — use choke-point rule. |
| **F — Haskell mirror** | `stream-F` | `Haskell/**` | See `CONTRIBUTING.md`; don’t bump `.cabal` without freeze. |
| **G — Python sim** | `stream-G` | `sim/**`, `sim/tests/**` | Often parallel to Lean if not adding new Lean names. |
| **H — Epistemic / runtime** | `stream-H` | `Lean/Epistemic*.lean`, telemetry docs | Overlap with **E** and **G** — align on schema names. |

**Currently reserved in-editor (example):** `p3-epistemic-sensing` — ODE/PPO / runtime vs Epistemic modules; prefer **stream H** and touch `Epistemic*` + related docs. **Grounding checklist:** [`Docs/EPISTEMIC_RUNTIME_GROUNDING.md`](EPISTEMIC_RUNTIME_GROUNDING.md).

---

## Active claims

*Agents: add a row when you start; update status when you finish. **Only `ACTIVE` / `PARTIAL` / `BLOCKED` rows belong here** — move completed work to [Archive](#archive-completed-claims) so the table stays a real coordination surface.*

| Status | Stream | Branch (optional) | Owner / agent | Scope (one line) | Started |
|:------:|:------:|-------------------|---------------|------------------|---------|
| `PARTIAL` | H | — | *(claim)* | **`p3-epistemic-sensing`:** production sim/RL loggers emit JSON matching **`export_sample_telemetry_trace.py`** / consumer schema | 2026-03-21 |
| | D | — | *(unclaimed — claim before edit)* | **Axiom removal:** prove or shrink `klein_inequality` + `vonNeumannEntropy_nondecreasing_unital` when Mathlib matrix log exists | — |
| | A0 | — | *(unclaimed)* | **Coq/Agda** ports per **`A0_COQ_AGDA_BACKLOG.md`** | — |

*Second parallel agent:* insert a new row above when you start (pick **one** stream + list paths). Do not edit the same hot file as an existing **`ACTIVE`** / **`PARTIAL`** row without agreeing first.

**Status values:** `ACTIVE` · `PARTIAL` · `BLOCKED` · `DONE` · `STALE`

### Archive (completed claims)

*Historical — do not treat as “someone is still on this.”*

| Completed | Stream | Owner (historical) | Summary |
|-----------|--------|-------------------|---------|
| 2026-03-21 | A | Cursor | `GeneralDimension` + `LandauerBound` (`pathEntropyBits_n`, diagonal Landauer bounds). |
| 2026-03-21 | B | Cursor | `TensorPartialTrace.lean` — `tensorDensity`, partial trace on product states, Kronecker PSD. |
| 2026-03-21 | C | Antigravity | `MeasurementChannel` fixes + `PMICVisibility`; `SchrodingerDynamics`, `LindbladDynamics`, `GateCompat` thermo scaffold. |
| 2026-03-21 | D | Antigravity + Claude Code | `VonNeumannEntropy` unitary invariance proved; DPI/Klein → **axiom**; project **0 sorry**. |
| 2026-03-21 | E | Antigravity | `SimLeanBridge`, `telemetry_trace_consumer`, optional scipy CI, `PROVENANCE.md`. |
| 2026-03-22 | E | Cursor | Stats/doc reconciliation: **457** thm / **33** lem / **0** sorry / **3** axiom across `PROOF-STATUS`, `README`, `VERIFY`, `TODO-TRACKING`, `GAP_CLOSURE`, `REMAINING_WORK_PLAN`, `OnePager`, `generate_spectacular_gif.py`, `CHANGELOG`; multi-agent notes. |

---

## Merge order (when streams touch shared layers)

1. **Library / proofs** (A–D) — merge in dependency order if needed: **A** before **D** when both change `InfoEntropy`.
2. **Dynamics (C)** — after `DensityState` / `MeasurementChannel` stable.
3. **E / CI / README** — last or in small dedicated PRs.

---

## Quick “do not collide” list

| Path | Risk |
|------|------|
| `Lean/lakefile.lean` | **High** — single writer |
| `README.md` (hero stats) | **High** |
| `Lean/DataProcessingInequality.lean` | **High** — axiom layer, 0 sorry |
| `Lean/InfoEntropy.lean` | **Medium** — streams A & D |
| `Lean/DensityState.lean` | **Medium** — streams B & C |
| `CHANGELOG.md` | **Low** if appending only |

> [!IMPORTANT]
> **Coordination mandate:** Before touching `DataProcessingInequality.lean`, `README.md`, or `lakefile.lean`, agents **must** add an `ACTIVE` row in the Active Claims table above with their stream ID and paths. This prevents merge conflicts on high-risk shared files.

---

## Changelog

When you add a **new Lean root**, update `CHANGELOG.md` under `[Unreleased]` and bump `Lean/VERIFY.md` module map in the same PR when possible.
