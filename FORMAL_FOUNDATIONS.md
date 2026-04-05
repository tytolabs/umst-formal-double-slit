# Formal foundations — `umst-formal-double-slit`

**Version:** Wave 6.5.2 — **2026-04-04**

## Single physical axiom (Lean `axiom`)

| Location | Name | Role |
|----------|------|------|
| `Lean/LandauerLaw.lean` | `physicalSecondLaw` | Same constitutional second-law input as core `umst-formal` (Landauer layer). |

No other `axiom` declarations remain under `Lean/`.

## Theorems (formerly risk items; all proved)

| Location | Name | Note |
|----------|------|------|
| `Lean/LindbladDynamics.lean` | `dephasingSolution_tendsto_diagonal`, alias `dephasing_tendsto_diagonal` | Off-diagonal `Tendsto` at `atTop` via `Real.tendsto_exp_neg_atTop_nhds_zero` and `Filter.Tendsto.ofReal`. |
| `Lean/GeneralVisibility.lean` | `fringeVisibility_n_le_one` | `V ≤ 1` from PSD–Schur + Cauchy–Schwarz (`coherenceL1_carrier_le`). Qubit bridge: `QuantumClassicalBridge.fringeVisibility_le_one`. |

## Witness module

`lake build FormalFoundations` imports `LandauerLaw` + `LindbladDynamics`, witnesses the dephasing limit, and defines `umst_double_slit_formal_complete`.

## Build

```bash
cd Lean && lake build
```

## Build scope

Default `lake build` covers the **core formal layer** only (`lakefile.lean` `roots`). **Test** modules (`Test*.lean`, `test_tensor_eigen.lean`), **optional** stubs (`LogSum.lean`, `MatrixLog.lean`), and **scaffold** files (`FlashMoERuntimeScaffold.lean`) are **excluded**. They have been **manually grep-checked** for tactic `sorry` and stray project `axiom` declarations. **Count methodology:** [`Docs/COUNT-METHODOLOGY.md`](Docs/COUNT-METHODOLOGY.md); regenerate via `python3 scripts/lean_declaration_stats.py`.

## Paper Claims ↔ Formal Lemmas

Manual map from the **five-paper** programme to this package (and the sibling thermo core). Not machine-checked against publications.

| Theme | Claim (informal) | Formal anchor(s) |
|--------|------------------|------------------|
| **I. Clausius–Duhem / rational gate** | Four inequalities define admissibility | `Gate.Admissible`; `helmholtzAntitone` (ψ model in `Gate.lean`) |
| **II. 100% admissibility for checked steps** | `gateCheck = true` ⇒ `Admissible` | `Gate.gateCheckSound` |
| **III. Graded compositional safety** | Composable n-step mass / Kleisli discipline | `Gate.admissibleN_compose`; `Constitutional` |
| **IV. Landauer / observation** | Second-law axiom → Landauer layer | `LandauerLaw.physicalSecondLaw`; `LandauerBound`, `MeasurementChannel`, `ErasureChannel` |
| **V. Double-slit, TMI, epistemics** | Visibility cap, dephasing limit, trajectory MI | `GeneralVisibility.fringeVisibility_n_le_one`, `QuantumClassicalBridge.fringeVisibility_le_one`, `LindbladDynamics.dephasingSolution_tendsto_diagonal`, `EpistemicMI`, `EpistemicTrajectoryMI` |

DIB Kleisli semantics and full **Field/Core** functor for `discover`/`invent`/`build` live in **`umst-formal`** (`DIBKleisli.lean`).

## Wave 6.5 verification audit (closure pass)

| Check | Result |
|--------|--------|
| `lake build` (all `lakefile` roots) | **Succeeded** (verified in workspace) |
| `^axiom ` in `Lean/*.lean` (excluding `.lake`) | **1** — `LandauerLaw.physicalSecondLaw` only |
| Tactic `sorry` / `admit` / `Admitted` in `Lean/*.lean` | **None** (the word “sorry” appears only in **comments** in: `Gate.lean`, `Activation.lean`, `Naturality.lean`) |
| `theorem` / `lemma` in **`lakefile` roots only** (59 modules) | **537** `theorem`, **34** `lemma` (total **571**) — same line-count convention as `umst-formal` |
| All `Lean/*.lean` (excludes `.lake`; includes tests / scratch) | **546** `theorem`, **35** `lemma` (total **581**) |
| Lean files **outside** default roots | `Test3.lean`, `Test4.lean`, `TestEntropy.lean`, `TestFixes.lean`, `TestMixed.lean`, `test_tensor_eigen.lean`, optional `LogSum.lean` / `MatrixLog.lean`, `FlashMoERuntimeScaffold.lean` — **not** in default `lake build` |

### Cold rebuild (audit)

Procedure: `rm -rf .lake && lake build` under `Lean/`. **Result:** `Build completed successfully.` **Stderr/stdout:** no lines matching `warning:` or `error:` (captured log: Mathlib clone `info:` lines + success).

## Logical / physical alignment (informal cross-check)

| Topic | Formal anchor | Note |
|--------|----------------|------|
| Thermodynamic gate + graded safety | `Gate` (imported stack), `admissibleN_compose` | Same rational gate predicate as `umst-formal`; composition theorem proved. |
| Landauer / collapse / observation | `LandauerLaw`, `LandauerBound`, `MeasurementChannel`, `ErasureChannel`, `WhichPathMeasurementUpdate` | **Single** project `axiom`: `physicalSecondLaw`; quantum channels built on top. |
| Double-slit / complementarity | `DoubleSlit`, `Complementarity`, `GeneralVisibility`, `QuantumClassicalBridge` | Fringe visibility **bound** (`fringeVisibility_n_le_one`, qubit bridge); not a claim of experimental calibration. |
| Dephasing / decoherence | `LindbladDynamics.dephasingSolution_tendsto_diagonal` | **Theorem** (analytic limit), not axiom. |
| TMI / epistemic layer | `EpistemicMI`, `EpistemicTrajectoryMI`, telemetry modules | Information-theoretic **definitions + proved lemmas** in-repo; mapping to paper prose is **manual**. |

**Papers:** not machine-checked against this repo. **Mathlib** adds transitive axioms under imports.

## Green-flag status

**GREEN FLAG – Fully Complete** for: default `lake` roots, **zero** tactic `sorry` / `admit` / `Admitted`, **one** project `axiom` (`physicalSecondLaw`), cold `lake build` **without** `warning:`/`error:` in captured output.

Wave **6.5.2**: **`LindbladStreamD`** root (`streamD_limit_to_Lueders_states`); **`DataProcessingInequality`**: `vonNeumannEntropy_nondecreasing_unital_CPTP_n` for **unitary single-Kraus** maps on **`Fin n`** (full arbitrary unital CPTP on general `n` remains future work). **`scripts/lean_declaration_stats.py`** excludes `.lake` from “all Lean” scans. Epistemic “contracts” remain formal scaffolding, not runtime certificates.
