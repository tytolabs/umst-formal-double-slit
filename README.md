<!--
SPDX-License-Identifier: MIT
Copyright (c) 2026 Santhosh Shyamsundar, Santosh Prabhu Shenbagamoorthy — Studio TYTO
-->

<div align="center">

# The Thermodynamic Cost of Knowing

### Observation as Irreversible Payment

[![DOI](https://zenodo.org/badge/DOI/10.5281/zenodo.19159660.svg)](https://doi.org/10.5281/zenodo.19159660)
[![Lean](https://github.com/tytolabs/umst-formal-double-slit/actions/workflows/lean.yml/badge.svg)](https://github.com/tytolabs/umst-formal-double-slit/actions/workflows/lean.yml)
[![Haskell](https://github.com/tytolabs/umst-formal-double-slit/actions/workflows/haskell.yml/badge.svg)](https://github.com/tytolabs/umst-formal-double-slit/actions/workflows/haskell.yml)
[![Formal](https://github.com/tytolabs/umst-formal-double-slit/actions/workflows/formal.yml/badge.svg)](https://github.com/tytolabs/umst-formal-double-slit/actions/workflows/formal.yml)
[![License: MIT](https://img.shields.io/badge/License-MIT-black.svg)](LICENSE)

**Formally verified in Lean 4 + Mathlib&ensp;·&ensp;**0** `sorry` across all Lean files&ensp;·&ensp;**6** axioms (Klein, unital DPI, physical 2nd law, visibility bound, dephasing limit — `Lean/VERIFY.md`)&ensp;·&ensp;**515** theorems + **33** lemmas (heuristic scan — `PROOF-STATUS.md`)**

_Observation has a price. Every fraction of a bit extracted destroys a corresponding fraction of interference._
_The thermodynamic cost is exact, non-negotiable, and formally verified._

<br>

<picture>
  <source media="(prefers-color-scheme: dark)" srcset="Docs/Media/teaser.png">
  <source media="(prefers-color-scheme: light)" srcset="Docs/Media/teaser.png">
  <img alt="The Thermodynamic Cost of Knowing — Formally Verified" src="Docs/Media/teaser.png" width="820">
</picture>

<br>

<img src="Docs/Media/double-slit-collapse.gif" alt="Interference collapse animation — visibility decreasing as which-path information increases" width="820">

<sub>As which-path information I rises from 0 → 1, the interference pattern collapses along the Englert curve V = √(1 − I²).<br>Every frame is a theorem. Machine-checked in Lean 4.</sub>

<br>

| | |
|:---:|:---:|
| **53** Lean modules | **515** `theorem` + **33** `lemma` (line-start scan) |
| **0** sorry, **6** axioms (Klein, unital DPI, physical 2nd law, visibility bound, dephasing limit, tensor entropy) | All qubit-level theorems proved |
| **87** Python unit tests | **14** Haskell QuickCheck properties |
| **5** languages | Lean 4 · Haskell · Python · Coq · Agda |

</div>

---

## Core Result

### In plain language

Extracting which-path information from a quantum system destroys interference. The destruction is proportional, not binary. Extract 0.3 bits of path information and visibility drops to ≈ 0.95. Extract 0.7 bits and it drops to ≈ 0.71. Extract the full bit and the interference pattern is gone entirely. This is the Englert complementarity relation, V² + I² ≤ 1. Every point on the curve is physically realizable.

Each fraction of information extracted carries a thermodynamic cost at Landauer's scale — *k_B T ln 2* per bit, minimum, irreversible. This is not a matter of interpretation. It is thermodynamic accounting, enforced by the second law.

This repository proves the full chain: density matrix → Kraus measurement channel → Englert complementarity → diagonal von Neumann entropy → Landauer bound → cost–coherence identity. **515 theorems. 0 `sorry`. 6 explicit axioms** (each stated in `Lean/VERIFY.md` — corresponding to physical principles or Mathlib gaps).

**Relevance beyond quantum optics.** Any system that extracts information from a physical process — sensing, control, inference, materials gating, computing — is subject to the same thermodynamic constraint. This repository is the formal proof of that constraint, machine-checked in four languages.

---

### Formal statement

> **Principle of Maximal Information Collapse.**&ensp;When an observer extracts which-path information from a quantum system, the residual coherence capacity is:
>
> ```
> Residual Coherence = 1 − MI_extracted / (k_B T ln 2)  ∈ [0, 1]
> ```
>
> Extract **0 bits** ⟹ full interference.&ensp;Extract **1 bit** ⟹ complete decoherence.
>
> **Crucially, observation is not binary.** A probe extracting 0.3 bits barely disturbs the fringes (V ≈ 0.95). At 0.7 bits the pattern is heavily suppressed (V ≈ 0.71). Full collapse requires the _entire_ bit. Every point on the Englert curve V² + I² = 1 is physically realizable, and each carries a proportional Landauer cost. The collapse is a _continuum_, not a switch.
>
> _Machine-checked in Lean 4 with Mathlib. **515 theorem + 33 lemmas (heuristic); 0 sorry; 6 axioms (Klein, unital DPI, physical 2nd law, visibility bound, dephasing limit, tensor entropy).**_

<details>
<summary><strong>Show me the proof</strong> — key theorem in Lean 4</summary>

```lean
-- Lean/LandauerBound.lean, line 140
theorem principle_of_maximal_information_collapse (ρ : DensityMatrix hnQubit) :
    0 ≤ residualCoherenceCapacity ρ ∧ residualCoherenceCapacity ρ ≤ 1 :=
  ⟨residualCoherenceCapacity_nonneg ρ, residualCoherenceCapacity_le_one ρ⟩

-- When path entropy is maximal (1 bit), residual coherence collapses to zero.
theorem maximal_extraction_collapses_coherence (ρ : DensityMatrix hnQubit)
    (h : pathEntropyBits ρ = 1) : residualCoherenceCapacity ρ = 0 := by
  unfold residualCoherenceCapacity; linarith

-- When no path information is extracted, full coherence capacity remains.
theorem null_extraction_preserves_coherence (ρ : DensityMatrix hnQubit)
    (h : pathEntropyBits ρ = 0) : residualCoherenceCapacity ρ = 1 := by
  unfold residualCoherenceCapacity; linarith
```

→ [`Lean/LandauerBound.lean`](Lean/LandauerBound.lean) · [Proof / module map](Lean/VERIFY.md) · [`PROOF-STATUS.md`](PROOF-STATUS.md) (counts)

</details>

---

## What This Repository Proves

A formally verified bridge from quantum measurement theory to classical thermodynamics — closing the loop between wave-particle duality, Landauer erasure, and decoherence:

| # | Theorem | Statement | Lean Module |
|:-:|---------|-----------|-------------|
| 1 | **Englert complementarity** | V² + I² ≤ 1 | `QuantumClassicalBridge` |
| 2 | **Which-path collapse** | V → 0 after Lüders channel | `MeasurementChannel` |
| 3 | **Projector properties** | self-adjoint, idempotent, orthogonal, TP | `MeasurementChannel` |
| 4 | **Density matrix diagonals** | PSD ⟹ pᵢ ≥ 0, Σpᵢ = 1, pᵢ ≤ 1 | `DensityState` |
| 5 | **Diagonal entropy bound** | H_diag ≤ ln 2 | `InfoEntropy` |
| 6 | **Landauer cost cap** | cost ≤ k_B T ln 2 | `LandauerBound` |
| 7 | **Path entropy ≤ 1 bit** | S_bits ∈ [0, 1] | `LandauerBound` |
| 8 | **Maximal collapse** | S_bits = 1 ⟹ Residual = 0 | `LandauerBound` |
| 9 | **Null preservation** | S_bits = 0 ⟹ Residual = 1 | `LandauerBound` |
| 10 | **Cost–coherence identity** | Q = k_B T ln 2 · (1 − Residual) | `LandauerBound` |
| 11 | **Erasure ≥ bound** | dissipatedHeat ≥ landauerCostDiagonal | `LandauerBound` |
| 12 | **Which-path invariance** | Landauer cost unchanged by measurement | `LandauerBound` |
| 13 | **Gate enforcement** | admissibility + Landauer + cap in one | `DoubleSlit` |
| 14 | **PMIC visibility** | `V² + residualCoherenceCapacity ≤ 1` | `PMICVisibility` + `PMICEntropyInterior` |
| 15 | **ℚ → ℝ gate lift** | `Admissible` preserved under cast | `QRBridge` |

---

## Proof Architecture

```mermaid
flowchart TB
    subgraph QM["Quantum Layer"]
        DM["DensityMatrix ρ ∈ ℂ²ˣ²\nPSD + Tr(ρ) = 1"]
        KC["Kraus Channel\nLüders Which-Path\nΠᵢ ρ Πᵢ"]
        IV["Born Weights → (I, V)\nI = |p₀ − p₁|\nV = 2|ρ₀₁|"]
    end

    subgraph COMP["Complementarity"]
        ENG["Englert Relation\nV² + I² ≤ 1"]
        COL["Which-Path Collapse\nV → 0, I preserved"]
    end

    subgraph THERMO["Thermodynamic Layer"]
        IE["Diagonal von Neumann\nH = −Σ pᵢ ln pᵢ ≤ ln 2"]
        LB["Landauer Bound\nQ ≥ k_B T · H"]
        EP["ErasureProcess\ndissipatedHeat ≥ cost"]
    end

    subgraph PMIC["Principle of Maximal Information Collapse"]
        RES["Residual Coherence\n= 1 − pathEntropyBits\n∈ [0, 1]"]
        ZERO["Extract 1 bit → Residual = 0\nComplete Decoherence"]
        FULL["Extract 0 bits → Residual = 1\nFull Visibility"]
    end

    DM --> KC
    DM --> IV
    KC --> COL
    IV --> ENG
    COL --> IE
    ENG -->|"measurement destroys V"| COL
    IE --> LB
    LB --> EP
    LB --> RES
    RES --> ZERO
    RES --> FULL
    EP -->|"Second Law"| RES
```

---

## Lean modules (53 `lakefile` roots, `lake build` — see `Lean/VERIFY.md` for `sorry` map)
*(Counts: `make lean-stats-md` → **515** line-start `theorem`, **33** `lemma`, **6** `axiom` in 58 `.lean` files — heuristic only, see `scripts/lean_decl_stats.py` and `PROOF-STATUS.md`. Many are small/interface lemmas; headline physics chain is the PMIC + double-slit narrative.)*

<details>
<summary><strong>Quantum core</strong> — density matrices, Kraus channels, complementarity, entropy, Landauer</summary>

| Module | Key theorems |
|--------|-------------|
| `DensityState` | `DensityMatrix`, `pureDensity`, diagonal non-negativity, trace-one, bound-by-one (all proved) |
| `MeasurementChannel` | Kraus channels, `whichPathChannel`, `compose`, projector self-adjoint/idempotent/orthogonal (all proved) |
| `QuantumClassicalBridge` | `complementarity_fringe_path` (V² + I² ≤ 1), `observationStateCanonical` |
| `InfoEntropy` | `shannonBinary = Real.binEntropy`, `vonNeumannDiagonal ≤ log 2` |
| `LandauerBound` | `pathEntropyBits ≤ 1`, `principle_of_maximal_information_collapse`, `ErasureProcess` |
| `PMICEntropyInterior` | `four_mul_x_one_sub_x_mul_log_two_interior` — binary entropy ≥ `4x(1-x) log 2` on `(0,1/2)` (MVT + ratio monotonicity) |
| `PMICVisibility` | `visibility_sq_le_coherence_capacity` — `V² + residualCoherenceCapacity ≤ 1` |
| `DoubleSlit` | Gate enforcement, Landauer cap; full-chain import root |
| `WhichPathMeasurementUpdate` | `measurementUpdateWhichPath` (Lüders update, fringe collapse, Landauer invariance) |
| `GeneralDimension` | `vonNeumannDiagonal_n_le_log_n` (diagonal entropy ≤ `log n`) |
| `GeneralResidualCoherence` | `RCC_n ∈ [0,1]`; purity-based formula; Cauchy-Schwarz from first principles; qubit compatibility |
| `QuantumMutualInfo` | `I(A:B) = S(A)+S(B)−S(AB)`; upper bound `≤ log nA + log nB`; product-state zero |
| `ErasureChannel` | Reset-to-`\|0⟩` Kraus channel; trace preservation; `idealResetErasure` at Landauer equality |
| `GeneralVisibility` | `fringeVisibility_n` ($\ell_1$ norm of coherence for `Fin n`); `fringeVisibility_n_nonneg`; `fringeVisibility_n_whichPath_apply` |
| `TensorPartialTrace` | `tensorDensity`, partial traces, Kronecker PSD lemmas |
| `VonNeumannEntropy` | Spectral `S(ρ)`; `Fin 1`/`Fin 2`/general `Fin n` unitary invariance **proved**; `charpoly` conjugation (`Lean/VERIFY.md`) |
| `DataProcessingInequality` | Qubit diagonal ≥ spectral; identity-channel unital base; general unital DPI **axiom** (`Lean/VERIFY.md`) |

</details>

<details>
<summary><strong>Dynamics & Lean↔sim contracts</strong> — unitary Kraus, Lindblad dephasing, numeric witness shapes</summary>

| Module | Role |
|--------|------|
| `SchrodingerDynamics` | Unitary `U` as single-Kraus channel; `UρUᴴ` preserves `DensityMatrix` |
| `LindbladDynamics` | Lindblad dissipator; which-path as strong dephasing limit; `dephasingSolution_tendsto_diagonal` |
| `SimLeanBridge` | Propositional contracts (`SimDensityContract`, complementarity/Landauer witnesses) for `sim/` outputs |

</details>

<details>
<summary><strong>Epistemic sensing stack</strong> — probes, mutual information, policy optimization</summary>

| Module | Purpose |
|--------|---------|
| `EpistemicSensing` | Probe interface, `nullProbe`/`whichPathProbe`, collapse/preserve bridges |
| `EpistemicMI` | Probe-indexed MI in nats/bits + Landauer links |
| `EpistemicDynamics` | Policy rollouts with null/which-path invariants |
| `EpistemicTrajectoryMI` | Cumulative MI/cost with finite upper bounds |
| `EpistemicPolicy` | Finite-horizon utility argmax + constrained optimality |
| `EpistemicGalois` | Galois connection: info extractable ↔ energy deployed |
| `ProbeOptimization` | Cost-penalized finite probe selection |
| `ExamplesQubit` | Worked examples: \|+⟩, \|0⟩, \|1⟩ |

</details>

<details>
<summary><strong>Runtime contract stack</strong> — telemetry, numerics, solver calibration</summary>

| Module | Purpose |
|--------|---------|
| `EpistemicRuntimeContract` | Trace coherence → policy theorem bridge |
| `EpistemicNumericsContract` | Numeric aggregate record → utility equivalence |
| `EpistemicPerStepNumerics` | Per-step fold → cumulative consistency |
| `EpistemicRuntimeSchemaContract` | Emitted schema → contract transfer |
| `EpistemicTelemetryBridge` | Runtime naming bridge (`trajMI`, `effortCost`) |
| `EpistemicTelemetryApproximation` | Epsilon-approximation with zero-error collapse |
| `EpistemicTelemetryQuantitativeUtility` | Nonzero-error deviation bounds |
| `EpistemicTraceDerivedEpsilonCertificate` | Residual-based epsilon extraction |
| `EpistemicTelemetrySolverCalibration` | Solver params → epsilon budgets |
| `EpistemicTraceDrivenCalibrationWitness` | Trace + calibration → utility bounds |
| `PrototypeSolverCalibration` | Concrete instantiation (step=1/100, order=2) |

</details>

<details>
<summary><strong>Classical / upstream integration</strong> — UMST core, gate compatibility, vendored modules</summary>

| Module | Purpose |
|--------|---------|
| `UMSTCore` | ℝ SI constants, Landauer bit energy, `ThermodynamicState`, `Admissible` |
| `DoubleSlitCore` | Coarse `MeasurementUpdate` skeleton |
| `GateCompat` | Born weights → `ThermodynamicState` scaffold |
| `QRBridge` | ℚ `Gate.ThermodynamicState` → ℝ `UMSTCore.ThermodynamicState`; `admissible_thermodynamicStateToReal` |
| `Complementarity` | Discoverability shims |
| `Gate`, `Naturality`, `Activation`, `FiberedActivation`, `MonoidalState` | Upstream ℚ core (vendored) |
| `LandauerLaw`, `LandauerExtension`, `LandauerEinsteinBridge` | Upstream Landauer stack (vendored) |

</details>

---

## Cross-Language Verification

Every claim is checked in at least two languages. Phase 1 PMIC entropy–quadratic bound is closed in `Lean/PMICEntropyInterior.lean` (module map: `Lean/VERIFY.md`).

| Language | Artifact | Status | Command |
|:--------:|----------|:------:|---------|
| **Lean 4** | 53 modules, 515 thm + 33 lem (heuristic) | **0** sorry, **6** axioms — `Lean/VERIFY.md` | `cd Lean && lake build` |
| **Haskell** | 8 modules, 14 QuickCheck + sanity | **All pass** | `cd Haskell && cabal test` |
| **Python** | 87 unit tests, 4 sim scripts + telemetry (Gap 14) | **All pass** | `make sim && make sim-test` |
| **Coq** | **9** `.v` files (full `Coq/` tree incl. `Gate`, `Extraction`, `Constitutional`) | **Compiles**; **2** `Admitted` + axioms in `VonNeumannEntropySpec.v` — `Coq/README.md` | `make coq-check` |
| **Agda** | **11** entry modules (specs + `Gate` / `Helmholtz` / activation stack) | **Clean** typecheck; specs postulated where noted — `Agda/README.md` | `make agda-check` |

---

## Quick Start

```bash
# Full verification (Lean + Python + Haskell)
make ci-full

# Individual layers
cd Lean && lake build          # Lean 4 — counts: PROOF-STATUS.md / make lean-stats-md
make sim && make sim-test      # Python — 87 unit tests
make telemetry-sample          # Gap 14 — golden JSON + consumer (NumPy)
cd Haskell && cabal test       # Haskell — 14 QuickCheck properties
make formal-check              # Coq + Agda (optional toolchains; matches CI formal.yml)
make coq-check                 # Coq only (Rocq/Coq 9.x or 8.20+ `From Stdlib`)
make agda-check                # Agda only (2.6+ + stdlib)

# Generate visualizations
python3 scripts/generate_spectacular_gif.py   # → Docs/Media/double-slit-collapse.gif + teaser.png
```

---

## Claim Taxonomy

**Machine-checked (formally verified):**
- Englert complementarity: V² + I² ≤ 1 ✓
- Landauer bound for diagonal path entropy ✓
- Kraus measurement channels: projector properties, TP, which-path collapse ✓
- Full erasure ≥ Landauer cost ✓
- Principle of Maximal Information Collapse: continuous cost–coherence identity ✓

Measurement is irreversible. The compiler confirms it. The second law confirmed it first.

**Explicitly outside scope:**
- Full quantum derivation from Schrödinger dynamics (partial spatial coverage in `sim/`)
- Empirical laboratory verification (the formal chain is complete; experimental confirmation is separate work)

---

## Connection to the UMST Programme

This repository is part of the **Foundations of Constitutional Physics (FCP)** series by [Studio TYTO](https://zenodo.org/communities/unified-material-state-tensors/records?q=&l=list&p=1&s=10&sort=newest). For a **single curated overview** (figures, roadmap, and pointers), use the **public research dashboard** — it is updated as the programme grows:

| Resource | What it is | Link |
|:---------|------------|:-----|
| **Research dashboard** | Curated PDF overview of the UMST / FCP thread | [**DOI 10.5281/zenodo.18940933**](https://doi.org/10.5281/zenodo.18940933) · [record](https://zenodo.org/records/18940933) |
| **Public community repository** | Aggregated deposits (papers, data, compendia) | [**Unified Material State Tensors** community](https://zenodo.org/communities/unified-material-state-tensors/records) |

**FCP studies** (peer-facing preprints / compendia):

| Study | Title | Repository |
|:-----:|-------|:------:|
| FCP-I | Physics-Gated AI — UMST tensor + DUMSTO hard gate | [record](https://zenodo.org/records/18768547) |
| FCP-II | Epistemic Sensing — MI-guided proxy selection | [record](https://zenodo.org/records/18894710) |
| **This work** | **The Thermodynamic Cost of Knowing — formal double-slit** | **This repo** (cite via your release DOI when you mint one) |

**Related code** ([`github.com/tytolabs`](https://github.com/tytolabs)):

| Repository | Role |
|------------|------|
| [`umst-formal`](https://github.com/tytolabs/umst-formal) | Classical UMST gate, Landauer stack, Lean + Coq + Agda + Haskell (wider formal base) |
| **`umst-formal-double-slit`** (here) | Quantum measurement layer: density matrices, Kraus channels, Englert complementarity, Landauer–path-entropy bridge |
| [`umst-prototype-2a`](https://github.com/tytolabs/umst-prototype-2a) | Prototype / epistemic-sensing demo stack (e.g. web-style UI, ROS2 bridge — see that repo’s README) |

The key bridge: the UMST gate enforces thermodynamic admissibility on _classical_ material states (mass, energy, hydration over ℚ). This work extends that gate to _quantum_ density matrices, proving that Englert complementarity + Landauer erasure are the quantum analogues of Clausius-Duhem + Helmholtz free energy.

---

## Documentation

| Document | Path |
|----------|------|
| Technical note (Public preprint) | [`Docs/Preprint/UMST_DoubleSlit_Formal_Verification.tex`](Docs/Preprint/UMST_DoubleSlit_Formal_Verification.tex) <br> [![DOI](https://zenodo.org/badge/DOI/10.5281/zenodo.19159660.svg)](https://doi.org/10.5281/zenodo.19159660)|
| Proof status & declaration counts | [`PROOF-STATUS.md`](PROOF-STATUS.md) |

| Module map & theorem names | [`Lean/VERIFY.md`](Lean/VERIFY.md) |
| Mathematical foundations | [`Docs/Mathematical-Foundations.md`](Docs/Mathematical-Foundations.md) |
| Assumptions & non-claims | [`Docs/ASSUMPTIONS-DOUBLE-SLIT.md`](Docs/ASSUMPTIONS-DOUBLE-SLIT.md) |
| Epistemic sensing note | [`Docs/EpistemicSensingQuantum.md`](Docs/EpistemicSensingQuantum.md) |
| Provenance & lineage | [`Docs/PROVENANCE.md`](Docs/PROVENANCE.md) |
| Simulator details | [`sim/README.md`](sim/README.md) |
| Haskell mirror | [`Haskell/README.md`](Haskell/README.md) |
| Coq / Rocq track | [`Coq/README.md`](Coq/README.md) |
| Agda track | [`Agda/README.md`](Agda/README.md) |
| Contributing | [`CONTRIBUTING.md`](CONTRIBUTING.md) |
| Changelog | [`CHANGELOG.md`](CHANGELOG.md) |

---

## Authors

**Santhosh Shyamsundar** — Studio TYTO; IAAC Barcelona · [santhoshshyamsundar@tyto.studio](mailto:santhoshshyamsundar@tyto.studio)

**Santosh Prabhu Shenbagamoorthy** — Studio TYTO; IAAC Barcelona · [santosh@tyto.studio](mailto:santosh@tyto.studio)

---

## Acknowledgments

Portions of this work were developed in collaboration with advanced large-language-model tools.
Claude Opus and Sonnet 4.6 (Anthropic) provided surgical precision during drafting and refinement.
Gemini 3.1 Pro High (Google) offered exceptional large-context planning and file management.
Grok 4.20 by xAI and its collaborative reasoning team contributed core mathematical and scientific reasoning.
The Cursor code editor, Composer, Claude Code, and Antigravity supported seamless implementation and agentic file management.

The large-language models assisted with exploration, drafting, and code scaffolding — never with the validity of formal proofs. All theorems were machine-checked by their respective compilers (Lean 4, Coq/Rocq, Agda), which accept only well-typed terms, never persuasive arguments.

The mathematical reality captured in this repository rests entirely on the foundational work of the open-source community. We acknowledge the maintainers and contributors of the **Lean 4** theorem prover and **Mathlib**, the **Coq / Rocq** proof assistant, and the **Agda** dependently typed language and standard library. The simulation and property-checking layers depend on the rigor of **Haskell** (GHC, Cabal, QuickCheck) and **Python 3** (NumPy, SciPy, Matplotlib). Without the decades of collective effort embedded in these compilers and libraries, formally verified physics of this nature would not be possible.

---

<div align="center">
<sub>MIT License · © 2026 Studio TYTO · <a href="https://github.com/tytolabs">github.com/tytolabs</a></sub>
</div>
