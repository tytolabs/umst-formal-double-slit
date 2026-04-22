<!--
SPDX-License-Identifier: MIT
Copyright (c) 2026 Santhosh Shyamsundar, Santosh Prabhu Shenbagamoorthy — Studio TYTO
-->

# Changelog — umst-formal-double-slit

All notable changes to this **standalone repository** are listed here. The upstream framework repo has its own history.

## [Unreleased]

### Fixed (2026-04-22)

- **GitHub Actions `formal.yml` (Coq job)** — create `Coq/_extract/` before `rocq compile` so `Extraction.v` can emit `gate_extracted.ml` (matches root `Makefile` `coq-check`; fixes CI failure `No such file or directory` on `Coq/_extract/gate_extracted.ml`).

### Documentation (2026-04-22)

- **Count verification** — re-ran `python3 scripts/lean_declaration_stats.py`; headline **59** roots · **537+34** (roots-only) / **546+35** (all `Lean/*.lean`) unchanged from `README.md` / `PROOF-STATUS.md`. Cross-linked maintenance: sibling **`tytolabs/umst-formal`** Lean totals refreshed the same day (FPD wave + snapshot) for downstream **`tytolabs/egoff`** registry parity work.

### Added (Wave 6.5.2 — 2026-04-04)

- **`Lean/LindbladStreamD.lean`** — discrete **stream-D** sampling of qubit dephasing; **`streamD_limit_to_Lueders_states`** (composes `dephasingSolution_tendsto_diagonal` with `n : ℕ → ∞`). New `lakefile` root **`LindbladStreamD`**.
- **`Lean/DataProcessingInequality.lean`** — **`vonNeumannEntropy_nondecreasing_unital_CPTP_n`**: unital CPTP given by a **single unitary Kraus** on **`Fin n`**; von Neumann entropy **unchanged** (DPI with equality). **Does not** settle arbitrary multi-Kraus unital CPTP on general `n`.

### Fixed (documentation / tooling)

- **`scripts/lean_declaration_stats.py`** — exclude **`.lake`** from “all `Lean`” and axiom scans (avoids Mathlib dependency noise); refreshed counts: **59** roots, **537+34** roots-only / **546+35** all-Lean.
- **Lean stats / axioms (2026-04)** — **`FORMAL_FOUNDATIONS.md`**, **`PROOF-STATUS.md`**, **`README.md`**, **`Lean/VERIFY.md`**, **`Docs/PROVENANCE.md`**, preprint TeX, **`scripts/generate_spectacular_gif.py`**: **59** lake roots; **537+34** (roots) / **546+35** (all `Lean/*.lean`, script excludes `.lake`); **1** Lean `axiom` (`physicalSecondLaw`); visibility + dephasing limits are **theorems**. Methodology: **`Docs/COUNT-METHODOLOGY.md`**, **`scripts/lean_declaration_stats.py`**.
- **`Docs/PROVENANCE.md`** — axiom inventory: **1** Lean `axiom`; fringe visibility + dephasing diagonal limit **theorems** (supersedes earlier “3 axioms” wording).
- **`Docs/ASSUMPTIONS-DOUBLE-SLIT.md`** — DPI non-claim narrowed to **arbitrary multi-Kraus** unital CPTP; documents proved **unitary single-Kraus** `Fin n` case and qubit which-path instances.
- **`Lean/VERIFY.md`** — module row for **`GeneralVisibility`**; cross-link from “Not in this track yet” to README + assumptions doc.

### Added (general dimension & limits — Phase 2 & 4)

- **`Lean/GeneralVisibility.lean`** — Gap 2: defined rigorous $\ell_1$ norm of coherence (`fringeVisibility_n`) for arbitrary `Fin n` dimensional epistemic sensing.
- **`Lean/GateCompat.lean`** — Gap 10: generalized metric hook for physical multi-slit hydration leveraging `fringeVisibility_n` across `ThermodynamicState`.
- **`Lean/LindbladDynamics.lean`** — Gap 12: explicit topological filter boundary (`dephasingSolution_tendsto_diagonal`) proving continuous exponential trace limits toward Lüders states as $t \to \infty$.

### Added (telemetry boundary schemas — Phase 6)

- **`sim/telemetry_trace_consumer.py`** — Gap 14 & 18: strict `pydantic` mapping (`BaseModel` tracing) limiting trace inputs natively against `SimLeanBridge` type contracts.
- **`Haskell/src/TelemetryParser.hs`** — Gap 14: extensive GHC Generic `Aeson FromJSON` structs implementing pure functional ingress parsing.

### Added (general-n RCC, QMI, erasure, sorry elimination)

- **`Lean/GeneralResidualCoherence.lean`** — Gap 3 (extended): General-n **Residual Coherence Capacity** via purity decomposition `RCC_n = (Tr(ρ²) - Σpᵢ²)/(1 - Σpᵢ²)`. Fully proved: `RCC_n ∈ [0,1]` (Cauchy-Schwarz from first principles via 2×2 PSD submatrices), `RCC_n = 0 ↔ diagonal`, `RCC_n = 1 ↔ pure`, qubit compatibility `RCC_2 = |ρ₀₁|²/(p₀p₁)`. **0 sorry**.
- **`Lean/QuantumMutualInfo.lean`** — Quantum mutual information `I(A:B) = S(A) + S(B) - S(AB)`, conditional entropy, `I ≤ log nA + log nB` upper bound, `I(A:B) = 0` for product states. Tensor additivity `S(ρ⊗σ) = S(ρ)+S(σ)` is **proved** as `vonNeumannEntropy_tensorDensity_eq` in **`KroneckerEigen.lean`** (see `PROOF-STATUS.md`).
- **`Lean/ErasureChannel.lean`** — Concrete reset-to-`|0⟩` erasure channel (Kraus operators `K₀`, `K₁`), trace preservation, output always `|0⟩⟨0|`, zero output entropy. Provides `ErasureProcess` saturation of Landauer bound.

### Fixed (sole remaining sorry eliminated)

- **`GeneralResidualCoherence.lean` line 155** — `trace_sq_le_one`: The hidden sorry in the broken circular `calc` was replaced by a complete Lean 4 proof. Key lemma: `normSq(ρᵢⱼ) ≤ (ρᵢᵢ).re * (ρⱼⱼ).re` proved for all i,j by applying PSD quadratic form to specific vectors on 2×2 submatrices. Three-case proof: `p > 0` (H2 vector), `p = 0, q > 0` (H1 vector), `p = q = 0` (four sign-testing vectors force b = 0). **Total project sorry count: 0**.

### Added (Coq/Agda — A0 quantum parity)

- **`Coq/DensityStateSpec.v`** — 2×2 density matrix record + PSD constraints; **proved**: `p0_le_one`, `p1_le_one`, `coherence_bounded`, `p0_p1_le_quarter`.
- **`Coq/ComplementaritySpec.v`** — Englert complementarity **V²+D²≤1** fully **proved** (real algebra / `lra`, no `nlra` dependency).
- **`Coq/VonNeumannEntropySpec.v`** — `negMulLog` and core lemmas **proved**; **`shannon_binary_le_ln2`** and **`negMulLog_zero_interval`** as **axioms** (replacing `Admitted`); **`vonNeumannDiagonal_zero_iff_diagonal_pure`** **proved**; spectral entropy partly **axiomatised** (see file).
- **`Agda/DensityStateSpec.agda`** — density matrix spec over ℚ; properties postulated (authority: Lean).
- **`Agda/ComplementaritySpec.agda`** — Englert relation postulated.
- **`Agda/VonNeumannEntropySpec.agda`** — Von Neumann entropy + DPI specs postulated.
- **`Docs/A0_COQ_AGDA_BACKLOG.md`** — refreshed inventory; priorities 1–4 all done.

### Changed (Coq / Agda verification environments)

- **`Makefile`** — **`coq-check`** compiles all **9** `Coq/*.v` files in order; **`agda-check`** type-checks all **11** Agda entry modules; **`formal-check`** runs both. Wrapper **`scripts/formal_check.sh`**.
- **`Coq/_CoqProject`** — lists **`-Q . UMSTFormal`** and the full module set (for `coq_makefile` / IDE).
- **Coq** — `From UMSTFormal` imports in `MeasurementCost.v`, `Constitutional.v`, `Extraction.v`; **`Extraction.v`** uses **`From Stdlib`** extraction libs and writes OCaml to **`Coq/_extract/`** (gitignored).
- **Agda** — `Gate.agda` / `Helmholtz.agda` use **`natToℚ`** instead of **`mkℚ`** + coprimality lemmas (stdlib API variance).
- **`.github/workflows/formal.yml`** — CI: Docker **`rocq/rocq-prover:9.0`** + Ubuntu **`agda`**; runs **`make coq-check`** / **`make agda-check`**.
- **Docs** — **`Coq/README.md`**, **`Agda/README.md`**, **`CONTRIBUTING.md`**, **`PROOF-STATUS.md`**, **`scripts/README.md`**.

### Added (sim — PML + 3D Schrödinger)

- **`sim/schrodinger_2d_pml.py`** — true PML (polynomial-graded conductivity) for 2D split-step; `pml_conductivity_profile`, `pml_damping_mask_2d`, `split_step_evolve_2d_pml`.
- **`sim/schrodinger_3d_split_step.py`** — 3D FFT split-step with soft double-slit in (y,z) plane; `make_grid_3d`, `initial_gaussian_3d`, `kinetic_half_step_3d`, `absorption_mask_3d`.
- **`sim/tests/test_schrodinger_2d_pml.py`** — 6 PML mask tests (shape, symmetry, damping, σ=0/n=0 recovery).
- **`sim/tests/test_schrodinger_3d_split_step.py`** — 19 tests (grid, Gaussian, potential, absorption mask, free norm conservation).
- Python unit tests: **62 → 87** (+25).

### Changed (docs — stats reconciliation)

- **`README.md`**, **`PROOF-STATUS.md`**, **`Lean/VERIFY.md`**, **`Docs/OnePager-DoubleSlit.tex`**, **`scripts/generate_spectacular_gif.py`**, **`CHANGELOG.md`**, **`Docs/PARALLEL_WORK.md`** — heuristic counts updated: **457** `theorem`, **33** `lemma`, **87** Python tests; cross-language table: Coq 9 `.v` files, Agda 11 entry modules.

### Added (license headers)

- **MIT SPDX headers** on first-party **`Lean/**/*.lean`**, **`sim/**/*.py`**, **`scripts/**/*.py`**, **`Haskell/**/*.hs`**, **`Coq/**/*.v`**, **`Agda/**/*.agda`**, **`Docs/*.tex`**, and **`.md`** docs; maintenance tool **`scripts/add_spdx_headers.py`** (skips **`.lake`**, **`dist-newstyle`**, **`.pytest_cache`**, …); documented in **`CONTRIBUTING.md`** and **`scripts/README.md`**.
- **`.gitignore`** — **`**/.pytest_cache/`** so pytest cache is not committed.

### Fixed (Haskell layout)

- **Module shadowing:** root-level duplicates of `MeasurementCost` / `LandauerExtension` / `MonoidalState` moved to **`Haskell/legacy/`** so GHC’s `-i` (package dir) no longer picks them over **`src/`**. **`cabal build all`** + **`cabal test`** succeed.
- **Stub executable:** `app/Main.hs` no longer references missing `MyLib`; **`umst-formal-double-slit` exe** is a minimal placeholder (use **`cabal test`** for QuickCheck).

### Changed (Lean — **0 sorry** milestone)

- **`VonNeumannEntropy.lean`** — `vonNeumannEntropy_unitarily_invariant` general `Fin n` **proved** (was sorry). New helper lemmas: `charmatrix_diagonal'`, `charpoly_diagonal'`, `IsHermitian.charpoly_eq_prod_eigenvalues`, `eigenvalue_multiset_eq_of_charpoly_eq`.
- **`DataProcessingInequality.lean`** — removed placeholder Klein / general-unital **axioms**; **proved** algebraic unital DPI for the qubit which-path channel (`vonNeumannEntropy_nondecreasing_unital_whichPath`, from diagonal spectrum + Tier 1b log-sum bound).
- **All docs** — updated from "1 sorry" to "0 sorry, 3 axioms" (`VERIFY.md`, `README.md`, …). *(Historical: visibility + dephasing were later proved; current inventory is **1** axiom — see **`FORMAL_FOUNDATIONS.md`**.)*

### Added (Lean — Gaps 5, 10, 12, 18)

- **`SchrodingerDynamics.lean`** — Gap 5: unitary evolution as Kraus channel (`unitaryChannel`), PSD/trace preservation, adjoint involutivity.
- **`LindbladDynamics.lean`** — Gap 12: Lindblad dissipator, qubit dephasing bridge (`whichPath_eq_rho_plus_dissipator`).
- **`GateCompat.lean`** — Gap 10: `thermoCalibratedScaffold` with `freeEnergy = -landauerCostDiagonal`, Admissible invariance, Landauer bound.
- **`SimLeanBridge.lean`** — Gap 18: formal type contracts (`SimDensityContract`, `SimPathProjectionContract`, `SimComplementarityWitness`, `SimLandauerWitness`).

### Added (engineering — Gaps 14, 16, 19)

- **`sim/telemetry_trace_consumer.py`** — Gap 14: runtime trace contract validator (DensityMatrix, PathProjection, Complementarity, Landauer).
- **`sim/requirements-optional.txt`** — Gap 16: added `scipy>=1.7.0`.
- **`Docs/PROVENANCE.md`** — Gap 19: formal authorship provenance.

### Changed (docs — proof inventory sync)

- **`Lean/VERIFY.md`**, **`PROOF-STATUS.md`**, **`README.md`**, **`Docs/OnePager-DoubleSlit.tex`**, **`Docs/GAP_CLOSURE_PLAN.md`**, **`Docs/TODO-TRACKING.md`**, **`Docs/PARALLEL_WORK.md`**, **`Docs/REMAINING_WORK_PLAN.md`**, **`Docs/SORRY_ROADMAP.md`**, **`scripts/generate_spectacular_gif.py`** — **0** `sorry`; **3** `axiom` (Klein + unital DPI + `physicalSecondLaw`); **`vonNeumannEntropy_unitarily_invariant`** **proved**; heuristic counts **457** `theorem` / **33** `lemma` where pasted.

### Changed (docs — Python test count)

- **`README.md`**, **`PROOF-STATUS.md`**, **`Docs/OnePager-DoubleSlit.tex`** — Python **`unittest`** count **54 → 62** (`unittest discover -s sim/tests`).

### Changed (build)

- **`Makefile`** — target **`telemetry-sample`**: `export_sample_telemetry_trace.py --validate`.
- **`.github/workflows/lean.yml`** — after **`unittest`**, runs **`export_sample_telemetry_trace.py --validate`** (Gap 14 regression).
- **`CONTRIBUTING.md`**, **`sim/README.md`** — document **`make telemetry-sample`**.

### Added (sim — telemetry golden producer)

- **`sim/export_sample_telemetry_trace.py`** — reference **emitter** for Gap 14: 3-step qubit demo (`|+⟩`, repeat, Lüders diagonal) with `SimLeanBridge` + nested **`emitted`** + **`aggregate`**; `--validate` runs **`telemetry_trace_consumer.py`**. **`sim/tests/test_export_sample_telemetry_trace.py`** — export→consume round-trip.

### Added (docs — remaining work plan)

- **`Docs/REMAINING_WORK_PLAN.md`** — ordered backlog with **Phase 5 explicitly deferred** to stream **D**; points at Gap 14 / A0 / a1 / post–Phase-5 stats refresh. **`TODO-TRACKING.md`**, **`PARALLEL_WORK.md`**, **`README.md`** link it.

### Changed (sim — EmittedStepRecord metadata)

- **`sim/telemetry_trace_consumer.py`** — optional **`thermodynamicAdmissible`** / **`confidence`** checks; nested **`emitted`** object + precedence for MI/cost/metadata; **`sim/tests/test_telemetry_trace_consumer.py`** extended.

### Changed (docs — multi-agent handoff)

- **`Docs/TODO-TRACKING.md`** — **Phase 5** ownership (other agent, stream **D**); **backlog checklist** for A0 full ports, a1 cross-language work, sim/RL **emitting** aggregates; **`EmittedStepRecord`** metadata validated in **`telemetry_trace_consumer.py`** when present.
- **`Docs/PARALLEL_WORK.md`** — stream **D** → **ACTIVE** for Phase 5 `sorry` closure.
- **`Docs/EPISTEMIC_RUNTIME_GROUNDING.md`** — **`thermodynamicAdmissible` / `confidence`** documented for Python consumer (flat or nested **`emitted`**).

### Changed (sim — Gap 14 telemetry)

- **`sim/telemetry_trace_consumer.py`** — optional per-step **epistemic** validation: `stepMI`/`trajMI` (nats, `≤ ln 2`), `stepCost`/`effortCost` (joules, `≤ k_B T ln 2`), and **MI–cost consistency** `cost ≈ k_B T · MI`. **Aggregate:** root or nested `aggregate` with `aggregateMI`/`aggregateCost` — **catalog** bounds (`≤ n ln 2`, `≤ n k_B T ln 2`) and, when every step has MI+cost, **fold sum** checks vs totals; partial per-step epistemic + aggregates → failed `EpistemicFold_skipped` gate. Docstring + **`sim/README.md`** + **`EPISTEMIC_RUNTIME_GROUNDING.md`** updated.
- **`sim/tests/test_telemetry_trace_consumer.py`** — regression tests for aliases, MI bound failure, legacy Sim-only traces, aggregate+fold, and partial-step fold gate.

### Added (docs — p3 epistemic / runtime)

- **`Docs/EPISTEMIC_RUNTIME_GROUNDING.md`** — checklist mapping each **`Epistemic*.lean`** (+ `PrototypeSolverCalibration`) to runtime / sim obligations; links **`SimLeanBridge`**, stream **H**, **Gap 14**. **`TODO-TRACKING.md`**, **`PARALLEL_WORK.md`**, **`README.md`** cross-link it.

### Changed (docs — backlog reconciliation)

- **`Docs/GAP_CLOSURE_PLAN.md`**, **`Docs/TODO-TRACKING.md`**, **`Docs/PARALLEL_WORK.md`** — aligned with **landed** Lean: **`GateCompat`** calibrated scaffold (**Gap 10** partial), **`SchrodingerDynamics`** (**Gap 5** done), **`LindbladDynamics`** + which-path / dephasing (**Gap 12** partial), **`SimLeanBridge`** contract types (**Gap 18** partial); stream **E** claim set to **PARTIAL**.
- **`Docs/A0_COQ_AGDA_BACKLOG.md`** — new coordination doc for **A0** Coq/Agda parity (port order, `make coq-check` / `make agda-check`).
- **`README.md`** — documentation table links **`TODO-TRACKING.md`** and **`A0_COQ_AGDA_BACKLOG.md`**.

### Changed (docs — README)

- **`README.md`** — **48** `lakefile` roots (was 42); module tables add **`GeneralDimension`**, **`TensorPartialTrace`**, **`VonNeumannEntropy`**, **`DataProcessingInequality`**, and a **Dynamics & Lean↔sim** section (`SchrodingerDynamics`, `LindbladDynamics`, `SimLeanBridge`).

### Changed (docs — Lean counts)

- **`PROOF-STATUS.md`**, **`README.md`**, **`Lean/VERIFY.md`**, **`Docs/OnePager-DoubleSlit.tex`**, **`scripts/generate_spectacular_gif.py`** — refreshed heuristic declaration counts (**457** `theorem`, **33** `lemma`, **54** files, sum **714** kinds); OnePager / GIF now show **0** `sorry`, **3** `axiom`, and **48** modules.
- **`Docs/OnePager-DoubleSlit.tex`** — bibliography entry `\bibitem{umst-formal}` no longer claims “59 theorems, 0 sorry”; aligned with double-slit track stats above.

### Added (Lean — unital DPI base case)

- **`DataProcessingInequality.lean`** — **`KrausChannel.identity_isUnital`** (`identity_map`), **`vonNeumannEntropy_identity_apply`**, **`vonNeumannEntropy_nondecreasing_unital_identity`** (Tier 2 without Klein for `KrausChannel.identity`).

### Changed (docs / status)

- **`PROOF-STATUS.md`** — sorry inventory: **0** `sorry`; **3** `axiom` (Klein, unital DPI, physicalSecondLaw); historical DensityState/MeasurementChannel sorries called out separately.
- **`Lean/VERIFY.md`**, **`Docs/TODO-TRACKING.md`**, **`Docs/GAP_CLOSURE_PLAN.md`**, **`Docs/PARALLEL_WORK.md`** — Phase 5: **0** `sorry`; general unitary **proved** via `charpoly`; Klein/unital DPI → **axiom**; **`Fin 1`/`Fin 2` unitary** + **identity-channel** entropy facts proved.

### Changed (docs — cross-links)

- **`Lean/MeasurementChannel.lean`** module doc — pointer to **`DataProcessingInequality`** for unital / identity-channel entropy lemmas.

### Changed (Lean — DensityState naming)

- **`DensityState.lean`** — underlying record is **`DensityMatCore`**; public **`DensityMatrix`** remains an `abbrev`; lemmas live in **`DensityMat`** (`DensityMat.ext`, `trace_eq_one`, …) to avoid Lean namespace/structure path collisions.
- **`DensityState.lean`** — section `hn` is **`variable {hn : 0 < n}`** (implicit). Using **`(hn : 0 < n)`** made `hn` the first *explicit* argument of every lemma, breaking calls like `diag_nonneg_complex_n ρ` (type mismatch).

### Added (Lean — von Neumann spectral bookkeeping)

- **`VonNeumannEntropy.lean`** — **`vonNeumannEntropy_congr_eigenvalues`**, **`vonNeumannEntropy_eq_of_eigenvalues_reindex`** (`Fintype.sum_equiv`); documents the remaining glue for **`vonNeumannEntropy_unitarily_invariant`** (build `e : Fin n ≃ Fin n` from similarity / spectrum). Import **`Mathlib.Algebra.BigOperators.Group.Finset`** for `Fintype.sum_equiv`.
- **`VonNeumannEntropy.lean`** — proved **`charmatrix_unitary_conj`** and **`charpoly_unitary_conj`** (`det_units_conj` on embedded `ℂ → ℂ[X]` coefficients); full unitary entropy invariance still needs linking `charpoly` / spectrum to **ordered** `IsHermitian.eigenvalues`.
- **`VonNeumannEntropy.lean`** — qubit layer: **`det_eq_of_charpoly_eq`**, **`vonNeumannEntropy_eq_of_det_carrier_eq_two`**, **`vonNeumannEntropy_unitarily_invariant_two`** (`Fin 2`). Imports **`Charpoly.Coeff`**, **`Algebra.BigOperators.Fin`**.
- **`DensityState.lean`** — **`pureDensity_carrier`**: use **`pureDensity (hn := hn) ψ hψ`** in the LHS so elaboration sees the section `hn` (avoid duplicate `{hn}` binder vs `variable {hn}`).
- **`VonNeumannEntropy.lean`** — **`densityMatrix_carrier_eq_one`**, **`vonNeumannEntropy_unitarily_invariant_one`** (`Fin 1` trivial sector).

### Added (Lean — Gap 11 / Tier 1b)

- **`DataProcessingInequality.lean`** — full proof of **`vonNeumannDiagonal_ge_vonNeumannEntropy`** (qubit): det bound + `binEntropy_strictAntiOn` on `[1/2,1]`.

### Added (Lean — Phase 3 / composite)

- **`TensorPartialTrace.lean`** — Kronecker / `tensorDensity` on `Fin (na*nb)`; **`partialTraceRight*`** + **`partialTraceLeft*`** (product + flattened indices); **`trace_partialTrace*Prod`** / **`trace_partialTrace*Fin`** (partial trace preserves **`Matrix.trace`**); **`posSemidef_kronecker`**. Root in `lakefile.lean` (after `DensityState`).

### Added (Lean — Phase 2 / general dimension)

- **`GeneralDimension.lean`** — proves **`vonNeumannDiagonal_n_le_log_n`** (Jensen on `negMulLog` + algebraic peel); new root in `lakefile.lean`.
- **`LandauerBound.lean`** — **`pathEntropyBits_n`**, **`landauerCostDiagonal_n`**, and **`landauerCostDiagonal_n_le_logb_landauerBitEnergy`** (imports `GeneralDimension`; max `logb 2 n` bit-equivalents).
- **Qubit API alignment:** `vonNeumannDiagonal_n_eq_vonNeumannDiagonal` (`InfoEntropy`); `pathEntropyBits_n_qubit_eq`, `landauerCostDiagonal_n_qubit_eq` (`LandauerBound`).

### Changed (Lean — Phase 1 / PMIC)

- `PMICEntropyInterior.lean` — **closed** the interior bound `4 x (1-x) log 2 ≤ binEntropy x` on `(0,1/2)` (MVT on `entropyBoundK`, strict antitone of `binEntropy / (t(1-t))`). **Zero `sorry`** in PMIC chain.
- `PMICVisibility.lean` — imports `PMICEntropyInterior`; `visibility_sq_le_coherence_capacity` fully proved.
- `QRBridge.lean` — ℚ → ℝ `Admissible` lift (`admissible_thermodynamicStateToReal`); root in `lakefile.lean`.
- `Docs/PHASE1_GAP_CLOSURE.md` — Phase 1 gaps marked **done** for Gaps 1, 13, 17.

### Added (formal — integrated from upstream framework)

- **Lean:** `LandauerLaw.lean`, `LandauerExtension.lean`, `LandauerEinsteinBridge.lean`, `Gate.lean`, `Naturality.lean`, `Activation.lean`, `FiberedActivation.lean`, `MonoidalState.lean` — registered as extra roots in `Lean/lakefile.lean` (alongside `UMST.DoubleSlit` modules).
- **Haskell:** `LandauerExtension.hs`, `MonoidalState.hs`; QuickCheck blocks `prop_le_*` / `prop_ms_*`; test suite **`landauer-einstein-sanity`** (`Haskell/test/LandauerEinsteinSanity.hs`).
- **Coq:** `Coq/LandauerEinsteinBridge.v`, `Coq/_CoqProject`, `Coq/README.md`; **`make coq-check`** in root `Makefile`.
- **Agda:** `Agda/LandauerEinsteinTrace.agda`; **`make agda-check`**.
- **Gitignore:** Coq `*.vo` / `*.glob` / `.*.aux`; Agda `_build/`.

### Added (docs / coordination)

- `Docs/GAP_CLOSURE_PLAN.md` — **6-phase / 19-gap** tracker vs original Lean roadmap: Phase 1 **done** (incl. `PMICEntropyInterior`), Phases 2–6 **TODO/PARTIAL**, parallel “swarm” streams, checklist.
- `Docs/PARALLEL_WORK.md` — **multi-agent coordination:** stream IDs (A–H), choke points (`lakefile`, README), **active claims** table, merge hints.
- `Docs/TODO-TRACKING.md` — reconciles milestones vs in-editor todos; **`a1-measurement-cost`** row = **PARTIAL** (Lean + Haskell in tree). **A0 Coq/Agda** described as **tracked**, not “out of scope / cancelled.”

### Fixed (Python / tests)

- `sim/tests/test_qutip_parity.py` — pass **Kraus operator lists** (`identity_kraus()`, `which_path_kraus()`) into `kraus_apply`, not the factory functions.

### Added (Python / sim)

- `sim/schrodinger_2d_sparse_fd_expm_smoke.py` — CSR FD **H** + soft slit **V**; **`expm_multiply`** vs dense **`expm`**; `sim/tests/test_schrodinger_2d_sparse_fd_expm_smoke.py` (skips without SciPy sparse).
- `sim/schrodinger_2d_complex_absorb_mask.py` — separable **complex** edge mask (real taper × ``e^{iφ}``); **κ=0** ≡ real sponge; `sim/tests/test_schrodinger_2d_complex_absorb_mask.py`.
- `sim/benchmark_schrodinger_2d_split_step_vs_fd.py` — timings + max rel **ρ** gap (split-step vs FD+`expm`); `sim/tests/test_benchmark_schrodinger_2d_split_step_vs_fd.py` (skips without SciPy).
- `sim/qutip_schrodinger_2d_slit_parity.py` — QuTiP vs scipy on **FD H + diag soft slit V**; optional split-step vs FD ρ diagnostic; `sim/tests/test_qutip_2d_slit_parity.py`.
- `sim/schrodinger_2d_absorbing_edges.py` — 2D soft slit + separable edge sponge; `sim/tests/test_schrodinger_2d_absorbing_edges.py`; CSV matches `plot_schrodinger_2d_soft_double_slit_svg.py`.
- `sim/qutip_schrodinger_2d_free_parity.py` — QuTiP `sesolve` vs `scipy.linalg.expm` on the same 2D periodic FD free Hamiltonian; optional FFT-vs-FD diagnostic; `sim/tests/test_qutip_2d_free_parity.py`.
- `sim/schrodinger_2d_soft_double_slit.py` — 2D Strang split-step, soft screen + two y-openings; validate vs 2D FFT (`--v0 0`); `sim/tests/test_schrodinger_2d_soft_double_slit.py`.
- `sim/plot_schrodinger_2d_soft_double_slit_svg.py` — stdlib heatmap SVG; `sim/tests/test_plot_schrodinger_2d_soft_double_slit_svg.py`.
- `sim/schrodinger_1d_free_fft.py` — free 1D Schrödinger on a periodic grid (NumPy FFT), validated vs `spatial_free_gaussian_1d`; `sim/tests/test_schrodinger_1d_free_fft.py` (skipped without NumPy). `sim/requirements-optional.txt` — explicit **`numpy`** line.
- `sim/schrodinger_1d_split_step.py` — Strang split-step with optional Gaussian barrier; `sim/tests/test_schrodinger_1d_split_step.py` (V=0 vs FFT, barrier norm smoke).
- `sim/schrodinger_1d_soft_double_slit.py` — soft screen + two openings; `sim/tests/test_schrodinger_1d_soft_double_slit.py`.
- `sim/plot_schrodinger_split_step_svg.py` — stdlib SVG for `schrodinger_split_step_rho.csv`; `sim/tests/test_plot_schrodinger_split_step_svg.py`.
- `sim/plot_schrodinger_absorbing_edges_svg.py` — stdlib SVG for `schrodinger_absorbing_edges_rho.csv`; `sim/tests/test_plot_schrodinger_absorbing_edges_svg.py`.
- `sim/schrodinger_1d_absorbing_edges.py` — edge sponge after each Strang step; `sim/tests/test_schrodinger_1d_absorbing_edges.py`.
- `sim/plot_schrodinger_soft_double_slit_svg.py` — stdlib SVG for rho + scaled V; `sim/tests/test_plot_schrodinger_soft_double_slit_svg.py`.
- `sim/spatial_free_gaussian_1d.py` — closed-form |ψ|² for a spreading 1D Gaussian (stdlib); `sim/tests/test_spatial_free_gaussian.py`. Documented in `sim/README.md`; **not** added to default `make sim` / lean.yml four-script block (unittest covers it).
- `sim/classical_double_slit_far_field.py` — Fraunhofer double-slit intensity (stdlib); `sim/tests/test_classical_double_slit_far_field.py`. Same integration pattern as other optional sim scripts.
- `sim/plot_classical_double_slit_svg.py` — stdlib SVG for that curve; `sim/tests/test_plot_classical_double_slit_svg.py`.
- `sim/plot_spatial_free_gaussian_svg.py` — stdlib SVG for |ψ|² vs x; `sim/tests/test_plot_spatial_free_gaussian_svg.py`.

### Changed (CI / coordination)

- `.github/workflows/lean.yml`, `haskell.yml` — **`paths`** filters so jobs skip doc-only / unrelated edits (Lean+sim+`Makefile` vs `Haskell/**`).
- `.github/workflows/lean.yml`, `haskell.yml` — **`concurrency`** groups (cancel superseded runs on same ref).
- `Makefile` — **`ci-full`** target (`ci-local` + `haskell-test`).

### Added (tooling / docs)

- `scripts/README.md` — how to run `lean_decl_stats.py` / `make lean-stats-md`.

### Added (Haskell)

- `Haskell/cabal.project.freeze` — dependency pins from `cabal freeze` (Hackage `index-state` + constraints).

### Changed (docs / CI)

- `scripts/lean_decl_stats.py --markdown` prints **repo-relative** `Lean` path when run from repo root.
- `PROOF-STATUS.md` — Lean stats block uses portable `Lean` root (no machine-specific paths).
- `Haskell/cabal.project` — `packages: .` for explicit project root + future freeze; `haskell.yml` cache key includes `cabal.project` / optional `.freeze`.

### Added (repo hygiene)

- Root **`.gitignore`** — `Haskell/dist-newstyle/`, Python `__pycache__`, `.DS_Store`.

### Added (Lean)

- **UMSTCore** — ℝ Landauer scale + `ThermodynamicState` + `Admissible` conjuncts.
- **DensityState** — `DensityMatrix`, `pureDensity`, `DensityMatrix.ext`.
- **MeasurementChannel** — Kraus channels, `whichPathChannel` (Lüders dephasing), `compose` / `apply_compose`.
- **QuantumClassicalBridge** — `pathWeight`, `whichPathDistinguishability`, `fringeVisibility`, `complementarity_fringe_path`, `observationStateCanonical`.
- **InfoEntropy** — `shannonBinary` (= Mathlib `Real.binEntropy`), `vonNeumannDiagonal`, `vonNeumannDiagonal_le_log_two`.
- **LandauerBound** — `pathEntropyBits`, `landauerCostDiagonal`, `pathEntropyBits_le_one`, `landauerCostDiagonal_le_landauerBitEnergy`.
- **EpistemicSensing** — `QuantumProbe`, `nullProbe`/`whichPathProbe`, max witnesses (`Set` + finite-family argmax, strict-positive selection), collapse/preserve theorems, Landauer-from-strength bounds.
- **GateCompat** — `thermoFromQubitPath`, `admissible_thermoFromQubitPath_whichPath`.
- **Complementarity** — discoverability shims over the bridge.
- **DoubleSlit** — import closure, `measurementUpdateWhichPath`, Landauer equalities along which-path, plus narrative wrappers: `interference_preserved_identity`, `collapse_fringe_on_whichPath`, `measurementUpdateWhichPath_gateEnforcement`.
- **EpistemicMI** — probe-indexed MI (`PathProbe`) in nats/bits, with Landauer-cost links.
- **EpistemicDynamics** — probe-policy rollouts with null/which-path invariants.
- **EpistemicTrajectoryMI** — cumulative finite-horizon MI/cost and bounds.
- **EpistemicPolicy** — finite-horizon policy utility, argmax, constrained policy optimality.
- **EpistemicRuntimeContract** — trace-coherence and aggregate-contract bridge between rollout traces and policy theorems.
- **EpistemicNumericsContract** — numeric rollout record (`NumericTraceRecord`), consistency predicates, and utility equivalence to `policyUtility`.
- **EpistemicPerStepNumerics** — per-step record (`PerStepNumericRecord`), finite-fold consistency to cumulative MI/cost, and projection bridge to `NumericTraceRecord`.
- **EpistemicRuntimeSchemaContract** — emitted runtime schema (`EmittedStepRecord`, `EmittedTraceSchema`) plus transfer theorems from rollout-consistent emitted traces to per-step/aggregate utility contracts.
- **EpistemicTelemetryBridge** — runtime telemetry naming bridge (`trajMI`, `effortCost`) with explicit consistency assumptions and theorem transfer to emitted/per-step/aggregate contracts.
- **EpistemicTelemetryApproximation** — epsilon-approximation interface for runtime numerics (ODE/PPO surrogates) with zero-error transfer to exact telemetry/schema/numeric contracts.
- **EpistemicTelemetryQuantitativeUtility** — explicit nonzero-error utility deviation bounds from aggregate approximation assumptions (`εMI`, `εCost`, `λ`, `T`).
- **EpistemicTraceDerivedEpsilonCertificate** — residual-based epsilon extraction from concrete telemetry traces with direct transfer to quantitative utility bounds.
- **EpistemicTelemetrySolverCalibration** — explicit solver calibration parameters (`stepSize`, `order`, error coefficients) mapped to epsilon budgets with transfer assumptions for utility bounds.
- **EpistemicTraceDrivenCalibrationWitness** — trace witness wrapper (`TraceCalibrationWitnessAt`) that packages telemetry and calibration assumptions and transfers directly to utility-bound theorems.
- **PrototypeSolverCalibration** — concrete prototype calibration constants with explicit epsilon-budget formulas and specialized utility-bound wrappers.
- **ProbeOptimization** — `ProbeUtility`, finite argmax selection, admissibility-constrained optimality existence.
- **ExamplesQubit** — `rhoPlus`, `rhoZero`, `rhoOne`; imports **`ProbeOptimization`**; epistemic/optimization + measurement-update corollaries.
- **Docs** — `ASSUMPTIONS-DOUBLE-SLIT.md` (scope / non-claims).

### Added (tooling / docs)

- `Lean/VERIFY.md`, `PROOF-STATUS.md`.
- `Docs/EpistemicSensingQuantum.md` — index of epistemic + quantum Lean modules and sim parity (working note).
- `Docs/TODO-TRACKING.md` — milestone vs todo reconciliation.
- `CONTRIBUTING.md` — PR checklist (`make ci-local`, optional pip, Lean note).
- `sim/tests/test_toy_matplotlib_smoke.py` — optional smoke test for `toy_double_slit_mi_gate.py --plot` when matplotlib is installed.
- `sim/tests/test_toy_gif_smoke.py` — optional smoke test for `--generate-gif` when matplotlib + imageio are installed.
- `scripts/lean_decl_stats.py` + **`make lean-stats`** — heuristic Lean declaration counts (`.lake` excluded).
- `Haskell/README.md` — build/test instructions for the Cabal mirror.
- `.github/workflows/haskell.yml` — CI `cabal test` on Ubuntu (GHC 9.14); **Cabal store + `dist-newstyle` cache** (`actions/cache@v4`).
- **`make haskell-test`** — local Cabal test from repo `Makefile`.
- `Docs/OnePager-DoubleSlit.tex` — compact LaTeX one-pager (`pdflatex` locally).
- `Makefile` (`lean`, `lean-clean`, `sim`, `sim-test`, `ci-local`).
- `.github/workflows/lean.yml`.
- `sim/tests/test_toy_double_slit.py` (toy simulator regression checks).
- `sim/qubit_kraus_sweep.py` — stdlib 2×2 Kraus (identity + Lüders which-path) with Lean-aligned `V`, `I`, `V²+I²` checks; default `sim/out/qubit_kraus_sweep.csv`.
- `sim/tests/test_qubit_kraus_sweep.py`.
- `sim/plot_complementarity_svg.py` — stdlib SVG Englert quarter-disk from `qubit_kraus_sweep.csv` (`sim/out/complementarity_qubit_sweep.svg`); `--validate` checks `V²+I²≤1`.
- `sim/plot_toy_complementarity_svg.py` — stdlib SVG (I,V) curve from `results_double_slit_toy.csv` (`sim/out/complementarity_toy_sweep.svg`).
- `sim/tests/test_complementarity_svg.py`.
- `sim/tests/test_toy_complementarity_svg.py`.
- `sim/qutip_qubit_kraus.py` + `sim/requirements-optional.txt` + `sim/tests/test_qutip_parity.py` (QuTiP parity; tests skip if `qutip` missing).
- `sim/README.md` (simulator usage, output paths, Python roadmap).
- `.github/workflows/lean.yml` — post-Lean Python `sim` + `unittest` on Ubuntu.

### Not in scope (yet)

- Full spatial double-slit / Schrödinger dynamics from first principles; Haskell QC in default CI; theorem-count automation in CI.
