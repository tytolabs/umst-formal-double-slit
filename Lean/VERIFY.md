<!--
SPDX-License-Identifier: MIT
Copyright (c) 2026 Santhosh Shyamsundar, Santosh Prabhu Shenbagamoorthy — Studio TYTO
-->

# Double-slit Lean track — verification

From `umst-formal-double-slit/Lean/`:

```bash
lake build
```

Expected: **success** (all roots in `lakefile.lean`).

**Scope / assumptions:** `../Docs/ASSUMPTIONS-DOUBLE-SLIT.md`.  
**Multi-agent:** see **`../CONTRIBUTING.md`**.  
**Sorry:** **none** in any Lean file — **0 `sorry`** across the entire project. **Phase 5 (information theory):** **`VonNeumannEntropy.lean`** — general `Fin n` **`vonNeumannEntropy_unitarily_invariant`** is **proved** (via `charpoly` + eigenvalue multiset). **`DataProcessingInequality.lean`** — general unital DPI / **Klein** stated as **axiom** (requires Mathlib matrix logarithm infrastructure); identity channel + qubit DPI **proved**. **Tier 1b** (qubit diagonal ≥ spectral) is **proved** (`vonNeumannDiagonal_ge_vonNeumannEntropy`). **6 axioms** (line-start heuristic, see **`../PROOF-STATUS.md`**): `klein_inequality`, `vonNeumannEntropy_nondecreasing_unital`, `physicalSecondLaw`, `fringeVisibility_n_le_one`, `dephasingSolution_tendsto_diagonal`, `vonNeumannEntropy_tensorDensity`.

**CI:** `.github/workflows/lean.yml` (Lean + Python sim; caches `Lean/.lake`); `.github/workflows/haskell.yml` (Cabal tests in `Haskell/`); `.github/workflows/formal.yml` (`make coq-check` in Docker **`rocq/rocq-prover:9.0`**, `make agda-check` on Ubuntu with `agda-stdlib`).  
**Stats (heuristic):** from repo root, `make lean-stats` / `make lean-stats-md` → `scripts/lean_decl_stats.py`. *Last pasted to `PROOF-STATUS.md`:* **515** `theorem`, **33** `lemma`, **6** `axiom`, **58** `.lean` files (line-start scan, not a full parser).

## Module map (high level)

| Module | Role |
|--------|------|
| `UMSTCore` | ℝ Landauer scale + `Admissible` shape |
| `DensityState` | `DensityMatrix` (= `DensityMatCore`), `pureDensity`, `DensityMat.ext` |
| `TensorPartialTrace` | `tensorDensity`, `partialTraceRight*` / `partialTraceLeft*` (product + `Fin (na*nb)`), `trace_partialTrace*Prod` / `trace_partialTrace*Fin`, `posSemidef_kronecker` |
| `MeasurementChannel` | `KrausChannel`, `map` / `apply`, `compose`, `whichPathChannel`, Lüders diagonal |
| `DoubleSlitCore` | `ObservationState`, `ObservationState.ext`, complementarity interface |
| `QuantumClassicalBridge` | `pathWeight`, `whichPathDistinguishability`, `fringeVisibility`, `complementarity_fringe_path`, `observationStateCanonical`, `observationStateOf` |
| `InfoEntropy` | `shannonBinary`, `vonNeumannDiagonal`, `vonNeumannDiagonal_n`, `vonNeumannDiagonal_whichPath_apply` |
| `GeneralDimension` | `vonNeumannDiagonal_n_le_log_n` (diagonal entropy ≤ `log n`, nats) |
| `VonNeumannEntropy` | `vonNeumannEntropy` (spectral `negMulLog` sum); **`vonNeumannEntropy_congr_eigenvalues`**, **`vonNeumannEntropy_eq_of_eigenvalues_reindex`**; **`charmatrix_unitary_conj`**, **`charpoly_unitary_conj`**; **`vonNeumannEntropy_unitarily_invariant_one`** / **`_two`**; general **`vonNeumannEntropy_unitarily_invariant`** (`Fin n`) **proved** |
| `DataProcessingInequality` | `vonNeumannDiagonal_ge_vonNeumannEntropy` (qubit Schur); `KrausChannel.IsUnital`; `whichPath_increases_entropy`; identity-channel DPI proved; general unital DPI + Klein as **axiom** |
| `LandauerBound` | `pathEntropyBits`, `landauerCostDiagonal`, `landauerCostDiagonal_whichPathInvariant`; general `n`: `pathEntropyBits_n`, `landauerCostDiagonal_n_le_logb_landauerBitEnergy` |
| `EpistemicSensing` | `QuantumProbe`, `nullProbe`/`whichPathProbe`, `ProbeStrength`, `IsMaxMIProbeAt`, finite-family argmax, collapse/preserve theorems, Landauer-from-strength bounds |
| `EpistemicMI` | `PathProbe`, `EpistemicMI`, `epistemicMIBits`, `epistemicLandauerCost` links to `landauerCostDiagonal` |
| `EpistemicDynamics` | `stepProbe`, `rollout`, `nullPolicy`/`whichPathPolicy` invariants |
| `EpistemicTrajectoryMI` | `cumulativeEpistemicMI`, `cumulativeEpistemicLandauerCost` and bounds |
| `EpistemicPolicy` | `policyUtility`, finite policy argmax, constrained policy optimality existence |
| `EpistemicRuntimeContract` | runtime trace coherence/contract and bridge lemmas to policy dominance |
| `EpistemicNumericsContract` | numeric rollout record (`NumericTraceRecord`), consistency, and utility-equivalence bridge |
| `EpistemicPerStepNumerics` | per-step record (`PerStepNumericRecord`), fold-to-aggregate consistency, projection to numeric aggregate record |
| `EpistemicRuntimeSchemaContract` | emitted runtime schema + rollout-consistency transfer to per-step/aggregate utility contracts |
| `EpistemicTelemetryBridge` | runtime telemetry naming bridge (`trajMI` / `effortCost`) with consistency transfer into existing numeric contracts |
| `EpistemicTelemetryApproximation` | epsilon-approximation assumptions for runtime numerics + zero-error transfer to exact contracts |
| `EpistemicTelemetryQuantitativeUtility` | nonzero-error utility deviation bounds from aggregate approximation assumptions |
| `EpistemicTraceDerivedEpsilonCertificate` | residual-based epsilon certificates derived from telemetry traces with direct utility-bound transfer |
| `EpistemicTelemetrySolverCalibration` | explicit solver-parameter-to-epsilon calibration layer and utility-bound transfer assumptions |
| `EpistemicTraceDrivenCalibrationWitness` | witness object pairing telemetry traces with calibration assumptions and direct utility-bound transfer |
| `PrototypeSolverCalibration` | concrete calibration constants and explicit epsilon/utility-bound corollaries |
| `SchrodingerDynamics` | `unitaryChannel` (unitary as single-Kraus), PSD/trace preservation, `unitaryChannel_apply` / `DensityMatrix` closure |
| `LindbladDynamics` | `dissipator`, `lindbladGenerator`, qubit dephasing, `whichPath_eq_rho_plus_dissipator` |
| `SimLeanBridge` | `SimDensityContract`, `SimPathProjectionContract`, `SimComplementarityWitness`, `SimLandauerWitness` (trust-boundary contracts) |
| `GateCompat` | `thermoFromQubitPath`, `admissible_thermoFromQubitPath_whichPath` |
| `QRBridge` | `thermodynamicStateToReal`, `admissible_thermodynamicStateToReal` (ℚ → ℝ `Admissible`) |
| `Complementarity` | `complementarityEnglert`, `observationCanonical_complementary` (shim over bridge) |
| `PMICEntropyInterior` | `four_mul_x_one_sub_x_mul_log_two_interior`, `entropyBoundK_pos`, `quad_log_lt_of_lt_half` (PMIC entropy–quadratic, no `sorry`) |
| `PMICVisibility` | `visibility_sq_le_coherence_capacity`, `four_mul_x_one_sub_x_mul_log_two_le_binEntropy`, `quadratic_le_entropy_bits` |
| `DoubleSlit` | Full-chain imports; gate enforcement and Landauer cap packaging |
| `WhichPathMeasurementUpdate` | **`measurementUpdateWhichPath`** (`MeasurementUpdate` for Lüders which-path); fringe collapse + Landauer invariance (split from `DoubleSlit` to break import cycle with `EpistemicSensing`) |
| `ProbeOptimization` | `ProbeUtility`, finite argmax (`exists_optimalProbeIndexAt`), admissibility-constrained optimization |
| `ExamplesQubit` | **`rhoPlus`**, **`rhoZero`**, **`rhoOne`**; epistemic/optimization + Landauer corollaries |
| `MeasurementCost` | probe costs vs Landauer bit-energy cap |
| `EpistemicGalois` | info–energy Galois connection (Lean) |
| `GeneralResidualCoherence` | `residualCoherenceCapacity_purity` (purity-based `RCC_n ∈ [0,1]`); `RCC_n = 0 ↔ diagonal`, `RCC_n = 1 ↔ pure`; Cauchy-Schwarz for PSD matrices proved from first principles; qubit compatibility `RCC_2 = \|ρ₀₁\|²/(p₀p₁)` |
| `QuantumMutualInfo` | `quantumMutualInfo` (`I(A:B) = S(A)+S(B)-S(AB)`); `quantumConditionalEntropy`; upper bound `I ≤ log nA + log nB`; product-state zero; one axiom: `vonNeumannEntropy_tensorDensity` |
| `ErasureChannel` | Reset-to-`\|0⟩` Kraus operators; trace preservation; output always `\|0⟩⟨0\|`; zero output entropy; `idealResetErasure` at Landauer equality |
| `LandauerLaw` | *(integrated upstream reference)* `T_LandauerLaw`: `ErasureProcess`, `physicalSecondLaw`, `landauerBound`, Shannon on `Fin n` |
| `LandauerExtension` | *(integrated)* temp scaling, n-bit bound, additivity, 300 K positivity |
| `LandauerEinsteinBridge` | *(integrated)* SI `k_B`, `c`, `massEquivalent`, numeric brackets at 300 K |
| `Gate` | *(integrated)* ℚ `ThermodynamicState`, `Admissible`, gate theorems (full UMST L₀ core) |
| `Naturality` | *(integrated)* `MaterialClass`, `stateFor`, material-agnostic gate lemmas |
| `Activation` | *(integrated)* `Engine`, `activation`, `ActivatedUMST`, totality + negative witnesses |
| `FiberedActivation` | *(integrated)* `engineFiber`, universality, covering, characteristic engines |
| `MonoidalState` | *(integrated)* `combine` on ℚ `ThermodynamicState`, unit/midpoint/convexity lemmas |

**Note:** `UMSTCore` remains the **ℝ** scaffold for `GateCompat` / quantum composition; **`Gate`** is the independent ℚ formalization copied from the upstream framework. They are intentionally **not** merged into one file.

## Key proved facts (names to search)

- **Lüders / dephasing:** `KrausChannel.whichPath_map_eq_diagonal`, `whichPath_map_apply_entry`
- **Born weights after measurement:** `pathWeight_whichPath_apply`, `whichPathDistinguishability_whichPath_apply`
- **Channel algebra:** `KrausChannel.compose_map`, `KrausChannel.apply_compose`
- **PSD / coherence bound:** `normSq_coherence_le_product`
- **Englert complementarity:** `complementarity_fringe_path`, `Complementarity.complementarityEnglert`
- **PMIC / thermodynamic visibility:** `visibility_sq_le_coherence_capacity`, `four_mul_x_one_sub_x_mul_log_two_le_binEntropy`, `PMICEntropyInterior.four_mul_x_one_sub_x_mul_log_two_interior`
- **ℚ → ℝ gate:** `admissible_thermodynamicStateToReal`
- **Canonical observation state:** `observationStateCanonical`, `observationStateCanonical_complementary`
- **Fringe kill under which-path:** `fringeVisibility_whichPath_apply`
- **Classical packaging (external `V`):** `observationStateOf_complementary`, `observationStateOf_fringe_complementary`
- **Entropy (binary):** `vonNeumannDiagonal_nonneg`, `vonNeumannDiagonal_le_log_two`, `vonNeumannDiagonal_whichPath_apply`, `shannonBinary_symm`, `shannonBinary_eq_binEntropy`, `shannonBinary_le_log_two`
- **Entropy (general diagonal):** `vonNeumannDiagonal_n_nonneg`, `vonNeumannDiagonal_n_le_log_n`, `vonNeumannDiagonal_n_eq_vonNeumannDiagonal`
- **Landauer scale (diagonal entropy):** `landauerCostDiagonal_nonneg`, `pathEntropyBits_le_one`, `landauerCostDiagonal_le_landauerBitEnergy`, `landauerCostDiagonal_whichPathInvariant`
- **Landauer scale (general diagonal / `Fin n`):** `pathEntropyBits_n_nonneg`, `pathEntropyBits_n_le_logb_two`, `landauerCostDiagonal_n_nonneg`, `landauerCostDiagonal_n_le_logb_landauerBitEnergy`, `pathEntropyBits_n_qubit_eq`, `landauerCostDiagonal_n_qubit_eq`
- **T_LandauerLaw (integrated):** `landauerBound`, `landauerBound_nBit`, `binaryErasureEntropyDrop`, `physicalSecondLaw_uniform_binary`
- **Landauer–Einstein bridge (integrated):** `massEquivalent_pos`, tight numeric mass bracket theorems at 300 K (see module)
- **Monoidal state (integrated):** `combine_one`, `combine_zero`, `combine_density_between`, `combine_freeEnergy_le`
- **Fibered activation (integrated):** `engineFiber_nonempty`, `strength_universal`, `activation_at_least_two`
- **Epistemic interface:** `whichPathProbe`, `nullProbe`, `whichPathProbe_strength_invariant`, `IsMaxMIProbeAt`, `whichPathProbe_isMax_on_singleton`, `whichPathProbe_isMax_on_null_pair`, `exists_maxProbeIndexAt`, `argmaxProbeIndexAt_spec`, `argmax_nullWhichFamily_eq_which_of_pos`, `interference_preserved_nullProbe`, `collapse_on_whichPathProbe`, `LandauerCostFromProbeStrength_le_landauerBitEnergy`
- **Probe optimization:** `ProbeUtility`, `exists_optimalProbeIndexAt`, `argmaxUtilityProbeIndexAt_spec`, `ProbeSelectionAdmissible_nullProbe`, `ProbeSelectionAdmissible_whichPathProbe`, `exists_constrainedOptimalAt`
- **Epistemic MI:** `epistemicMI_whichPath`, `epistemicMIBits_whichPath`, `epistemicLandauerCost_whichPath`, `epistemicLandauerCost_null`
- **Epistemic dynamics:** `rollout_nullPolicy`, `rollout_whichPathPolicy_visibility_zero_of_pos`, `rollout_whichPathPolicy_distinguishability_invariant`
- **Trajectory aggregation:** `cumulativeEpistemicMI_nonneg`, `cumulativeEpistemicMI_le`, `cumulativeEpistemicLandauerCost_nonneg`, `cumulativeEpistemicLandauerCost_le`, `cumulativeEpistemicMI_nullPolicy`
- **Policy optimization:** `exists_optimalPolicyIndexAt`, `argmaxPolicyIndexAt_spec`, `exists_constrainedOptimalPolicyAt`, `exists_constrainedOptimal_basicPolicyFamily`
- **Epistemic runtime contract:** `RuntimeTraceCoherent`, `RuntimeTraceContractMI`, `RuntimeTraceContractLandauer`, `policyAdmissible_iff_traceStepsAdmissible`, `constrainedOptimal_traceUtilityDominates`
- **Epistemic numerics contract:** `NumericTraceRecord.ofRollout`, `NumericTraceConsistent`, `NumericTraceFullyConsistent`, `traceRecordPolicyUtility_eq_policyUtility`, `traceRecordPolicyUtility_le_aggregateMI`
- **Epistemic per-step numerics:** `PerStepNumericRecord.ofRollout`, `PerStepNumericConsistent`, `perStepConsistent_implies_aggregateConsistent`, `ofRollout_toNumericTraceRecord`, `perStepRecordPolicyUtility_eq_policyUtility`
- **Epistemic runtime schema bridge:** `EmittedTraceSchema`, `EmittedTraceRolloutConsistent`, `emittedRolloutConsistent_toPerStepConsistent`, `emittedRolloutConsistent_toNumericTraceConsistent`, `ofRollout_policyUtility_eq`
- **Epistemic telemetry bridge:** `RuntimeTelemetrySchemaConsistent`, `telemetrySchemaConsistent_toNumericTraceConsistent`, `telemetrySchemaConsistent_policyUtility_eq`, `RuntimeTelemetrySchema.ofRollout`
- **Epistemic telemetry approximation:** `RuntimeTelemetrySchemaApproxConsistent`, `telemetryApprox_zero_implies_exact`, `telemetryApprox_zero_policyUtility_eq`, `telemetryApprox_ofRollout_zero`
- **Epistemic telemetry quantitative utility:** `utilityApproxBound`, `numericApprox_utility_diff_le`, `utilityApproxBound_nonneg`, `utilityApproxBound_zero`
- **Epistemic trace-derived epsilon certificate:** `traceResidualMI`, `traceResidualCost`, `traceResidual_numericApproxConsistent`, `traceEpsilonCertificate_utility_diff_le`
- **Epistemic telemetry solver calibration:** `SolverCalibration`, `epsMIStep`, `epsCostStep`, `epsMIAgg`, `epsCostAgg`, `solverCalibration_utility_diff_le`
- **Epistemic trace-driven calibration witness:** `TraceCalibrationWitnessAt`, `traceCalibrationWitnessAt_utility_diff_le`, `traceCalibrationWitnessAt_bound_nonneg`
- **Prototype solver calibration:** `prototypeCalibration`, `prototypeCalibration_epsMIStep`, `prototypeCalibration_epsMIAgg`, `prototypeCalibration_utility_diff_le`
- **Python sim regression:** `make sim`, `make sim-test` — toy CSV (`sim/toy_double_slit_mi_gate.py`); toy complementarity SVG (`sim/plot_toy_complementarity_svg.py`); qubit Kraus + qubit SVG (`sim/qubit_kraus_sweep.py`, `sim/plot_complementarity_svg.py`); tests under `sim/tests/`. **CI** also `pip install -r sim/requirements-optional.txt` (QuTiP / matplotlib / imageio); locally those tests skip if packages missing.
- **Tensor / partial trace:** `partialTraceRightProd_kronecker`, `partialTraceRightFin_tensorDensity_carrier`, `partialTraceLeftProd_kronecker`, `partialTraceLeftFin_tensorDensity_carrier`, `trace_partialTraceRightProd`, `trace_partialTraceLeftProd`, `trace_partialTraceRightFin`, `trace_partialTraceLeftFin`, `tensorDensity`, `posSemidef_kronecker`, `conjTranspose_kronecker`
- **DPI / entropy (qubit):** `vonNeumannDiagonal_ge_vonNeumannEntropy`, `whichPath_increases_entropy`, `entropy_increase_from_measurement_nonneg`
- **Unital DPI (base case):** `KrausChannel.identity_isUnital`, `vonNeumannEntropy_identity_apply`, `vonNeumannEntropy_nondecreasing_unital_identity` (`DataProcessingInequality.lean`)
- **Spectral / unitary (matrix):** `charmatrix_unitary_conj`, `charpoly_unitary_conj`, `densityMatrix_carrier_eq_one`, `vonNeumannEntropy_unitarily_invariant_one`, `vonNeumannEntropy_eq_of_det_carrier_eq_two`, `vonNeumannEntropy_unitarily_invariant_two` (`VonNeumannEntropy.lean`)
- **Gate scaffold:** `thermoFromQubitPath_whichPath`, `admissible_thermoFromQubitPath_whichPath`
- **Coarse measurement update + narrative wrappers:** `measurementUpdateWhichPath`, `measurementUpdateWhichPath_new_V`, `measurementUpdateWhichPath_I_eq`, `measurementUpdateWhichPath_landauer_eq`, `measurementUpdateWhichPath_landauer_le_landauerBitEnergy`, `interference_preserved_identity`, `collapse_fringe_on_whichPath`, `measurementUpdateWhichPath_gateEnforcement`

## Not in this track yet (needs design / approval)

- Full unital DPI proof (Klein axiom → theorem when Mathlib `matrix log` ready)
- Nontrivial hydration/strength from QM; calibrated `thermoFromQubitPath`
- Stronger equivalence-style DoubleSlit narrative (`⟺`) and detector-model refinements
- Full QuTiP-based spatial simulator (optional QuTiP **qubit** parity is in `sim/qutip_qubit_kraus.py`)

## Recently completed (formerly "not in this track")

- **Physical equality Landauer** for concrete erasure channel: `ErasureChannel.lean` — reset-to-`|0⟩` Kraus operators, `idealResetErasure` at Landauer equality, 0 sorry ✓
- **Quantum mutual information**: `QuantumMutualInfo.lean` — `I(A:B) = S(A)+S(B)-S(AB)`, upper bound, product-state zero, 0 sorry ✓
- **General-`n` residual coherence** (`GeneralResidualCoherence.lean`): purity-based `RCC_n`, Cauchy-Schwarz from first principles, qubit compatibility proved, `trace_sq_le_one` sorry eliminated ✓
- **Matplotlib animation / GIF export**: `scripts/generate_sim_gifs.py` — 1D/2D wave GIFs with `--validate` flag; `make sim-gifs` / `make sim-gifs-validate` ✓
- **`lean4checker`**: independent Lean kernel re-verification of `.olean` files added to `.github/workflows/lean.yml` ✓
- **`WhichPathMeasurementUpdate`**: split from `DoubleSlit` to break import cycle with `EpistemicSensing` ✓
