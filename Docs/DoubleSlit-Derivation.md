# double-slit repository — derivation chain (Lean)

Human-readable map of what is **proved** in `umst-formal-double-slit/Lean/`. See `Lean/VERIFY.md` for theorem names and `PROOF-STATUS.md` for scope / non-claims.

## 1. Quantum layer

1. **`DensityMatrix`** — PSD + trace 1 (`DensityState.lean`).
2. **Kraus channel** — TP sum, `map` / `apply`, composition (`MeasurementChannel.lean`).
3. **Which-path (Lüders)** — `whichPathChannel` dephases to diagonal; diagonal entries fixed (`whichPath_map_eq_diagonal`, `whichPath_map_apply_entry`).

## 2. Path statistics ↔ coarse `(I, V)`

1. **Born weights** `pathWeight ρ i` from diagonal (`QuantumClassicalBridge.lean`).
2. **Coarse which-path score** `I = |p₀ − p₁|`, fringe visibility `V = 2|ρ₀₁|`.
3. **PSD constraint** → `|ρ₀₁|² ≤ p₀ p₁` → **Englert-style** `V² + I² ≤ 1` (`complementarity_fringe_path`).
4. **`ObservationState`** — `observationStateCanonical ρ`; **`MeasurementUpdate`** — `measurementUpdateWhichPath ρ` (`DoubleSlit.lean`): `I` invariant under Lüders on this readout, `V → 0`.

## 3. Entropy (binary, nats)

1. **`shannonBinary`** = Mathlib **`Real.binEntropy`** (`shannonBinary_eq_binEntropy`).
2. **`shannonBinary p ≤ log 2`**, hence **`vonNeumannDiagonal ρ ≤ log 2`** (`InfoEntropy.lean`).
3. Lüders which-path **does not change** diagonal entropy (`vonNeumannDiagonal_whichPath_apply`).

## 4. Landauer scale (hook, not heat)

1. **`pathEntropyBits ρ`** = `vonNeumannDiagonal ρ / log 2` ∈ `[0, 1]`.
2. **`landauerCostDiagonal ρ T`** = `k_B T log 2 × pathEntropyBits` (`LandauerBound.lean`).
3. **≤ one Landauer bit-energy** at same `T`: `landauerCostDiagonal ρ T ≤ landauerBitEnergy T`.
4. Invariant along `measurementUpdateWhichPath` (`landauerCostDiagonal_whichPathInvariant` / `measurementUpdateWhichPath_landauer_eq`).
5. Along that update, both endpoints satisfy **`landauerCostDiagonal ρ T ≤ landauerBitEnergy T`** (`measurementUpdateWhichPath_landauer_le_landauerBitEnergy`).

## 5. UMST gate shape (scaffold)

1. **`thermoFromQubitPath`** maps `(p₀, p₁)` into a minimal `ThermodynamicState` (`GateCompat.lean`).
2. **`Admissible`** before/after which-path (same scaffold) — `admissible_thermoFromQubitPath_whichPath`.

## 6. Worked examples (Lean)

- **`ExamplesQubit.rhoPlus`** (|+⟩): **`p₀ = p₁ = 1/2`**, **`V = 1`**, **`I = 0`**, maximal diagonal entropy / Landauer hook; **`measurementUpdateWhichPath`** ends with **`V = 0`**; **`ObservationState.ext`** proves coarse equality facts.
- **`ExamplesQubit.rhoZero`** / **`rhoOne`**: computational **|0⟩** / **|1⟩** — **`V = 0`**, **`I = 1`**, zero diagonal-entropy hook; **`measurementUpdateWhichPath`** **idle** on the coarse interface.

## Open (needs further design)

- Tie **`landauerCostDiagonal`** to **measured dissipation** (erasure / explicit bath model).
- Full **spatial** double-slit (fringe pattern in position basis), not only the path qubit.
- **Haskell/Python** checks and publication figures.
