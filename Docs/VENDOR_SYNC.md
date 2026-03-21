# Vendored formal artifacts — how to keep them aligned

Upstream reference is typically **`../umst-formal`** (or your fork). This repo vendors a **slice** of its Lean/Haskell/Coq/Agda so the double-slit checkout stays **self-contained**.

## Files to diff when upstream changes

| Area | Paths here | Typical upstream paths |
|------|------------|-------------------------|
| Landauer stack | `Lean/LandauerLaw.lean`, `LandauerExtension.lean`, `LandauerEinsteinBridge.lean` | same under `Lean/` |
| UMST ℚ core + activation | `Lean/Gate.lean`, `Naturality.lean`, `Activation.lean`, `FiberedActivation.lean`, `MonoidalState.lean` | same |
| Haskell parity | `Haskell/src/LandauerExtension.hs`, `MonoidalState.hs` | `Haskell/*.hs` |
| Rational sanity test | `Haskell/test/LandauerEinsteinSanity.hs` | `Haskell/test/LandauerEinsteinSanity.hs` |
| Coq bridge | `Coq/LandauerEinsteinBridge.v` | `Coq/LandauerEinsteinBridge.v` |
| Agda stub | `Agda/LandauerEinsteinTrace.agda` | `Agda/LandauerEinsteinTrace.agda` |

After copying, run **`cd Lean && lake build`**, **`make ci-full`**, and (if installed) **`make coq-check`** / **`make agda-check`**.

## Recommendations

1. **Do not merge `Gate.lean` into `UMSTCore.lean`.** Keep **ℝ** `UMSTCore` (quantum/classical scaffold) separate from **ℚ** `Gate` (UMST L₀ core).
2. **Haskell `landauerBitEnergy`:** appears in both `DoubleSlit` and `LandauerExtension`; tests use `import qualified LandauerExtension as LE` where needed.
3. **FiberedActivation:** upstream has **no** Haskell mirror — don’t invent one without a spec review.
4. **CI:** Coq/Agda are **Makefile-only** unless you add a workflow job.
5. **Growing `Coq/` / `Agda/`:** update `_CoqProject` / Agda layout only after coordinating in **`Docs/PARALLEL_WORK.md`**.
