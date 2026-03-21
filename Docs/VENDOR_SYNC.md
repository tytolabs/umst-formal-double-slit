# Vendored formal artifacts — how to keep them aligned

Parent repo (typical path: `../umst-formal`). This fork vendors a **slice** of its Lean/Haskell/Coq/Agda so `umst-formal-double-slit` stays **self-contained**.

## Files to diff when upstream changes

| Area | Paths here | Typical upstream paths |
|------|------------|-------------------------|
| Landauer stack | `Lean/LandauerLaw.lean`, `LandauerExtension.lean`, `LandauerEinsteinBridge.lean` | same under `Lean/` |
| UMST ℚ core + activation | `Lean/Gate.lean`, `Naturality.lean`, `Activation.lean`, `FiberedActivation.lean`, `MonoidalState.lean` | same |
| Haskell parity | `Haskell/src/LandauerExtension.hs`, `MonoidalState.hs` | `Haskell/*.hs` |
| Rational sanity test | `Haskell/test/LandauerEinsteinSanity.hs` | `Haskell/test/LandauerEinsteinSanity.hs` |
| Coq bridge | `Coq/LandauerEinsteinBridge.v` | `Coq/LandauerEinsteinBridge.v` |
| Agda stub | `Agda/LandauerEinsteinTrace.agda` | `Agda/LandauerEinsteinTrace.agda` |

After copying, always run **`cd Lean && lake build`**, **`make ci-full`**, and (if installed) **`make coq-check`** / **`make agda-check`**.

## Recommendations

1. **Do not merge `Gate.lean` into `UMSTCore.lean`.** The fork keeps **ℝ** operational scaffolding (`UMSTCore`) for quantum/classical composition separate from the **ℚ** UMST core (`Gate`).
2. **Haskell `landauerBitEnergy`:** defined in both `DoubleSlit` (used by measurement layers) and `LandauerExtension` (parent parity). Tests use **`import qualified LandauerExtension as LE`** for extension-only props; consider a single re-export module later if duplication becomes painful.
3. **FiberedActivation:** parent has **no** Haskell mirror — do not invent one without a Lean↔Haskell spec review.
4. **CI:** Coq/Agda checks are **Makefile-only** today. Add a workflow job if branch protection should enforce them (install `coq` / `agda` on Ubuntu runners; cache opam if needed).
5. **Growing `Coq/` / `Agda/`:** extend `_CoqProject` and Agda `Makefile` like parent only after updating **`PARALLEL_WORK.md`** so swarm agents don’t collide.
