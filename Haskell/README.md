# Haskell mirror (QuickCheck)

This package **mirrors** selected Lean definitions from the double-slit repository (`DensityState`, `MeasurementChannel`, `DoubleSlit`, **`LandauerExtension`**, **`MonoidalState`**, `MeasurementCost`, `EpistemicGalois`) for **property-based testing** and engineering sanity checks.

## Build & test

From **`umst-formal-double-slit/Haskell/`**:

```bash
cabal update
cabal build
cabal test   # runs `umst-formal-double-slit-test` + `landauer-einstein-sanity`
```

Project root is pinned by **`cabal.project`** (`packages: .`). **`cabal.project.freeze`** is committed for reproducible CI (run `cabal freeze` in `Haskell/` after changing `build-depends` in the `.cabal` file, then commit the updated freeze).

GHC / `base` bounds are set in `umst-formal-double-slit.cabal` (currently **GHC 9.14-era** `base`).

## Scope

- **Parity / core properties:** maintained by the dedicated Haskell track (do not duplicate that work from the Lean/Python side).
- **CI:** see `.github/workflows/haskell.yml` (runs `cabal test` on Ubuntu).

## CI

GitHub Actions caches the Cabal store and `dist-newstyle` (see `.github/workflows/haskell.yml`).

## Related

- Formal proofs: `../Lean/` + `../Lean/VERIFY.md`
- Tracking: `../Docs/TODO-TRACKING.md`
