# Scope: this repo vs upstream reference, and going standalone

Plain-language map of **what lives in this folder** vs **what lives elsewhere**.

## Vocabulary

| Phrase | Meaning |
|--------|---------|
| **This repo / this checkout** | Everything under `umst-formal-double-slit/`. If it is not on disk here, it is not “done” for *this* product. |
| **Upstream / `umst-formal`** | The wider UMST formal project. Some coordination docs refer to files that exist **there**; vendored copies here are listed in **`Docs/VENDOR_SYNC.md`**. |
| **Separate repo** | You may `git init` or point `origin` at a remote that tracks **only** this tree; sync with upstream manually if you want. |

## What is solid *here*

- **Lean:** `lake build`; double-slit stack; vendored `LandauerLaw` / `Gate` / `MonoidalState` / … (see **`Lean/VERIFY.md`**).
- **Haskell:** `cabal test` (two suites).
- **Python:** `sim/` scripts + `sim/tests/` (optional deps widen coverage).
- **Coq / Agda:** minimal trees + `make coq-check` / `make agda-check`.

## What is still open *here*

- **`p3-epistemic-sensing`:** runtime / ODE–PPO evidence vs `Epistemic*` lemmas.
- **Richer `InfoEntropy`**, concrete erasure vs Landauer beyond current hooks.
- **Full A0 Coq/Agda parity** beyond `LandauerEinsteinBridge.v` + Agda trace stub.
- **Sim roadmap:** PML, 3D, sparse QuTiP, etc. (see **`sim/README.md`**).

## Housekeeping

- Re-paste **`make lean-stats-md`** into **`PROOF-STATUS.md`** after large Lean edits.
- If **branch protection** requires CI on every PR, note **`paths` filters** in workflows may skip doc-only changes — widen paths or add a no-op check job if needed.
