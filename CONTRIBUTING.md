# Contributing — `umst-formal-double-slit`

## Before you open a PR

1. From repo root: **`make ci-local`** (Lean + Python sim + `unittest`).
2. Optional: **`make haskell-test`** if you touch `Haskell/` (matches `haskell.yml` CI), or **`make ci-full`** for `ci-local` + Haskell in one command.
3. If you use optional Python stacks locally: **`pip install -r sim/requirements-optional.txt`** so QuTiP / matplotlib tests don’t skip.
4. Multi-agent / swarm edits: read **`Docs/PARALLEL_WORK.md`** (hot paths + **suggested next jobs** table) and avoid duplicating work without checking files already exist.

## Lean

- `cd Lean && lake build` (or `make lean`) after changing any `.lean` or `lakefile.lean`.
- **`make lean-stats`** / **`make lean-stats-md`** — heuristic Lean decl counts (`scripts/lean_decl_stats.py`, `--markdown` for paste into docs). See **`scripts/README.md`**.

## Python

- Default pipeline is **stdlib** for the SVG plotters; optional **matplotlib / imageio / QuTiP** live in `sim/requirements-optional.txt` (also installed in GitHub Actions before tests).

## Haskell

- The **`Haskell/`** package is developed in parallel (QuickCheck / mirroring Lean). Prefer **not** editing `Haskell/*` from the Lean/Python agent session unless you own that track; verify with **`make haskell-test`** or `cabal test` from `Haskell/`. If you change **`build-depends`** in the `.cabal` file, run **`cabal freeze`** and commit **`cabal.project.freeze`**.

## Where to document changes

- User-facing summary: **`CHANGELOG.md`**
- Theorem / build status: **`PROOF-STATUS.md`**, **`Lean/VERIFY.md`**
