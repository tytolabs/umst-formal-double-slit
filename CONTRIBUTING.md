# Contributing — `umst-formal-double-slit`

## Before you open a PR

1. From repo root: **`make ci-local`** (Lean + Python sim + `unittest`).
2. Gap 14 telemetry: **`make telemetry-sample`** (golden JSON export + consumer; also runs in **`lean.yml`** after unittests).
3. Optional: **`make haskell-test`** if you touch `Haskell/` (matches `haskell.yml` CI), or **`make ci-full`** for `ci-local` + Haskell in one command.
4. If you use optional Python stacks locally: **`pip install -r sim/requirements-optional.txt`** so QuTiP / matplotlib tests don’t skip.
5. Multi-agent / swarm edits: coordinate via issues/PRs and scan **`CHANGELOG.md`** for recent ownership; optional `Docs/*` tracking files may exist in some checkouts.
6. If you touch **`Coq/`** or **`Agda/`**: from repo root run **`make formal-check`** (or separately **`make coq-check`** / **`make agda-check`**). Toolchain notes: **`Coq/README.md`**, **`Agda/README.md`**. CI: **`.github/workflows/formal.yml`**.

## License (SPDX)

The repository is **MIT** (`LICENSE`). New **first-party** sources should carry:

- **Lean** — block at the **very top** of the file (before `import`):

  ```lean
  /-
  SPDX-License-Identifier: MIT
  Copyright (c) 2026 Santhosh Shyamsundar, Santosh Prabhu Shenbagamoorthy — Studio TYTO
  -/
  ```

- **Python** — after the shebang (if any), before docstrings/imports:

  ```python
  # SPDX-License-Identifier: MIT
  # Copyright (c) 2026 Santhosh Shyamsundar, Santosh Prabhu Shenbagamoorthy — Studio TYTO
  ```

- **Haskell** — at the **very top** (before `{-# LANGUAGE` / Haddock `---`):

  ```haskell
  -- SPDX-License-Identifier: MIT
  -- Copyright (c) 2026 Santhosh Shyamsundar, Santosh Prabhu Shenbagamoorthy — Studio TYTO
  ```

- **LaTeX** — after a leading `%!TEX` magic line (if present), else line 1:

  ```latex
  % SPDX-License-Identifier: MIT
  % Copyright (c) 2026 Santhosh Shyamsundar, Santosh Prabhu Shenbagamoorthy — Studio TYTO
  ```

- **Markdown** — HTML comment at the top (invisible on GitHub render):

  ```markdown
  <!--
  SPDX-License-Identifier: MIT
  Copyright (c) 2026 Santhosh Shyamsundar, Santosh Prabhu Shenbagamoorthy — Studio TYTO
  -->
  ```

- **Coq** — at the **very top** (before any other `(* … *)` banner):

  ```coq
  (* SPDX-License-Identifier: MIT *)
  (* Copyright (c) 2026 Santhosh Shyamsundar, Santosh Prabhu Shenbagamoorthy — Studio TYTO *)
  ```

- **Agda** — at the **very top** (before `{-|` or `{-# OPTIONS`):

  ```agda
  -- SPDX-License-Identifier: MIT
  -- Copyright (c) 2026 Santhosh Shyamsundar, Santosh Prabhu Shenbagamoorthy — Studio TYTO
  ```

From repo root, **`python3 scripts/add_spdx_headers.py`** idempotently adds the above to **`Lean/**/*.lean`** (skips **`.lake`**), **`sim/**/*.py`**, **`scripts/**/*.py`**, **`Haskell/**/*.hs`** (skips **`dist-newstyle`**, **`dist`**, **`.stack-work`**), **`Coq/**/*.v`**, **`Agda/**/*.agda`**, **`Docs/*.tex`**, and **repo-wide `*.md`** (skips **`.pytest_cache`**, etc.). **Do not** retarget it at vendored trees.

## Lean

- `cd Lean && lake build` (or `make lean`) after changing any `.lean` or `lakefile.lean`.
- **`make lean-stats`** / **`make lean-stats-md`** — heuristic Lean decl counts (`scripts/lean_decl_stats.py`, `--markdown` for paste into docs). See **`scripts/README.md`**.

## Python

- Default pipeline is **stdlib** for the SVG plotters; optional **matplotlib / imageio / QuTiP** live in `sim/requirements-optional.txt` (also installed in GitHub Actions before tests).
- **Gap 14:** `sim/telemetry_trace_consumer.py` + `sim/export_sample_telemetry_trace.py` need **NumPy** (in optional requirements). See **`sim/README.md`** (*Telemetry trace consumer*) and **`Lean/VERIFY.md`** (`SimLeanBridge` + epistemic runtime modules).

## Haskell

- The **`Haskell/`** package is developed in parallel (QuickCheck / mirroring Lean). Prefer **not** editing `Haskell/*` from the Lean/Python agent session unless you own that track; verify with **`make haskell-test`** or `cabal test` from `Haskell/`. If you change **`build-depends`** in the `.cabal` file, run **`cabal freeze`** and commit **`cabal.project.freeze`**.

## Coq / Agda

- **`make coq-check`** — all `Coq/*.v` (Rocq/Coq 9.x or 8.20+ with `From Stdlib`). See **`Coq/README.md`** and **`Coq/_CoqProject`**.
- **`make agda-check`** — all Agda entry modules in dependency order (Agda 2.6+ + matching stdlib). See **`Agda/README.md`**.
- **`make formal-check`** or **`scripts/formal_check.sh`** — both tracks in one go.

## Where to document changes

- User-facing summary: **`CHANGELOG.md`**
- Theorem / build status: **`PROOF-STATUS.md`**, **`Lean/VERIFY.md`**
