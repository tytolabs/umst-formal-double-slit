SPDX-FileCopyrightText: 2026 Santosh Prabhu Shenbagamoorthy and Santhosh Shyamsundar
SPDX-License-Identifier: MIT
<!--
-->

# Maintenance scripts

| Script | Usage |
|--------|--------|
| `lean_decl_stats.py` | Heuristic counts of `theorem` / `lemma` / `def` / … in `Lean/**/*.lean` (skips `.lake`). |
| `add_spdx_headers.py` | Idempotently prepends MIT `SPDX-License-Identifier` + copyright to `Lean/**/*.lean`, `sim/**/*.py`, `scripts/**/*.py`, `Haskell/**/*.hs`, `Coq/**/*.v`, `Agda/**/*.agda`, `Docs/*.tex`, repo `*.md` (skips `.lake`, `dist-newstyle`, `.pytest_cache`, …). |
| `formal_check.sh` | Runs **`make formal-check`** (Coq + Agda) from repo root; same as CI **`.github/workflows/formal.yml`**. |

From repo root:

```bash
make lean-stats      # plain text
make lean-stats-md   # markdown bullets → paste into `PROOF-STATUS.md`
```

Avoid editing this script in the same PR as large `PROOF-STATUS` rewrites unless intentional.

Full local verification including Haskell: from repo root run **`make ci-full`** (see root **`Makefile`** / **`CONTRIBUTING.md`**).

Formal verification (optional toolchains): **`make formal-check`** or **`./scripts/formal_check.sh`**; see **`Coq/README.md`** and **`Agda/README.md`**.
