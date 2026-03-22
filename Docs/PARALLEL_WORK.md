<!--
SPDX-License-Identifier: MIT
Copyright (c) 2026 Santhosh Shamsundar, Santosh Prabhu Shenbagamoorthy — Studio TYTO
-->

# Multi-agent / parallel work

**Canonical swarm split (tracks A–I, dependency notes):** [`Docs/SWARM_WORK.md`](SWARM_WORK.md).

**Choke points (serialize merges):**

- `Lean/lakefile.lean` — adding roots / import order
- `README.md` / `PROOF-STATUS.md` — stats and badge claims (refresh after large Lean edits)

**CI:** `.github/workflows/lean.yml` runs `lake build` then **lean4checker** (independent `.olean` verification).
