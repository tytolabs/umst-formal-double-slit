<!--
SPDX-License-Identifier: MIT
Copyright (c) 2026 Santhosh Shyamsundar, Santosh Prabhu Shenbagamoorthy — Studio TYTO
-->

# Agda (`Agda/`)

Spec modules mirror the Lean narrative (density matrices, complementarity, entropy, gate, activation). **Authority for full proofs** remains Lean unless a lemma is proved locally.

## Requirements

- **Agda** 2.6+ with the **Agda standard library** that matches your Agda (e.g. 2.8.x + bundled stdlib).
- From repo root, all modules type-check via:

```bash
make agda-check
```

Or the combined formal track:

```bash
make formal-check    # Coq + Agda
# or
./scripts/formal_check.sh
```

`make agda-check` runs every `*.agda` entry module in dependency order (see root **`Makefile`**).

## CI

`.github/workflows/formal.yml` installs Agda from Ubuntu packages and runs `make agda-check`. If your local stdlib layout differs from CI, set `AGDA_DIR` / library files as usual for your installation.

## Notes

- Rationals like **100** and **450** in `Gate.agda` / `Helmholtz.agda` use a small `natToℚ` helper so we do not depend on coprimality lemma names that changed across stdlib versions.
