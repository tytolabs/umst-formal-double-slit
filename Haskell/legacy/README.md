<!--
SPDX-License-Identifier: MIT
Copyright (c) 2026 Santhosh Shyamsundar, Santosh Prabhu Shenbagamoorthy — Studio TYTO
-->

# Legacy Haskell mirrors (not built)

Older copies of modules that also live under `src/`. They were kept at the package root for historical reference but **must not** sit next to `src/` while Cabal passes GHC `-i` (current package dir): otherwise they **shadow** the `src/` modules and break the build.

**Canonical library sources:** `../src/*.hs` as listed in `../umst-formal-double-slit.cabal`.
