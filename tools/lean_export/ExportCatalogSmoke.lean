SPDX-FileCopyrightText: 2026 Santosh Prabhu Shenbagamoorthy and Santhosh Shyamsundar
SPDX-License-Identifier: MIT
/-

Smoke entry point: `lake env lean ../tools/lean_export/ExportCatalogSmoke.lean` from `Lean/`
runs `ExportCatalog.main` without executing the compiled `export_catalog` binary — useful when
native `lake exe` hits platform loader issues while the evaluator still works.

See README.md in this directory.
-/

import ExportCatalog

#eval main []
