# Lean export tools

## Canonical export (drift pins)

**`make lean-catalog-export`** (Python `export_catalog.py`) is the **only** supported path for
`artifacts/catalog.json` and `artifacts/catalog.lock.json` used by CI, `verify_umst_stack.sh`,
and **umst-manifold** digest pins. See `artifacts/README.md` (Lake vs Python).

## Catalog JSON (`export_catalog`)

Emits a **machine-readable** index of the default Lake `roots` for `lean_lib «UMST.DoubleSlit»` (see `Lean/lakefile.lean`). Output path: **`artifacts/catalog.json`** at the repository root (directory is created if missing).

### Run

From the **Lean package** directory (same as CI):

```bash
cd Lean
lake exe export_catalog
```

From the **repository root** without changing your shell directory:

```bash
(cd Lean && lake exe export_catalog)
```

If the native binary fails to launch on your host (rare macOS `dyld` loader issues with some
toolchain builds), build the module and run the same `main` via the Lean evaluator:

```bash
cd Lean
lake build ExportCatalog
lake env lean ../tools/lean_export/ExportCatalogSmoke.lean
```

### Related: Python `export_catalog.py` (canonical)

`make lean-catalog-export` invokes **`export_catalog.py`** for the **full** catalog and lock.
Use **`--roots-only`** on the same script (writes `artifacts/catalog-roots.json` by default)
if you need the compact `{ version, entries }` root list without running Lake.

### Cross-repo export (preview + gated merge)

```bash
python3 tools/lean_export/export_catalog.py \
  --lean-root Lean \
  --also-lean-root ../umst-formal/Lean \
  --also-lean-repo-tag umst-formal \
  --cross-repo-only
```

Preview always includes per-module `repo` tags. Default (no env) keeps canonical
`catalog.json` primary-only. Set `APPROVE_CROSS_REPO_MERGE=1` to write a unified catalog.
See `Docs/EXPORT_COVERAGE.md` § Cross-repo export.

The **`lake exe export_catalog`** path is optional and must **not** replace the pinned
`artifacts/catalog.json` used for drift (different schema; see `artifacts/README.md`).

### Schema

Top level:

| Field       | Type   | Meaning |
|------------|--------|---------|
| `version`  | string | Catalog format version (bump when shape changes). |
| `entries`  | array  | Catalog records. |

Each `entries[]` object:

| Field    | Type   | Meaning |
|----------|--------|---------|
| `id`     | string | Stable id (currently the full Lean module name). |
| `module` | string | Lean module name, e.g. `UMST.DoubleSlit.UMSTCore`. |
| `kind`   | string | Always `root` for this exporter. |
| `name`   | string | Short root name (Lake root component). |

### Maintenance

The pinned list lives in `ExportCatalog.lean` (`pinnedRootNames`). When you add or remove a root in `Lean/lakefile.lean`, update that array so the JSON stays accurate.
