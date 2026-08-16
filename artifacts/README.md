SPDX-FileCopyrightText: 2026 Santosh Prabhu Shenbagamoorthy and Santhosh Shyamsundar
SPDX-License-Identifier: MIT
# Lean catalog artifacts

Machine-readable exports of the UMST.DoubleSlit Lean tree for downstream consumers (e.g. **umst-manifold**).

| File | Role |
|------|------|
| `catalog.json` | Full module index: per-file SHA-256, declaration names, import lines, and a coarse import graph. |
| `catalog.lock.json` | Pin file: canonical `catalog_digest_hex` and `module_count` (must match `catalog.json`). |
| `catalog-cross-repo-preview.json` | **Dry-run only** (`--also-lean-root`); not used for CI pins. Regenerated on demand; optional local file. |

Cross-repo preview (scaffold):

```bash
python3 tools/lean_export/export_catalog.py \
  --lean-root Lean \
  --also-lean-root ../umst-formal/Lean \
  --also-lean-repo-tag umst-formal \
  --cross-repo-only
```

See `Docs/EXPORT_COVERAGE.md` § Cross-repo dry-run scaffold.

## Lake vs Python (do not mix)

Two exporters exist; they produce **different JSON shapes** on purpose:

| Path | Tool | Schema | Used for drift / pins |
|------|------|--------|------------------------|
| **`make lean-catalog-export`** | `tools/lean_export/export_catalog.py` | `version`, `lean_root`, `modules[]`, `module_graph_edges`, **`digest`** | **Yes** — `catalog.lock.json` and **umst-manifold** `upstream_catalog_digest_hex` |
| `lake exe export_catalog` (in `Lean/`) | `ExportCatalog.lean` | `version`, `entries[]` (root list only) | **No** — auxiliary; same default filename would **overwrite** the pinned catalog |

**Canonical workflow:** always regenerate pinned artifacts with **`make lean-catalog-export`**. Do not point CI or `verify_umst_stack.sh` at `lake exe` for `artifacts/catalog.json`.

Optional compact root list (Lake-shaped, separate file):

```bash
python3 tools/lean_export/export_catalog.py --lean-root Lean --roots-only --roots-out artifacts/catalog-roots.json
```


## Regenerate (canonical)

From the repository root:

```bash
make lean-catalog-export
```

Equivalent:

```bash
python3 tools/lean_export/export_catalog.py --lean-root Lean --out artifacts/catalog.json
```

The exporter writes **`artifacts/catalog.lock.json`** next to the catalog (same digest and module count).

### Digest definition

The `digest` field in `catalog.json` is SHA-256 (hex, lowercase) of the JSON object **without** the `digest` key, serialized with `sort_keys=True` and compact separators `(",", ":")` (see `tools/lean_export/export_catalog.py`).

## Consistency checks

```bash
python3 - <<'PY'
import json, hashlib
from pathlib import Path

root = Path("artifacts")
cat = json.loads((root / "catalog.json").read_text())
lock = json.loads((root / "catalog.lock.json").read_text())
assert lock["catalog_digest_hex"] == cat["digest"]
assert lock["module_count"] == len(cat["modules"])
print("ok digest", cat["digest"], "modules", len(cat["modules"]))
PY
```

## umst-manifold coupling

**umst-manifold** `build.rs` hashes the **verbatim bytes** of its own `artifacts/catalog.lock.json` (role `manifold_runtime_lock`) into `UMST_CATALOG_LOCK_SHA256_HEX`. That lock records:

- `upstream_catalog_digest_hex` — must equal `catalog.json` → `digest` here
- `module_count` — must equal `len(modules)` here

After Lean changes, regenerate here, then update **umst-manifold** `artifacts/catalog.lock.json` if the digest or module count changed, and rebuild manifold:

```bash
cd ../umst-manifold && cargo build
```

Optional override at build time: `UMST_CATALOG=/path/to/catalog.lock.json`.

## Lake executable (optional)

Inside `Lean/` you can also run `lake exe export_catalog` (see `tools/lean_export/README.md`). The Makefile/Python path above is the supported CI/local workflow for pinned artifacts.
