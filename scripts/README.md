# Maintenance scripts

| Script | Usage |
|--------|--------|
| `lean_decl_stats.py` | Heuristic counts of `theorem` / `lemma` / `def` / … in `Lean/**/*.lean` (skips `.lake`). |

From repo root:

```bash
make lean-stats      # plain text
make lean-stats-md   # markdown bullets → paste into `PROOF-STATUS.md`
```

Avoid editing this script in the same PR as large `PROOF-STATUS` rewrites unless intentional.

Full local verification including Haskell: from repo root run **`make ci-full`** (see root **`Makefile`** / **`CONTRIBUTING.md`**).
