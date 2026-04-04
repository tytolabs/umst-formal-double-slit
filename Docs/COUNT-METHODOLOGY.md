# Lean declaration counts — methodology

**Authoritative summary:** [FORMAL_FOUNDATIONS.md](../FORMAL_FOUNDATIONS.md) (Wave 6.5.1+).

## Rules

- **Lake roots:** Parsed from [`Lean/lakefile.lean`](../Lean/lakefile.lean) by [`scripts/lean_declaration_stats.py`](../scripts/lean_declaration_stats.py).
- **`theorem` / `lemma`:** Line-start `theorem ` / `lemma ` in each root module; **roots-only** vs **all `Lean/*.lean`** (includes tests and optional files not in `roots`) are reported separately in `FORMAL_FOUNDATIONS.md`.
- **Project `axiom`:** Should be only `physicalSecondLaw` in `LandauerLaw.lean` (visibility and dephasing limits are **theorems**).

## Regenerate

```bash
python3 scripts/lean_declaration_stats.py
python3 scripts/lean_declaration_stats.py --json
```
